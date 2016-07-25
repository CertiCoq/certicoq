(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import L2.compile.
Require L2.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Defs := L2.compile.Defs.
Definition L2EC := L2.compile.envClass.
Definition L2Env := L2.compile.environ.
Definition L2Pgm := L2.compile.Program.


Inductive Term : Type :=
| TRel       : nat -> Term
| TSort      : Srt -> Term
| TProof     : Term
| TProd      : name -> Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term -> Term
| TConst     : string -> Term
| TAx        : Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat -> Terms -> Term
| TCase      : nat * list nat (* #parameters, args per branch *) ->
               Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsDefs_ind from Trm_ind', Trms_ind', Defs_ind'.
Combined Scheme TrmTrms_ind from Trm_ind', Trms_ind'.
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation tunit t := (tcons t tnil).

Fixpoint tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Fixpoint tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.


(** turn (App fn [x1;...;xn]) into (App (... (App fn x1) x2 ...) xn) **)
Function mkApp (fn:Term) (xs:Terms) : Term :=
    match xs with
      | tnil => fn
      | tcons b ys => mkApp (TApp fn b) ys
    end.

(** turn (Constructor [x1;...;xn; 0;...k]])  with arity n+k into
*** (Lam ... (Lam (Const [x1;...;xn; 0;...k])...))
**)
Function mkEta (cstr:Term) (xtraArity:nat) : Term :=
    match xtraArity with
      | 0 => cstr
      | S n => mkEta (TLambda nAnon cstr) n
    end.

Lemma mkEta_under_Lambda:
  forall n t, mkEta (TLambda nAnon t) n = TLambda nAnon (mkEta t n).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.


(** Lookup constructor arity in L2 environ (to avoid mutual dependency
*** between converting L2 terms to L3 and L2 environs to L3)
**)
Section EtaExpand.
Variable p: AstCommon.environ L2.compile.Term.

(** compute list of variables for eta expanding a constructor
*** (which may already be partially applied)
**)
Function etaArgs (n:nat) : Terms :=
  match n with
    | 0 => tnil
    | S m => tcons (TRel m) (etaArgs m)
  end.

Function etaExp_cnstr (i:inductive) (n:nat) (args:Terms) : exception Term :=
  match cnstrArity p i n with
    | Ret arity =>
      match nat_compare (tlength args) arity with
        | Eq => Ret (TConstruct i n args)
        | Lt => let k := arity - (tlength args)
                in Ret (mkEta (TConstruct i n (tappend args (etaArgs k))) k)
        | Gt => Exc ("more arguments than constructor arity: "
                       ++ (nat_to_string (tlength args)) ++ (" ")
                       ++ (nat_to_string arity))
      end
    | Exc x => Exc x
  end.

Function strip (t:L2Term) : exception Term :=
  match t with
    | L2.compile.TProof => Ret TProof
    | L2.compile.TRel n => Ret (TRel n)
    | L2.compile.TSort s => Ret (TSort s)
    | L2.compile.TCast s => strip s
    | L2.compile.TProd nm bod => 
      match strip bod with
        | Ret sbod => Ret (TProd nm sbod)
        | x => x
      end
    | L2.compile.TLambda nm bod =>
      match strip bod with
        | Ret sbod => Ret (TLambda nm sbod)
        | x => x
      end
    | L2.compile.TLetIn nm dfn bod => 
      match strip dfn, strip bod with
        | Ret sdfn, Ret sbod => Ret (TLetIn nm sdfn sbod)
        | Exc s, Ret _ => Exc ("strip dfn fails:" ++ s)
        | Ret _, Exc s => Exc ("strip bod fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip dfn and strip bod fail"
      end
    | L2.compile.TApp fn arg args =>
      match strip arg, strips args with
        | Ret sarg, Ret sargs =>
          match fn with 
            | L2.compile.TConstruct i n => etaExp_cnstr i n (tcons sarg sargs)
            | x => match strip x with
                     | Ret sx => Ret (mkApp sx (tcons sarg sargs))
                     | x => x
                   end
          end
        | Exc s, Ret _ => Exc ("strip arg fails:" ++ s)
        | Ret _, Exc s => Exc ("strips args fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip arg and strips args fail"
      end
    | L2.compile.TConst nm =>
      match L2.program.lookup nm p with
        | Some (AstCommon.ecTrm _) => Ret (TConst nm)
        | Some (AstCommon.ecTyp _ 0 nil) => Ret (TAx)
        | Some (AstCommon.ecTyp _ _ _) =>
          Exc "L2.compile.lookup nm p returns a type"
        | None => Exc "L2.compile.lookup nm p misses"
      end
    | L2.compile.TInd i => Ret (TInd i)
    | L2.compile.TConstruct i n => etaExp_cnstr i n tnil
    | L2.compile.TCase n mch brs =>
      match strip mch, strips brs with
        | Ret smch, Ret sbrs => Ret (TCase n smch sbrs)
        | Exc s, Ret _ => Exc ("strip mch fails:" ++ s)
        | Ret _, Exc s => Exc ("strips brs fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip mch and strips brs fail"
      end
    | L2.compile.TFix ds n =>
      match stripDs ds with
        | Ret sds => Ret (TFix sds n)
        | Exc s => Exc "stripDs ds fails"
      end
   end
with strips (ts:L2Terms) : exception Terms := 
  match ts with
    | L2.compile.tnil => Ret tnil
    | L2.compile.tcons t ts =>
      match strip t, strips ts with
        | Ret st, Ret sts => Ret (tcons st sts)
        | Exc s, Ret _ => Exc ("strip t fails:" ++ s)
        | Ret _, Exc s => Exc ("strips ts fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip t and strips ts fail"
      end
  end
with stripDs (ts:L2Defs) : exception Defs := 
  match ts with
    | L2.compile.dnil => Ret dnil
    | L2.compile.dcons nm t m ds =>
      match strip t, stripDs ds with
        | Ret st, Ret sds => Ret (dcons nm st m sds)
        | Exc s, Ret _ => Exc ("strip t fails:" ++ s)
        | Ret _, Exc s => Exc ("stripDs ds fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip t and stripDs ds fail"
      end
  end.
Functional Scheme strip_ind' := Induction for strip Sort Prop
with strips_ind' := Induction for strips Sort Prop
with stripDs_ind' := Induction for stripDs Sort Prop.
(*** Anomaly: Uncaught exception Term.DestKO. Please report.
Combined Scheme stripStripsStripDs_ind
         from strip_ind', strips_ind', stripDs_ind'.
***)


Function stripEC (ec:L2EC) : exception (AstCommon.envClass Term) :=
  match ec with
    | AstCommon.ecTrm t =>
      match strip t with
        | Ret u => ret (ecTrm u)
        | Exc s => raise ("L3.compile, stripEC: " ++ s)
      end
    | AstCommon.ecTyp _ n itp => ret (ecTyp _ n itp)
  end.

End EtaExpand.

Function stripEnv (p:L2Env) : exception (AstCommon.environ Term) :=
  match p with
    | nil => Ret nil
    | cons (nm, AstCommon.ecTyp _ 0 nil) q =>   (** remove axioms from env **)
      stripEnv q
    | cons (nm, ec) q =>
      match stripEC q ec, stripEnv q with
        | Ret u, Ret r => Ret (cons (nm, u) r)
        | Exc s, Ret _ => Exc ("strip q t fails:" ++ s)
        | Ret _, Exc s => Exc ("stripEnv q fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip q t and stripEnv q fail"
      end
  end.

Definition stripProgram (p:L2Pgm) : exception (AstCommon.Program Term) :=
  match stripEnv (AstCommon.env p),
        strip (AstCommon.env p) (AstCommon.main p) with
    | Ret q, Ret t => ret {| env:= q; main:= t |}
    | _, _ => raise ("L3 stripProgram; fails")
  end.


(** L0-to-L3 translations **)
Definition program_Program (p:program) : exception  (AstCommon.Program Term) :=
  match L2.compile.program_Program p with
    | Ret q => stripProgram q
    | Exc str => raise ("L3 program_Program: " ++ str)
  end.
Definition term_Term (e:L2.compile.environ) (t:term) : exception Term :=
  match L2.compile.term_Term t with
    | Exc str => raise ("L2.compile.term_Term failed: " ++ str)
    | Ret trm => strip e trm
  end.

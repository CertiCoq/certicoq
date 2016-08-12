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
Definition L2EC := envClass L2Term.
Definition L2Env := environ L2Term.
Definition L2Pgm := Program L2Term.


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
| TConstruct : inductive -> nat (* index *) ->
               nat (* arity *) -> Terms -> Term
| TCase      : inductive * nat * list nat (* # pars, args per branch *) ->
               Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
| TWrong : Term
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


(** compute list of variables for eta expanding a constructor
*** (which may already be partially applied)
**)
Function etaArgs (n:nat) : Terms :=
  match n with
    | 0 => tnil
    | S m => tcons (TRel m) (etaArgs m)
  end.

Function etaExp_cnstr (i:inductive) (n arity:nat) (args:Terms) : Term :=
  match nat_compare (tlength args) arity with
    | Datatypes.Eq => (TConstruct i n arity args)
    | Lt => let k := arity - (tlength args)
            in (mkEta (TConstruct i n arity (tappend args (etaArgs k))) k)
    | Gt => TWrong
  end.

Function strip (t:L2Term) : Term :=
  match t with
    | L2.compile.TProof => TProof
    | L2.compile.TRel n => (TRel n)
    | L2.compile.TSort s => (TSort s)
    | L2.compile.TCast s => strip s
    | L2.compile.TProd nm bod => TProd nm (strip bod)
    | L2.compile.TLambda nm bod => TLambda nm (strip bod)
    | L2.compile.TLetIn nm dfn bod => TLetIn nm (strip dfn) (strip bod)
    | L2.compile.TApp fn arg args =>
      let sarg := strip arg in
      let sargs := strips args in
      match fn with 
        | L2.compile.TConstruct i n arty =>
          etaExp_cnstr i n arty (tcons sarg sargs)
        | x => mkApp (strip x) (tcons sarg sargs)
       end
    | L2.compile.TConst nm => TConst nm
    | L2.compile.TAx => TAx
    | L2.compile.TInd i => (TInd i)
    | L2.compile.TConstruct i n arity => etaExp_cnstr i n arity tnil
    | L2.compile.TCase n mch brs => TCase n (strip mch) (strips brs)
    | L2.compile.TFix ds n => TFix (stripDs ds) n
    | L2.compile.TWrong => TWrong
   end
with strips (ts:L2Terms) : Terms := 
  match ts with
    | L2.compile.tnil => tnil
    | L2.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripDs (ts:L2Defs) : Defs := 
  match ts with
    | L2.compile.dnil => dnil
    | L2.compile.dcons nm t m ds => dcons nm (strip t) m (stripDs ds)
  end.
Functional Scheme strip_ind' := Induction for strip Sort Prop
with strips_ind' := Induction for strips Sort Prop
with stripDs_ind' := Induction for stripDs Sort Prop.
(*** Anomaly: Uncaught exception Term.DestKO. Please report. ***
Combined Scheme stripStripsStripDs_ind
         from strip_ind', strips_ind', stripDs_ind'.
***)


Function stripEC (ec:L2EC) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp _ n itp
  end.


Function stripEnv (p:L2Env) : environ Term :=
  match p with
    | nil => nil
               (****************
    | cons (nm, ecTyp _ _ nil) q =>  stripEnv q  (** remove axioms from env **)
***********************)
    | cons (nm, ec) q => cons (nm, stripEC ec) (stripEnv q)
  end.

Definition stripProgram (p:L2Pgm) : AstCommon.Program Term :=
  {| env:= stripEnv (env p); main:= strip (AstCommon.main p) |}.


(** L1-to-L3 translations **)
Definition program_Program (p:program) : Program Term :=
  stripProgram (L2.compile.program_Program p).

(*******************
Definition term_Term' (e:L2.compile.environ) (t:term) : Term  :=
  strip e (L2.compile.term_Term t).
************************)

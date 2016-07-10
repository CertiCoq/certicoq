
(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Export Template.Ast.
Require Import Common.Common.
Require Import L1.compile.


Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1Term := L1.compile.Term.
Definition L1Terms := L1.compile.Terms.
Definition L1Defs := L1.compile.Defs.
Definition L1EC := L1.compile.envClass.
Definition L1Env := L1.compile.environ.
Definition L1Pgm := L1.compile.Program.


Inductive Term : Type :=
| TRel       : nat -> Term
| TSort      : Srt -> Term
| TProof     : Term
| TCast      : Term -> cast_kind -> Term -> Term
| TProd      : name -> Term (* type *) -> Term -> Term
| TLambda    : name -> Term (* type *) -> Term -> Term
| TLetIn     : name ->
               Term (* dfn *) -> Term (* type *) -> Term (* body *) -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat -> Term
| TCase      : (nat * list nat) (* # of parameters, args per branch *) ->
               Term (* type info *) -> Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsDefs_ind from Trm_ind', Trms_ind', Defs_ind'.
Combined Scheme TrmTrms_ind from Trm_ind', Trms_ind'.
Scheme Trm_ind2 := Induction for Term Sort Type
  with Trms_ind2 := Induction for Terms Sort Type
  with Defs_ind2 := Induction for Defs Sort Type.
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation tunit t := (tcons t tnil).


(*** \box in case branches: need tappend, mkApp and instantiate ***)
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ _ ts => S (dlength ts)
  end.
(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
    | TApp fn b bs => TApp fn b (tappend bs args)
    | fn => match args with
              | tnil => fn
              | tcons c cs => TApp fn c cs
            end
  end.
Section Instantiate_sec.
Variable (tin:Term).
Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a ts =>
      mkApp (instantiate n t) (tcons (instantiate n a) (instantiates n ts))
    | TLambda nm ty bod =>
      TLambda nm (instantiate n ty) (instantiate (S n) bod)
    | TProd nm ty bod => TProd nm (instantiate n ty) (instantiate (S n) bod)
    | TCase np ty s ts =>
      TCase np (instantiate n ty) (instantiate n s) (instantiates n ts)
    | TLetIn nm tdef ty bod =>
      TLetIn nm (instantiate n tdef) (instantiate n ty) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TCast t ck ty => TCast (instantiate n t) ck (instantiate n ty)
    | x => x
  end
with instantiates (n:nat) (args:Terms) {struct args} : Terms :=
       match args with
         | tnil => tnil
         | tcons t ts => tcons (instantiate n t) (instantiates n ts)
       end
with instantiateDefs (n:nat) (ds:Defs) {struct ds} : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm ty bod rarg ds =>
           dcons nm (instantiate n ty)
                 (instantiate n bod) rarg (instantiateDefs n ds)
       end.
Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop
with instantiates_ind' := Induction for instantiates Sort Prop
with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop.
End Instantiate_sec.

Fixpoint applyBranchToProof (br:Term) :=
  match br with
    | TLambda _ _ body => instantiate TProof 0 (applyBranchToProof body)
    | x => x
  end.

Function L1Term_Term (t:L1Term) : Term :=
  match t with
    | L1.compile.TRel n => TRel n
    | L1.compile.TSort srt => TSort srt
    | L1.compile.TCast _ _ (L1.compile.TCast _ _ (L1.compile.TSort SProp)) =>
      TProof
    | L1.compile.TCast tm ck ty =>
      TCast (L1Term_Term ty) ck (L1Term_Term tm)
    | L1.compile.TProd nm ty bod =>
      TProd nm (L1Term_Term ty) (L1Term_Term bod)
    | L1.compile.TLambda nm ty bod =>
      TLambda nm (L1Term_Term ty) (L1Term_Term bod)
    | L1.compile.TLetIn nm dfn ty bod =>
      TLetIn nm (L1Term_Term dfn) (L1Term_Term ty) (L1Term_Term bod)
    | L1.compile.TApp fn arg args =>
      TApp (L1Term_Term fn) (L1Term_Term arg) (L1Terms_Terms args)
    | L1.compile.TConst pth => TConst pth
    | L1.compile.TInd ind => TInd ind
    | L1.compile.TConstruct ind m => TConstruct ind m
    | L1.compile.TCase m ty mch brs =>
      match L1Term_Term mch, L1Terms_Terms brs with
        | TProof, tunit br => applyBranchToProof br
        | Mch, Brs => TCase m (L1Term_Term ty) Mch Brs
      end
    | L1.compile.TFix defs m => TFix (L1Defs_Defs defs) m
  end
with L1Terms_Terms (ts:L1Terms) : Terms :=
       match ts with
         | L1.compile.tnil => tnil
         | L1.compile.tcons u us => tcons (L1Term_Term u) (L1Terms_Terms us)
       end
with L1Defs_Defs (ds:L1Defs) : Defs :=
       match ds with
         | L1.compile.dnil => dnil
         | L1.compile.dcons nm ty tm m ds =>
           dcons nm (L1Term_Term ty) (L1Term_Term tm) m (L1Defs_Defs ds)
       end.
(****
Functional Scheme L1Term_Term_ind' := Induction for L1Term_Term Sort Prop
with terms_Terms_ind' := Induction for terms_Terms Sort Prop
with wcbvDEvals_ind' := Induction for defs_Defs Sort Prop.
Combined Scheme L1Term_TermEvalsDEvals_ind
         from L1Term_Term_ind', terms_Terms_ind', wcbvDEvals_ind'.
***)

(** environments and programs **)
Definition envClass := AstCommon.envClass Term.
Definition environ := AstCommon.environ Term.
Definition Program := AstCommon.Program Term.

Function L1EC_EC (ec:L1EC) : envClass :=
  match ec with
    | ecTrm _ t => ecTrm Term (L1Term_Term t)
    | ecTyp _ n itp => ecTyp Term n itp
    | ecAx _ => ecAx Term
  end.

Definition L1Env_Env: L1Env -> environ :=
  List.map (fun (nmec: string * L1EC) => (fst nmec, L1EC_EC (snd nmec))).

Definition L1Pgm_Program (p:L1Pgm) : Program :=
  {| env:= L1Env_Env (env _ p);
     main:= L1Term_Term (main _ p) |}.


(*** from L0 to L1_5 ***)
Definition program_Program (p:program) : exception Program :=
  match L1.compile.program_Program p (Ret nil) with
    | Exc s => raise s
    | Ret q => Ret (L1Pgm_Program q)
  end.
Definition term_Term (t:term) : exception Term :=
  match L1.compile.term_Term t with
    | Exc s => raise s
    | Ret q => Ret (L1Term_Term q)
  end.

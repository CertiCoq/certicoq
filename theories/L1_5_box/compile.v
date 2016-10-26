
(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Export Template.Ast.
Require Import Common.Common.
Require Import L1g.compile.


Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gDefs := L1g.compile.Defs.
Definition L1gEC := envClass L1gTerm.
Definition L1gEnv := environ L1gTerm.
Definition L1gPgm := Program L1gTerm.


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
| TAx        : Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat (* index in datatype *) ->
               nat (* arity *) -> Term
| TCase      : (inductive * nat * list nat) (* # of parameters, args per branch *) ->
               Term (* type info *) -> Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : Term
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
                  | Datatypes.Eq => tin
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
    | TCast t ck ty => instantiate n t
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

Function L1gTerm_Term (t:L1gTerm) : Term :=
  match t with
    | L1g.compile.TRel n => TRel n
    | L1g.compile.TSort srt => TSort srt
    | L1g.compile.TCast _ _ (L1g.compile.TCast _ _ (L1g.compile.TSort SProp)) =>
      TProof
    | L1g.compile.TCast tm ck ty =>
      TCast (L1gTerm_Term tm) ck (L1gTerm_Term ty)
    | L1g.compile.TProd nm ty bod =>
      TProd nm (L1gTerm_Term ty) (L1gTerm_Term bod)
    | L1g.compile.TLambda nm ty bod =>
      TLambda nm (L1gTerm_Term ty) (L1gTerm_Term bod)
    | L1g.compile.TLetIn nm dfn ty bod =>
      TLetIn nm (L1gTerm_Term dfn) (L1gTerm_Term ty) (L1gTerm_Term bod)
    | L1g.compile.TApp fn arg args =>
      TApp (L1gTerm_Term fn) (L1gTerm_Term arg) (L1gTerms_Terms args)
    | L1g.compile.TConst pth => TConst pth
    | L1g.compile.TAx => TAx
    | L1g.compile.TInd ind => TInd ind
    | L1g.compile.TConstruct ind m arty => TConstruct ind m arty
    | L1g.compile.TCase m ty mch brs =>
      match L1gTerm_Term mch, L1gTerms_Terms brs with
        | TProof, tunit br => applyBranchToProof br
        | Mch, Brs => TCase m (L1gTerm_Term ty) Mch Brs
      end
    | L1g.compile.TFix defs m => TFix (L1gDefs_Defs defs) m
    | L1g.compile.TWrong _ => TWrong
  end
with L1gTerms_Terms (ts:L1gTerms) : Terms :=
       match ts with
         | L1g.compile.tnil => tnil
         | L1g.compile.tcons u us => tcons (L1gTerm_Term u) (L1gTerms_Terms us)
       end
with L1gDefs_Defs (ds:L1gDefs) : Defs :=
       match ds with
         | L1g.compile.dnil => dnil
         | L1g.compile.dcons nm ty tm m ds =>
           dcons nm (L1gTerm_Term ty) (L1gTerm_Term tm) m (L1gDefs_Defs ds)
       end.
(****
Functional Scheme L1gTerm_Term_ind' := Induction for L1gTerm_Term Sort Prop
with terms_Terms_ind' := Induction for terms_Terms Sort Prop
with wcbvDEvals_ind' := Induction for defs_Defs Sort Prop.
Combined Scheme L1gTerm_TermEvalsDEvals_ind
         from L1gTerm_Term_ind', terms_Terms_ind', wcbvDEvals_ind'.
***)

(** environments and programs **)
Function L1gEC_EC (ec:L1gEC) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (L1gTerm_Term t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition L1gEnv_Env: L1gEnv -> environ Term :=
  List.map (fun (nmec: string * L1gEC) => (fst nmec, L1gEC_EC (snd nmec))).

Definition L1gPgm_Program (p:L1gPgm) : Program Term:=
  {| env:= L1gEnv_Env (env p);
     main:= L1gTerm_Term (main p) |}.


(*** from L1 to L1_5 ***)
Definition program_Program (p:program) : Program Term :=
  L1gPgm_Program (L1g.compile.program_Program p).

Definition term_Term (e:AstCommon.environ L1gTerm) (t:term) : Term :=
  L1gTerm_Term (L1g.compile.term_Term e t).

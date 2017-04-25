
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Export Template.Ast.
Require Import Common.Common.
Require Import L2k.compile.
Require Import L2k.term.


Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2kTerm := L2k.compile.Term.
Definition L2kTerms := L2k.compile.Terms.
Definition L2kDefs := L2k.compile.Defs.
Definition L2kEC := envClass L2kTerm.
Definition L2kEnv := environ L2kTerm.
Definition L2kPgm := Program L2kTerm.


Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term
| TCast      : Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name ->
               Term (* dfn *) -> Term (* body *) -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TAx        : Term
| TConstruct : inductive -> nat (* index in datatype *) -> Terms -> Term
| TCase      : inductive ->
               Term (* discriminee *) -> Defs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : Term
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
Notation tunit t := (tcons t tnil).
Notation dunit nm t m d := (dcons nm t m d dnil).


(*** \box in case branches: need tappend, mkApp and instantiate ***)
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
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
    | TLambda nm  bod =>
      TLambda nm  (instantiate (S n) bod)
    | TCase np s ts =>
      TCase np (instantiate n s) (instantiateDefs n ts)
    | TLetIn nm tdef bod =>
      TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TCast t => instantiate n t
    | TConstruct i m args => TConstruct i m (instantiates n args)
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
         | dcons nm bod rarg ds =>
           dcons nm (instantiate n bod) rarg (instantiateDefs n ds)
       end.
Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop
with instantiates_ind' := Induction for instantiates Sort Prop
with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop.
End Instantiate_sec.

Fixpoint m_Proofs m : Terms :=
  match m with
    | 0 => tnil
    | S n => tcons TProof (m_Proofs n)
  end.
Fixpoint applyBranchToProof nargs (br:Term) : Term :=
  match nargs with
    | 0 => br
    | S m => mkApp br (tcons TProof (m_Proofs m))
  end.

Function L2kTerm_Term (t:L2kTerm) : Term :=
  match t with
    | L2k.compile.TRel n => TRel n
    | L2k.compile.TProof t => TProof
    | L2k.compile.TCast tm => TCast (L2kTerm_Term tm)
    | L2k.compile.TLambda nm bod => TLambda nm (L2kTerm_Term bod)
    | L2k.compile.TLetIn nm dfn bod =>
      TLetIn nm (L2kTerm_Term dfn) (L2kTerm_Term bod)
    | L2k.compile.TApp fn arg args =>
      mkApp (L2kTerm_Term fn) (tcons (L2kTerm_Term arg) (L2kTerms_Terms args))
    | L2k.compile.TConst pth => TConst pth
    | L2k.compile.TAx => TAx
    | L2k.compile.TConstruct ind m args =>
      TConstruct ind m (L2kTerms_Terms args)
    | L2k.compile.TCase m mch brs =>
      match L2k.term.isProof_dec mch with
        | left _ =>
          match brs with
            | L2k.compile.dunit _ br n =>
              applyBranchToProof n (L2kTerm_Term br)
            | _ => TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs)
          end
        | right _ => TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs)
      end
    | L2k.compile.TFix defs m => TFix (L2kDefs_Defs defs) m
    | L2k.compile.TWrong => TWrong
  end
with L2kTerms_Terms (ts:L2kTerms) : Terms :=
       match ts with
         | L2k.compile.tnil => tnil
         | L2k.compile.tcons u us => tcons (L2kTerm_Term u) (L2kTerms_Terms us)
       end
with L2kDefs_Defs (ds:L2kDefs) : Defs :=
       match ds with
         | L2k.compile.dnil => dnil
         | L2k.compile.dcons nm tm m ds =>
           dcons nm (L2kTerm_Term tm) m (L2kDefs_Defs ds)
       end.
(****
Functional Scheme L2kTerm_Term_ind' := Induction for L2kTerm_Term Sort Prop
with L2kTerms_Terms_ind' := Induction for L2kTerms_Terms Sort Prop
with L2Defs_Defs_ind' := Induction for L2Defs_Defs Sort Prop.
Combined Scheme L2kTerm_TermEvalsDEvals_ind
         from L2kTerm_Term_ind', L2kTerms_Terms_ind', L2Defs_Defs_ind'.
***)

(***
Lemma L2kTerm_Term_Case:
  forall mch brs,
    match mch, brs with
      | L2k.term.TProof _, L2k.compile.dunit _ br n =>
        applyBranchToProof n (L2kTerm_Term br)
      | _, _ => TCase m (L2kTerm_Term mch) (L2Defs_Defs brs)
    end.
                  
              forall m brs, L2kTerm_Term (L2k.compile.TCase m mch brs) =
                            TCase m (L2kTerm_Term mch) (L2Defs_Defs brs).
Proof.
***)

Lemma L2kTerm_Term_Case_not_Proof:
  forall mch, ~ L2k.term.isProof mch ->
              forall m brs, L2kTerm_Term (L2k.compile.TCase m mch brs) =
                            TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs).
Proof.
  intros mch hmch m brs.
  destruct brs, mch; cbn; try reflexivity.
  elim hmch. auto.
Qed.

Lemma L2kTerm_Term_Case_not_dunit:
  forall brs, L2k.compile.dlength brs <> 1 ->
              forall m mch, L2kTerm_Term (L2k.compile.TCase m mch brs) =
                            TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs).
Proof.
  intros brs hmch m mch.
  destruct brs; intros; cbn; destruct mch; try reflexivity.
  - destruct brs; try reflexivity.
    + cbn in hmch. elim hmch. reflexivity.
Qed.


(** environments and programs **)
Function L2kEC_EC (ec:L2kEC) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (L2kTerm_Term t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition L2kEnv_Env: L2kEnv -> environ Term :=
  List.map (fun (nmec: string * L2kEC) => (fst nmec, L2kEC_EC (snd nmec))).

Definition L2kPgm_Program (p:L2kPgm) : Program Term:=
  {| env:= L2kEnv_Env (env p);
     main:= L2kTerm_Term (main p) |}.


(*** from L2 to L2_5 ***)
Definition program_Program (p:program) : Program Term :=
  L2kPgm_Program (L2k.compile.program_Program p).

(***
Definition term_Term (e:AstCommon.environ L2kTerm) (t:term) : Term :=
  L2kTerm_Term (L2k.compile.term_Term e t).
***)

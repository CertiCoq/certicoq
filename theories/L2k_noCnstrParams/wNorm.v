
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.
Require Import Common.Common.
Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
Require Import L2k.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Local Open Scope program_scope.
Set Implicit Arguments.

(** Weak typed normal form: normal form of wndEval:
*** no wndEval steps possible (including no steps in type fields.
**)
Section Sec_environ.
Variable p:environ Term.

Inductive WNorm: Term -> Prop :=
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNConstruct: forall i n args, WNorms args -> WNorm (TConstruct i n args)
| WNProof: WNorm TProof
| WNPrim p: WNorm (TPrim p)
| WNApp: forall fn t,
    WNorm fn ->
    ~ isLambda fn -> ~ isFix fn -> ~ isConstruct fn -> fn <> TProof ->
    ~ isPrim fn ->
    WNorm t ->
    WNorm (TApp fn t)
with WNorms: Terms -> Prop :=
     | WNtnil: WNorms tnil
     | WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts).
Hint Constructors WNorm WNorm : core.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
  with WNorms_ind' := Induction for WNorms Sort Prop.
Combined Scheme WNormWNorms_ind from WNorm_ind', WNorms_ind'.

Lemma WNorms_tappendl:
  forall ts us, WNorms (tappend ts us) -> WNorms ts.
Proof.
  induction ts; intros us h.
  - constructor.
  - simpl in h. apply WNtcons; inversion_Clear h.
    + assumption.
    + eapply IHts. eassumption.
Qed.

(** Wcbv reaches weak normal form **)
Lemma Wcbv_WNorm:
  (forall t s, WcbvEval p t s -> WNorm s) /\
  (forall t ts, WcbvEvals p t ts -> WNorms ts).  
Proof.
  apply WcbvEvalEvals_ind; intros;
    try (solve[constructor; try assumption]); try assumption.
  - destruct a as [a [b [c [d e]]]]. constructor; try assumption.  
Qed.

(** every normal form is hit **)
Lemma WNorm_Wcbv:
  (forall s, WNorm s -> exists t, WcbvEval p t s) /\
  (forall ts, WNorms ts -> exists us, WcbvEvals p us ts).  
Proof.
  apply WNormWNorms_ind; intros.
  - exists (TLambda nm bod). constructor.
  - exists (TFix ds br). constructor.
  - dstrctn H. exists (TConstruct i n x). now constructor.
  - exists TProof. constructor.
  - exists (TPrim p0); constructor.
  - dstrctn H. dstrctn H0. exists (TApp x x0). now apply wAppCong. 
  - exists tnil. constructor.
  - dstrctn H. dstrctn H0. exists (tcons x x0). now constructor.
Qed.
 

End Sec_environ.

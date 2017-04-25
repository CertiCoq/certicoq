
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import L3.term.
Require Import L3.program.
Require Import L3.wcbvEval.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Local Open Scope program_scope.
Set Implicit Arguments.

(** Weak typed normal form of wndEval: no wndEval steps possible. **)
Inductive WNorm: Term -> Prop :=
| WNPrf: WNorm TProof
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNCase: forall mch n brs,
            WNorm mch -> ~ isConstruct mch ->
            WNorm (TCase n mch brs)
| WNConstruct: forall i n args,
                 WNorms args -> WNorm (TConstruct i n args)
| WNApp: forall fn t,
           WNorm fn -> WNorm t ->
           ~ (isLambda fn) -> ~ (isFix fn) -> WNorm (TApp fn t)
with WNorms: Terms -> Prop :=
| WNtnil: WNorms tnil
| WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts).
Hint Constructors WNorm WNorm.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
      with WNorms_ind' := Induction for WNorms Sort Prop.
Combined Scheme WNormWNorms_ind from WNorm_ind', WNorms_ind'.


(** WNorm is decidable **)
Lemma WNorm_dec: 
  (forall t, WNorm t \/ ~ WNorm t) /\
  (forall ts, WNorms ts \/ ~ WNorms ts) /\
  (forall (ds:Defs), True).
Proof.
  Ltac rght := solve [right; intros h; inversion_Clear h; contradiction].
  Ltac lft := solve [left; constructor; assumption].
  apply TrmTrmsDefs_ind; intros; auto;
  try (solve[right; intros h; inversion h]);
  try (solve[left; constructor]).
  - destruct (isLambda_dec t). rght.
    destruct (isFix_dec t). rght.
    destruct H; destruct H0; try rght.
    + left. apply WNApp; auto.
  - destruct H.
    + left. constructor. assumption.
    + right. intros h. elim H. inversion h. assumption.
  - destruct H; try rght.
    + destruct (isConstruct_dec t).
      * right. destruct H1 as [x0 [x1 [x2 j]]]. subst. intros h.
        inversion_Clear h. elim H5. auto.
      * destruct H0.
        { left. constructor; assumption. }
  - destruct H, H0;
    try (solve [right; intros h; inversion_Clear h; contradiction]).
    + left; constructor; auto.
Qed.


(** If a program is in weak normal form, it WcbvEval to itself **)
Lemma pre_wNorm_WcbvEval_rfl:
  forall p,
    (forall t, WNorm t -> forall s, WcbvEval p t s -> t = s) /\
    (forall ts, WNorms ts -> forall ss, WcbvEvals p ts ss -> ts = ss).
Proof.
  intros p; apply WNormWNorms_ind; intros; auto; 
  try (solve [inversion H; reflexivity]).
  - inversion_Clear H0.
    + rewrite (H _ H4) in n0. elim n0. auto.
    + rewrite (H _ H5). reflexivity.
  - inversion H0.
    + rewrite (H args'). reflexivity. assumption.
  - inversion_Clear H1.
    + rewrite (H _ H4) in n. elim n. exists nm, bod. reflexivity.
    + rewrite (H _ H4) in n0. elim n0. exists dts, m. reflexivity.
    + apply f_equal2.
      * apply H. assumption.
      * apply H0. assumption.
  - inversion_Clear H1. rewrite (H _ H4). rewrite (H0 _ H6). reflexivity.
Qed.


Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section parametric.
  Variable T : Type.
  Variable R : T -> T -> Prop.

  (** Reflexivity **)
  Inductive makeRefl : T -> T -> Prop :=
  | RRefl : forall x, makeRefl x x
  | RStep : forall x y, R x y -> makeRefl x y.

  Global Instance Refl_makeRefl : Reflexive makeRefl.
  Proof.
    constructor.
  Qed.

  Global Instance Refl_makeTrans : Transitive R -> Transitive makeRefl.
  Proof.
    intro. intro. intros. inversion H0; clear H0; subst; auto.
    inversion H1; clear H1; subst; auto using RStep.
    apply RStep. etransitivity; eauto.
  Qed.

  (** Transitivity **)
  Inductive makeTrans : T -> T -> Prop :=
  | TStep : forall x y, R x y -> makeTrans x y
  | TTrans : forall x y z, makeTrans x y -> makeTrans y z -> makeTrans x z.

  Global Instance Trans_makeTrans : Transitive makeTrans.
  Proof.
    intro. intros; eapply TTrans; eassumption.
  Qed.

  Global Instance Trans_makeRefl : Reflexive R -> Reflexive makeTrans.
  Proof.
    intro. intro. apply TStep. reflexivity.
  Qed.

  Inductive leftTrans : T -> T -> Prop :=
  | LTFin : forall x y, R x y -> leftTrans x y
  | LTStep : forall x y z, R x y -> leftTrans y z -> leftTrans x z.

  Inductive rightTrans : T -> T -> Prop :=
  | RTFin : forall x y, R x y -> rightTrans x y
  | RTStep : forall x y z, rightTrans x y -> R y z -> rightTrans x z.

  (** Equivalence of definitions of transitivity **)
  Fixpoint leftTrans_rightTrans_acc x y (l : leftTrans y x) : forall z, rightTrans z y -> rightTrans z x :=
    match l in leftTrans y x return forall z, rightTrans z y -> rightTrans z x with
      | LTFin _ _ pf => fun z pfR => RTStep pfR pf
      | LTStep _ _ _ pf pfL => fun z pfR =>
        leftTrans_rightTrans_acc pfL (RTStep pfR pf)
    end.

  Fixpoint rightTrans_leftTrans_acc x y (l : rightTrans x y) : forall z, leftTrans y z -> leftTrans x z :=
    match l in rightTrans x y return forall z, leftTrans y z -> leftTrans x z with
      | RTFin _ _ pf => fun z pfR => LTStep pf pfR
      | RTStep _ _ _ pf pfL => fun z pfR =>
        rightTrans_leftTrans_acc pf (LTStep pfL pfR)
    end.

  Theorem leftTrans_rightTrans : forall x y,
    leftTrans x y <-> rightTrans x y.
  Proof.
    split.
    { destruct 1. apply RTFin; assumption.
      eapply leftTrans_rightTrans_acc. eassumption. eapply RTFin. eassumption. }
    { destruct 1. apply LTFin. assumption.
      eapply rightTrans_leftTrans_acc. eassumption. eapply LTFin. eassumption. }
  Qed.

  Fixpoint leftTrans_makeTrans_acc x y (l : leftTrans x y) : makeTrans x y :=
    match l in leftTrans x y return makeTrans x y with
      | LTFin _ _ pf => TStep pf
      | LTStep _ _ _ pf pfL =>
        TTrans (TStep pf) (leftTrans_makeTrans_acc pfL)
    end.

  Fixpoint leftTrans_trans x y (l : leftTrans x y) : forall z (r : leftTrans y z), leftTrans x z :=
    match l in leftTrans x y return forall z (r : leftTrans y z), leftTrans x z with
      | LTFin _ _ pf => fun _ pfL => LTStep pf pfL
      | LTStep _ _ _ pf pfL => fun _ pfR => LTStep pf (leftTrans_trans pfL pfR)
    end.

  Theorem makeTrans_leftTrans : forall s s',
    makeTrans s s' <-> leftTrans s s'.
  Proof.
    split; intros.
    { induction H. eapply LTFin. eassumption.
      eapply leftTrans_trans; eassumption. }
    { apply leftTrans_makeTrans_acc. assumption. }
  Qed.

  Theorem makeTrans_rightTrans : forall s s',
    makeTrans s s' <-> rightTrans s s'.
  Proof.
    intros. etransitivity. apply makeTrans_leftTrans. apply leftTrans_rightTrans.
  Qed.

  Definition RTStep_left : forall x y z : T, R x y -> rightTrans y z -> rightTrans x z.
    intros. revert H. revert x.
    induction H0.
    { intros. eapply RTStep. eapply RTFin. eassumption. eassumption. }
    { intros. eapply RTStep. eapply IHrightTrans. eassumption. eassumption. }
  Defined.

End parametric.

Section param.
  Variable T : Type.
  Variable R : T -> T -> Prop.

  Theorem makeTrans_idem : forall s s',
    makeTrans (makeTrans R) s s' <-> makeTrans R s s'.
  Proof.
    split.
    { induction 1; eauto using TTrans. }
    { eapply TStep. }
  Qed.

  Theorem makeTrans_makeRefl_comm : forall s s',
    makeTrans (makeRefl R) s s' <-> makeRefl (makeTrans R) s s'.
  Proof.
    split.
    { induction 1;
      repeat match goal with
               | [ H : makeRefl _ _ _ |- _ ] => inversion H; clear H; subst
             end; eauto using RRefl, RStep, TStep, TTrans. }
    { intros. inversion H; clear H; subst; auto. apply TStep. apply RRefl.
      induction H0; eauto using RStep, TStep, TTrans. }
  Qed.

  Theorem makeRefl_idem : forall s s',
    makeRefl (makeRefl R) s s' <-> makeRefl R s s'.
  Proof.
    split; inversion 1; subst; eauto using RStep, RRefl.
  Qed.

End param.

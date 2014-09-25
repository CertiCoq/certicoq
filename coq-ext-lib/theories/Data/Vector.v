Require Import ExtLib.Data.Fin.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section parametric.
  Variable T : Type.

  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  Definition vector_hd n (v : vector (S n)) : T :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S _ => T
                                end with
      | Vnil => tt
      | Vcons _ x _ => x
    end.

  Definition vector_tl n (v : vector (S n)) : vector n :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S n => vector n
                                end with
      | Vnil => tt
      | Vcons _ _ x => x
    end.

  Theorem vector_eta : forall n (v : vector n),
                         v = match n as n return vector n -> vector n with
                               | 0 => fun _ => Vnil
                               | S n => fun v => Vcons (vector_hd v) (vector_tl v)
                             end v.
  Proof.
    destruct v; auto.
  Qed.

  Fixpoint get {n : nat} (f : fin n) : vector n -> T :=
    match f in fin n return vector n -> T with
      | F0 n => @vector_hd _
      | FS n f => fun v => get f (vector_tl v)
    end.

  Fixpoint put {n : nat} (f : fin n) (t : T) : vector n -> vector n :=
    match f in fin n return vector n -> vector n with
      | F0 _ => fun v => Vcons t (vector_tl v)
      | FS _ f => fun v => Vcons (vector_hd v) (put f t (vector_tl v))
    end.


  Theorem get_put_eq : forall {n} (v : vector n) (f : fin n) val,
                         get f (put f val v) = val.
  Proof.
    induction n.
    { inversion f. }
    { remember (S n). destruct f.
      inversion Heqn0; subst; intros; reflexivity.
      inversion Heqn0; subst; simpl; auto. }
  Qed.

  Theorem get_put_neq : forall {n} (v : vector n) (f f' : fin n) val,
                          f <> f' ->
                          get f (put f' val v) = get f v.
  Proof.
    induction n.
    { inversion f. }
    { remember (S n); destruct f. 
      { inversion Heqn0; clear Heqn0; subst; intros. 
        destruct (fin_case f'); try congruence.
        destruct H0; subst. auto. }
      { inversion Heqn0; clear Heqn0; subst; intros. 
        destruct (fin_case f').
        subst; auto.
        destruct H0; subst. simpl.
        eapply IHn. congruence. } }
  Qed.

  Section ForallV.
    Variable P : T -> Prop.

    Inductive ForallV  : forall n, vector n -> Prop :=
    | ForallV_nil : ForallV Vnil
    | ForallV_cons : forall n e es, P e -> @ForallV n es -> ForallV (Vcons e es).

    Definition ForallV_vector_hd n (v : vector (S n)) (f : ForallV v) : P (vector_hd v) :=
      match f in @ForallV n v return match n as n return vector n -> Prop with
                                       | 0 => fun _ => True
                                       | S _ => fun v => P (vector_hd v)
                                     end v
      with
        | ForallV_nil => I
        | ForallV_cons _ _ _ pf _ => pf
      end.

    Definition ForallV_vector_tl n (v : vector (S n)) (f : ForallV v) : ForallV (vector_tl v) :=
      match f in @ForallV n v return match n as n return vector n -> Prop with
                                       | 0 => fun _ => True
                                       | S _ => fun v => ForallV (vector_tl v)
                                     end v
      with
        | ForallV_nil => I
        | ForallV_cons _ _ _ _ pf => pf
      end.
  End ForallV.

End parametric.

Arguments vector T n.
Arguments vector_hd {T n} _.
Arguments vector_tl {T n} _.

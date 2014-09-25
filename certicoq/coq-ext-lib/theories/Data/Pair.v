Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.

Section PairWF.
  Variables T U : Type.
  Variable RT : T -> T -> Prop.
  Variable RU : U -> U -> Prop.

  Inductive R_pair : T * U -> T * U -> Prop :=
  | L : forall l l' r r',
    RT l l' -> R_pair (l,r) (l',r')
  | R : forall l r r',
    RU r r' -> R_pair (l,r) (l,r').

  Hypothesis wf_RT : well_founded RT.
  Hypothesis wf_RU : well_founded RU.

  Theorem wf_R_pair : well_founded R_pair.
  Proof.
    red. intro x.
    destruct x. generalize dependent u.
    apply (well_founded_ind wf_RT (fun t => forall u : U, Acc R_pair (t, u))) .
    do 2 intro.

    apply (well_founded_ind wf_RU (fun u => Acc R_pair (x,u))). intros.
    constructor. destruct y.
    remember (t0,u). remember (x,x0). inversion 1; subst;
    inversion H4; inversion H3; clear H4 H3; subst; eauto.
  Defined.
End PairWF.

Section PairParam.
  Variable T : Type.
  Variable eqT : T -> T -> Prop.
  Variable U : Type.
  Variable eqU : U -> U -> Prop.

  Variable EDT : RelDec eqT.
  Variable EDU : RelDec eqU.

  Global Instance RelDec_equ_pair : RelDec (fun x y => eqT (fst x) (fst y) /\ eqU (snd x) (snd y)) :=
  { rel_dec := fun x y =>
    if rel_dec (fst x) (fst y) then
      rel_dec (snd x) (snd y)
    else false }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_equ_pair : RelDec_Correct RelDec_equ_pair.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; intuition.
  Qed.
End PairParam.

Section PairEq.
  Variable T : Type.
  Variable U : Type.

  Variable EDT : RelDec (@eq T).
  Variable EDU : RelDec (@eq U).

  (** Specialization for equality **)
  Global Instance RelDec_eq_pair : RelDec (@eq (T * U)) :=
  { rel_dec := fun x y =>
    if rel_dec (fst x) (fst y) then
      rel_dec (snd x) (snd y)
    else false }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_eq_pair : RelDec_Correct RelDec_eq_pair.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; congruence.
  Qed.
End PairEq.

Global Instance Injective_pair T U (a :T) (b:U) c d : Injective ((a,b) = (c,d)) :=
{| result := a = c /\ b = d |}.
Proof. abstract (inversion 1; intuition). Defined.
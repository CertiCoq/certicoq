(* Ensemble library utilities. Part of the CertiCoq project.
 * Author: Anonymized, 2016
 *)

From Stdlib Require Import Classes.Morphisms Arith NArith.BinNat Lists.List Sorting.Permutation.
From compcert.lib Require Import Coqlib.
From Stdlib Require Import Sets.Ensembles.

Import ListNotations.

Close Scope Z_scope.

Ltac inv H := inversion H; clear H;  subst.

#[global] Hint Constructors Singleton : core.
#[global] Hint Constructors Union : core.
#[global] Hint Constructors Intersection : core.
#[global] Hint Unfold In : core.

Create HintDb Ensembles_DB.

(** * Usefull notations. Inspired from https://github.com/QuickChick/QuickChick/blob/master/src/Sets.v *)

Declare Scope Ensembles_scope.

Notation "x \in A" := (Ensembles.In _ A x) (at level 70, only parsing) : Ensembles_scope.

Infix "<-->" := (Ensembles.Same_set _) (at level 70, no associativity) : Ensembles_scope.

Infix "\subset" := (Ensembles.Included _) (at level 70, no associativity) : Ensembles_scope.

Open Scope Ensembles_scope.

Notation "[ 'set' x : T | P ]" := (fun x : T => P)
  (at level 0, x at level 99, only parsing) : Ensembles_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, only parsing) : Ensembles_scope.

Notation "[ 'set' a ]" := (Ensembles.Singleton _ a)
  (at level 0, a at level 99, format "[ 'set'  a ]") :  Ensembles_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") :  Ensembles_scope.

Notation "A :|: B" := (Union _ A B) (at level 52, left associativity)
                      : Ensembles_scope.
Notation "a |: A" := ([set a] :|: A) (at level 52, left associativity)
                     : Ensembles_scope.

Notation "A :&: B" := (Intersection _ A B) (at level 48, left associativity)
                      : Ensembles_scope.

Notation "a &: B" := (Intersection _ [set a] B) (at level 48, left associativity)
                     : Ensembles_scope.

Notation "A \\ B" := (Setminus _ A B) (at level 52, left associativity)
                     : Ensembles_scope.

(** * Equivalence and preorder properties *)

Lemma Included_refl {A} (s1 : Ensemble A) :
  s1 \subset s1.
Proof.
  intros x Hin; eauto.
Qed.


Lemma Included_trans {A} (s1 s2 s3 : Ensemble A) :
  s1 \subset s2 ->
  s2 \subset s3 ->
  s1 \subset s3.
Proof.
  intros H1 H2 x HIn.
  eapply H2. eapply H1; eauto.
Qed.

#[global] Instance PreOrder_Included {A} : PreOrder (@Included A).
Proof.
  constructor.
  now apply Included_refl.
  intros ? ? ? ? ?. now eapply Included_trans; eauto.
Qed.

Lemma Same_set_refl A (s : Ensemble A) :
  s <--> s.
Proof.
  split; apply Included_refl.
Qed.

Lemma Same_set_sym A (s1 s2 : Ensemble A) :
  s1 <--> s2 ->
  s2 <--> s1.
Proof.
  intros [H1 H2]; split; eauto.
Qed.

Lemma Same_set_trans {A} (s1 s2 s3 : Ensemble A) :
  s1 <--> s2 ->
  s2 <--> s3 ->
  s1 <--> s3.
Proof.
  intros [H1 H2] [H3 H4]. split; eapply Included_trans; eauto.
Qed.

#[global] Instance Equivalence_Same_set {A} : Equivalence (@Same_set A).
Proof.
  constructor.
  now apply Same_set_refl.
  intros ? ? ?. now eapply Same_set_sym.
  intros ? ? ? ? ?. now eapply Same_set_trans; eauto.
Qed.

#[global] Hint Immediate Same_set_refl Included_refl : Ensembles_DB.

Ltac edb := eauto with Ensembles_DB.

(** * Decidability  instances *)

Class Decidable {A} (S : Ensemble A) : Type :=
 { Dec : forall x, { S x } + {~ S x} }.

#[global] Instance Decidable_Union {A} (S1 S2 : Ensemble A)
         {H1 : Decidable S1} {H2 : Decidable S2} : Decidable (Union A S1 S2).
Proof.
  constructor. intros x.
  edestruct (@Dec _ _ H1 x); try now left; constructor.
  edestruct (@Dec _ _ H2 x); try now left; constructor.
  right. intros Hun. inv Hun; eauto.
Qed.

#[global] Instance Decidable_Intersection {A} (S1 S2 : Ensemble A)
         {H1 : Decidable S1} {H2 : Decidable S2} : Decidable (Intersection A S1 S2).
Proof.
  constructor. intros x.
  edestruct (@Dec _ _ H1 x); edestruct (@Dec _ _ H2 x);
  try (now left; constructor); right; intros Hc; inv Hc; eauto.
Qed.

#[global] Instance Decidable_Setminus {A} s1 s2 { H1 : Decidable s1 }
         { H2 : Decidable s2 } : Decidable (Setminus A s1 s2).
Proof.
  constructor. intros x. destruct H1, H2. destruct (Dec1 x).
  - right. intros Hc. inv Hc; eauto.
  - destruct (Dec0 x). left. constructor; eauto.
    right. intros Hc. inv Hc. eauto.
Qed.

(** $\{x\}$ is decidable. TODO : generalize the type *)
#[global] Instance DecidableSingleton_positive x : Decidable (Singleton positive x).
Proof.
  constructor. intros x'.
  destruct (peq x x'); subst. left; constructor.
  right. intros Hc. inv Hc; eauto.
Qed.

(** TODO make it proper? *)
Lemma Decidable_Same_set A (S1 S2 : Ensemble A) :
  S1 <--> S2 ->
  Decidable S1 ->
  Decidable S2.
Proof.
  intros Heq Hdec. constructor. intros x.
  destruct Hdec as [Dec]. destruct (Dec x) as [Hin | Hnin].
  left; eapply Heq; eauto.
  right; intros Hc; eapply Hnin; eapply Heq; eauto.
Qed.


(** * Proper instances *)

#[global] Instance Proper_Union_l A :
  Proper (Same_set A ==> Logic.eq ==> Same_set A)
         (Union A).
Proof.
  constructor; subst; intros x' H'; destruct H'; destruct H as [H1 H2]; eauto.
Qed.

#[global] Instance Proper_Union_r A :
  Proper (Logic.eq ==> Same_set A ==> Same_set A)
         (Union A).
Proof.
  constructor; subst; intros x' H'; destruct H'; destruct H0 as [H1 H2]; eauto.
Qed.



#[global] Instance Proper_Setminus_l A :
  Proper (Same_set A ==> Logic.eq ==> Same_set A)
         (Setminus A).
Proof.
  constructor; intros x' H'; destruct H as [H1 H2];
  inv H'; constructor; eauto.
Qed.

#[global] Instance Proper_Setminus_r A :
  Proper (Logic.eq ==> Same_set A ==> Same_set A)
         (Setminus A).
Proof.
  constructor; intros x' H'; destruct H0 as [H1 H2];
  inv H'; constructor; eauto.
Qed.

#[global] Instance Proper_Intersection_l A :
  Proper (Same_set A ==> Logic.eq ==> Same_set A)
         (Intersection A).
Proof.
  constructor; subst; intros x' H'; destruct H'; constructor; firstorder.
Qed.

#[global] Instance Proper_Intersection_r A :
  Proper (Logic.eq ==> Same_set A ==> Same_set A)
         (Intersection A).
Proof.
  constructor; subst; intros x' H'; destruct H'; constructor; firstorder.
Qed.

#[global] Instance Proper_Disjoint_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Disjoint A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2]; inv H';
  constructor; intros x' HIn; inv HIn; eapply H; constructor; eauto.
Qed.

#[global] Instance Proper_Disjoint_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Disjoint A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2]; inv H';
  constructor; intros x' HIn; inv HIn; eapply H; constructor; eauto.
Qed.

#[global] Instance Proper_In {A} :
  Proper (Same_set A ==> Logic.eq ==> iff) (Ensembles.In A).
Proof.
  constructor; intros H'; subst; destruct H as [H1 H2]; eauto.
Qed.

#[global] Instance Proper_Included_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Included A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2];
  intros x' HIn; eauto.
Qed.

#[global] Instance Proper_Included_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Included A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2];
  intros x' HIn; eauto.
Qed.

#[global] Instance Proper_Same_set_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Same_set A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2]; destruct H' as [H3 H4];
  constructor; eauto; eapply Included_trans; eauto.
Qed.

#[global] Instance Proper_Same_set_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Same_set A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2]; destruct H' as [H3 H4];
  constructor; eauto; eapply Included_trans; eauto.
Qed.

#[global] Instance Complement_Proper {A : Type} : Proper (Same_set A ==> Same_set A) (Complement A).
Proof.
  intros s1 s2 [Hin1 Hin2]; split; intros x Hc Hc'; eapply Hc; eauto.
Qed.

(** * Useful definitions and lemmas *)

(** ** Commutativity properties *)

Lemma Union_commut {A} (s1 s2 : Ensemble A) :
  (s1 :|: s2) <--> (s2 :|: s1).
Proof.
  split; intros x H; inv H; eauto.
Qed.

Lemma Intersection_commut {A} (s1 s2 : Ensemble A) :
  Same_set A (Intersection A s2 s1) (Intersection A s1 s2).
Proof.
  split; intros x H; inv H; constructor; eauto.
Qed.

Lemma Disjoint_sym {A} s1 s2 :
  Disjoint A s2 s1 -> Disjoint A s1 s2.
Proof.
  intros H. inv H.
  constructor. intros x HIn. inv HIn.
  eapply H0; eauto.
Qed.

#[global] Hint Immediate Union_commut Intersection_commut : Ensembles_DB.

(** ** Associativity properties *)

Lemma Union_assoc {A} s1 s2 s3 :
  Same_set A (Union A s1 (Union A s2 s3))
           (Union A (Union A s1 s2) s3).
Proof.
  split; intros x HIn; inv HIn; eauto; inv H; eauto.
Qed.

Lemma Intersection_assoc {A} s1 s2 s3 :
  Same_set A (Intersection A s1 (Intersection A s2 s3))
           (Intersection A (Intersection A s1 s2) s3).
Proof.
  split; intros x HIn; inv HIn.
  inv H0. now eauto.
  inv H. now eauto.
Qed.

#[global] Hint Immediate Union_assoc Intersection_assoc : Ensembles_DB.

(** ** Distributitvity properties *)

Lemma Setminus_Union_distr {A} s1 s2 s3 :
  Same_set A (Setminus A (Union A s1 s2) s3)
           (Union A (Setminus A s1 s3) (Setminus A s2 s3)).
Proof.
  split; intros x H; inv H; inv H0;
  try (now try left; constructor; eauto);
  now right; constructor; eauto.
Qed.

Lemma Union_Intersection_distr {A} s1 s2 s3:
  Same_set A (Union A (Intersection A s1 s2) s3)
           (Intersection A (Union A s1 s3) (Union A s2 s3)).
Proof.
  split; intros x H; inv H; eauto.
  inv H0. now eauto.
  now inv H0; inv H1; eauto.
Qed.

Lemma Intersection_Union_distr :
  forall (A : Type) (s1 s2 s3 : Ensemble A),
    (s1 :|: s2) :&: s3 <--> (s1 :&: s3) :|: (s2 :&: s3).
Proof.
  intros A s1 s2 s3.
  split; intros x.
  - intros [H1 H2]. inv H2; eauto.
  - intros Hin. inv Hin; eauto; inv H; eauto.
Qed.

Lemma Intersection_Disjoint :
  forall (A : Type) (s1 s2 : Ensemble A),
    Disjoint _ s1 s2 ->
    s1 :&: s2 <--> Empty_set _.
Proof.
  intros A s1 s2 Hd.
  split; intros x.
  - intros H1; inv H1. exfalso; eapply Hd; eauto.
  - intros Hc; inv Hc.
Qed.

Lemma Intersection_Setmius_Disjoint {A} (S1 S2 S3 : Ensemble A) :
  Disjoint _ S2 S3 ->
  (S1 \\ S2) :&: S3 <--> S1 :&: S3.
Proof.
  intros Hd. split.
  - intros x Hin. inv Hin. inv H. constructor; eauto.
  - intros x Hin. inv Hin. constructor; eauto.
    constructor. eassumption. intros Hc. eapply Hd; constructor; eauto.
Qed.

Lemma Intersection_Setmius_Setminus_Disjoint {A} (S1 S2 S3 S4 : Ensemble A) :
  Disjoint _ S3 S4 ->
  (S1 \\ (S2 \\ S4)) :&: S3 <--> (S1 \\ S2) :&: S3.
Proof.
  intros Hd. split.
  - intros x Hin. inv Hin. inv H. constructor; eauto. constructor; eauto.
    intros Hc. eapply H2; eauto. constructor. eassumption.
    intros Hc'. eapply Hd; constructor; eauto.
  - intros x Hin. inv Hin. constructor; eauto. inv H.
    constructor. eassumption. intros Hc. eapply Hd; constructor; eauto.
    inv Hc. exfalso; eauto.
Qed.


#[global] Hint Immediate Setminus_Union_distr Union_Intersection_distr : Ensembles_DB.

(** ** Compatibility properties *)

Lemma Included_Union_compat {A} s1 s1' s2 s2' :
  Included A s1 s2 ->
  Included A s1' s2' ->
  Included A (Union A s1 s1') (Union A s2 s2').
Proof.
  intros H1 H2 x Hin. inv Hin; eauto.
Qed.

Lemma Same_set_Union_compat {A} s1 s1' s2 s2' :
  Same_set A s1 s2 ->
  Same_set A s1' s2' ->
  Same_set A (Union A s1 s1') (Union A s2 s2').
Proof.
  intros [H1 H2] [H3 H4].
  split; apply Included_Union_compat; eauto.
Qed.

Lemma Included_Setminus_compat {A} s1 s1' s2 s2' :
  Included A s1 s2 ->
  Included A s2' s1' ->
  Included A (Setminus A s1 s1') (Setminus A s2 s2').
Proof.
  intros H1 H2 x H; inv H; constructor; eauto.
Qed.


Lemma Same_set_Setminus_compat {A} s1 s1' s2 s2' :
  Same_set A s1 s2 ->
  Same_set A s1' s2' ->
  Same_set A (Setminus A s1 s1') (Setminus A s2 s2').
Proof.
  intros [H1 H2] [H3 H4].
  split; apply Included_Setminus_compat; eauto.
Qed.

Lemma Setminus_Intersection_distr {A} (S1 S2 S3 : Ensemble A) :
  (S1 :&: S2) \\ S3 <--> (S1 \\ S3) :&: (S2 \\ S3).
Proof.
  split; intros x H1.
  inv H1. inv H. constructor; constructor; eauto.
  inv H1. inv H; inv H0. constructor; eauto.
Qed.


#[global] Hint Resolve Included_Union_compat Same_set_Union_compat
     Included_Setminus_compat Same_set_Setminus_compat : Ensembles_DB.

(** ** [Empty_set] is neutral *)

Lemma Union_Empty_set_neut_r {A} s:
  Same_set A (Union A s (Empty_set A)) s.
Proof.
  split; intros x H; eauto. inv H; eauto. inv H0.
Qed.

Lemma Union_Empty_set_neut_l (A : Type) (s : Ensemble A):
  Same_set A (Union A (Empty_set A) s) s.
Proof.
  split; intros x H; try inv H; eauto. inv H0.
Qed.

Lemma Setminus_Empty_set_neut_r {A} s :
  Same_set A (Setminus A s (Empty_set A)) s.
Proof.
  split; intros x H; try inv H; eauto.
  constructor; eauto. intros H'; inv H'.
Qed.

#[global] Hint Immediate Union_Empty_set_neut_r Union_Empty_set_neut_l
     Setminus_Empty_set_neut_r : Ensembles_DB.

(** ** [Empty_set] is absorbing *)

Lemma Intersection_Empty_set_abs_r {A} s:
  Same_set A (Intersection A s (Empty_set A)) (Empty_set A).
Proof.
  split; intros x H; eauto; inv H; eauto.
Qed.

Lemma Intersection_Empty_set_abs_l {A} s:
  Same_set A (Intersection A (Empty_set A) s) (Empty_set A).
Proof.
  split; intros x H; eauto; inv H; eauto.
Qed.

Lemma Setminus_Empty_set_abs_r {A} s :
  Same_set A (Setminus A (Empty_set A) s) (Empty_set _).
Proof.
  split; intros x H; inv H; eauto.
Qed.

#[global] Hint Immediate Intersection_Empty_set_abs_r Intersection_Empty_set_abs_l
     Setminus_Empty_set_abs_r  : Ensembles_DB.

(** ** Idemptotency properties *)

Lemma Union_idempotent {A} s :
  Same_set A (Union _ s s) s.
Proof.
  split; intros x H; eauto.
  inv H; eauto.
Qed.

Lemma Intersection_idempotent {A} s :
  Same_set A (Intersection _ s s) s.
Proof.
  split; intros x H; eauto.
  inv H; eauto.
Qed.

#[global] Hint Immediate Union_idempotent Intersection_idempotent : Ensembles_DB.

(** ** De Morgan's laws *)

Lemma Union_DeMorgan {A} s1 s2 :
  Same_set A (Complement _ (Union _ s1 s2))
           (Intersection _ (Complement _ s1) (Complement _ s2)).
Proof.
  split; intros x H.
  now constructor; intros Hc; eauto.
  inv H. intros Hc; inv Hc; eauto.
Qed.

Lemma Intersection_DeMorgan {A} s1 s2 :
  Decidable s1 ->
  Same_set A (Complement _ (Intersection _ s1 s2))
           (Union _ (Complement _ s1) (Complement _ s2)).
Proof.
  intros Hdec. split; intros x H.
  destruct Hdec. destruct (Dec0 x); eauto.
  right. intros Hc. eapply H. constructor; eauto.
  inv H; intros Hc; inv Hc; eauto.
Qed.

Lemma Intersection_DeMorgan' {A} s1 s2 :
  Decidable s2 ->
  Same_set A (Complement _ (Intersection _ s1 s2))
           (Union _ (Complement _ s1) (Complement _ s2)).
Proof.
  intros Hdec. split; intros x H.
  destruct Hdec. destruct (Dec0 x); eauto.
  left. intros Hc. eapply H. constructor; eauto.
  inv H; intros Hc; inv Hc; eauto.
Qed.

#[global] Hint Immediate Union_DeMorgan : Ensembles_DB.

(** ** Complement is involutive *)

Lemma Complement_involutive_l {A} s :
  Included A s (Complement _ (Complement _ s)).
Proof.
  intros x H Hc. eauto.
Qed.

Lemma Complement_involutive_r {A} s :
  Decidable s ->
  Included A (Complement _ (Complement _ s)) s.
Proof.
  intros Hdec x H. destruct Hdec. destruct (Dec0 x); eauto.
  exfalso; eauto.
Qed.

#[global] Hint Immediate Complement_involutive_l : Ensembles_DB.

(** ** Inclusion properties *)

Lemma Included_Empty_set {A} s :
  Included A (Empty_set A) s.
Proof.
  intros x H. inv H.
Qed.

Lemma Included_Union_l {A} s1 s2 :
  Included A s1 (Union A s1 s2).
Proof.
  intros x HIn. constructor. eauto.
Qed.

Lemma Included_Union_r {A} s1 s2 :
  Included A s2 (Union A s1 s2).
Proof.
  intros x HIn. constructor 2. eauto.
Qed.

Lemma Union_Included_l {A} S1 S2 S3 :
  Union A S1 S2 \subset S3 ->
  S1 \subset S3.
Proof.
  firstorder.
Qed.

Lemma Union_Included_r {A} S1 S2 S3 :
  Union A S1 S2 \subset S3 ->
  S2 \subset S3.
Proof.
  firstorder.
Qed.

Lemma Included_Union_preserv_l {A} s1 s2 s3 :
  Included A s1 s2 ->
  Included A s1 (Union A s2 s3).
Proof.
  intros H x H'. left; eauto.
Qed.

Lemma Included_Union_preserv_r {A} s1 s2 s3 :
  Included A s1 s3 ->
  Included A s1 (Union A s2 s3).
Proof.
  intros H x H'. right; eauto.
Qed.

Lemma Setminus_Included_Included_Union {A} s1 s2 s3 :
  Included A s1 (Union _ s2 s3) ->
  Included A (Setminus _ s1 s3) s2.
Proof.
  intros H x Hm; inv Hm.
  eapply H in H0. inv H0; try contradiction.
  eassumption.
Qed.

Lemma Setminus_Included {A} s1 s2 :
  Included A (Setminus A s1 s2) s1.
Proof.
  intros x HIn. inv HIn. eauto.
Qed.

Lemma Setminus_Included_preserv {A} s1 s2 s3 :
  Included A s1 s3 ->
  Included A (Setminus A s1 s2) s3.
Proof.
  intros Hin1 x Hin2. inv Hin2. eauto.
Qed.

Lemma Union_Included {A} S1 S2 S :
  Included A S1 S ->
  Included A S2 S ->
  Included A (Union A S1 S2) S.
Proof.
  intros H1 H2 x Hin; inv Hin; eauto.
Qed.

Lemma Singleton_Included {A} x S :
  In A S x ->
  Included A (Singleton A x) S.
Proof.
  intros H x' Hin; inv Hin; eauto.
Qed.

Lemma Singleton_Included_r {A : Type} (x : A) (S : Ensemble A) :
  [set x] \subset S -> In A S x.
Proof.
  firstorder.
Qed.

Lemma Included_Setminus {A} s1 s2 s3:
  Disjoint A s1 s3 ->
  Included A s1 s2 ->
  Included A s1 (Setminus A s2 s3).
Proof.
  intros Hd Hin x H. constructor; eauto.
  intros Hc. eapply Hd; eauto.
Qed.

Lemma Included_Union_Setminus_Included_Union {A} s1 s2 s3 s4 :
  Decidable s3 ->
  Included A s3 s4 ->
  Included A s1 (Union _ s2 s4) ->
  Included A s1 (Union _ (Setminus A s2 s3) s4).
Proof.
  intros Hd Hin Hin' x H. eapply Hin' in H. inv H; eauto.
  destruct Hd as [D]. destruct (D x); eauto.
  left; constructor; eauto.
Qed.

#[global] Hint Immediate Included_Empty_set Included_Union_l Included_Union_r
     Setminus_Included : Ensembles_DB.
#[global] Hint Resolve Included_Union_preserv_l Included_Union_preserv_r Setminus_Included_preserv
     Setminus_Included_Included_Union Union_Included Singleton_Included
     Included_Setminus Included_Union_Setminus_Included_Union : Ensembles_DB.

(** ** Disjoint properties *)

Lemma Disjoint_In_l {A} (s1 s2 : Ensemble A) x :
  Disjoint _ s1 s2 ->
  x \in s1 ->
  ~ x \in s2.
Proof.
  intros Hd Hin Hc. eapply Hd. constructor; eauto.
Qed.

Lemma Disjoint_Setminus_l {A} s1 s2 s3 :
  Included A s3 s2 ->
  Disjoint A (Setminus A s1 s2) s3.
Proof.
  intros Hincl.
  constructor. intros x HIn. inv HIn. inv H.
  apply H2. apply Hincl in H0; eauto.
Qed.

Lemma Disjoint_Setminus_r {A} s1 s2 s3 :
  Included A s1 s3 ->
  Disjoint A s1 (Setminus A s2 s3).
Proof.
  intros Hincl.
  constructor. intros x HIn. inv HIn. inv H0.
  apply H2. eauto.
Qed.

Lemma Disjoint_Empty_set_l {A} s :
  Disjoint A (Empty_set A) s.
Proof.
  constructor. intros x Hin. inv Hin. inv H.
Qed.

Lemma Disjoint_Empty_set_r {A} s :
  Disjoint A s (Empty_set A).
Proof.
  constructor. intros x Hin. inv Hin. inv H0.
Qed.

Lemma Disjoint_Union_l {A} s1 s2 s3 :
  Disjoint A (Union A s1 s2) s3 ->
  Disjoint A s1 s3.
Proof.
  intros H. inv H.
  constructor. intros x Hin. inv Hin. eapply H0; eauto.
Qed.

Lemma Disjoint_Union_r {A} s1 s2 s3 :
  Disjoint A (Union A s1 s2) s3 ->
  Disjoint A s2 s3.
Proof.
  intros H. inv H.
  constructor. intros x Hin. inv Hin. eapply H0; eauto.
Qed.

Lemma Disjoint_Included_l {A} s1 s2 s3 :
  Included A s1 s3 ->
  Disjoint A s3 s2 ->
  Disjoint A s1 s2.
Proof.
  intros H1 H2. inv H2. constructor. intros x Hin.
  inv Hin. eapply H; eauto.
Qed.

Lemma Disjoint_Included_l_sym {A} s1 s2 s3 :
  Included A s1 s3 ->
  Disjoint A s2 s3 ->
  Disjoint A s1 s2.
Proof.
  intros H1 H2. inv H2. constructor. intros x Hin.
  inv Hin. eapply H; eauto.
Qed.

Lemma Disjoint_Included_r_sym {A} s1 s2 s3 :
  Included A s3 s2 ->
  Disjoint A s2 s1 ->
  Disjoint A s1 s3.
Proof.
  intros H1 H2. inv H2. constructor. intros x Hin.
  inv Hin. eapply H; eauto.
Qed.

Lemma Disjoint_Included_r {A} s1 s2 s3 :
  Included A s3 s2 ->
  Disjoint A s1 s2 ->
  Disjoint A s1 s3.
Proof.
  intros H1 H2. inv H2. constructor. intros x Hin.
  inv Hin. eapply H; eauto.
Qed.

Lemma Disjoint_Included A s1 s2 s3 s4 :
  Included A s4 s2 ->
  Included A s3 s1 ->
  Disjoint A s1 s2 ->
  Disjoint A s3 s4.
Proof.
  intros H1 H2 HD. inv HD. constructor. intros x H'.
  inv H'. eapply H; constructor; eauto.
Qed.

Lemma Disjoint_Singleton_r {A} s x :
  ~ In _ s x ->
  Disjoint A s (Singleton A x).
Proof.
  intros H. constructor. intros x' Hin. inv Hin. inv H1. contradiction.
Qed.

Lemma Disjoint_Singleton_l {A} s x :
  ~ Ensembles.In _ s x ->
  Disjoint A (Singleton A x) s.
Proof.
  intros H. constructor. intros x' Hin. inv Hin. inv H0. contradiction.
Qed.

Lemma Union_Disjoint_l A s1 s2 s3 :
  Disjoint A s1 s3 ->
  Disjoint A s2 s3 ->
  Disjoint A (Union A s1 s2) s3.
Proof.
  intros H1 H2. constructor. intros x H. inv H.
  inv H0. eapply H1; eauto.
  eapply H2; eauto.
Qed.

Lemma Union_Disjoint_r A s1 s2 s3 :
  Disjoint A s1 s2 ->
  Disjoint A s1 s3 ->
  Disjoint A s1 (Union A s2 s3).
Proof.
  intros H1 H2. constructor. intros x H. inv H.
  inv H3. eapply H1; eauto.
  eapply H2; eauto.
Qed.

Lemma Setminus_Disjoint_preserv_l {A} s1 s2 s3:
  Disjoint A s1 s3 ->
  Disjoint A (Setminus A s1 s2) s3.
Proof.
  intros Hd. constructor; intros x H. inv H.
  inv H0. eapply Hd; eauto.
Qed.

Lemma Setminus_Disjoint_preserv_r {A} s1 s2 s3:
  Disjoint A s1 s2 ->
  Disjoint A s1 (Setminus A s2 s3).
Proof.
  intros Hd. constructor; intros x H. inv H.
  inv H1. eapply Hd; eauto.
Qed.


Lemma Union_Same_set_Disjoint {A} (S1 S2 S3 : Ensemble A) :
  S1 :|: S2 <--> S1 :|: S3 ->
  Disjoint _ S1 S2 ->
  Disjoint _ S1 S3 ->
  S2 <--> S3.
Proof.
  intros Heq HD HD'. split; intros x Hin.
  - assert (Hin' : (S1 :|: S3) x).
    { eapply Heq. now right. }
    inv Hin'; eauto.
    exfalso. eapply HD; eauto.
  - assert (Hin' : (S1 :|: S2) x).
    { eapply Heq. now right. }
    inv Hin'; eauto.
    exfalso. eapply HD'; eauto.
Qed.


#[global] Hint Resolve Disjoint_Setminus_l Disjoint_Setminus_r Union_Disjoint_l
     Union_Disjoint_r Disjoint_Singleton_l Disjoint_Singleton_r
     Setminus_Disjoint_preserv_l Setminus_Disjoint_preserv_r  : Ensembles_DB.

#[global] Hint Immediate Disjoint_Empty_set_l Disjoint_Empty_set_r : Ensembles_DB.

(** ** Set difference properties *)

Lemma Union_Setminus {A} S1 S2 {Hdec: Decidable S2 } :
  Same_set A (Union A S1 S2) (Union A (Setminus A S1 S2) S2).
Proof.
  split; intros x H; inv H; try (now constructor).
  edestruct (Dec x); try (now constructor).
  inv H0. constructor; eauto.
Qed.

Lemma Setminus_Same_set_Empty_set {A} s:
  Same_set A (Setminus A s s) (Empty_set A).
Proof.
  split; intros x H; inv H; contradiction.
Qed.


Lemma Setminus_Union {A} s1 s2 s3:
  Same_set A (Setminus A (Setminus A s1 s2) s3)
           (Setminus A s1 (Union A s2 s3)).
Proof.
  split; intros x H'; inv H'. inv H.
  constructor; eauto. intros Hc; inv Hc; eauto.
  constructor; eauto. constructor; eauto.
Qed.

Lemma Union_Setminus_Same_set {A} (S1 S2 : Ensemble A) {HD : Decidable S2} :
  S2 \subset S1 ->
  S1 <--> S2 :|: (S1 \\ S2).
Proof.
  intros Heq. split; intros x Hin.
  - destruct HD. destruct (Dec0 x).
    + now left.
    + right. constructor; eauto.
  - inv Hin; eauto. inv H; eauto.
Qed.

Lemma Union_Setminus_Included {A} s1 s2 s3:
  Decidable s3 ->
  Included A s3 s1 ->
  Same_set A (Union A s1 (Setminus A s2 s3))
           (Union A s1 s2).
Proof.
  intros Hdec H.
  split; intros x H'; inv H'; eauto.
  inv H0; eauto.
  destruct Hdec. destruct (Dec0 x); eauto.
  right. constructor; eauto.
Qed.

Lemma Setminus_Included_Empty_set_r {A} s1 s2 :
  Included A s1 s2 ->
  Included A (Setminus A s1 s2) (Empty_set A).
Proof.
  intros H1 x H; inv H. apply H1 in H0. contradiction.
Qed.


Lemma Setminus_Disjoint {A} s1 s2 :
  Disjoint A s1 s2 ->
  Same_set A (Setminus A s1 s2) s1.
Proof.
  intros D; split; inv D; intros x H'; try inv H'; eauto.
  constructor; eauto. intros Hc. eapply H; eauto.
Qed.

Lemma Union_Setminus_Setminus_Union {A} s1 s2 s3 :
  Decidable s3 ->
  Same_set A (Union A (Setminus A s1 s2) s3)
           (Setminus A (Union A s1 s3) (Setminus A s2 s3)).
Proof.
  intros Hdec.
  rewrite Setminus_Union_distr.
  rewrite (Setminus_Disjoint s3);
    eauto using Disjoint_sym, Disjoint_Setminus_l, Included_refl.
  split; intros x H; inv H; eauto; inv H0. constructor. constructor; eauto.
  intros Hc. inv Hc; eauto.
  destruct (@Dec _ _ Hdec x); eauto.
  left. constructor; eauto. intros Hc. apply H1; constructor; eauto.
Qed.

Lemma Included_Union_Setminus {A} s1 s2:
  Decidable s2 ->
  Included A s1 (Union A (Setminus A s1 s2) s2).
Proof.
  intros Hdec x H. destruct (@Dec _ _ Hdec x); eauto.
  left; eauto. constructor; eauto.
Qed.

Lemma Union_Included_Union_Setminus {A} s1 s2 s3 :
  Decidable s3 ->
  Included _ s3 s2 ->
  Same_set A (Union _ s1 s2) (Union A (Setminus A s1 s3) s2).
Proof.
  intros Hdec HIn. split; intros x H.
  - destruct (@Dec _ _ Hdec x); eauto. inv H; eauto.
    left; eauto. constructor; eauto.
  - inv H; eauto. inv H0; eauto.
Qed.

Lemma Setminus_Included_Empty_set {A} s1 s2 :
  Included A s1 s2 ->
  Same_set A (Setminus A s1 s2) (Empty_set A).
Proof.
  intros H; split; intros x H'; inv H'. exfalso; eauto.
Qed.

Lemma Setminus_Union_Included {A} s1 s2 s3 :
  Included A s2 s3 ->
  Same_set A (Setminus _ (Union _ s1 s2) s3) (Setminus _ s1 s3).
Proof.
  intros H.
  rewrite Setminus_Union_distr.
  rewrite (Setminus_Included_Empty_set s2 s3); eauto.
  now rewrite (Union_Empty_set_neut_r).
Qed.

Lemma Setminus_Included_mon {A} s1 s2 s2' s3 :
  Included A (Setminus A s1 s2) s3 ->
  Included A s2 s2' ->
  Included A (Setminus A s1 s2') s3.
Proof.
  intros H1 H2 x Hin. inv Hin. eapply H1. constructor; eauto.
Qed.

Lemma Included_Setminus_antimon {A} (s1 s1' s2 s3 : Ensemble A) :
  Included A (Setminus A s1 s2) s3 ->
  Included A s1' s1 ->
  Included A (Setminus A s1' s2) s3.
Proof.
  intros H H1 x H2.
  eapply H. inv H2. constructor; eauto.
Qed.

Lemma Included_Setminus_Disjoint {A} s1 s2 :
  Disjoint _ s1 s2 ->
  Same_set A s1 (Setminus _ s1 s2).
Proof.
  intros Hd.
  split; intros x H. constructor; eauto. intros Hc; eapply Hd; eauto.
  inv H; eauto.
Qed.

Lemma Setminus_Included_Empty_set_l {A} s1 s2 :
  Decidable s2 ->
  Included A (Setminus A s1 s2) (Empty_set A) ->
  Included A s1 s2.
Proof.
  intros Hdec H1 x H.
  destruct (@Dec _ _ Hdec x); eauto.
  exfalso.
  assert (Hsuff : Empty_set _ x) by (eapply H1; constructor; eauto).
  inv Hsuff.
Qed.

#[global] Hint Immediate Setminus_Same_set_Empty_set Setminus_Union : Ensembles_DB.
#[global] Hint Resolve  Setminus_Disjoint Setminus_Included_Empty_set
     Setminus_Union_Included Included_Setminus_Disjoint : Ensembles_DB.

(** ** Other properties *)

Lemma Union_Same_set {A} s1 s2 :
  Included A s1 s2 ->
  Same_set _ (Union _ s1 s2) s2.
Proof.
  intros Hin; split.
  - intros x Hx. inv Hx; eauto.
  - now apply Included_Union_r.
Qed.

Lemma Intersection_Same_set {A} s1 s2 :
  Included A s1 s2 ->
  Same_set _ (Intersection _ s1 s2) s1.
Proof.
  intros Hin; split.
  - intros x Hx. inv Hx; eauto.
  - intros x Hx. constructor; eauto.
Qed.


Lemma not_In_Empty_set {A} x :
  ~ (In A (Empty_set A) x).
Proof.
  intros Hc; inv Hc.
Qed.

Lemma Included_Empty_set_l {A} s :
  Included A s (Empty_set A) ->
  Same_set A (Empty_set A) s.
Proof.
  intros H; split; eauto.
  intros x H'. inv H'.
Qed.

Lemma Included_Empty_set_r {A} s :
  Included A s (Empty_set A) ->
  Same_set A s (Empty_set A).
Proof.
  intros H; split; eauto.
  intros x H'. inv H'.
Qed.

Lemma Union_Same_set_Empty_set_l {A} s1 s2 :
  Same_set A (Union A s1 s2) (Empty_set A) ->
  Same_set A s1 (Empty_set A).
Proof.
  intros [H1 H2]. split; intros x H; try inv H.
  eapply H1; eauto.
Qed.

Lemma Union_Same_set_Empty_set_r {A} s1 s2 :
  Same_set A (Union A s1 s2) (Empty_set A) ->
  Same_set A s2 (Empty_set A).
Proof.
  intros [H1 H2]. split; intros x H; try inv H.
  eapply H1; eauto.
Qed.

Lemma Union_Same_set_Empty_set {A} s1 s2 :
  Same_set A (Union A s1 s2) (Empty_set  A) ->
  Same_set A s1 (Empty_set A) /\ Same_set A s2 (Empty_set A) .
Proof.
  split; eauto using Union_Same_set_Empty_set_l, Union_Same_set_Empty_set_r.
Qed.

Lemma Complement_Disjoint {A} S1 S2 :
  Included A S1 S2 ->
  Disjoint A (Complement _ S2) S1.
Proof.
  intros Hin. constructor. intros x Hin'.
  inv Hin'. eauto.
Qed.


Lemma Complement_antimon {A} S1 S2 :
  Included A S1 S2 ->
  Included A (Complement _ S2) (Complement _ S1).
Proof.
  intros Hin x Hin' y. eauto.
Qed.

#[global] Hint Immediate not_In_Empty_set : Ensembles_DB.
#[global] Hint Resolve  Included_Empty_set_l Included_Empty_set_r Complement_antimon
     Complement_Disjoint : Ensembles_DB.

(** ** Big union *)

Definition big_cup {A B} (S : Ensemble A) (f : A -> Ensemble B) : Ensemble B :=
  fun y => exists x, S x /\ f x y.

Notation "\bigcup_ i F" := (big_cup (Full_set _) (fun i => F))
  (at level 41, F at level 41, i at level 0,
   format "'[' \bigcup_ i '/  '  F ']'") : Ensembles_scope.
Notation "\bigcup_ ( i : t ) F" := (big_cup (Full_set t) (fun i => F))
  (at level 41, F at level 41, i at level 50, only parsing) : Ensembles_scope.
Notation "\bigcup_ ( i 'in' A ) F" := (big_cup A (fun i => F))
  (at level 41, F at level 41, i, A at level 50,
   format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'") : Ensembles_scope.


Lemma Union_big_cup {A B} (S1 S2 : Ensemble A) f :
  Same_set _ (big_cup (Union A S1 S2) f)
           (Union B (big_cup S1 f) (big_cup S2 f)).
Proof.
  split; intros x H.
  - destruct H as [y [H1 H2]]. inv H1.
    + left; exists y; eauto.
    + right; exists y; eauto.
  - inv H; destruct H0 as [y [H1 H2]];
    exists y; split; eauto. left; eauto. right; eauto.
Qed.

Lemma Setminus_big_cup {A B} S1 S2 f :
  Same_set B (big_cup S1 (fun (x : A) => (Setminus _ (f x) S2)))
           (Setminus B (big_cup S1 f) S2).
Proof.
  split; intros x H.
  - inv H. inv H0. inv H1. constructor; eauto. exists x0; split; eauto.
  - inv H. inv H0. inv H. exists x0. split; eauto. constructor; eauto.
Qed.

Lemma big_cup_Singleton {A B} (x : A) f :
  Same_set B (big_cup (Singleton _ x) f) (f x).
Proof.
  split; intros x' H.
  - inv H. destruct H0 as [H1 H2]. inv H1; eauto.
  - exists x; split; eauto. constructor; eauto.
Qed.

Lemma big_cup_Empty_set {A B} f :
  Same_set B (big_cup (Empty_set A) f) (Empty_set B).
Proof.
  split; intros x' H; inv H. inv H0. inv H.
Qed.

Lemma big_cup_const {A B} s1 s2 :
  Inhabited A s1 ->
  Same_set B (big_cup s1 (fun (_  : A) => s2)) s2.
Proof.
  intros [x H].
  split; intros x' H'.
  - inv H'. inv H0; eauto.
  - exists x. split; eauto.
Qed.

Lemma Included_big_cup_l {A B} S1 S2 f :
  Included A S1 S2 ->
  Included B (big_cup S1 f) (big_cup S2 f).
Proof.
  intros H x [y [Hin Hf]].
  eexists; split; eauto. apply H; eauto.
Qed.

Lemma Included_big_cup_r {A B} S f g :
  (forall (x : A), Same_set B (f x) (g x)) ->
  Included B (big_cup S f) (big_cup S g).
Proof.
  intros H  x H''.
  inv H''. inv H0. eexists; split; eauto.
  apply H; eauto.
Qed.

Lemma Included_big_cup {A B} S1 S2 f g :
  (forall (x : A), Same_set B (f x) (g x)) ->
  Included A S1 S2 ->
  Included B (big_cup S1 f) (big_cup S2 g).
Proof.
  intros H H' x H''.
  eapply Included_big_cup_l. eassumption.
  eapply Included_big_cup_r; eassumption.
Qed.

Lemma Same_Set_big_cup_l {A B} S1 S2 f :
  Same_set A S1 S2 ->
  Same_set B (big_cup S1 f) (big_cup S2 f).
Proof.
  intros H.
  split; intros x H'.
  - inv H'. inv H0. eexists; split; eauto. apply H; eauto.
  - inv H'. inv H0. eexists; split; eauto. apply H; eauto.
Qed.

#[global] Instance Proper_big_cup {A B} : Proper (Same_set A ==> eq ==> Same_set B) big_cup.
Proof.
  intros ? ? ? ? ? ?; subst. now apply Same_Set_big_cup_l.
Qed.

Lemma Same_Set_big_cup_r {A B} S f g :
  (forall (x : A), Same_set B (f x) (g x)) ->
  Same_set B (big_cup S f) (big_cup S g).
Proof.
  intros H.
  split; intros x H'.
  - inv H'. inv H0. eexists; split; eauto. apply H; eauto.
  - inv H'. inv H0. eexists; split; eauto. apply H; eauto.
Qed.

Lemma Same_Set_big_cup {A B} S1 S2 f g :
  (forall (x : A), Same_set B (f x) (g x)) ->
  Same_set A S1 S2 ->
  Same_set B (big_cup S1 f) (big_cup S2 g).
Proof.
  intros H.
  split; intros x H'.
  - inv H'. inv H0. inv H1. eexists; split; eauto. apply H2; eauto.
    apply H; eauto.
  - inv H'. inv H0. inv H1. eexists; split; eauto. apply H3; eauto.
    apply H; eauto.
Qed.

Lemma bigcup_merge {A} (F : nat -> Ensemble A) :
  \bigcup_n (\bigcup_m (F (n + m)%nat)) <-->  \bigcup_n (F n).
Proof.
  split; intros x [i [_ Hin]].
  - destruct Hin as [j [_ Hin]].
    exists (i + j)%nat. split; eauto. constructor.
  - exists 0%nat. split. now constructor. exists i.
      split; eauto. constructor.
Qed.

#[global] Hint Immediate Union_big_cup Setminus_big_cup big_cup_Singleton
     big_cup_Empty_set: Ensembles_DB.
#[global] Hint Resolve Included_big_cup_l Same_Set_big_cup_l : Ensembles_DB.

(** * List of sets union *)

Fixpoint Union_list {A} (l : list (Ensemble A)) : Ensemble A :=
  match l with
    | nil => Empty_set _
    | cons x xs => x :|: Union_list xs
  end.


(** * Coercion from lists *)

Definition FromList {A} (l : list A) : Ensemble A :=
  fun x => List.In x l.

(* TODO : generalize the type *)
#[global] Instance Decidable_FromList (l : list positive) : Decidable (FromList l).
Proof.
  constructor. intros x. induction l.
  - right. intros H. inv H.
  - destruct (peq a x) as [Hin | Hnin].
    + subst. left. constructor. eauto.
    + destruct IHl. left. now constructor 2.
      right. intros Hc. eapply Hnin. inv Hc; eauto.
      congruence.
Qed.

Lemma FromList_nil {A}  :
  Same_set A (FromList nil) (Empty_set A).
Proof.
  split; intros x H; inv H.
Qed.

Lemma FromList_cons {A} x (l : list A) :
  Same_set A (FromList (x::l)) (Union A (Singleton A x) (FromList l)).
Proof.
  constructor; intros x' H.
  - inv H; eauto.
  - inv H. inv H0; constructor; eauto.
    constructor 2. eauto.
Qed.

Lemma FromList_app {A} (l1 l2 : list A) :
  Same_set _ (FromList (l1 ++ l2)) (Union _ (FromList l1) (FromList l2)).
Proof.
  induction l1.
  - rewrite FromList_nil, Union_Empty_set_neut_l. now apply Same_set_refl.
  - rewrite FromList_cons, <- Union_assoc, <- IHl1,
    <- FromList_cons, app_comm_cons.
    now apply Same_set_refl.
Qed.

Lemma FromList_singleton {A} x :
  Same_set A (FromList [x]) (Singleton A x).
Proof.
  rewrite FromList_cons, FromList_nil, Union_Empty_set_neut_r.
  constructor; intros x' H; inv H; eauto.
Qed.

Lemma FromList_subset_included {A} (l1 l2 : list A) :
  FromList l1 \subset FromList l2 <->
  incl l1 l2.
Proof.
  split; eauto.
Qed.

Lemma Same_set_FromList_length {A} (l1 l2 : list A) :
  NoDup l1 ->
  FromList l1 \subset FromList l2 ->
  List.length l1 <= List.length l2.
Proof.
  eapply NoDup_incl_length.
Qed.

Lemma FromList_Union_split {A} (l : list A) S1 S2 :
  FromList l \subset Union _ S1 S2 ->
  exists l1 l2,
    Permutation (l1 ++ l2) l /\
    FromList l1 \subset S1 /\
    FromList l2 \subset S2.
Proof.
  induction l; intros Hun.
  - exists [], []. firstorder.
  - rewrite FromList_cons in Hun.
    assert (Hin1 := Union_Included_l _ _ _ Hun).
    assert (Hin2 := Union_Included_r _ _ _ Hun).
    eapply Singleton_Included_r in Hin1.
    edestruct IHl as [l1 [l2 [Hperm [Hs1 Hs2]]]]; eauto.
    inv Hin1.
    + eexists (a :: l1), l2.
      split; [| split ].
      rewrite <- app_comm_cons. eapply perm_skip.
      eassumption.
      rewrite FromList_cons. eapply Union_Included; eauto.
      eapply Singleton_Included. eauto.
      eassumption.
    + eexists l1, (a :: l2).
      split; [| split ].
      rewrite Permutation_app_comm.
      rewrite <- app_comm_cons. eapply perm_skip.
      rewrite <- Permutation_app_comm. eassumption.
      eassumption.
      rewrite FromList_cons. eapply Union_Included; eauto.
      eapply Singleton_Included. eauto.
Qed.

#[global] Instance Decidable_FromList_gen A (H : forall (x y : A), {x = y} + {x <> y}) (l : list A) :
  Decidable (FromList l).
Proof.
  constructor. intros x. induction l.
  - right. intros H1. inv H1.
  - destruct (H a x); subst.
    + left. constructor. eauto.
    + destruct IHl. left. now constructor 2.
      right. intros Hc. inv Hc; eauto.
Qed.

(* TODO move *)
#[global] Instance Decidable_map_UnionList {A B : Type} (f : A -> Ensemble B) (H : forall x, Decidable (f x)) l :
  Decidable (Union_list (map f l)).
Proof.
  induction l; constructor.
  - intros x; right; intros Hc; inv Hc.
  - intros x. simpl.
    destruct (H a) as [Hdec]. destruct (Hdec x); eauto.
    + left. left. eassumption.
    + destruct IHl as [Hdec']. destruct (Hdec' x).
      left; right; eauto.
      right; intros Hc.
      inv Hc; contradiction.
Qed.

Lemma In_Union_list {A} (l : list (Ensemble A)) s:
  List.In s l ->
  s \subset Union_list l.
Proof.
  intros Hin. induction l.
  - now inv Hin.
  - inv Hin. now eapply Included_Union_l.
    simpl. eapply Included_Union_preserv_r.
    eapply IHl; eauto.
Qed.

Lemma Union_lists_exists {A} (x : A) ls :
  x \in Union_list ls ->
        exists S, List.In S ls /\ x \in S.
Proof.
  induction ls; intros Hin; try now inv Hin.
  inv Hin.
  - eexists. split; eauto. now left.
  - edestruct IHls as [S [Hin1 Hin2]].
    eassumption.
    eexists. split; eauto. now right.
Qed.


#[global] Hint Immediate FromList_nil FromList_cons FromList_app
     FromList_singleton : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?B (Union _ ?A ?D))) =>
rewrite (Union_assoc A B C), (Union_assoc B A D), (Union_commut A B) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ (Union _ ?B ?A) ?D)) =>
rewrite (Union_assoc A B C), (Union_commut A B) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ (Union _ ?B ?A) ?D)
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_commut A B) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?B (Union _ ?A ?D))) =>
rewrite (Union_assoc A B C), (Union_assoc B A D), (Union_commut A B) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ (Union _ ?B ?A) ?D)) =>
rewrite (Union_assoc A B C), (Union_commut A B) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ (Union _ ?B ?A) ?D)
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_commut A B) : Ensembles_DB.



#[global] Hint Extern 1 (Same_set _ _ (Union _ (Union _ ?A ?A) ?C)) =>
rewrite (Union_Same_set A A); [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ (Union _ (Union _ ?A ?A) ?C) _) =>
rewrite (Union_Same_set A A);  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ _ (Union _ ?A (Union _ ?A ?C))) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ (Union _ ?A (Union _ ?A ?C)) _) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Included _ _ (Union _ (Union _ ?A ?A) ?C)) =>
rewrite (Union_Same_set A A); [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ (Union _ ?A ?A) ?C) _) =>
rewrite (Union_Same_set A A);  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Included _ _ (Union _ ?A (Union _ ?A ?C))) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ ?A (Union _ ?A ?C)) _) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ _ (Union _ (Union _ ?A ?A) ?C)) =>
rewrite (Union_Same_set A A); [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ (Union _ (Union _ ?A ?A) ?C) _) =>
rewrite (Union_Same_set A A);  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ _ (Union _ ?A (Union _ ?A ?C))) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ (Union _ ?A (Union _ ?A ?C)) _) =>
rewrite (Union_assoc A A C), (Union_Same_set A A);
  [| now apply Included_refl ] : Ensembles_DB.


#[global] Hint Extern 1 (Same_set _
                        (Setminus _ _ (Union _ _ _))
                        (Setminus _ (Setminus _ _ _) _)) =>
rewrite Setminus_Union : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Setminus _ (Setminus _ _ _) _)
                        (Setminus _ _ (Union _ _ _))) =>
rewrite Setminus_Union : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Setminus _ (Union _ _ _) _)
                        (Union _ (Setminus _ _ ?A) (Setminus _ _ ?A))) =>
rewrite Setminus_Union_distr : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ (Setminus _ _ ?A) (Setminus _ _ ?A))
                        (Setminus _ (Union _ _ _) _)) =>
rewrite Setminus_Union_distr : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Setminus _ _ (Union _ _ _))
                        (Setminus _ (Setminus _ _ _) _)) =>
rewrite Setminus_Union : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Setminus _ (Setminus _ _ _) _)
                        (Setminus _ _ (Union _ _ _))) =>
rewrite Setminus_Union : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Setminus _ (Union _ _ _) _)
                        (Union _ (Setminus _ _ ?A) (Setminus _ _ ?A))) =>
rewrite Setminus_Union_distr : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ (Setminus _ _ ?A) (Setminus _ _ ?A))
                        (Setminus _ (Union _ _ _) _)) =>
rewrite Setminus_Union_distr : Ensembles_DB.


#[global] Hint Extern 1 (Same_set _ (Union _ (Empty_set _) _) _) =>
rewrite Union_Empty_set_neut_l : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ (Empty_set _) _) _) =>
rewrite Union_Empty_set_neut_l :  Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ (Union _ (Empty_set _) _) _) =>
rewrite Union_Empty_set_neut_l : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ (Union _ _ (Empty_set _)) _) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ _ (Empty_set _)) _) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ (Union _ _ (Empty_set _)) _) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ _ (Union _ (Empty_set _) _)) =>
rewrite Union_Empty_set_neut_l : Ensembles_DB.

#[global] Hint Extern 1 (Included _ _ (Union _ (Empty_set _) _)) =>
rewrite Union_Empty_set_neut_l :  Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ _ (Union _ (Empty_set _) _)) =>
rewrite Union_Empty_set_neut_l : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ _ (Union _ _ (Empty_set _))) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.

#[global] Hint Extern 1 (Included _ _ (Union _ _ (Empty_set _))) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.

#[global] Hint Extern 1 (Disjoint _ _ (Union _ _ (Empty_set _))) =>
rewrite Union_Empty_set_neut_r : Ensembles_DB.


#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?D (Union _ ?A ?E))) =>
rewrite (Union_assoc A B C), (Union_assoc D A E), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?D (Union _ ?A ?E))
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_assoc D A E), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?D (Union _ ?E ?A))) =>
rewrite (Union_assoc A B C), (Union_assoc D E A), (Union_commut (Union _ D E) A),
<- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?D (Union _ ?E ?A))
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_assoc D E A), (Union_commut (Union _ D E) A),
<- (Union_assoc A B C) : Ensembles_DB.


#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ (Union _ ?D ?A) ?E)) =>
rewrite (Union_assoc A B C), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.


#[global] Hint Extern 1 (Same_set _
                        (Union _ (Union _ ?D ?A) ?E)
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?A ?B)
                        (Union _ ?C ?A)) =>
rewrite (Union_commut C A) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _
                        (Union _ ?C ?A)
                        (Union _ ?A ?B)) =>
rewrite (Union_commut C A) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?D (Union _ ?A ?E))) =>
rewrite (Union_assoc A B C), (Union_assoc D A E), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?D (Union _ ?A ?E))
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_assoc D A E), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ ?D (Union _ ?E ?A))) =>
rewrite (Union_assoc A B C), (Union_assoc D E A), (Union_commut (Union _ D E) A),
<- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?D (Union _ ?E ?A))
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_assoc D E A), (Union_commut (Union _ D E) A),
<- (Union_assoc A B C) : Ensembles_DB.


#[global] Hint Extern 1 (Included _
                        (Union _ ?A (Union _ ?B ?C))
                        (Union _ (Union _ ?D ?A) ?E)) =>
rewrite (Union_assoc A B C), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.


#[global] Hint Extern 1 (Included _
                        (Union _ (Union _ ?D ?A) ?E)
                        (Union _ ?A (Union _ ?B ?C))) =>
rewrite (Union_assoc A B C), (Union_commut D A),
<- (Union_assoc A B C), <- (Union_assoc A D E) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?A ?B)
                        (Union _ ?C ?A)) =>
rewrite (Union_commut C A) : Ensembles_DB.

#[global] Hint Extern 1 (Included _
                        (Union _ ?C ?A)
                        (Union _ ?A ?B)) =>
rewrite (Union_commut C A) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ (Union _ ?A (Union _ _ _)) (Union _ (Union _ ?A ?B) ?C)) =>
rewrite <- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 1 (Same_set _ (Union _ (Union _ ?A ?B) ?C) (Union _ ?A (Union _ _ _))) =>
rewrite <- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ ?A (Union _ _ _)) (Union _ (Union _ ?A ?B) ?C)) =>
rewrite <- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 1 (Included _ (Union _ (Union _ ?A ?B) ?C) (Union _ ?A (Union _ _ _))) =>
rewrite <- (Union_assoc A B C) : Ensembles_DB.

#[global] Hint Extern 5 (Disjoint _ ?A ?B) =>
eapply Disjoint_Included_r; [| eassumption ] : Ensembles_DB.
#[global] Hint Extern 5 (Disjoint _ ?A ?B) =>
eapply Disjoint_Included_l; [| eassumption ] : Ensembles_DB.

#[global] Hint Extern 5 (Disjoint _ ?A ?B) =>
eapply Disjoint_Included_r_sym; [| eassumption ] : Ensembles_DB.
#[global] Hint Extern 5 (Disjoint _ ?A ?B) =>
eapply Disjoint_Included_l_sym; [| eassumption ] : Ensembles_DB.


Definition Proj1 {A B} (S : Ensemble (A * B)) : Ensemble A :=
  [ set x | exists y, (x, y) \in S ].

Definition Proj2 {A B} (S : Ensemble (A * B)) : Ensemble B :=
  [ set x | exists y, (y, x) \in S ].

Definition Prod {A B} (S : Ensemble A) (S' : Ensemble B) : Ensemble (A * B) :=
  [ set z | let '(x, y) := z in  x \in S /\ y \in S' ].

#[global] Instance Proj1_Proper A B : Proper (Same_set (A * B) ==> Same_set A) Proj1.
Proof.
  firstorder.
Qed.

#[global] Instance Proj2_Proper A B : Proper (Same_set (A * B) ==> Same_set B) Proj2.
Proof.
  firstorder.
Qed.

#[global] Instance Prod_Proper1 A B : Proper (Same_set A ==> eq ==> Same_set (A * B)) Prod.
Proof.
  intros s1 s2 Hseq x1 x2 Heq; subst.
  unfold Prod; split; intros [x y]; firstorder.
Qed.

#[global] Instance Proj_Proper2 A B S : Proper (Same_set B  ==> Same_set (A * B)) (Prod S).
Proof.
  intros s1 s2 Hseq; subst.
  unfold Prod; split;
  intros [x y]; firstorder.
Qed.

Lemma Proj1_Union A B (S1 : Ensemble (A * B)) (S2 : Ensemble (A * B)) :
  Proj1 (S1 :|: S2) <--> Proj1 S1 :|: Proj1 S2.
Proof.
  split; intros x Hin. destruct Hin as [y Hin]. inv Hin.
  left. eexists. eassumption.
  right. eexists. eassumption.
  destruct Hin; inv H.
  eexists. left. eassumption.
  eexists. right. eassumption.
Qed.

Lemma Proj2_Union A B (S1 : Ensemble (A * B)) (S2 : Ensemble (A * B)) :
  Proj2 (S1 :|: S2) <--> Proj2 S1 :|: Proj2 S2.
Proof.
  split; intros x Hin. destruct Hin as [y Hin]. inv Hin.
  left. eexists. eassumption.
  right. eexists. eassumption.
  destruct Hin; inv H.
  eexists. left. eassumption.
  eexists. right. eassumption.
Qed.

Lemma Prod_Union1 A B (S1 S2 : Ensemble A) (S3 : Ensemble B) :
  Prod (S1 :|: S2) S3 <--> Prod S1 S3 :|: Prod S2 S3.
Proof.
  split; intros [x y] Hin. destruct Hin as [Hin1 Hin2].
  inv Hin1. now left; firstorder.
  now right; firstorder.
  destruct Hin as [[Hin1 Hin2] | [Hin1 Hin2]];
    now firstorder.
Qed.

Lemma Prod_Union2 A B (S1 : Ensemble A) (S2 S3 : Ensemble B) :
  Prod S1 (S2 :|: S3) <--> Prod S1 S2 :|: Prod S1 S3.
Proof.
  split; intros [x y] Hin.
  destruct Hin as [Hin1 Hin2].
  inv Hin2. now left; firstorder.
  now right; firstorder.
  destruct Hin as [[Hin1 Hin2] | [Hin1 Hin2]];
    now firstorder.
Qed.

Lemma Proj1_Prod A B (S1 : Ensemble A) (S2 : Ensemble B) { HI : Inhabited B S2} :
  Proj1 (Prod S1 S2) <--> S1.
Proof.
  split; intros x; intros Hin.
  destruct Hin as [y [Hin1 Hin2]]. eassumption.
  destruct HI. eexists; split; eauto.
Qed.

Lemma Proj1_Prod_Included A B (S1 : Ensemble A) (S2 : Ensemble B) :
  Proj1 (Prod S1 S2) \subset S1.
Proof.
  intros x; intros Hin.
  destruct Hin as [y [Hin1 Hin2]]. eassumption.
Qed.

Lemma Proj2_Prod_Included A B (S1 : Ensemble A) (S2 : Ensemble B) :
  Proj2 (Prod S1 S2) \subset S2.
Proof.
  intros x; intros Hin.
  destruct Hin as [y [Hin1 Hin2]]. eassumption.
Qed.

Lemma prod_Proj1 A B (S : Ensemble (A * B)) x y :
  (x, y) \in S -> x \in Proj1 S.
Proof.
  firstorder.
Qed.

Lemma prod_Proj2 A B (S : Ensemble (A * B)) x y :
  (x, y) \in S -> y \in Proj2 S.
Proof.
  firstorder.
Qed.

Lemma Prod_proj A B (S1 : Ensemble A) (S2 : Ensemble B) z :
  z \in Prod S1 S2 ->
        fst z \in S1 /\ snd z \in S2.
Proof.
  destruct z. firstorder.
Qed.

Lemma proj_Prod A B (S1 : Ensemble A) (S2 : Ensemble B) z :
  fst z \in S1 -> snd z \in S2 -> z \in Prod S1 S2.
Proof.
  destruct z. firstorder.
Qed.


Lemma Included_Union_Setminus_Included {A} (S1 S2 S3 : Ensemble A)
      {Hd : Decidable S2}:
  S1 \\ S2 \subset S3 ->
  S1 \subset S2 :|: S3.
Proof.
  intros Hsub x Hin. destruct Hd as [Hd].
  destruct (Hd x); eauto.
  right.
  eapply Hsub. constructor; eauto.
Qed.

Lemma Setminus_Setminus_Included {A}
      (S1 S2 S3 : Ensemble A) {Hd : Decidable S3}:
  S1 \\ (S2 \\ S3) \subset S1 \\ S2 :|: S3.
Proof.
  intros x Hin. inv Hin.
  destruct Hd as [Hd].
  destruct (Hd x); eauto.
  left; constructor; eauto.
  intros Hc; eapply H0; constructor; eauto.
Qed.


Lemma Setminus_Setminus_Same_set A (S1 S2 S3 : Ensemble A) :
  Decidable S3 ->
  S3 \subset S1 ->
  (S1 \\ (S2 \\ S3)) <--> ((S1 \\ S2) :|: S3).
Proof.
  intros Hd Hin. split.
  now apply Setminus_Setminus_Included.
  destruct Hd as [D]. intros x H. destruct (D x) as [Hin' | Hnin].
  - constructor. now eapply Hin.
    intros Hc; inv Hc; eauto.
  - inv H.
    + inv H0. constructor; eauto. intros Hc.
      inv Hc; eauto.
    + exfalso; eauto.
Qed.


Lemma Same_set_Intersection_Setminus {A: Type} (S1 S2 S3 : Ensemble A)
      {_ : Decidable S3}:
  S2 \subset S3 ->
  S1 :&: (S3 \\ S2) :|: (S1 \\ S3) <--> S1 \\ S2.
Proof.
  intros Hsub; split; intros x Hin; inv Hin.
  - inv H. inv H1. constructor; eauto.
  - inv H; constructor; eauto.
  - destruct X as [Hdec]. destruct (Hdec x).
    + left. constructor; eauto.
      constructor; eauto.
    + right. constructor; eauto.
Qed.

Lemma Included_Intersection_compat {A : Type} (s1 s2 s3 s4 : Ensemble A) :
  s1 \subset s2 ->
  s3 \subset s4 ->
  s1 :&: s3 \subset s2 :&: s4.
Proof.
  intros H1 H2 x [Hin1 Hin2]. firstorder.
Qed.

Lemma Included_Intersection {A : Type} (s1 s2 s3 : Ensemble A) :
  s1 \subset s2 ->
  s1 \subset s3 ->
  s1 \subset s2 :&: s3.
Proof.
  now firstorder.
Qed.


Lemma Included_Intersection_l {A : Type} (s1 s2 : Ensemble A) :
  s1 :&: s2 \subset s1.
Proof.
  intros x [Hin1 Hin2]; eauto.
Qed.

Lemma Included_Intersection_r {A : Type} (s1 s2 : Ensemble A) :
  s1 :&: s2 \subset s2.
Proof.
  intros x [Hin1 Hin2]; eauto.
Qed.

Lemma Same_set_Intersection_compat {A : Type} (s1 s2 s3 s4 : Ensemble A):
  s1 <--> s2 -> s3 <--> s4 -> s1 :&: s3 <--> s2 :&: s4.
Proof.
  intros H1 H2; split; eapply Included_Intersection_compat;
  (try now apply H1); try now apply H2.
Qed.

Lemma Disjoint_Intersection_r {A} (s1 s2 s3 : Ensemble A) :
  Disjoint _ s2 s3 ->
  Disjoint _ (s1 :&: s2) (s1 :&: s3).
Proof with (now eauto with Ensembles_DB).
  intros Hd.
  eapply Disjoint_Included; [| | eassumption ];
  now eapply Included_Intersection_r.
Qed.

Lemma Setminus_compose {A} (s1 s2 s3 : Ensemble A) `{Decidable _ s2} :
  s1 \subset s2 ->
  s2 \subset s3 ->
  s2 \\ s1 :|: (s3 \\ s2) <--> s3 \\ s1.
Proof.
  intros H1 H2; split; intros x Hin.
  - inv Hin.
    + inv H0. constructor; eauto.
    + inv H0. constructor; eauto.
  - inv Hin. destruct H as [Hdec].
    destruct (Hdec x).
    + left. constructor; eauto.
    + right. constructor; eauto.
Qed.

Ltac normalize_sets :=
  match goal with
  | [|- context[FromList []]] => rewrite FromList_nil
  | [|- context[FromList(_ :: _)]] => rewrite FromList_cons
  | [|- context[FromList(_ ++ _)]] => rewrite FromList_app
  | [|- context[FromList [_ ; _]]] => rewrite FromList_cons
  | [|- context[Union _ _ (Empty_set _)]] =>
    rewrite Union_Empty_set_neut_r
  | [|- context[Union _ (Empty_set _) _]] =>
    rewrite Union_Empty_set_neut_l
  | [|- context[Setminus _ (Empty_set _) _]] =>
    rewrite Setminus_Empty_set_abs_r
  | [|- context[Setminus _ _ (Empty_set _)]] =>
    rewrite Setminus_Empty_set_neut_r
  | [ H : context[FromList []] |- _] => rewrite FromList_nil in H
  | [ H : context[FromList(_ :: _)] |- _] => rewrite FromList_cons in H
  | [ H : context[FromList(_ ++ _)] |- _] => rewrite FromList_app in H
  | [ H : context[FromList [_ ; _]] |- _] => rewrite FromList_cons in H
  | [ H : context[Union _ _ (Empty_set _)] |- _ ] =>
    rewrite Union_Empty_set_neut_r in H
  | [ H : context[Union _ (Empty_set _) _] |- _] =>
    rewrite Union_Empty_set_neut_l in H
  | [ H : context[Setminus _ (Empty_set _) _] |- _] =>
    rewrite Setminus_Empty_set_abs_r in H
  | [ H : context[Setminus _ _ (Empty_set _)] |- _] =>
    rewrite Setminus_Empty_set_neut_r in H
  end.

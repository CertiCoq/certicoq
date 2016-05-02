Require Import Morphisms List Ensembles.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

Hint Constructors Singleton.
Hint Constructors Union.
Hint Constructors Intersection.
Hint Unfold In.

Class Decidable {A} (S : Ensemble A) : Type :=
 { Dec : forall x, S x \/ ~ S x }.

Instance DecidableUnion {A} (S1 S2 : Ensemble A)
         {H1 : Decidable S1} {H2 : Decidable S2} : Decidable (Union A S1 S2).
Proof.
  constructor. intros x.
  edestruct (@Dec _ _ H1 x); try now left; constructor.
  edestruct (@Dec _ _ H2 x); try now left; constructor.
  right. intros Hun. inv Hun; eauto.
Qed.

Instance DecidableIntersection {A} (S1 S2 : Ensemble A)
         {H1 : Decidable S1} {H2 : Decidable S2} : Decidable (Intersection A S1 S2).
Proof.
  constructor. intros x.
  edestruct (@Dec _ _ H1 x); edestruct (@Dec _ _ H2 x);
  try (now left; constructor); right; intros Hc; inv Hc; eauto.
Qed.

Instance Decidable_Setminus {A} s1 s2 { H1 : Decidable s1 }
         { H2 : Decidable s2 } : Decidable (Setminus A s1 s2).
Proof.
  constructor. intros x. destruct H1, H2. destruct (Dec1 x).
  - right. intros Hc. inv Hc; eauto.
  - destruct (Dec0 x). left. constructor; eauto.
    right. intros Hc. inv Hc. eauto.
Qed.

Lemma Included_trans {A} s1 s2 s3 :
  Included A s1 s2 ->
  Included A s2 s3 ->
  Included A s1 s3.
Proof.
  intros H1 H2 x HIn.
  eapply H2. eapply H1; eauto.
Qed.


Instance Union_proper_l A :
  Proper (Same_set A ==> Logic.eq ==> Same_set A)
         (Union A).
Proof.
  constructor; subst; intros x' H'; destruct H'; destruct H as [H1 H2]; eauto.
Qed.

Instance Union_proper_r A :
  Proper (Logic.eq ==> Same_set A ==> Same_set A)
         (Union A).
Proof.
  constructor; subst; intros x' H'; destruct H'; destruct H0 as [H1 H2]; eauto.
Qed.

Instance Setminus_proper_l A :
  Proper (Same_set A ==> Logic.eq ==> Same_set A)
         (Setminus A).
Proof.
  constructor; intros x' H'; destruct H as [H1 H2];
  inv H'; constructor; eauto.
Qed.

Instance Setminus_proper_r A :
  Proper (Logic.eq ==> Same_set A ==> Same_set A)
         (Setminus A).
Proof.
  constructor; intros x' H'; destruct H0 as [H1 H2];
  inv H'; constructor; eauto.
Qed.

Instance Disjoint_proper_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Disjoint A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2]; inv H';
  constructor; intros x' HIn; inv HIn; eapply H; constructor; eauto.
Qed.

Instance Proper_In {A} :
  Proper (Same_set A ==> Logic.eq ==> iff) (In A).
Proof.
  constructor; intros H'; subst; destruct H as [H1 H2]; eauto.
Qed.

Instance Disjoint_proper_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Disjoint A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2]; inv H';
  constructor; intros x' HIn; inv HIn; eapply H; constructor; eauto.
Qed.

Instance Included_proper_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Included A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2];
  intros x' HIn; eauto.
Qed.

Instance Included_proper_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Included A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2];
  intros x' HIn; eauto.
Qed.


Instance Same_set_proper_l A :
  Proper (Same_set A ==> Logic.eq ==> iff)
         (Same_set A).
Proof.
  constructor; subst; intros H'; destruct H as [H1 H2]; destruct H' as [H3 H4];
  constructor; eauto; eapply Included_trans; eauto.
Qed.

Instance Same_proper_r A :
  Proper (Logic.eq ==> Same_set A ==> iff)
         (Same_set A).
Proof.
  constructor; subst; intros H'; destruct H0 as [H1 H2]; destruct H' as [H3 H4];
  constructor; eauto; eapply Included_trans; eauto.
Qed.

Lemma Included_Empty_set {A} s :
  Included A (Empty_set A) s.
Proof.
  intros x H. inv H.
Qed.

Lemma Union_Setminus {A} S1 S2 {Hdec: Decidable S2 } :
  Same_set A (Union A S1 S2) (Union A (Setminus A S1 S2) S2).
Proof.
  split; intros x H; inv H; try (now constructor).
  edestruct (Dec x); try (now constructor).
  inv H0. constructor; eauto.
Qed.

Lemma Disjoint_Setminus {A} s1 s2 s3 :
  Included A s3 s2 ->
  Disjoint A (Setminus A s1 s2) s3.
Proof.
  intros Hincl.
  constructor. intros x HIn. inv HIn. inv H.
  apply H2. apply Hincl in H0; eauto.
Qed.

Lemma Intersection_sym {A} s1 s2 :
  Same_set A (Intersection A s2 s1)
           (Intersection A s1 s2).
Proof.
  split; intros x H; inv H; constructor; eauto.
Qed.

Lemma Disjoint_sym {A} s1 s2 :
  Disjoint A s2 s1 ->
  Disjoint A s1 s2.
Proof.
  intros H. inv H. 
  constructor. intros x HIn. inv HIn.
  eapply H0; eauto.
Qed.

(* Lemma Disjoint_Singleton {A} x s1 : *)
(*   ~ s1 x -> *)
(*   Disjoint A (Singleton A x) s1. *)
(* Proof. *)
(*   intros H. constructor. *)
(*   intros x' HIn. inv HIn. inv H0. eauto. *)
(* Qed. *)

Lemma Subset_Setminus {A} s1 s2 :
  Included A (Setminus A s1 s2) s1.
Proof.
  intros x HIn. inv HIn. eauto.
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

Lemma Included_refl {A} s1 :
  Included A s1 s1.
Proof.
  intros x Hin; eauto.
Qed.

Lemma Same_set_refl A s :
  Same_set A s s.
Proof.
  split; apply Included_refl.
Qed.

Lemma Union_assoc {A} s1 s2 s3 :
  Same_set A (Union A s1 (Union A s2 s3))
           (Union A (Union A s1 s2) s3).
Proof.
  split; intros x HIn; inv HIn; eauto; inv H; eauto.
Qed.

Lemma Setminus_Union_distr {A} s1 s2 s3 :
  Same_set A (Setminus A (Union A s1 s2) s3)
           (Union A (Setminus A s1 s3) (Setminus A s2 s3)).
Proof.
  split; intros x H; inv H; inv H0; try (now try left; constructor; eauto);
  now right; constructor; eauto.
Qed.

Lemma Setminus_Empty_set {A} s:
  Same_set A (Setminus A s s) (Empty_set A).
Proof.
  split; intros x H; inv H; contradiction.
Qed.

Lemma Union_Empty_set_l {A} s:
  Same_set A (Union A s (Empty_set A)) s.
Proof.
  split; intros x H; eauto. inv H; eauto. inv H0.
Qed.

Lemma Setminus_Union {A} s1 s2 s3:
  Same_set A (Setminus A (Setminus A s1 s2) s3) 
           (Setminus A s1 (Union A s2 s3)).
Proof.
  split; intros x H'; inv H'. inv H.
  constructor; eauto. intros Hc; inv Hc; eauto.
  constructor; eauto. constructor; eauto.
Qed.

Lemma Setminus_Union_Included {A} s1 s2 s3:
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

Lemma Setminus_Included {A} s1 s2 s3:
  Included A s1 s2 ->
  Included A (Setminus A s1 s3) s2.
Proof.
  intros H.
  intros x H'; try inv H'; eauto.
Qed.

Lemma Union_Empty_set_r (A : Type) (s : Ensemble A):
  Same_set A (Union A (Empty_set A) s) s.
Proof.
  split; intros x H; try inv H; eauto. inv H0.
Qed.

Lemma Included_Union_compat {A} s1 s1' s2 s2' :
  Included A s1 s2 ->
  Included A s1' s2' ->
  Included A (Union A s1 s1') (Union A s2 s2').
Proof.
  intros H1 H2 x Hin. inv Hin; eauto.
Qed.

Lemma Union_sym {A} s1 s2 :
  Same_set A (Union A s1 s2) (Union A s2 s1).
Proof.
  split; intros x H; inv H; eauto.
Qed.

Lemma Disjoint_Empty_set_l {A} s :
  Disjoint A (Empty_set A) s.
Proof.
  constructor. intros x Hin. inv Hin. inv H.
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

Lemma Disjoint_Empty_set_r {A} s :
  Disjoint A s (Empty_set A).
Proof.
  constructor. intros x Hin. inv Hin. inv H0.
Qed.

Definition FromList {A} (l : list A) : Ensemble A :=
  fun x => List.In x l.

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

Lemma not_In_Empty_set {A} x :
  ~ (Ensembles.In A (Empty_set A) x).
Proof.
  intros Hc; inv Hc.
Qed.

Lemma Setminus_Empty_set_Included_l {A} s1 s2 :
  Decidable s2 ->
  Included A (Setminus A s1 s2) (Empty_set A) ->
  Included A s1 s2.
Proof.
  intros Hdec H1 x H.
  destruct (@Dec _ _ Hdec x); eauto.
  exfalso. eapply not_In_Empty_set. eapply H1. constructor; eauto.
Qed.

Lemma Setminus_Empty_set_Included_r {A} s1 s2 :
  Included A s1 s2 ->
  Included A (Setminus A s1 s2) (Empty_set A).
Proof.
  intros H1 x H; inv H. apply H1 in H0. contradiction.
Qed.

Definition big_cup {A B} (S : Ensemble A) (f : A -> Ensemble B) : Ensemble B := 
  fun y => exists x, S x /\ f x y.

Lemma Union_big_cup {A B} (S1 S2 : Ensemble A) f :
  Same_set _ (big_cup (Union A S1 S2) f) (Union B (big_cup S1 f) (big_cup S2 f)).
Proof.
  split; intros x H.
  - destruct H as [y [H1 H2]]. inv H1.
    + left; exists y; eauto.
    + right; exists y; eauto.
  - inv H; destruct H0 as [y [H1 H2]];
    exists y; split; eauto. left; eauto. right; eauto.
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

Lemma big_cup_const {A B} s1 s2 :
  Inhabited A s1 ->
  Same_set B (big_cup s1 (fun (_  : A) => s2)) s2.
Proof.
  intros [x H].
  split; intros x' H'.
  - inv H'. inv H0; eauto.
  - exists x. split; eauto.
Qed.

Lemma Setminus_big_cup {A B} S1 S2 f :
  Same_set B (big_cup S1 (fun (x : A) => (Setminus _ (f x) S2)))
           (Setminus B (big_cup S1 f) S2).
Proof.
  split; intros x H.
  - inv H. inv H0. inv H1. constructor; eauto. exists x0; split; eauto.
  - inv H. inv H0. inv H. exists x0. split; eauto. constructor; eauto.
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

Lemma Disjoint_Included_l {A} s1 s2 s3 :
  Included A s1 s3 ->
  Disjoint A s3 s2 ->
  Disjoint A s1 s2.
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


Lemma Disjoint_Singleton {A} s x :
  ~ s x ->
  Disjoint A s (Singleton A x).
Proof.
  intros H. constructor. intros x' Hin. inv Hin. inv H1. contradiction.
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
    eauto using Disjoint_sym, Disjoint_Setminus, Included_refl. 
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

Lemma Disjoint_Union A s1 s2 s3 :
  Disjoint A s1 s3 ->
  Disjoint A s2 s3 ->
  Disjoint A (Union A s1 s2) s3.
Proof.
  intros H1 H2. constructor. intros x H. inv H.
  inv H0. eapply H1; eauto.
  eapply H2; eauto.
Qed.

Lemma Same_set_sym A s1 s2 :
  Same_set A s1 s2 ->
  Same_set A s2 s1.
Proof.
  intros [H1 H2]; split; eauto.
Qed.

Lemma Setminus_Included_Empty_set {A} s1 s2 :
  Included A s1 s2 ->
  Same_set A (Setminus A s1 s2) (Empty_set A).
Proof.
  intros H; split; intros x H'; inv H'. exfalso; eauto.
Qed.
  
Lemma Setminus_Union_Inlcluded {A} s1 s2 s3 :
  Included A s2 s3 ->
  Same_set A (Setminus _ (Union _ s1 s2) s3) (Setminus _ s1 s3).
Proof.
  intros H.
  rewrite Setminus_Union_distr.
  rewrite (Setminus_Included_Empty_set s2 s3); eauto.
  now rewrite (Union_Empty_set_l).
Qed.

Lemma Proper_big_cup_l {A B} :
  Proper (Same_set A ==> Logic.eq ==> Same_set B) big_cup.
Proof.
  constructor; subst; intros x' H'.
  - inv H'. inv H0. eexists; split; eauto. eapply H; eauto.
  - inv H'. inv H0. eexists; split; eauto. eapply H; eauto.
Qed.

Lemma Included_big_cup {A B} S1 S2 f g :
  (forall (x : A), Same_set B (f x) (g x)) ->
  Included A S1 S2 ->
  Included B (big_cup S1 f) (big_cup S2 g).
Proof.
  intros H H' x H''.
  inv H''. inv H0. eexists; split; eauto. apply H'; eauto.
  apply H; eauto.
Qed.

Lemma Included_Union_mon_l {A} s1 s2 s3 :
  Included A s1 s2 ->
  Included A s1 (Union A s2 s3).
Proof.
  intros H x H'. left; eauto.
Qed.

Lemma Included_Union_mon_r {A} s1 s2 s3 :
  Included A s1 s3 ->
  Included A s1 (Union A s2 s3).
Proof.
  intros H x H'. right; eauto.
Qed.

Lemma Same_set_trans {A} s1 s2 s3 :
  Same_set A s1 s2 ->
  Same_set A s2 s3 ->
  Same_set A s1 s3.
Proof.
  intros [H1 H2] [H3 H4]. split; eapply Included_trans; eauto.
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

Lemma Setminus_Empty_set_Same_set {A} s :
  Same_set A (Setminus A s (Empty_set A)) s.
Proof.
  split; intros x H; try inv H; eauto.
  constructor; eauto. intros H'; inv H'.
Qed.

Lemma Included_Setminus {A} s1 s2 s2' s3 :
  Included A (Setminus A s1 s2) s3 ->
  Included A s2 s2' ->
  Included A (Setminus A s1 s2') s3.
Proof.
  intros H1 H2 x Hin. inv Hin. eapply H1. constructor; eauto.
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

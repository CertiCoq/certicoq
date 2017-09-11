(* Heaps for L6 semantics. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import Ensembles_util functions.
Require Import compcert.lib.Coqlib.

Close Scope Z_scope.

(* TODO move *)
Notation "A :|: B" := (Union _ A B) (at level 52, left associativity)
                      : Ensembles_scope.
Notation "a |: A" := ([set a] :|: A) (at level 52, left associativity)
                     : Ensembles_scope.

Notation "A :&: B" := (Intersection _ A B) (at level 48, left associativity)
                      : Ensembles_scope.

Notation "A \\ B" := (Setminus _ A B) (at level 52, left associativity)
                     : Ensembles_scope.


Module Type Heap.

  Parameter loc : Type.

  Parameter loc_dec : forall (l1 l2 : loc), { l1 = l2 } + { l1 <> l2 }.

  Parameter heap : Type -> Type. 
  
  Parameter emp : forall {A : Type}, heap A.
  
  Parameter get : forall {A : Type}, loc -> heap A -> option A.
  
  Parameter set : forall {A : Type}, A -> loc -> heap A -> heap A.
  
  Parameter alloc : forall {A : Type}, A -> heap A -> loc * heap A.

  Parameter gss :
    forall A (x : A) (l : loc) (H : heap A),
      get l (set x l H) = Some x. 

  Parameter gso :
    forall A (x : A) (l1 l2 : loc) (H : heap A),
      l1 <> l2 ->
      get l1 (set x l2 H) = get l1 H. 

  Parameter gas :
    forall A (x : A) (l : loc) (H H' : heap A),
      alloc x H = (l, H') ->
      get l H' = Some x. 

  Parameter gao :
    forall A (x : A) (l1 l2 : loc) (H H' : heap A),
      l1 <> l2 ->
      alloc x H = (l1, H') ->
      get l2 H' = get l2 H. 

  Parameter alloc_fresh :
    forall A (x : A) (l : loc) (H H' : heap A),
      alloc x H = (l, H') ->
      get l H = None.

  (** Subheap *)
  Definition subheap {A} (H1 H2 : heap A) :=
    forall x v, get x H1 = Some v -> get x H2 = Some v. 

  Infix "⊑" := subheap (at level 70, no associativity).
  
  Lemma alloc_subheap {A} (H1 H1' : heap A) l v :
    alloc v H1 = (l, H1') ->
    H1 ⊑ H1'.
  Proof.
    intros Ha x v' Hget. destruct (loc_dec x l); subst.
    + erewrite alloc_fresh in Hget; eauto; congruence.
    + erewrite gao; eauto.
  Qed.

  Lemma subheap_refl {A} (H : heap A) :
    H ⊑ H.
  Proof.
    firstorder. 
  Qed.

  Lemma subheap_trans {A} (H1 H2 H3 : heap A):
    H1 ⊑ H2 ->
    H2 ⊑ H3 ->
    H1 ⊑ H3.
  Proof.
    firstorder.
  Qed.

  (** Extensional equality of heaps *)
  Definition heap_eq {A} (S : Ensemble loc) (H1 H2 : heap A) :=
    forall x, x \in S -> get x H1 = get x H2.

  Notation  "S |- H1 ≡ H2" := (heap_eq S H1 H2) (at level 70, no associativity).
  
  Instance Equivalence_heap_eq {A} S : Equivalence (@heap_eq A S).
  Proof.
    constructor. now firstorder. now firstorder.
    intros x y z H1 H2 l Hin. rewrite H1; firstorder.
  Qed.

  Instance Proper_heap_eq {A} : Proper (Same_set loc ==> eq ==> eq ==> iff) (@heap_eq A).
  Proof.
    intros S1 S2 Heq x1 x2 Heq1 y1 y2 Heq2; subst. firstorder.
  Qed.
  
  Lemma heap_eq_antimon {A} S1 S2 (H1 H2 : heap A) :
    S1 \subset S2 ->
    S2 |- H1 ≡ H2 ->
    S1 |- H1 ≡ H2.
  Proof.
    firstorder.
  Qed.

  (** Domain *)
  Definition dom {A} (H : heap A) : Ensemble loc :=
    domain (fun l => get l H).
  
  Lemma dom_subheap {A} (H1 H2 : heap A) :
    H1 ⊑ H2 ->
    dom H1 \subset dom H2. 
  Proof.
    firstorder.
  Qed.

  Lemma subheap_heap_eq {A} (H1 H2 : heap A) :
    H1 ⊑ H2 ->
    dom H1 |- H1 ≡ H2.
  Proof.
    intros Hsub l [v Hget]. rewrite Hget.
    eapply Hsub in Hget. congruence.
  Qed.

  Lemma alloc_dom {A} H (v : A) l H' :
    alloc v H = (l, H') ->
    dom H' <--> Union _ [set l] (dom H).
  Proof. 
    intros Ha; split; intros l' Hl'. 
    - destruct Hl' as [v' Hget].
      destruct (loc_dec l l'); subst; eauto.
      right. eexists. erewrite <- gao; eauto.
    - inv Hl'.
      + inv H0. eexists; erewrite gas; eauto.
      + destruct H0 as [v' Hget].
        eexists v'. erewrite gao; eauto.
        intros Hc; subst. erewrite alloc_fresh in Hget; eauto.
        discriminate.
  Qed.

  Lemma alloc_In_dom {A} H1 (v :A) l H2 :
    alloc v H1 = (l, H2) ->
    l \in dom H2.
  Proof.
    intros. eexists. erewrite gas; eauto.
  Qed.

  Lemma heap_eq_dom {A} S (H1 H2 : heap A) S' :
    S |- H1 ≡ H2 ->
    S' \subset dom H1 ->
    S' \subset S ->
    S' \subset dom H2.
  Proof.
    intros Heq Hsub1 Hsub2 l Hin.
    specialize (Hsub1 l Hin). destruct Hsub1 as [v Hget].
    rewrite Heq in Hget; eauto.  eexists; eauto.
  Qed.

  (** The restriction of a heap in a given domain *)
  Parameter restrict : forall {A}, Ensemble loc -> heap A -> heap A -> Prop.  

  Parameter restrict_subheap :
    forall A S (H1 H2 : heap A),
      restrict S H1 H2 ->
      H2 ⊑ H1.

  Parameter restrict_In :
    forall A (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      l \in S -> 
      get l H' = get l H. 
  
  Parameter restrict_notIn :
    forall A (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      ~ l \in S -> 
      get l H' = None.

  (** Restriction in a decidable domain exists. Useful for garbage collection *)
  Parameter restrict_exists :
    forall A S (H : heap A),
      Decidable S ->
      exists H', restrict S H H'.

  Lemma restrict_domain :
    forall A S (H1 H2 : heap A),
      Decidable S ->
      restrict S H1 H2 ->
      dom H2 <--> (dom H1 :&: S).
  Proof.
    intros A S H1 H2 HD HR. split.
    - intros l Hd2. constructor.
      eapply dom_subheap. eapply restrict_subheap. eassumption.
      eassumption.
      destruct HD. destruct (Dec l); eauto.
      eapply restrict_notIn in H; [| eassumption ].
      destruct Hd2. congruence.
    - intros l Hi. inv Hi.
      eapply restrict_In in H0; [| eassumption ].
      destruct H as [v Hget]. exists v. congruence.
  Qed.      

  (** Size of a heap *)

  (** The cardinality of the domain *)
  Parameter size : forall {A}, heap A -> nat.
  
  Parameter size_with_measure : forall {A}, (A -> nat) -> heap A -> nat.
  
  Parameter size_emp :
    forall (A : Type), @size A emp = 0%nat.
  
  Parameter size_alloc :
    forall (A : Type) (x : A) (H : heap A) (H' : heap A) (l : loc) (s : nat),
      size H = s ->
      alloc x H = (l, H') ->
      size H' = (s + 1)%nat.

  Parameter size_subheap :
    forall A (H1 H2 : heap A), H1 ⊑ H2 -> size H1 <= size H2.
  
  Parameter size_with_measure_emp :
    forall (A : Type) f, @size_with_measure A f emp = 0%nat.
  
  Parameter size_with_measure_alloc :
    forall (A : Type) f (x : A) (H : heap A) (H' : heap A) (l : loc) (s : nat),
      size_with_measure f H = s ->
      alloc x H = (l, H') ->
      size_with_measure f H' = (s + f x)%nat.

  Parameter size_with_measure_subheap :
    forall A f (H1 H2 : heap A),
      H1 ⊑ H2 ->
      size_with_measure f H1 <= size_with_measure f H2.

  (** Split a heap. Not used. *)
  
  Parameter splits : forall {A}, heap A -> heap A -> heap A -> Prop. 

  Parameter splits_spec_Some :
    forall {A} (H1 H2 H : heap A) (l : loc) (v : A),
      splits H H1 H2 ->
      get l H = Some v ->
      (get l H1 = Some v /\ get l H2 = None) \/
      (get l H2 = None /\ get l H2 = Some v).

  Parameter splits_spec_None :
    forall {A} (H1 H2 H : heap A) (l : loc),
      splits H H1 H2 ->
      get l H = None ->
      get l H1 = None /\ get l H2 = None.

Lemma splits_subheap_l {A} (H H1 H2 : heap A) : 
    splits H H1 H2 -> H1 ⊑ H.
  Proof.
    intros Hs l v Hget. destruct (get l H) eqn:Heq'.
    - eapply splits_spec_Some in Heq'; eauto.
      destruct Heq' as [[Heq1 Heq22] | [Heq1 Heq2]]; congruence.
    -  eapply splits_spec_None in Heq'; eauto.
       destruct Heq'; congruence.
  Qed.

  Lemma splits_subheap_r {A} (H H1 H2 : heap A) : 
    splits H H1 H2 -> H2 ⊑ H.
  Proof.
    intros Hs l v Hget. destruct (get l H) eqn:Heq'.
    - eapply splits_spec_Some in Heq'; eauto.
      destruct Heq' as [[Heq1 Heq22] | [Heq1 Heq2]]; congruence.
    -  eapply splits_spec_None in Heq'; eauto.
       destruct Heq'; congruence.
  Qed.

End Heap.
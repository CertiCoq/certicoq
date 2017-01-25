(* Heaps for L6 semantics. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import Ensembles_util functions.
From Libraries Require Import Coqlib.


Module Type Heap.

  Parameter loc : Type.

  Parameter loc_dec : forall (l1 l2 : loc), { l1 = l2 } + { l1 <> l2 }.

  Parameter heap : Type -> Type. 
  
  Parameter emp : forall {A}, heap A.
  
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
  
  (** The restriction of a heap in a given domain *)
  Parameter restrict : forall {A}, Ensemble loc -> heap A -> heap A -> Prop.  
  
  Parameter restrict_In :
    forall A (x : A) (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      l \in S -> 
      get l H' = get l H. 
  
  Parameter restrict_notIn :
    forall A (x : A) (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      ~ l \in S -> 
      get l H = get l H'.

  (** The size of a heap *)
  Parameter size : forall {A}, heap A -> nat -> Prop.

  Parameter size_with_measure : forall {A}, (A -> nat) -> heap A -> nat -> Prop.
  
  Parameter size_emp :
    forall (A : Type), @size A emp 0.

  Parameter size_alloc :
    forall (A : Type) (x : A) (H : heap A) (s : nat),
      size H s ->
      size (snd (alloc x H)) (s + 1).

  Parameter size_with_measure_emp :
    forall (A : Type) f, @size_with_measure A f emp 0.

  Parameter size_with_measure_alloc :
    forall (A : Type) f (x : A) (H : heap A) (s : nat),
      size_with_measure f H s ->
      size_with_measure f (snd (alloc x H)) (s + f x).

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
    
  Definition subheap {A} (H1 H2 : heap A) :=
    forall x v, get x H1 = Some v -> get x H2 = Some v. 

  Infix "⊑" := subheap (at level 70, no associativity).

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

  Lemma alloc_subheap {A} (H1 H1' : heap A) l v :
    alloc v H1 = (l, H1') ->
    H1 ⊑ H1'.
  Proof.
    intros Ha x v' Hget. destruct (loc_dec x l); subst.
    + erewrite alloc_fresh in Hget; eauto; congruence.
    + erewrite gao; eauto.
  Qed.

  Definition dom {A} (H : heap A) : Ensemble loc :=
    domain (fun l => get l H).
   
  Lemma dom_subheap {A} (H1 H2 : heap A) :
    H1 ⊑ H2 ->
    dom H1 \subset dom H2. 
  Proof.
    firstorder.
  Qed.

  Lemma heap_eq_antimon {A} S1 S2 (H1 H2 : heap A) :
    S1 \subset S2 ->
    S2 |- H1 ≡ H2 ->
    S1 |- H1 ≡ H2.
  Proof.
    firstorder.
  Qed.
  
End Heap.
(* Heaps for L6 semantics. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms Sorting.Permutation.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import Ensembles_util functions List_util cps set_util.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Module Type Heap.

  Definition loc := positive.
  
  Parameter heap : Type -> Type. 
  
  Parameter emp : forall {A : Type}, heap A.
  
  Parameter get : forall {A : Type}, loc -> heap A -> option A.
  
  Parameter set : forall {A : Type}, A -> loc -> heap A -> heap A.
  
  Parameter alloc : forall {A : Type}, A -> heap A -> loc * heap A.
  
  Parameter emp_get :
    forall (A : Type) (l : loc), get l (@emp A) = None. 

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
  
  (** Extensional equality of heaps *)
  Definition heap_eq {A} (S : Ensemble loc) (H1 H2 : heap A) :=
    forall x, x \in S -> get x H1 = get x H2.

  Notation  "S |- H1 ≡ H2" := (heap_eq S H1 H2) (at level 70, no associativity).
  
  (** Domain *)
  Definition dom {A} (H : heap A) : Ensemble loc :=
    domain (fun l => get l H).
  
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


  (** Elements *)
  Parameter heap_elements : forall {A}, heap A -> list (loc * A).

  Parameter heap_elements_sound :
    forall (A : Type) (h : heap A) (l : loc) (v : A),
      List.In (l, v) (heap_elements h) -> get l h = Some v.

  Parameter heap_elements_complete :
    forall (A : Type) (h : heap A) (l : loc) (v : A),
      get l h = Some v -> List.In (l, v) (heap_elements h).
  
  Parameter heap_elements_NoDup :
    forall (A : Type) (h : heap A),
     NoDup (heap_elements h).


  (** Elements filter *)
  Parameter heap_elements_filter : forall {A} (H : Ensemble loc) {_ : ToMSet H}, heap A -> list (loc * A).
  
  Parameter heap_elements_filter_sound :
    forall (A : Type) (S : Ensemble loc) {H : ToMSet S} (h : heap A) (l : loc) (v : A),
      List.In (l, v) (heap_elements_filter S h) -> get l h = Some v /\ l \in S.
  
  Parameter heap_elements_filter_complete :
    forall (A : Type) (S : Ensemble loc) {H : ToMSet S} (h : heap A) (l : loc) (v : A),
      get l h = Some v -> l \in S -> List.In (l, v) (heap_elements_filter S h).
  
  Parameter heap_elements_filter_NoDup :
    forall (A : Type)  (S : Ensemble loc) {H : ToMSet S} (h : heap A),
     NoDup (heap_elements_filter S h).
  
  Parameter heap_elements_filter_set_Equal :
    forall (A : Type)  (S1 : Ensemble loc) {H1 : ToMSet S1}  (S2 : Ensemble loc) {H2 : ToMSet S2} (h : heap A),
      S1 <--> S2 ->
      heap_elements_filter S1 h = heap_elements_filter S2 h.

  (** Size of a heap *)

  (** The cardinality of the domain *)
  Definition size {A : Type} (h : heap A) : nat := List.length (heap_elements h).
  
  Definition size_with_measure {A : Type} (f : A -> nat) (h : heap A) : nat :=
    fold_left (fun acc h => acc + f (snd h)) (heap_elements h) 0%nat.

  Definition max_with_measure {A : Type} (f : A -> nat) (h : heap A) : nat :=
    fold_left (fun acc h => max acc (f (snd h))) (heap_elements h) 0%nat.
  
  Definition size_with_measure_filter {A : Type}
             (f : A -> nat) (S : Ensemble loc) {H : ToMSet S}  (h : heap A) : nat :=
    fold_left (fun acc h => acc + f (snd h)) (heap_elements_filter S h) 0%nat.


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

End Heap.

Module HeapLemmas (H : Heap).

  Import H.
  
  Lemma loc_dec : forall (l1 l2 : loc), { l1 = l2 } + { l1 <> l2 }.
  Proof.
    intros l1 l2. 
    eapply Pos.eq_dec.
  Qed.

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
      destruct HD. destruct (Dec l) as [Hin | Hnin]; eauto.
      eapply restrict_notIn in Hnin; [| eassumption ].
      destruct Hd2. congruence.
    - intros l Hi. inv Hi.
      eapply restrict_In in H0; [| eassumption ].
      destruct H as [v Hget]. exists v. congruence.
  Qed.      
  
  Lemma heap_elements_empty (A : Type) :
    @heap_elements A emp = [].
  Proof.
    destruct (@heap_elements _ emp) as [| [l v] ls] eqn:Hh.
    reflexivity.
    assert (Hd : get l emp = Some v).
    { eapply heap_elements_sound. rewrite Hh. now constructor. }
    rewrite emp_get in Hd. discriminate.
  Qed.

  Lemma heap_elements_alloc (A : Type) (h h' : heap A) (l : loc) (v : A) :
    alloc v h = (l, h') -> 
    Permutation (heap_elements h') ((l, v) :: (heap_elements h)) .
  Proof.
    intros Ha. 
    eapply NoDup_Permutation.
    - eapply heap_elements_NoDup. 
    - constructor.
      intros Hin. eapply heap_elements_sound in Hin.
      eapply alloc_fresh in Ha. congruence.
      eapply heap_elements_NoDup.
    - intros [l' v']; split; intros Hin.
      + eapply heap_elements_sound in Hin. 
        destruct (loc_dec l l'); subst.
        * erewrite gas in Hin; [| eassumption ]. 
          inv Hin. now constructor.
        * erewrite gao in Hin; eauto.
          constructor 2. eapply heap_elements_complete.
          eassumption.
      + inv Hin.
        * inv H.
          eapply heap_elements_complete.
          erewrite gas; [| eassumption ].
          reflexivity.
        * eapply heap_elements_sound in H.
          eapply heap_elements_complete.
          erewrite gao; eauto.
          intros Hc. subst.
          erewrite alloc_fresh in H; eauto.
          congruence.
  Qed.

  Lemma heap_elements_filter_empty (A : Type) (S : Ensemble loc) {H : ToMSet S}:
    @heap_elements_filter A S H emp = [].
  Proof.
    destruct (@heap_elements_filter _ _ _ emp) as [| [l v] ls] eqn:Hh.
    reflexivity.
    assert (Hd : get l emp = Some v). 
    { eapply heap_elements_filter_sound with (S := S). rewrite Hh. now constructor. }
    rewrite emp_get in Hd. discriminate.
  Qed.
  
  Lemma heap_elements_filter_alloc (A : Type) (S : Ensemble loc) {H : ToMSet S}
        (h h' : heap A) (l : loc) (v : A) :
    alloc v h = (l, h') ->
    l \in S ->
    Permutation (heap_elements_filter S h') ((l, v) :: (heap_elements_filter S h)).
  Proof.
    intros Ha Hin. 
    eapply NoDup_Permutation.
    - eapply heap_elements_filter_NoDup. 
    - constructor.
      intros Hin'. eapply heap_elements_filter_sound in Hin'.
      inv Hin'.
      eapply alloc_fresh in Ha. congruence.
      eapply heap_elements_filter_NoDup.
    - intros [l' v']; split; intros Hin'.
      + eapply heap_elements_filter_sound in Hin'. 
        destruct (loc_dec l l'); subst.
        * erewrite gas in Hin'; [| eassumption ]. 
          inv Hin'. inv H0. now constructor.
        * erewrite gao in Hin'; eauto.
          inv Hin'. constructor 2. eapply heap_elements_filter_complete.
          eassumption. eassumption.
      + inv Hin'.
        * inv H0.
          eapply heap_elements_filter_complete.
          erewrite gas; [| eassumption ].
          reflexivity. eassumption.
        * eapply heap_elements_filter_sound in H0. inv H0.
          eapply heap_elements_filter_complete.
          erewrite gao; eauto.
          intros Hc. subst.
          erewrite alloc_fresh in H1; eauto.
          congruence. eassumption.
  Qed.

  Lemma heap_elements_filter_alloc_nin (A : Type)
        (S : Ensemble loc) {H : ToMSet S}
        (h h' : heap A) (l : loc) (v : A) :
    alloc v h = (l, h') ->
    ~ l \in S ->
    Permutation (heap_elements_filter S h') (heap_elements_filter S h).
  Proof.
    intros Ha Hin. 
    eapply NoDup_Permutation.
    - eapply heap_elements_filter_NoDup. 
    - eapply heap_elements_filter_NoDup. 
    - intros [l' v']; split; intros Hin'.
      + eapply heap_elements_filter_sound in Hin'. 
        destruct (loc_dec l l'); subst.
        * erewrite gas in Hin'; [| eassumption ]. 
          inv Hin'. contradiction.
        * erewrite gao in Hin'; eauto.
          inv Hin'. eapply heap_elements_filter_complete.
          eassumption. eassumption.
      + eapply heap_elements_filter_sound in Hin'. 
        inv Hin'. 
        eapply heap_elements_filter_complete; eauto.
        erewrite gao; eauto.
        intros Hc; subst; contradiction.
  Qed.

  Lemma heap_elements_filter_add (A : Type) (S : Ensemble loc) {H : ToMSet S}
        (H : heap A) (l : loc) (v : A) :
    get l H = Some v ->
    ~ l \in S ->
    Permutation (heap_elements_filter (l |: S) H) ((l, v) :: (heap_elements_filter S H)) .
  Proof.
    intros Hget Hnin.
    eapply NoDup_Permutation.
    - eapply heap_elements_filter_NoDup. 
    - constructor.
      intros Hin. eapply Hnin. 
      edestruct heap_elements_filter_sound as [Hin1 Hin2];
        eassumption.
      eapply heap_elements_filter_NoDup. 
    - intros [l' v']. split.
      + intros Hin. edestruct heap_elements_filter_sound as [Hin1 Hin2].
        eassumption.
        eapply PS.add_spec in Hin2. inv Hin2.
        * rewrite Hget in Hin1. inv Hin1. now constructor.
        * constructor 2. eapply heap_elements_filter_complete; eassumption.
      + intros Hin. inv Hin.
        * inv H0.
          eapply heap_elements_filter_complete. eassumption.
          eapply PS.add_spec. eauto.
        * edestruct heap_elements_filter_sound as [Hin1 Hin2].
          eassumption.
          eapply heap_elements_filter_complete. eassumption.
          eapply PS.add_spec. now right.
  Qed.

  
  Lemma subheap_Subperm (A : Type) (h1 h2 : heap A) : 
    h1 ⊑ h2 ->
    Subperm (heap_elements h1) (heap_elements h2).
  Proof.
    intros Hsub.
    eapply incl_Subperm.
    now eapply heap_elements_NoDup.
    intros [l v] Hin. eapply heap_elements_sound in Hin. 
    eapply heap_elements_complete.
    eauto.
  Qed.

  Lemma subheap_filter_Subperm (A : Type) (s : PS.t) (h1 h2 : heap A) : 
    h1 ⊑ h2 ->
    Subperm (heap_elements_filter s h1) (heap_elements_filter s h2).
  Proof.
    intros Hsub.
    eapply incl_Subperm.
    now eapply heap_elements_filter_NoDup.
    intros [l v] Hin. eapply heap_elements_filter_sound in Hin. 
    inv Hin. eapply heap_elements_filter_complete; eauto.
  Qed.
  
  Lemma size_emp :
    forall (A : Type), @size A emp = 0%nat.
  Proof.
    intros. unfold size. simpl.
    rewrite heap_elements_empty. reflexivity.
  Qed.

  Lemma size_alloc (A : Type) (x : A) (H : heap A) (H' : heap A) (l : loc) (s : nat):
    size H = s ->
    alloc x H = (l, H') ->
    size H' = (s + 1)%nat.
  Proof.
    intros Hs1 Ha.
    unfold size in *. eapply heap_elements_alloc in Ha.
    erewrite Permutation_length; [| eassumption ].
    simpl. omega.
  Qed.

  Lemma size_subheap :
    forall A (H1 H2 : heap A), H1 ⊑ H2 -> size H1 <= size H2.
  Proof.
    intros A H1 H2 Hsub.
    eapply Subperm_length.
    eapply subheap_Subperm.
    eassumption.
  Qed.

  Lemma size_with_measure_emp (A : Type) f :
    @size_with_measure A f emp = 0%nat.
  Proof.
    unfold size_with_measure.
    rewrite heap_elements_empty. reflexivity.
  Qed.

  Lemma size_with_measure_alloc
        (A : Type) f (x : A) (H : heap A) (H' : heap A) (l : loc) (s : nat) : 
    size_with_measure f H = s ->
    alloc x H = (l, H') ->
    size_with_measure f H' = (s + f x)%nat.
  Proof.
    intros Hs1 Ha.
    unfold size_with_measure in *. eapply heap_elements_alloc in Ha.
    erewrite fold_permutation; [| now firstorder | eassumption ].
    simpl.
    replace (f x) with ((fun acc h => acc + f (snd h)) 0 (l, x)); [| reflexivity ].
    erewrite List_util.fold_left_comm with (f0 := fun acc h => acc + f (snd h)); [| now firstorder ].
    omega.
  Qed.

  Lemma size_with_measure_subheap :
    forall A f (H1 H2 : heap A),
      H1 ⊑ H2 ->
      size_with_measure f H1 <= size_with_measure f H2.
  Proof.
    intros A f H1 H2 Hsub. unfold size_with_measure.
    eapply fold_left_subperm; eauto.
    now firstorder.
    now firstorder.
    now firstorder.
    now firstorder.
    eapply subheap_Subperm. eassumption.
  Qed.


  Lemma max_with_measure_emp (A : Type) f :
    @max_with_measure A f emp = 0%nat.
  Proof.
    unfold max_with_measure.
    rewrite heap_elements_empty. reflexivity.
  Qed.

  Lemma max_with_measure_alloc
        (A : Type) f (x : A) (H : heap A) (H' : heap A) (l : loc) (s : nat) : 
    max_with_measure f H = s ->
    alloc x H = (l, H') ->
    max_with_measure f H' = max s (f x).
  Proof.
    intros Hs1 Ha.
    unfold max_with_measure in *. eapply heap_elements_alloc in Ha.
    erewrite fold_permutation; [| | eassumption ].
    simpl.
    replace (f x) with ((fun acc h => max acc (f (snd h))) 0 (l, x)); [| reflexivity ].  
    erewrite List_util.fold_left_comm with (f0 := fun acc h => max acc (f (snd h))).
    rewrite Hs1. reflexivity.

    intros y [l1 x1] [l2 x2]; simpl. 
    rewrite <- !Max.max_assoc, (Max.max_comm (f x1)). reflexivity.

    intros [l1 x1] [l2 x2] y; simpl. 
    rewrite <- !Max.max_assoc, (Max.max_comm (f x1)). reflexivity.
  Qed.

  Lemma max_with_measure_subheap :
    forall A f (H1 H2 : heap A),
      H1 ⊑ H2 ->
      max_with_measure f H1 <= max_with_measure f H2.
  Proof.
    intros A f H1 H2 Hsub. unfold max_with_measure.
    eapply fold_left_subperm; eauto.
    + now firstorder.
    + intros x1 x2 [l1 x3] Hleq. simpl.
      eapply le_trans. eassumption. eapply Max.le_max_l.
    + intros x1 x2 [l1 x3] Hleq. simpl.
      eapply NPeano.Nat.max_le_compat_r. eassumption.
    + intros [l1 x1] [l2 x2] y; simpl. 
      rewrite <- !Max.max_assoc, (Max.max_comm (f x1)).
      reflexivity.
    + eapply subheap_Subperm. eassumption.
  Qed.

  Lemma size_with_measure_filter_emp (A : Type) (s : PS.t) f :
    @size_with_measure_filter A f s emp = 0%nat.
  Proof.
    unfold size_with_measure_filter.
    rewrite heap_elements_filter_empty. reflexivity.
  Qed.

  Lemma size_with_measure_filter_alloc
        (A : Type) f (s : PS.t) (x : A) (H : heap A) (H' : heap A) (l : loc) (m : nat) : 
    size_with_measure_filter f s H = m ->
    alloc x H = (l, H') ->
    PS.In l s ->
    size_with_measure_filter f s H' = (m + f x)%nat.
  Proof.
    intros Hs1 Ha Hin.
    unfold size_with_measure_filter in *. eapply heap_elements_filter_alloc in Ha; [| eassumption ].
    erewrite fold_permutation; [| now intros; firstorder | eassumption ].
    simpl.
    replace (f x) with ((fun acc h => acc + f (snd h)) 0 (l, x)); [| reflexivity ].
    erewrite List_util.fold_left_comm with (f0 := fun acc h => acc + f (snd h)); [| now firstorder ].
    omega.
  Qed.

  Lemma size_with_measure_filter_alloc_in
        (A : Type) f (s : PS.t) (x : A) (H : heap A) (H' : heap A) (l : loc) (m : nat) : 
    size_with_measure_filter f s H = m ->
    alloc x H = (l, H') ->
    ~ PS.In l s ->
    size_with_measure_filter f s H' = m.
  Proof.
    intros Hs1 Ha Hnin.
    unfold size_with_measure_filter in *. eapply heap_elements_filter_alloc_nin in Ha; [| eassumption ].
    erewrite fold_permutation; [| now intros; firstorder | eassumption ].
    eassumption.
  Qed.
  
  Lemma size_with_measure_filter_subheap :
    forall A f (s : PS.t) (H1 H2 : heap A),
      H1 ⊑ H2 ->
      size_with_measure_filter f s H1 <= size_with_measure_filter f s H2.
  Proof.
    intros A f s H1 H2 Hsub. unfold size_with_measure_filter.
    eapply fold_left_subperm; eauto.
    now firstorder.
    now firstorder.
    now firstorder.
    now firstorder.
    eapply subheap_filter_Subperm. eassumption.
  Qed.

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

End HeapLemmas.
From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms Sorting.Permutation.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From CertiCoq.L6 Require Import Ensembles_util functions List_util cps set_util Heap.heap.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Module MHeap : Heap.

  Definition loc := positive. 

  Record heap' (block : Type) :=
    mkHeap
      { mheap : M.t block;
        mdom : Ensemble positive;
        mdom_spec : forall x, x \in mdom <-> exists v, M.get x mheap = Some v;
        next : positive;
        next_spec : forall x, (next <= x)%positive -> M.get x mheap = None }.

  Definition heap block := heap' block. 

  Program Definition emp (A : Type) := mkHeap A (M.empty A) (Empty_set _) _ 1 _.
  Next Obligation.
    split; intros; try (zify; omega).
    inv H.
    destruct H as [v Hgetv].
    rewrite M.gempty in Hgetv. congruence.
  Qed.
  Next Obligation.
    rewrite M.gempty. congruence.
  Qed.
  
  
  Definition get {A : Type} l (h : heap A) : option A :=
    M.get l (mheap A h).


      Definition in_dom {A : Type} l h : {l \in mdom A h} + {~ l \in mdom A h}.  
  Proof.
    destruct (get l h) eqn:Hget.
    - destruct h. unfold get in *. left. simpl in *.
      eapply mdom_spec0. eexists; eauto. 
    - destruct h. unfold get in *. right. simpl in *.
      intros Hc. eapply mdom_spec0 in Hc. destruct Hc.
      congruence.
  Qed. 

  Program Definition set {A : Type} v l h : option (heap A) :=
    match in_dom l h with
      | left Hin =>
        Some (mkHeap A (M.set l v (mheap A h)) (mdom A h) _ (next A h) _)
      | right Hnin => None 
    end.
  Next Obligation. 
    clear Heq_anonymous.
    destruct (peq x l); subst.
    - rewrite M.gss. split; eauto.
    - rewrite M.gso; [| eassumption ].
      eapply h.
  Qed.
  Next Obligation. 
    clear Heq_anonymous.
    destruct (peq x l); subst.
    - destruct h as [h1 d1 dspec1 f1 fspec1].
      simpl in *. eapply fspec1 in H. eapply dspec1 in Hin.
      destruct Hin. congruence. 
    - rewrite M.gso; eauto. eapply h. eassumption. 
  Qed.
  
  Program Definition alloc {A : Type} (v : A) (h : heap A) :=
    let l := next A h in
    (l, mkHeap A (M.set l v (mheap A h)) (l |: mdom A h) _ ((next A h) + 1) _). 
  Next Obligation.
    
    destruct (peq x (next A h)); subst.
    - rewrite M.gss. split; eauto.
    - rewrite M.gso; eauto. split; intros H.
      inv H. inv H0; contradiction.
      eapply h; eauto.

      right; eapply h; eauto.
  Qed. 
  Next Obligation.
    
    destruct (peq x (next A h)); subst.
    - zify; omega.
    - rewrite M.gso; eauto. eapply h.
      zify; omega.
  Qed.
  
  Lemma emp_get A l : @get A l (@emp A) = None.
  Proof.
    unfold emp. unfold get. simpl. rewrite  M.gempty. reflexivity. 
  Qed. 

  Lemma gss A v l h h' :
    @set A v l h = Some h' ->
    @get A l h' = Some v.  
  Proof.
    intros Hs. unfold set in Hs.
    destruct (in_dom l h).
    - inv Hs. unfold get. simpl. rewrite M.gss.
      reflexivity. 
    - congruence.
  Qed.

  Lemma gso A v l l' h h' :
    @set A v l h = Some h' ->
    l <> l' ->
    @get A l' h' = @get A l' h.  
  Proof.
    intros Hs Hneq. unfold set in Hs.
    destruct (in_dom l h).
    - inv Hs. unfold get. simpl. rewrite M.gso.
      reflexivity. intros Hc; subst; eauto. 
    - congruence.
  Qed.
  
  Lemma gas (A : Type) (x : A) l (H H' : heap A) :
    alloc x H = (l, H') -> get l H' = Some x.
  Proof. 
    intros Ha.
    unfold alloc, get in *. inv Ha. simpl.
    rewrite M.gss. reflexivity.
  Qed.

  Lemma gao (A : Type) (x : A) l1 l2 (H H' : heap A) :
    l1 <> l2 ->
    alloc x H = (l1, H') ->
    get l2 H' = get l2 H.
  Proof.
    intros Hneq Ha.
    unfold alloc, get in *. inv Ha. simpl.
    rewrite M.gso. reflexivity. eauto. 
  Qed.
  
  Lemma alloc_fresh (A : Type) (x : A) (l : loc) (H H' : heap A) :
    alloc x H = (l, H') -> get l H = None.
  Proof. 
    intros Ha. 
    unfold alloc, get in *. inv Ha. eapply H.
    zify; omega. 
  Qed. 

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
  
  Definition restrict (A : Type) S (H1 H2 : heap A) : Prop :=
    H2 ⊑ H1 /\
    dom H2 <--> dom H1 :&: S.
  
  Lemma restrict_subheap (A : Type) (S : Ensemble loc) (H1 H2 : heap A) :
    restrict A S H1 H2 -> H2 ⊑ H1.
  Proof.
    intros Hr. destruct Hr; eauto. 
  Qed.

  
  Lemma restrict_In (A : Type) (l : loc) (S : Ensemble loc) (H H' : heap A) :
     restrict A S H H' -> In loc S l -> get l H' = get l H.
  Proof.
    intros [Hsub Hdom] Hin. unfold subheap in *.
    destruct (get l H') as [b1|] eqn:Hget. 
    - symmetry. eauto.
    - destruct (get l H) as [b2|] eqn:Hget'; eauto. 
      assert (Hc : l \in dom H :&: S).
      { constructor; eauto. eexists; eauto. }
      eapply Hdom in Hc. 
      destruct Hc as [l' Hgetc']. congruence.
  Qed.
        
  Lemma restrict_notIn (A : Type) (l : loc) (S : Ensemble loc) (H H' : heap A) :
    restrict A S H H' -> ~ In loc S l -> get l H' = None.
  Proof. 
    intros [Hsub Hdom] Hin. unfold subheap in *.
    destruct (get l H') as [b1|] eqn:Hget; eauto.

    assert (Hc : l \in dom H :&: S).
    { eapply Hdom. eexists; eauto. }

    inv Hc; contradiction. 
  Qed.


  Definition restrict_map {A : Type} (S : Ensemble loc) {Hs : Decidable S} (m : M.t A) := 
    M.fold (fun mr x v => if @Dec _ S _ x then mr else M.remove x mr) m m.     

  Lemma Sublist_refl A (l : list A) :
    Sublist l l. 
  Proof.
    induction l; eauto. 
    - now constructor.
    - constructor 3; eauto.
  Qed. 

  Lemma restrict_map_submap_strong (A : Type) (S : Ensemble loc) {Hs : Decidable S} (m : M.t A) x v l :
    incl l (M.elements m) ->
    list_norepet (map fst l) ->
    M.get x (fold_left
               (fun (a : M.t A) (p : positive * A) =>
                  if Dec (fst p) then a else M.remove (fst p) a) l m) = Some v ->
    M.get x m = Some v.
  Proof.    
    revert m.
    induction l as [| [l1 v1] l IHl1]; intros m Hspec Hr Hget.
    - eassumption.
    - simpl in Hget. simpl in *.
      destruct (@Dec positive S Hs l1).
      * inv Hr. eapply IHl1; eauto.
        intros y Hin.
        assert (Hin' : List.In y ((l1, v1) :: l)) by now right.
        eapply Hspec in Hin'. eassumption.
      * { eapply IHl1 in Hget; try eauto.
          - destruct (peq x l1).
            subst. rewrite M.grs in Hget. congruence.
            rewrite M.gro in Hget; eassumption.
          - intros y Hin.
            assert (Hin' : List.In y ((l1, v1) :: l)) by now right.
            eapply Hspec in Hin'.
            
            destruct y as [l2 v2].
            eapply M.elements_complete in Hin'.
            eapply M.elements_correct.
            rewrite M.gro. eassumption.
            intros Hceq; subst. inv Hr. eapply H1.
            
            eapply in_map with (f := fst) in Hin. eassumption.
            
          - inv Hr. eassumption.  }
  Qed.

  Lemma restrict_map_same_strong (A : Type) (S : Ensemble loc) {Hs : Decidable S} (m : M.t A) x v l :
    incl l (M.elements m) ->
    list_norepet (map fst l) ->
    x \in S ->
    M.get x m = Some v -> 
    M.get x (fold_left
               (fun (a : M.t A) (p : positive * A) =>
                  if Dec (fst p) then a else M.remove (fst p) a) l m) = Some v.
  Proof.    
    revert m.
    induction l as [| [l1 v1] l IHl1]; intros m Hspec Hr Hin Hget.
    - eassumption.
    - simpl in Hget. simpl in *.
      destruct (@Dec positive S Hs l1).
      * inv Hr. eapply IHl1; eauto.
        intros y Hin'.
        assert (Hin'' : List.In y ((l1, v1) :: l)) by now right.
        eapply Hspec in Hin''. eassumption.
      * { eapply IHl1; try eauto.
          - intros y Hin1.
            assert (Hin' : List.In y ((l1, v1) :: l)) by now right.
            eapply Hspec in Hin'.
            
            destruct y as [l2 v2].
            eapply M.elements_complete in Hin'.
            eapply M.elements_correct.
            rewrite M.gro. eassumption.
            intros Hceq; subst. inv Hr. eapply H1.
            
            eapply in_map with (f := fst) in Hin1. eassumption.
           
          - inv Hr. eassumption.
          - rewrite M.gro. eassumption. intros Hc; subst. contradiction. } 
  Qed.

  Corollary restrict_map_submap (A : Type) (S : Ensemble loc) {Hs : Decidable S} (m : M.t A) x v :
    M.get x (restrict_map S m) = Some v -> M.get x m = Some v. 
  Proof.    
    unfold restrict_map. rewrite M.fold_spec.
    eapply restrict_map_submap_strong. now (clear; firstorder).
    eapply Maps.PTree.elements_keys_norepet.       
  Qed.
 
  
  Lemma restrict_map_spec (A : Type) (S : Ensemble loc) {Hs : Decidable S} (m : M.t A) x v :
    M.get x (restrict_map S m) = Some v <-> x \in S /\ M.get x m = Some v. 
  Proof.
    assert (Hsuf :
              (x, v) \in FromList (M.elements m) /\ M.get x (restrict_map S m) = Some v <->
              (x, v) \in FromList (M.elements m) /\ x \in S /\ M.get x m = Some v).
    { unfold restrict_map. rewrite M.fold_spec. 
      assert (Hsub : incl (M.elements m) (M.elements m)) by (clear; firstorder).
      
      assert (Hnd  : list_norepet (map fst (M.elements m))).
      { eapply Maps.PTree.elements_keys_norepet. } 
       
      revert Hsub Hnd. generalize (M.elements m) at 1 3 4 5 6. intros l. revert m. 
      induction l as [| [l1 v1] l IHl1]; intros m Hspec Hr. 
      - simpl. rewrite FromList_nil. split; intros [H1 H2]; now inv H1.
      - simpl. rewrite FromList_cons.
        inv Hr. split. 
        + destruct (@Dec _ S _ l1).
          * { intros [Hget1 Hget2]. 
              inv Hget1.
              - inv H. subst. split; eauto. split; eauto. 
                eapply M.elements_complete. eapply Hspec. now constructor.
                
              - split. now right. eapply IHl1; try eassumption.
                
                intros y Hin.
                assert (Hin' : List.In y ((l1, v1) :: l)) by now right.
                eapply Hspec in Hin'. eassumption. 

                split. eassumption. eassumption. }
          * { simpl. intros [Hget1 Hget2].
              destruct (peq l1 x); subst.
              - (* extra lemma + congruence *)
                eapply restrict_map_submap_strong in Hget2; try eassumption.
                rewrite M.grs in Hget2. congruence.
                intros [l2 v2] Hin2.
                assert (Hin' : List.In (l2, v2)  ((x, v1) :: l)) by now right.
                eapply Hspec in Hin'. eapply M.elements_complete in Hin'.
                eapply M.elements_correct. rewrite M.gro. eassumption. 
                intros Hc; subst. eapply H1. eapply in_map with (f := fst) in Hin2.
                eassumption.
              - inv Hget1. inv H; contradiction. 
                split. now right.
                assert (Ha := conj H Hget2). 
                eapply IHl1 in Ha; try eassumption.
                destruct Ha as [_ [HinS Heq]]. split; eauto. rewrite M.gro in Heq. eassumption.  
                
                intros Hc; subst. rewrite M.grs in Heq. congruence.

                intros [l2 v2] Hin.
                assert (Hin' : List.In (l2, v2) ((l1, v1) :: l)) by now right.
                eapply M.elements_correct. rewrite M.gro.
                eapply M.elements_complete. eapply Hspec. now right.
                intros Hc. subst. eapply H1. eapply in_map with (f := fst) (x := (l1, v2)).
                eassumption. }
        + intros [Hin1 [Hin2 Hget1]].
          inv Hin1.
          * inv H.
            destruct (@Dec _ S _ x); try contradiction.

            split. now left.
            eapply restrict_map_same_strong; try eassumption. 
            
            intros [l2 v2] Hin. eapply Hspec. now right. 
          * assert (Hc : x <> l1). 
            { intros Hc. subst. eapply H1. eapply in_map with (f := fst) (x := (l1, v)).
              eassumption. }
            
            split. now right. 
            eapply IHl1; try eassumption.

            intros [l2 v2] Hin.
            assert (Hin' : List.In (l2, v2) ((l1, v1) :: l)) by now right.
            eapply Hspec in Hin'. eapply M.elements_complete in Hin'.
            eapply M.elements_correct.
            destruct (@Dec _ S _ l1); [ eassumption | ]. rewrite M.gro. eassumption.
            intros Hc'; subst. 
            eapply H1. eapply in_map with (f := fst) (x := (l1, v2)).
            eassumption.
            
            split. eassumption. split. eassumption. 

            destruct (@Dec _ S _ l1); [ eassumption | ]. rewrite M.gro; eassumption. } 

    split; intros H; eapply Hsuf.
    - split; eauto.
      eapply M.elements_correct. eapply restrict_map_submap. eassumption.
    - split; eauto. destruct H. 
      eapply M.elements_correct. eassumption. 
  Qed. 
    

    
  Program Definition restrict_heap A (S : Ensemble loc) {Hs : Decidable S} (h : heap A) : heap A :=
    mkHeap A (restrict_map S (mheap A h)) (mdom A h :&: S) _ (next A h) _. 
  Next Obligation. 
    split.
    - intros [y H1 H2]. 
      eapply h in H1. destruct H1 as [v Hget2]. 
      assert (Hand := conj H2 Hget2). eapply restrict_map_spec in Hand. 
      eexists; eassumption. 
    - intros [v Hin]. eapply restrict_map_spec in Hin. destruct Hin. split; eauto. 
      eapply h.  eexists; eauto. 
  Qed. 
  Next Obligation. 
    eapply h in H.
    destruct (M.get x (restrict_map S (mheap A h))) eqn:Hget; eauto.
    eapply restrict_map_spec in Hget. destruct Hget. congruence.
  Qed.     
    
  Lemma restrict_exists (A : Type) (S : Ensemble loc) (H : heap A) :
    Decidable S -> exists H' : heap A, restrict A S H H'.
  Proof. 
    intros Hs. eexists (restrict_heap A S H).
    split.
    - intros x v Hget. eapply restrict_map_spec. eassumption.
    - split. 
      + intros x [c Hget]. eapply restrict_map_spec in Hget.
        destruct Hget. split; eauto. eexists; eauto.
      + intros y [l [v Hd] Hin]. eexists.
        eapply restrict_map_spec. split; eauto.
  Qed.       
    
  Definition heap_elements {A : Type} (H : heap A) : list (loc * A) :=
    M.elements (mheap A H).

   Lemma heap_elements_sound (A : Type) (h : heap A) (l : loc) (v : A) : 
     List.In (l, v) (heap_elements h) -> get l h = Some v.
   Proof. 
     intros Hin. unfold heap_elements, get in *.
     eapply M.elements_complete. eassumption.
   Qed. 
   
   Lemma heap_elements_complete (A : Type) (h : heap A) (l : loc) (v : A) : 
     get l h = Some v -> List.In (l, v) (heap_elements h).
   Proof. 
     intro Hget. unfold heap_elements, get in *. eapply M.elements_correct.
     eassumption.
   Qed.

   Lemma list_norepet_NoDup A B (l : list (A * B)) :
     list_norepet (map fst l) ->
     NoDup l.
   Proof.
     induction l; intros Hnr.
     now constructor.
     simpl in Hnr. inv Hnr. constructor; [| now eauto ].
     intros Hc. eapply H1. eapply in_map. eassumption.
   Qed.
   
   Lemma heap_elements_NoDup (A : Type) (h : heap A) : NoDup (heap_elements h).
   Proof.
     unfold heap_elements.
     eapply list_norepet_NoDup. eapply M.elements_keys_norepet.
   Qed.

   Lemma NoDup_filter (A : Type) P (l : list A) :
     NoDup l -> NoDup (filter P l).
   Proof.
     intros Hnd; induction l. now constructor.
     inv Hnd. simpl. destruct (P a); eauto. constructor; eauto.
     intros Hc. eapply H1. 
     eapply filter_In. eassumption.
   Qed.

   Lemma filter_eq A P1 P2 (l : list A) :
     (forall x, P1 x = P2 x) ->
     filter P1 l = filter P2 l.
   Proof.
     intros Heq. induction l; eauto.
     simpl. rewrite Heq, IHl. reflexivity.
   Qed. 
     
   Definition heap_elements_filter {A : Type} S {Hs : ToMSet S} (h : heap A) : list (loc * A) :=
     filter (fun p => @Dec _ S _ (fst p)) (heap_elements h). 
                                                                                    

   Lemma heap_elements_filter_sound (A : Type) (S : Ensemble loc) (H : ToMSet S) 
         (h : heap A) (l : loc) (v : A) : 
     List.In (l, v) (heap_elements_filter S h) ->
     get l h = Some v /\ In loc S l.
   Proof. 
     intros Hin. unfold heap_elements_filter in *. eapply filter_In in Hin.
     destruct Hin as [Hin Hdec]. simpl in *. 
     split. eapply heap_elements_sound; eassumption.

     eapply proj_sumbool_true in Hdec. eassumption. 
   Qed. 
     
   Lemma heap_elements_filter_complete (A : Type) (S : Ensemble loc) (H : ToMSet S) 
         (h : heap A) (l : loc) (v : A) : 
     get l h = Some v ->
     In loc S l -> List.In (l, v) (heap_elements_filter S h).
   Proof.
     intros Hget Hin. unfold heap_elements_filter in *. eapply filter_In.
     split. eapply heap_elements_complete; eassumption.
     simpl. 
     eapply proj_sumbool_is_true. eassumption. 
   Qed. 

   
   Lemma heap_elements_filter_NoDup (A : Type) (S : Ensemble loc) (H : ToMSet S) (h : heap A) :
     NoDup (heap_elements_filter S h).
   Proof. 
     eapply NoDup_filter. eapply heap_elements_NoDup; eassumption. 
   Qed. 
     
   Lemma heap_elements_filter_set_Equal (A : Type) (S1 : Ensemble loc) (H1 : ToMSet S1)
             (S2 : Ensemble loc) (H2 : ToMSet S2) (h : heap A) : 
     S1 <--> S2 ->
     heap_elements_filter S1 h = heap_elements_filter S2 h.
   Proof.
     intros Heq. eapply filter_eq. intros x.

     destruct (@Dec positive S1 _ (fst x));
     destruct (@Dec positive S2 _ (fst x)); eauto. 
     - assert (Hs' : S2 (fst x)). eapply Heq. eassumption.
       contradiction. 
     - assert (Hs' : S1 (fst x)). eapply Heq. eassumption.
       contradiction. 
   Qed.      


   Definition heap_elements_minus {A : Type} S {Hs : ToMSet S} (h : heap A) : list (loc * A) :=
     filter (fun p => match @Dec _ S _ (fst p) with
                   | left _ => false
                   | right _ => true
                   end) (heap_elements h).
   
   
   Lemma heap_elements_minus_sound (A : Type) (S : Ensemble loc) (H : ToMSet S) 
         (h : heap A) (l : loc) (v : A) : 
     List.In (l, v) (heap_elements_minus S h) ->
     get l h = Some v /\ ~ In loc S l.
   Proof. 
     intros Hin. unfold heap_elements_minus in *. eapply filter_In in Hin.
     destruct Hin as [Hin Hdec]. simpl in *. 
     split. eapply heap_elements_sound; eassumption.

     destruct (@Dec positive S _ l); eauto. congruence. 
   Qed. 
   
   Lemma heap_elements_minus_complete (A : Type) (S : Ensemble loc) (H : ToMSet S) 
         (h : heap A) (l : loc) (v : A) : 
     get l h = Some v ->
     ~ In loc S l -> List.In (l, v) (heap_elements_minus S h).
   Proof.
     intros Hget Hin. unfold heap_elements_minus in *. eapply filter_In.
     split. eapply heap_elements_complete; eassumption.
     simpl. 
     destruct (@Dec positive S _ l); eauto. 
   Qed. 

   
   Lemma heap_elements_minus_NoDup (A : Type) (S : Ensemble loc) (H : ToMSet S) (h : heap A) :
     NoDup (heap_elements_minus S h).
   Proof. 
     eapply NoDup_filter. eapply heap_elements_NoDup; eassumption. 
   Qed. 
   
   Lemma heap_elements_minus_set_Equal (A : Type) (S1 : Ensemble loc) (H1 : ToMSet S1)
         (S2 : Ensemble loc) (H2 : ToMSet S2) (h : heap A) : 
     S1 <--> S2 ->
     heap_elements_minus S1 h = heap_elements_minus S2 h.
   Proof.
     intros Heq. eapply filter_eq. intros x.

     destruct (@Dec positive S1 _ (fst x));
       destruct (@Dec positive S2 _ (fst x)); eauto. 
     - assert (Hs' : S2 (fst x)). eapply Heq. eassumption.
       contradiction. 
     - assert (Hs' : S1 (fst x)). eapply Heq. eassumption.
       contradiction. 
   Qed.      
      
   Definition size {A : Type} (h : heap A) : nat := List.length (heap_elements h).
   
   Definition size_with_measure {A : Type} (f : A -> nat) (h : heap A) : nat :=
     fold_left (fun acc h => acc + f (snd h)) (heap_elements h) 0%nat.

   Definition size_with_measure_filter {A : Type}
              (f : A -> nat) (S : Ensemble loc) {H : ToMSet S}  (h : heap A) : nat :=
     fold_left (fun acc h => acc + f (snd h)) (heap_elements_filter S h) 0%nat.


   Definition max_with_measure {A : Type} (f : A -> nat) (h : heap A) : nat :=
     fold_left (fun acc h => max acc (f (snd h))) (heap_elements h) 0%nat.
   
   Definition max_with_measure_filter {A : Type}
              (f : A -> nat) (S : Ensemble loc) {H : ToMSet S} (h : heap A) : nat :=
     fold_left (fun acc h => max acc (f (snd h))) (heap_elements_filter S h) 0%nat.


   Definition size_with_measure_minus {A : Type}
              (f : A -> nat) (S : Ensemble loc) {H : ToMSet S}  (h : heap A) : nat :=
     fold_left (fun acc h => acc + f (snd h)) (heap_elements_minus S h) 0%nat.

End MHeap.

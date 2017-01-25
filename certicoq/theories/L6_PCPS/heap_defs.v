(* Heap definitions for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps cps_util eval List_util Ensembles_util functions
        identifiers heap.
From Libraries Require Import Coqlib.

Module HeapDefs (H : Heap).
  
  Import H.

  (** * Heap definitions *)
  
  (* Environment. All the values are boxed *)
  Definition env := M.t loc.
  
  (** The type of heap values *)
  Inductive val : Type :=
  | Vconstr: cTag -> list loc -> val
  | Vfun: env -> fundefs -> val.
  
  (** The result of the evaluation *)
  Definition res := (loc * heap val)%type.
  
  (** Approximation of results with fuel *)
  Fixpoint res_approx_fuel (n : nat) (r1 r2 : res) : Prop :=
    let (l1, H1) := r1 in
    let (l2, H2) := r2 in     
    forall v1,
      get l1 H1 = Some v1->
      exists v2,
        get l2 H2 = Some v2 /\
        match v1, v2 with
          | Vconstr c1 ls1, Vconstr c2 ls2 =>
            c1 = c2 /\
            forall i, (i < n)%nat ->
                 match n with
                   | 0%nat => True
                   | S n' =>
                     Forall2
                       (fun l1 l2 => res_approx_fuel (n'-(n'-i)) (l1, H1) (l2, H2)) ls1 ls2
                 end
          | Vfun rho1 B1, Vfun rho2 B2 =>
            B1 = B2 /\
            (forall i, (i < n)%nat ->
                  match n with
                    | 0%nat => True
                    | S n' =>
                      forall x, x \in (occurs_free_fundefs B1) ->
                                 (exists l1 l2, M.get x rho1 = Some l1 /\
                                           M.get x rho2 = Some l2 /\
                                           res_approx_fuel (n'-(n'-i)) (l1, H1) (l2, H2)) \/
                                 (M.get x rho1 = None /\ M.get x rho2 = None)
                  end)
          | _, _ => False
        end.

  (** Equivalent definition, unfolding the recursion *)
  Definition res_approx_fuel' (n : nat) (r1 r2 : res) : Prop :=
    let (l1, H1) := r1 in
    let (l2, H2) := r2 in
    forall v1,
      get l1 H1 = Some v1->
      exists v2, get l2 H2 = Some v2 /\
            match v1, v2 with
              | Vconstr c1 ls1, Vconstr c2 ls2 =>
                c1 = c2 /\
                forall i, (i < n)%nat ->
                     Forall2 (fun l1 l2 => res_approx_fuel i (l1, H1) (l2, H2)) ls1 ls2
              | Vfun rho1 B1, Vfun rho2 B2 =>
                B1 = B2 /\
                forall i x, (i < n)%nat -> 
                       x \in (occurs_free_fundefs B1) ->
                             (exists l1 l2, M.get x rho1 = Some l1 /\
                                       M.get x rho2 = Some l2 /\
                                       res_approx_fuel i (l1, H1) (l2, H2)) \/
                             (M.get x rho1 = None /\ M.get x rho2 = None)
              | _, _ => False
            end.
  
  (** Equivalence of the two definitions *)
  Lemma res_approx_fuel_eq n r1 r2 :
    res_approx_fuel n r1 r2 <-> res_approx_fuel' n r1 r2.
  Proof.
    destruct n; destruct r1 as [l1 H1]; destruct r2 as [l2 H2]; split; intros H v1 Hget1; 
    destruct (H v1 Hget1) as [v2 [Hget2 H']]; destruct v1; destruct v2;
    try (now intros; omega);
    try (destruct H' as [H1' H2']; repeat eexists; eauto; simpl; split; eauto; intros; omega).
    - destruct H' as [H1' H2'].
      repeat eexists; eauto; simpl; eauto; split; eauto; intros.
      assert (Heq : (i = n - (n - i))%nat) by omega. rewrite Heq.
      eauto.
    - destruct H' as [H1' H2'].
      repeat eexists; eauto; simpl; eauto; split; eauto; intros.
      assert (Heq : (i = n - (n - i))%nat) by omega. rewrite Heq.
      eauto.
    - destruct H' as [H1' H2'].
      repeat eexists; eauto; simpl; eauto; split; eauto; intros.
      assert (Heq : (i = n - (n - i))%nat) by omega. rewrite <- Heq.
      eauto.
    - destruct H' as [H1' H2'].
      repeat eexists; eauto; simpl; eauto; split; eauto; intros.
      assert (Heq : (i = n - (n - i))%nat) by omega. rewrite <- Heq.
      eauto.
  Qed.

  Opaque res_approx_fuel.

  (** Result equivalence *)
  Definition res_equiv (r1 r2 : res) : Prop :=
    forall n, res_approx_fuel' n r1 r2 /\ res_approx_fuel' n r2 r1.
  
  Infix "≈" := res_equiv (at level 70, no associativity).
  
  (** Approximation lifted to the environments *)
  Definition heap_env_approx (S : Ensemble var) p1 p2 : Prop :=
    let '(H1, rho1) := p1 in
    let '(H2, rho2) := p2 in
    forall x l, x \in S ->
           M.get x rho1 = Some l ->
           exists l', M.get x rho2 = Some l' /\
                 (l, H1) ≈ (l', H2).
  
  (** Equivalence lifted to the environments *)
  Definition heap_env_equiv S p1 p2 : Prop :=
    heap_env_approx S p1 p2 /\
    heap_env_approx S p2 p1.

  Notation "S |- p1 ⩪ p2" := (heap_env_equiv S p1 p2)
                               (at level 70, no associativity).

  (** The image of the environment *)
  Definition env_locs (rho : env) S := image' (fun x => M.get x rho) S.

  (** Size of values *)
  Definition size_val (v : val) : nat :=
    match v with
      | Vconstr t ls => (* The size of the constructor representation *)
        1 + length ls
      | Vfun rho B => (* The size of the closure record *)
        3 + fundefs_num_fv B
    end.
  
  Definition size_heap (H : heap val) (n : nat) : Prop :=
    size_with_measure size_val H n.
  
  (** The locations that appear on a value *)
  Definition locs (v : val) : Ensemble loc :=
    match v with
      | Vconstr t ls => FromList ls
      | Vfun rho B =>
        (* Take only the relevant part of the environment instead
           of its whole codomain *)
        env_locs rho (occurs_free_fundefs B)
    end.

  (** The location that are pointed by location in S *)
  Definition post (H : heap val) (S : Ensemble loc) :=
    [ set l : loc | exists l' v, l' \in S /\ get l' H = Some v /\ l \in locs v].
  
    
  Close Scope Z_scope.
  
  Definition lfp {A} (f : Ensemble A -> Ensemble A) :=
    \bigcup_( n : nat ) ((f ^ n) (Empty_set A)).
  
  (** Least fixed point characterization of heap reachability. *)
  Definition reach (H : heap val) (Si : Ensemble loc) : Ensemble loc :=
    lfp (fun S => Union _ Si (post H S)).
  
  (** Alternative characterization of heap reachability. *)
  Definition reach' (H : heap val) (Si : Ensemble loc) : Ensemble loc :=
    \bigcup_( n : nat ) (((post H) ^ n) (Si)).
  
  (* The to definitions should be equivalent. TODO: Do the proof *)
  Lemma reach_equiv H Si :
    reach H Si <--> reach' H Si.
  Proof.
  Abort.
  
  (** A heap is well-formed if there are not dangling pointers in the stored values *)
  Definition well_formed (S : Ensemble loc) (H : heap val) :=
    forall l v, l \in S -> get l H = Some v -> locs v \subset dom H.
  
  (** Well-formedness lifted to the environments. NOT USED *)
  Definition well_formed_env S (H : heap val) (rho : env):=
    forall x l, x \in S -> M.get x rho = Some l -> l \in dom H.
  
  (** A heap is closed in S if the locations of its image on S remain in S *)
  Definition closed (S : Ensemble loc) (H : heap val) : Prop :=
    forall l, l \in S -> exists v, get l H = Some v /\ locs v \subset S.

  (** Using S as the set of roots, garbage collect H1 *) 
  Definition collect (S : Ensemble loc) (H1 H2 : heap val) : Prop :=
    (* H2 is a subheap of H1 *)
    H2 ⊑ H1 /\
    (* the domain of H2 includes everything that is reachable *)
    reach' H1 S \subset dom H2.  

  (** The reachable part of the heap before and after collection are the same *)
  Lemma collect_heap_eq S H1 H2 :
    collect S H1 H2 ->
    (reach' H1 S) |- H1 ≡ H2.
  Proof.
    intros [Hc1 Hc2] l Hin. eapply Hc2 in Hin.
    destruct Hin  as [v Hget].
    rewrite Hget. eapply Hc1; eauto.
  Qed.

  (** [live S H1 H2] iff H2 is the live portion of H1, using S as roots *)
  Definition live (S : Ensemble loc) (H1 H2 : heap val) : Prop :=
    H2 ⊑ H1 /\
    dom H2 <--> reach' H1 S.
  
  Fixpoint def_funs (B : fundefs) (l : loc) (rho : env) {struct B}
  : env :=
    match B with
      | Fcons f _ _ _ B' =>
        M.set f l (def_funs B' l rho)
      | Fnil => rho
    end.


  (** * Lemmas about [post] and [reach'] *)
  
  Lemma post_heap_monotonic H1 H2 S :
    H1 ⊑ H2 ->
    post H1 S \subset post H2 S.
  Proof.
    unfold post. intros Hsub l [l' [v [Hin [Hget Hin']]]].
    exists l', v. split; eauto.
  Qed.
  
  Lemma post_set_monotonic S1 S2 H :
    S1 \subset S2 ->
    post H S1 \subset post H S2.
  Proof.
    unfold post. intros Hsub l [l' [v [Hin [Hget Hin']]]].
    exists l', v. split; eauto.
  Qed.

  Lemma reach'_set_monotonic H S1 S2 :
    S1 \subset S2 ->
    reach' H S1 \subset reach' H S2.
  Proof.
    intros Hsub; intros x [i [_ Hin]]. 
    exists i. split. constructor. eapply app_monotonic.
    + intros. now eapply post_set_monotonic.
    + eassumption.
    + eassumption.
  Qed.
  
  Lemma reach'_extensive H S :
    S \subset reach' H S.
  Proof.
    intros x Hin. exists 0; split; eauto.
    now constructor.
  Qed.
  
  Lemma Included_post_reach' H S :
    (post H S) \subset reach' H S.
  Proof.
    intros x Hin. exists 1; split; eauto.
    now constructor.
  Qed.
  
  Lemma reach_unfold H S :
    (reach' H S) <--> (Union _ S (reach' H (post H S))).
  Proof.
    split; intros x.
    - intros [i [_ Hin]]. 
      destruct i.
      + eauto.
      + right. exists i. split. now constructor.
        replace ((post H ^ i) (post H S))
        with (((post H ^ i) ∘ (post H ^ 1)) S) by eauto.
        rewrite <- app_plus. rewrite plus_comm. eassumption.
    - intros Hin. destruct Hin as [ x Hin | x [i [_ Hin]]].
      + now eapply reach'_extensive.
      + exists (i+1). split. now constructor.
          rewrite app_plus. eassumption.
  Qed.

  (** reach is a post fixed point of post. Post is monotonic so
      it is also a fixed point *)
  Lemma reach'_post_fixed_point H S :
    post H (reach' H S) \subset reach' H S.
  Proof.
    unfold post, reach'; simpl; intros x [l [v [[i [_ Hin]] Hin']]].
    exists (i + 1). split. now constructor.
    rewrite plus_comm, app_plus.
    exists l, v. split; eauto.
  Qed.
  
  Lemma reach'_post_fixed_point_n n H S :
    (post H ^ n) (reach' H S) \subset reach' H S.
  Proof.
    induction n. 
    - reflexivity.
    - replace (Datatypes.S n) with (n + 1). rewrite app_plus.
      eapply Included_trans.
      eapply app_monotonic. now intros; eapply post_set_monotonic.
      now apply reach'_post_fixed_point. eassumption.
      omega.
  Qed. 

  (** [reach'] is idempotent *)
  Lemma reach'_idempotent H S :
    reach' H S <--> reach' H (reach' H S).
  Proof.
    unfold reach'. split; intros x Hin.
    - exists 0. split. now constructor.
      simpl. eassumption.
    - rewrite <- bigcup_merge.
      destruct Hin as [m [_ Hin]].
      apply reach'_post_fixed_point_n in Hin.
      exists 0. split; eauto. now constructor.
  Qed.
  
  Lemma reach_spec H S S' :
    S \subset S' -> S' \subset reach' H S ->
    reach' H S <--> reach' H S'.
  Proof.
    intros Hsub1 Hsub2. split.
    - eapply reach'_set_monotonic. eassumption.
    - rewrite (reach'_idempotent H S).
      apply reach'_set_monotonic. eassumption.
  Qed.


  (** Proper instances *)
  Instance Proper_post : Proper (eq ==> Same_set loc ==> Same_set loc) post.
  Proof.
    intros x1 x2 Heq S1 S2 Heq'; subst; split; intros z [l [v [Hin [Hget Hin']]]].
    repeat eexists; eauto; now rewrite <- Heq'; eauto.
    repeat eexists; eauto; now rewrite Heq'; eauto.
  Qed.

  Lemma proper_post_n H n S1 S2 :
    S1 <--> S2 ->
    ((post H) ^ n) S1 <--> ((post H) ^ n) S2.
  Proof.
    induction n; eauto; intros Heq; simpl.
    rewrite IHn; eauto. reflexivity.
  Qed.

  Instance Proper_reach' : Proper (eq ==> Same_set _ ==> Same_set _) reach'.
  Proof.
    intros H1 H2 heq S1 S2 Hseq; subst; split; intros x [n [Hn Hin]].
    - eexists; split; eauto. eapply proper_post_n; eauto.
      now symmetry.
    - eexists; split; eauto. eapply proper_post_n; eauto.
  Qed.
  
  Lemma post_heap_eq S H1 H2 :
    S |- H1 ≡ H2 ->
    post H1 S <--> post H2 S.
  Proof.
    intros Heq; split; intros x [l [v [Hin [Hget Hin']]]].
    repeat eexists; eauto; now rewrite <- Heq; eauto.
    repeat eexists; eauto; now rewrite Heq; eauto.
  Qed.

  
  Lemma post_n_heap_eq n P H1 H2 :
    reach' H1 P |- H1 ≡ H2 ->
    (post H1 ^ n) P <--> (post H2 ^ n) P.
  Proof.
    induction n; intros Heq; try reflexivity.
    simpl. rewrite IHn; eauto. apply post_heap_eq.
    eapply heap_eq_antimon; eauto.
    rewrite <- IHn; eauto. intros l Hin; eexists; split; eauto.
    now constructor.
  Qed.

    Lemma post_n_heap_eq' n P H1 H2 :
    reach' H2 P |- H1 ≡ H2 ->
    (post H1 ^ n) P <--> (post H2 ^ n) P.
  Proof.
    induction n; intros Heq; try reflexivity.
    simpl. rewrite IHn; eauto. apply post_heap_eq.
    eapply heap_eq_antimon; eauto.
    intros l Hin; eexists; split; eauto.
    now constructor.
  Qed.
  
  Lemma reach'_heap_eq P H1 H2 :
    reach' H1 P |- H1 ≡ H2 ->
    reach' H1 P <--> reach' H2 P.
  Proof.
    intros Heq; split; intros l [n [HT Hp]]; eexists; split; eauto;
    try now eapply post_n_heap_eq; eauto.
    eapply post_n_heap_eq'; eauto.
    symmetry ; eauto.
  Qed.  
  
  Lemma reach'_post S H : 
    reach' H S <--> reach' H (Union loc S (post H S)).
  Proof.
    rewrite <- reach_spec with (S' := Union loc S (post H S)).
    reflexivity.
    now eauto with Ensembles_DB.
    apply Union_Included. now apply reach'_extensive.
    now apply Included_post_reach'.
  Qed.

    (** Reflexivity of [res_approx] *)
  Lemma reach_res_approx H1 H2 S l n :
    reach' H1 S <--> reach' H2 S ->
    (reach' H1 S) |- H1 ≡ H2  ->
    l \in S -> 
    res_approx_fuel n (l, H1) (l, H2).
  Proof.
    intros Hr Hsub Hin. revert H1 H2 S l Hr Hsub Hin.
    induction n using lt_wf_rec1; intros H1 H2 S l Hr Hsub Hin.
    destruct n.
    - simpl. intros. rewrite res_approx_fuel_eq; intros v Hget.
      rewrite Hsub in Hget. eexists; split; eauto. destruct v.
      split; eauto; intros. omega. split; eauto; intros; omega.
      eapply reach'_extensive. eassumption.
    - rewrite res_approx_fuel_eq; intros v Hget.
      assert (Hget1 := Hget). rewrite Hsub in Hget. eexists; split; eauto. destruct v.
      + split; eauto. intros i Hlt.
        eapply Forall2_same.  intros l' Hin'.
        eapply H with (S := Union _ S (post H1 S)); eauto.
        rewrite <- reach_spec with (H := H1) (S := S).
        rewrite <- reach_spec with (H := H2) (S := S).
        eassumption. now eauto with Ensembles_DB.
        apply Union_Included. now apply reach'_extensive.
        eapply Included_trans with (s2 := post H2 S).
        eapply (heap_eq_antimon) in Hsub; [| now apply reach'_extensive ].
        rewrite post_heap_eq; eauto. reflexivity.
        now apply Included_post_reach'.
        now eauto with Ensembles_DB.
        apply Union_Included. now apply reach'_extensive.
        eapply Included_trans with (s2 := post H2 S).
        eapply (heap_eq_antimon) in Hsub; [| now apply reach'_extensive ].
        rewrite post_heap_eq; eauto. reflexivity.
        rewrite Hr. now apply Included_post_reach'.
        now rewrite <- reach'_post.
        right. exists l. eexists. eauto.
      + split; [ reflexivity |].
        intros i x Hlt Hin'.
        destruct (M.get x e) eqn:Heq.
        * left; do 2 eexists. split; [| split ]; eauto.
          eapply H with (S := Union _ S (post H1 S)); eauto.
          rewrite <- reach_spec with (H := H1) (S := S).
          rewrite <- reach_spec with (H := H2) (S := S).
          eassumption. now eauto with Ensembles_DB.
          apply Union_Included. now apply reach'_extensive.
          eapply Included_trans with (s2 := post H2 S).
          eapply (heap_eq_antimon) in Hsub; [| now apply reach'_extensive ].
          rewrite post_heap_eq; eauto. reflexivity.
          now apply Included_post_reach'.
          now eauto with Ensembles_DB.
          apply Union_Included. now apply reach'_extensive.
          eapply Included_trans  with (s2 := post H2 S).
          eapply (heap_eq_antimon) in Hsub; [| now apply reach'_extensive ].
          rewrite post_heap_eq; eauto. reflexivity.
          rewrite Hr. now apply Included_post_reach'.
          now rewrite <- reach'_post.
          right. exists l. eexists. repeat split; eauto.
          exists x. split; eauto.
        * right; eauto.
      + eapply reach'_extensive. eassumption.
  Qed.
  
  Corollary reach_res_equiv H1 H2 S l : 
    reach' H1 S <--> reach' H2 S ->
    (reach' H1 S) |- H1 ≡ H2 ->
    l \in S -> 
    (l, H1) ≈ (l, H2).
  Proof.
    intros Hr Hsub Hin n; split; rewrite <- res_approx_fuel_eq;
    eapply reach_res_approx; eauto.
    now symmetry. symmetry. rewrite <- Hr. eassumption.
  Qed.
  
  Lemma Preorder_res_equiv_fuel i : preorder res (res_approx_fuel i).
  Proof.
    constructor.
    - induction i using lt_wf_rec1.
      intros [l H1]. rewrite res_approx_fuel_eq. intros v Hget.
      eexists; split; eauto. destruct v; split; eauto; intros.
      + eapply Forall2_refl; intros l'. eapply H. eassumption.
      + destruct (M.get x e) eqn:Hget'; eauto.
        left; do 2 eexists; repeat split; eauto.
        eapply H; eauto.
    - induction i using lt_wf_rec1.
      intros [l1 H1] [l2 H2] [l3 H3] Hap1 Hap2. rewrite res_approx_fuel_eq in *.
      intros v1 Hget. edestruct Hap1 as [v2 [Hget2 Hval2]]. eassumption.
      edestruct Hap2 as [v3 [Hget3 Hval3]]. eassumption.
      eexists; split; eauto.
      destruct v1; destruct v2; try contradiction; destruct v3; try contradiction.
      + destruct Hval2 as [Heq2 Hlt2]. destruct Hval3 as [Heq3 Hlt3]. subst.
        split; eauto; intros.
        eapply Forall2_trans_strong; eauto. intros. eapply H. eassumption.
        eapply H4. eapply H5.
      + destruct Hval2 as [Heq2 Hlt2]. destruct Hval3 as [Heq3 Hlt3]. subst.
        split; eauto; intros.
        edestruct Hlt2 as [[l1' [l2' [Hgetl1 [Hgetl2 Hap1']]]] | [Hn1 Hn2]];
          try eassumption;
          edestruct Hlt3 as [[l3' [l4' [Hgetl3 [Hgetl4 Hap2']]]] | [Hn1' Hn2']];
          try eassumption;
          try congruence; try eassumption.
        * left; repeat eexists; eauto.
          rewrite Hgetl2 in Hgetl3; inv Hgetl3.
          eapply H; eauto.
        * right; eauto.
  Qed.


  Instance Reflexive_res_equiv_fuel i : Reflexive (res_approx_fuel i).
  Proof.
    eapply Preorder_res_equiv_fuel.
  Qed.

  Instance Transitive_res_equiv_fuel i : Transitive (res_approx_fuel i).
  Proof.
    eapply Preorder_res_equiv_fuel.
  Qed.

  Instance Equivalence_res_equiv : Equivalence res_equiv.
  Proof.
    constructor.
    - intros res; split; rewrite <- res_approx_fuel_eq;
      eapply Preorder_res_equiv_fuel.
    - intros res res' H n. destruct (H n) as [H1 H2]. split; eauto.
    - intros res1 res2 res3 H1 H2. intros n;
      destruct (H1 n) as [Ht1 Ht2]; destruct (H2 n) as [Ht3 Ht4];
      rewrite <- res_approx_fuel_eq in *. 
      split. now eapply Preorder_res_equiv_fuel; eauto.
      rewrite <- res_approx_fuel_eq. 
      now eapply Preorder_res_equiv_fuel; eauto.
  Qed.

  Lemma reach_approx H1 H2 rho S : 
    reach' H1 (image' (fun x => M.get x rho) S) <--> reach' H2 (image' (fun x => M.get x rho) S) ->
    (reach' H1 (image' (fun x => M.get x rho) S)) |- H1 ≡ H2 -> 
    heap_env_approx S (H2, rho) (H1, rho).
  Proof.
    intros Hreach Hsub x l Hin Hget. 
    exists l. split. eassumption.
    eapply reach_res_equiv. symmetry. eassumption.
    symmetry. rewrite <- Hreach. eassumption.
    eexists. split; eauto.
  Qed.  

 
  Corollary reach_heap_env_equiv H1 H2 rho S : 
    reach' H1 (image' (fun x => M.get x rho) S) <--> reach' H2 (image' (fun x => M.get x rho) S) ->
    (reach' H1 (image' (fun x => M.get x rho) S)) |- H1 ≡ H2 -> 
    S |- (H1, rho) ⩪ (H2, rho).
  Proof.
    intros. split; eapply reach_approx; simpl; try eassumption.
    symmetry. eassumption. rewrite <- H. now symmetry.
  Qed.
   
   
  (** Well formedness preservation lemmas *)
  
   Lemma alloc_dom_subset (H H' : heap val) (v : val) (l : loc) :
     alloc v H = (l, H') ->
     dom H \subset dom H'.
   Proof.
     intros Ha l' [y Hget].
     destruct (loc_dec l l'); subst.
     - eexists. erewrite gas; eauto.
     - eexists. erewrite gao; eauto.
   Qed.
     
   Definition well_formed_alloc S (H H' : heap val) (v : val) (l : loc) :
     well_formed S H -> alloc v H = (l, H') ->
     locs v \subset (dom H) ->
     well_formed S H'.
   Proof.
     intros Hwf ha Hsub l' v' Sin Hget. destruct (loc_dec l l'); subst.
     - erewrite gas in Hget; eauto. inv Hget.
       eapply Included_trans. eassumption.
       now eapply alloc_dom_subset; eauto.
     - erewrite gao in Hget; eauto.
       eapply Included_trans. now eauto.
       now eapply alloc_dom_subset; eauto.
   Qed.
   
   Definition well_formed_env_alloc_extend S (H H' : heap val) rho x (v : val) (l : loc) :
     well_formed_env (Setminus _ S (Singleton _ x)) H rho -> alloc v H = (l, H') ->
     locs v \subset (dom H) ->
     well_formed_env S H' (M.set x l rho).
   Proof.
     intros Hwf ha Hsub x' l' Hin Hget. destruct (peq x x'); subst.
     - rewrite M.gss in Hget. inv Hget.
       eexists v. eapply gas. eauto.
     - rewrite M.gso in Hget; eauto. 
       eapply alloc_dom_subset; eauto. eapply Hwf; eauto.
       constructor; eauto. intros Hc; inv Hc; congruence.
   Qed.  

   Lemma Forall2_monotonic_strong (A : Type) (R R' : A -> A -> Prop) (l1 l2 : list A) :
     (forall x1 x2 : A, List.In x1 l1 -> List.In x2 l2 -> R x1 x2 -> R' x1 x2) ->
     Forall2 R l1 l2 -> Forall2 R' l1 l2.
   Proof.
     revert l2.
     induction l1 as [| x xs IHxs ]; intros l2 H Hall.
     - inv Hall; eauto. 
     - destruct l2; inv Hall. constructor; eauto.
       eapply H; eauto. now constructor. now constructor.
       eapply IHxs; eauto. intros. eapply H.
       now constructor; eauto. now constructor; eauto.
       eassumption.
   Qed.

   Lemma heap_env_approx_set S H1 H2 x l1 l2 rho1 rho2 :
     heap_env_approx (Setminus _ S (Singleton _ x)) (H1, rho1) (H2, rho2) ->
     (l1, H1) ≈ (l2, H2) ->
     heap_env_approx S (H1, M.set x l1 rho1) (H2, M.set x l2 rho2).
   Proof.
     intros Heq Hreq. intros y l Hin Hget.
     destruct (peq x y); subst; simpl in *. 
     - exists l2. rewrite M.gss in *; inv Hget; eauto.
     - rewrite M.gso in *; eauto. eapply Heq in Hget; eauto.
       constructor; eauto. intros Hc; inv Hc; congruence.
   Qed.



   Lemma heap_env_equiv_set S H1 H2 x l1 l2 rho1 rho2 :
     Setminus _ S (Singleton _ x) |- (H1, rho1) ⩪ (H2, rho2) ->
     (l1, H1) ≈ (l2, H2) ->
     S  |- (H1, M.set x l1 rho1) ⩪ (H2, M.set x l2 rho2).
   Proof.
     intros [Heq1 Heq2] Hreq. split.
     now eapply heap_env_approx_set.
     now eapply heap_env_approx_set; eauto; symmetry.
   Qed.
   
   Instance Proper_heap_env_approx : Proper (Same_set _ ==> eq ==> eq ==> iff) heap_env_approx.
   Proof.
     intros s1 s2 hseq p1 p2 Heq p1' p2' Heq'; subst; split; intros H1;
     destruct p2; destruct p2'; firstorder.
   Qed.

   Instance Proper_heap_env_equiv : Proper (Same_set _ ==> eq ==> eq ==> iff) heap_env_equiv.
   Proof.
     intros s1 s2 hseq p1 p2 Heq p1' p2' Heq'; subst.
     split; intros [h1 h2]; split; (try now rewrite hseq; eauto);
     rewrite <- hseq; eauto.
   Qed.

   Lemma heap_env_equiv_antimon S1 S2 H1 H2 rho1 rho2 :
     S1 |- (H1, rho1) ⩪ (H2, rho2) ->
     S2 \subset S1 ->
     S2 |- (H1, rho1) ⩪ (H2, rho2).
   Proof.
     firstorder.
   Qed.

   Lemma heap_env_equiv_setlist S H1 H2 xs ls1 ls2 rho1 rho2 rho1' rho2' :
     Setminus _ S (FromList xs) |- (H1, rho1) ⩪ (H2, rho2) ->
     setlist xs ls1 rho1 = Some rho1' -> setlist xs ls2 rho2 = Some rho2' ->
     Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) ls1 ls2  ->
     S  |- (H1, rho1') ⩪ (H2, rho2').
   Proof with (now eauto with Ensembles_DB).
     revert S rho1' rho2' ls1 ls2; induction xs;
     intros S  rho1' rho2' ls1 ls2 Heq Hs1 Hs2 Hall.
     - destruct ls1; destruct ls2; try discriminate. inv Hs1; inv Hs2; eauto.
       rewrite FromList_nil, Setminus_Empty_set_neut_r in Heq. eassumption.
     - destruct ls1; destruct ls2; try discriminate.
       inv Hall. simpl in Hs1, Hs2.
       destruct (setlist xs ls1 rho1) eqn:Hset1; try discriminate.
       destruct (setlist xs ls2 rho2) eqn:Hset2; try discriminate.
       inv Hs1; inv Hs2. eapply heap_env_equiv_set; eauto.
       eapply IHxs; eauto. eapply heap_env_equiv_antimon; eauto.
       rewrite FromList_cons...
   Qed.

   Lemma heap_env_equiv_def_funs S H1 H2 B l1 l2 rho1 rho2  :
     Setminus _ S (name_in_fundefs B) |- (H1, rho1) ⩪ (H2, rho2) ->
     (l1, H1) ≈ (l2, H2) ->
     S  |- (H1, def_funs B l1 rho1) ⩪ (H2, def_funs B l2 rho2).
   Proof with (now eauto with Ensembles_DB).
     revert S; induction B;
     intros S Heq Hreq.
     - simpl. eapply heap_env_equiv_set; eauto.
       eapply IHB; eauto. eapply heap_env_equiv_antimon; eauto.
       simpl. rewrite Setminus_Union...
     - simpl. rewrite Setminus_Empty_set_neut_r in Heq.
       eassumption.
   Qed.
   
   Lemma reachable_closed H S l v:
     l \in reach' H S ->
     get l H = Some v ->
     locs v \subset reach' H S.
   Proof.
     intros Hin Hget.
     eapply Included_trans;
       [| now eapply reach'_post_fixed_point_n with (n := 1)]; simpl.
     intros l' Hin'. do 2 eexists. split. eassumption. now split; eauto.
   Qed.

   Lemma reachable_in_dom H S :
     well_formed (reach' H S) H ->
     S \subset dom H ->
     reach' H S \subset dom H.
   Proof.
     intros H1 Hs l [n [_ Hr]]. destruct n; eauto.
     simpl in Hr. destruct Hr as [l' [v' [Hin [Hget Hin']]]].
     eapply H1; eauto. eexists; split; eauto. now constructor; eauto.
   Qed.

   Lemma res_approx_weakening S1 S2 H1 H2 H1' H2' l1 l2 i :
     closed S1 H1 -> closed S2 H2 ->
     res_approx_fuel' i (l1, H1) (l2, H2) ->
     H1 ⊑ H1' -> 
     H2 ⊑ H2' ->
     l1 \in S1 -> l2 \in S2 -> 
     res_approx_fuel' i (l1, H1') (l2, H2').
   Proof.
     intros Hwf1 Hwf2 Heq Hsub1 Hsub2.
     revert l1 l2 Heq; induction i using lt_wf_rec1; intros l1 l2 Heq Hdom1 Hdom2.
     intros v1 Hget1. edestruct (Hwf1 _ Hdom1) as [v1' [Hget1' Hsub1']].
     edestruct (Hwf2 _ Hdom2) as [v2' [Hget2' Hsub2']].
     specialize (Hsub1 _ _ Hget1'). rewrite Hsub1 in Hget1; inv Hget1.
     specialize (Hsub2 _ _ Hget2').
     edestruct Heq as [v2 [Hget2 Hm]]; eauto. rewrite Hget2 in Hget2'; inv Hget2'.
     eexists; split; [ now eauto |]. destruct v1; destruct v2'; try contradiction.
     + inv Hm; split; eauto. intros i' Hlt.
       eapply Forall2_monotonic_strong
       with (R :=  fun l3 l4 => l3 \in S1 -> l4 \in S2 -> res_approx_fuel i' (l3, H1') (l4, H2')).
       * intros l1' l2' Hin1 Hin2 Hyp. eapply Hyp; eauto.
       * eapply Forall2_monotonic; [| eauto ].
         intros. rewrite res_approx_fuel_eq. eapply H; eauto.
         rewrite <- res_approx_fuel_eq. eassumption.
     + inv Hm; split; eauto. intros i' x Hlt Hfv.
       specialize (H3 i' x Hlt Hfv). inversion H3 as [[l3 [l4 [Hget3 [Hget4 Hres]]]] | H3']; eauto.
       left. exists l3, l4. split; [| split ]; eauto.
       rewrite res_approx_fuel_eq. eapply H; eauto.
       rewrite <- res_approx_fuel_eq. eassumption.
       eapply Hsub1'; eauto. eexists; split; eauto.
       eapply Hsub2'; eauto. eexists; split; eauto.
   Qed.

   Lemma reach'_closed S H :
     well_formed (reach' H S) H ->
     S \subset dom H ->
     closed (reach' H S) H.
   Proof.
     intros HHwf sub l Hreach.
     edestruct reachable_in_dom as [v Hget]; eauto.
     eexists; split; eauto.
     eapply reachable_closed; eauto.
   Qed.

   Corollary res_equiv_weakening S1 S2 H1 H2 H1' H2' l1 l2 :
     closed S1 H1 -> closed S2 H2 ->
     (l1, H1) ≈ (l2, H2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     l1 \in S1 -> l2 \in S2 -> 
     (l1, H1') ≈ (l2, H2').
   Proof.
     intros Hwf1 Hwf2 Heq Hsub1 Hsub2 Hin1 Hin2 i. destruct (Heq i) as [Heq1 He2].
     split. now eapply (res_approx_weakening S1 S2 H1 H2 H1' H2'); eauto.
     now eapply (res_approx_weakening S2 S1 H2 H1 H2' H1'); eauto.
   Qed.

   Lemma Forall2_symm (A : Type) (R : A -> A -> Prop) (l1 l2 : list A) : 
     Symmetric R -> Forall2 R l1 l2 -> Forall2 R l2 l1.
   Proof.
     intros H Hall; induction Hall; eauto.
   Qed.

   Lemma Forall2_symm_strong (A : Type) (R1 R2 : A -> A -> Prop) (l1 l2 : list A) : 
     (forall l1 l2, R1 l1 l2 -> R2 l2 l1) -> Forall2 R1 l1 l2 -> Forall2 R2 l2 l1.
   Proof.
     intros H Hall; induction Hall; eauto.
  Qed.
   
   Lemma heap_env_approx_set_alloc_Vconstr S S1 S2 H1 H2 H1' H2' x t ls ls' l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 (Setminus _ S (Singleton _ x)) \subset S1 ->
     env_locs rho2 (Setminus _ S (Singleton _ x)) \subset S2 ->
     FromList ls \subset S1 ->
     FromList ls' \subset S2 -> 
     heap_env_approx (Setminus _ S (Singleton _ x)) (H1, rho1) (H2, rho2) ->
     alloc (Vconstr t ls) H1 = (l1, H1') -> alloc (Vconstr t ls') H2 = (l2, H2') ->
     Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) ls ls' ->
     heap_env_approx S (H1', (M.set x l1 rho1)) (H2', (M.set x l2 rho2)).
   Proof.
     intros Hwf1 Hwf2 He1 He2 Hl1 Hl2 Heq Hal1 Hal2 Hall; simpl; intros y l Hin Hget.
     destruct (peq x y); subst.
     + rewrite M.gss in *. inv Hget. eexists; split; eauto. split.
       * intros v Hget. erewrite gas in *; eauto. inv Hget. eexists; split; eauto.
         simpl. split; eauto. intros i Hlt.
         eapply Forall2_monotonic_strong
         with (R :=  fun l3 l4 => l3 \in S1 -> l4 \in S2 -> res_approx_fuel i (l3, H1') (l4, H2')).
         intros l1' l2' Hin1 Hin2 Hyp. eapply Hyp; eauto.
         eapply Forall2_monotonic; [| eauto ].
         intros. rewrite res_approx_fuel_eq. eapply (res_approx_weakening _ _ H1 H2); eauto.
         eapply H; eauto. now eapply alloc_subheap; eauto. now eapply alloc_subheap; eauto.
       * intros v Hget. erewrite gas in *; eauto. inv Hget. eexists; split; eauto.
         simpl. split; eauto. intros i Hlt.
         eapply Forall2_monotonic_strong
         with (R :=  fun l3 l4 => l3 \in S2 -> l4 \in S1 -> res_approx_fuel i (l3, H2') (l4, H1')).
         intros l1' l2' Hin1 Hin2 Hyp. eapply Hyp; eauto.
         eapply Forall2_symm_strong with (R2 := (fun l1 l2 : loc => (l1, H2) ≈ (l2, H1))) in Hall.
         eapply Forall2_monotonic; [| eauto ].
         intros. rewrite res_approx_fuel_eq. eapply (res_approx_weakening _ _ H2 H1); eauto.
         eapply H; eauto. now eapply alloc_subheap; eauto. now eapply alloc_subheap; eauto.
         intros; now symmetry.
     + rewrite M.gso in *; eauto. assert (Hget1 := Hget). eapply Heq in Hget.
       destruct Hget as [l' [Hget' Heq']]. eexists; split; eauto.
       eapply (res_equiv_weakening _ _ H1 H2  H1' H2'); eauto; simpl in *.
       now eapply alloc_subheap; eauto.
       now eapply alloc_subheap; eauto.
       eapply He1; eauto. repeat eexists; eauto.
       intros Hc; inv Hc. congruence.
       eapply He2; eauto. repeat eexists; eauto.
       intros Hc; inv Hc. congruence.
       econstructor; eauto. intros Hc; inv Hc; congruence.
   Qed.

   Corollary heap_env_equiv_set_alloc_Vconstr S S1 S2 H1 H2 H1' H2' x t ls ls' l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 (Setminus _ S (Singleton _ x)) \subset S1 ->
     env_locs rho2 (Setminus _ S (Singleton _ x)) \subset S2 ->
     FromList ls \subset S1 ->
     FromList ls' \subset S2 ->
     Setminus _ S (Singleton _ x) |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vconstr t ls) H1 = (l1, H1') -> alloc (Vconstr t ls') H2 = (l2, H2') ->
     Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) ls ls' ->
     S |- (H1', M.set x l1 rho1) ⩪ (H2', M.set x l2 rho2).
   Proof.
     intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hl1 Hl2 [Heq1 Heq2] Hal1 Hal2 Hall; split.
     now eapply (heap_env_approx_set_alloc_Vconstr _ _ _ H1 H2); eauto.
     eapply (heap_env_approx_set_alloc_Vconstr _ _ _ H2 H1); eauto.
     eapply Forall2_symm_strong; [| eassumption ]. intros; now symmetry; eauto.
   Qed.
   
   Instance Equivalence_heap_env_equiv S : Equivalence (heap_env_equiv S).
   Proof.
     constructor.
     - intros [H rho]; split; intros l Hget; eexists; split; eauto; reflexivity.
     - intros [H rho] [H' rho'] H1; split; intros v l Hin Hget;
       eapply H1; eauto.
     - edestruct Equivalence_res_equiv; eauto.
       intros [H rho] [H' rho'] [H'' rho''] H1 H2; split; intros v l Hin Hget.
       edestruct H1 as [H1' _]; eauto. edestruct H1' as [v1 [Hget1 Hres1]]; eauto.
       edestruct H2 as [H2' _]; eauto. edestruct H2' as [v2 [Hget2 Hres2]]; eauto.
       edestruct H2 as [_ H2']; eauto. edestruct H2' as [v2 [Hget2 Hres2]]; eauto.
       edestruct H1 as [_ H1']; eauto. edestruct H1' as [v1 [Hget1 Hres1]]; eauto.
   Qed.
   
   Lemma heap_env_approx_set_alloc_Vfun S S1 S2 H1 H2 H1' H2' x B l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 (Setminus _ S [set x]) \subset S1 ->
     env_locs rho2 (Setminus _ S [set x]) \subset S2 ->
     (occurs_free_fundefs B) \subset (Setminus _ S [set x]) ->
     Setminus _ S [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vfun rho1 B) H1 = (l1, H1') -> alloc (Vfun rho2 B) H2 = (l2, H2') ->
     heap_env_approx S (H1', (M.set x l1 rho1)) (H2', (M.set x l2 rho2)).
   Proof.
     intros Hwf1 Hwf2 He1 He2 Hsub [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
     destruct (peq x y); subst.
     - rewrite M.gss in *. inv Hget. eexists; split; eauto. split.
       + intros v Hget. erewrite gas in *; eauto. inv Hget. eexists; split; eauto.
         simpl. split; eauto. intros i x Hlt Hin'.
         destruct (M.get x rho1) eqn:Hget.
         * edestruct Heq1 as [x' [Hget' Heq']]; eauto.
           left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
           eapply (res_approx_weakening _ _ H1 H2); eauto.
           now destruct (Heq' i); eauto. 
           now eapply alloc_subheap; eauto.
           now eapply alloc_subheap; eauto. 
           eapply He1. now eexists; split; eauto.
           eapply He2. now eexists; split; eauto.
         * right; split; eauto.
           destruct (M.get x rho2) eqn:Hget'; eauto.
           edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence.
       + intros v Hget. erewrite gas in *; eauto. inv Hget. eexists; split; eauto.
         simpl. split; eauto. intros i x Hlt Hin'.
         destruct (M.get x rho1) eqn:Hget.
         * edestruct Heq1 as [x' [Hget' Heq']]; eauto.
           left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
           symmetry in Heq'. eapply (res_approx_weakening _ _ H2 H1); eauto.
           now destruct (Heq' i); eauto. 
           now eapply alloc_subheap; eauto.
           now eapply alloc_subheap; eauto. 
           eapply He2. now eexists; split; eauto.
           eapply He1. now eexists; split; eauto.
         * right; split; eauto.
           destruct (M.get x rho2) eqn:Hget'; eauto.
           edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence.
     - rewrite M.gso in *; eauto. assert (Hget1 := Hget). eapply Heq1 in Hget.
       destruct Hget as [l' [Hget' Heq']]. eexists; split; eauto.
       eapply (res_equiv_weakening _ _ H1 H2  H1' H2'); eauto; simpl in *.
       now eapply alloc_subheap; eauto.
       now eapply alloc_subheap; eauto.
       eapply He1; eauto. repeat eexists; eauto.
       intros Hc; inv Hc. congruence.
       eapply He2; eauto. repeat eexists; eauto.
       intros Hc; inv Hc. congruence.
       econstructor; eauto. intros Hc; inv Hc; congruence.
   Qed.

   Corollary heap_env_equic_set_alloc_Vfun S S1 S2 H1 H2 H1' H2' x B l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 (Setminus _ S [set x]) \subset S1 ->
     env_locs rho2 (Setminus _ S [set x]) \subset S2 ->
     (occurs_free_fundefs B) \subset (Setminus _ S [set x]) ->
     Setminus _ S [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vfun rho1 B) H1 = (l1, H1') -> alloc (Vfun rho2 B) H2 = (l2, H2') ->
     S |- (H1', (M.set x l1 rho1)) ⩪ (H2', (M.set x l2 rho2)).
   Proof.
     intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hsub Heq Hal1 Hal2; split.
     now eapply (heap_env_approx_set_alloc_Vfun _ _ _ H1 H2); eauto.
     eapply (heap_env_approx_set_alloc_Vfun _ _ _ H2 H1); eauto.
     symmetry; eauto.
   Qed.

   Lemma heap_env_approx_alloc_Vfun S S1 S2 H1 H2 H1' H2' B l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset S1 ->
     env_locs rho2 S \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vfun rho1 B) H1 = (l1, H1') -> alloc (Vfun rho2 B) H2 = (l2, H2') ->
     heap_env_approx S (H1', rho1) (H2', rho2).
   Proof.
     intros Hwf1 Hwf2 He1 He2  [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
     edestruct Heq1 as [x' [Hget' Heq']]; eauto.
     eexists; split; eauto.
     eapply (res_equiv_weakening _ _ H1 H2); eauto.
     now eapply alloc_subheap; eauto.
     now eapply alloc_subheap; eauto. 
     eapply He1. now eexists; split; eauto.
     eapply He2. now eexists; split; eauto.
   Qed.

   Corollary heap_env_equiv_alloc_Vfun S S1 S2 H1 H2 H1' H2' B l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset S1 ->
     env_locs rho2 S \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vfun rho1 B) H1 = (l1, H1') -> alloc (Vfun rho2 B) H2 = (l2, H2') ->
     S |- (H1', rho1) ⩪ (H2', rho2).
   Proof.
     intros. split.
     now eapply (heap_env_approx_alloc_Vfun _ _ _ H1 H2); eauto.
     now eapply (heap_env_approx_alloc_Vfun _ _ _ H2 H1); eauto; symmetry.
   Qed.
   
   Lemma env_locs_monotonic S1 S2 rho :
     S1 \subset S2 ->
     env_locs rho S1 \subset env_locs rho S2.
   Proof.
     firstorder.
   Qed.

   Instance Proper_env_locs : Proper (eq ==> Same_set _ ==> Same_set _) env_locs.
   Proof.
     intros rho1 rho2 heq s1 s2 Hseq; subst.
     firstorder.
   Qed.
  

   
   Lemma heap_env_equiv_def_funs_alloc S S1 S2 H1 H2 H1' H2' B B' l1 l2 rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 (Setminus _ S (name_in_fundefs B)) \subset S1 ->
     env_locs rho2 (Setminus _ S (name_in_fundefs B)) \subset S2 ->
     (occurs_free_fundefs B') \subset (Setminus _ S (name_in_fundefs B)) -> 
     (Setminus _ S (name_in_fundefs B)) |- (H1, rho1) ⩪ (H2, rho2) ->
     alloc (Vfun rho1 B') H1 = (l1, H1') -> alloc (Vfun rho2 B') H2 = (l2, H2') ->
     S |- (H1', def_funs B l1 rho1) ⩪ (H2', def_funs B l2 rho2).
   Proof with now eauto with Ensembles_DB.
     intros Hwf1 Hwf2 He1 He2 Hsub Heq Hal1 Hal2.
     revert S He1 He2 Hsub Heq; induction B; intros S He1 He2 Hsub Heq.
     - eapply heap_env_equiv_set; eauto.
       + simpl in *. eapply IHB; eauto.
         eapply Included_trans; eauto.
         eapply env_locs_monotonic...
         eapply Included_trans; eauto.
         eapply env_locs_monotonic...
         eapply Included_trans; eauto...
         eapply heap_env_equiv_antimon; eauto...
       + destruct Heq as [Heq1 Heq2]. split.
         { intros v1. erewrite !gas; eauto.
           intros Hget; eexists; split; eauto.
           inv Hget. split; eauto.
           intros i x Hlt Hin.
           destruct (M.get x rho1) eqn:Hget.
           - edestruct Heq1 as [x' [Hget' Heq']]; eauto.
             left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
             symmetry in Heq'. eapply (res_approx_weakening _ _ H1 H2); eauto.
             now destruct (Heq' i); eauto. 
             now eapply alloc_subheap; eauto.
             now eapply alloc_subheap; eauto. 
             eapply He1. now eexists; split; eauto.
             eapply He2. now eexists; split; eauto.
           - right; split; eauto.
             destruct (M.get x rho2) eqn:Hget'; eauto.
             edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence. }
         { intros v1. erewrite !gas; eauto.
           intros Hget; eexists; split; eauto.
           inv Hget. split; eauto.
           intros i x Hlt Hin.
           destruct (M.get x rho1) eqn:Hget.
           - edestruct Heq1 as [x' [Hget' Heq']]; eauto.
             left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
             symmetry in Heq'. eapply (res_approx_weakening _ _ H2 H1); eauto.
             now destruct (Heq' i); eauto. 
             now eapply alloc_subheap; eauto.
             now eapply alloc_subheap; eauto. 
             eapply He2. now eexists; split; eauto.
             eapply He1. now eexists; split; eauto.
           - right; split; eauto.
             destruct (M.get x rho2) eqn:Hget'; eauto.
             edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence. }
     - simpl in *. rewrite !Setminus_Empty_set_neut_r in He1, He2, Heq.
       eapply (heap_env_equiv_alloc_Vfun _ _ _ H1 H2); eauto.
   Qed.
   
   Lemma well_formed_env_antimon S1 S2 H rho :
     well_formed_env S1 H rho ->
     S2 \subset S1 ->
     well_formed_env S2 H rho.
   Proof.
     firstorder.
   Qed.

   Lemma getlist_in_dom S H rho ys ls :
     well_formed_env S H rho ->
     getlist ys rho = Some ls ->
     FromList ys \subset S ->
     FromList ls \subset dom H. 
   Proof.
     revert ls; induction ys; intros ls Hwf Hget Hin; destruct ls; simpl in *; try discriminate.
     - now eauto with Ensembles_DB.
     - now eauto with Ensembles_DB.
     - rewrite !FromList_cons in Hin. rewrite FromList_cons.
       destruct (M.get a rho) eqn:Hgeta; try discriminate.
       destruct (getlist ys rho) eqn:Hgetys; try discriminate.
       inv Hget. eapply Union_Included.
       eapply Singleton_Included. eapply Hwf; eauto. 
       eapply IHys; eauto. eapply Included_trans; now eauto with Ensembles_DB.
   Qed.

   Lemma heap_env_equiv_getlist_Forall2 S H1 H2 ys ls1 ls2 rho1 rho2 :
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     FromList ys \subset S ->
     getlist ys rho1 = Some ls1 ->
     getlist ys rho2 = Some ls2 ->
     Forall2 (fun l1 l2 : loc => (l1, H1) ≈ (l2, H2)) ls1 ls2.
   Proof.
     revert ls1 ls2; induction ys; intros ls1 ls2 Heq Hin Hg1 Hg2;
     destruct ls1; destruct ls2; simpl in *; try discriminate; try now constructor.
     - destruct (M.get a rho1) eqn:Heqa;
       destruct (getlist ys rho1) eqn:Heqys; try discriminate.
     - destruct (M.get a rho2) eqn:Heqa;
       destruct (getlist ys rho2) eqn:Heqys; try discriminate.
     - rewrite FromList_cons in Hin.
       destruct (M.get a rho1) eqn:Heqa;
         destruct (getlist ys rho1) eqn:Heqys; try discriminate. inv Hg1.
       eapply Heq in Heqa. destruct Heqa as [l' [Hget Heq']]. rewrite Hget in Hg2.
       destruct (getlist ys rho2) eqn:Heqys'; try discriminate. inv Hg2.
       constructor; eauto. eapply IHys; eauto.
       eapply Included_trans; now eauto with Ensembles_DB.
       eapply Included_trans; now eauto with Ensembles_DB.
   Qed.
   
   Lemma env_locs_set_not_In S rho x l :
     ~ x \in S ->
     env_locs (M.set x l rho) S <--> env_locs rho S.
   Proof.
     intros Hin; split; intros l' H1.
     - destruct H1 as [z [H1 H2]].
       destruct (peq z x); subst.
       + contradiction.
       + rewrite M.gso in *; eauto. eexists; eauto.
     - destruct H1 as [z [H1 H2]].
       destruct (peq z x); subst.
       + contradiction.
       + eexists. rewrite M.gso; eauto.
   Qed.

   Lemma env_locs_set S rho x l :
     x \in S ->
     env_locs (M.set x l rho) S <--> Union _ [set l] (env_locs rho (Setminus _ S [set x])).
   Proof.
     intros Hin; split; intros l' H1.
     - destruct H1 as [z [H1 H2]].
       destruct (peq z x); subst.
       + rewrite M.gss in *. inv H2; eauto.
       + rewrite M.gso in *; eauto. right. eexists; split; eauto.
         constructor; eauto. intros Hc; inv Hc; eauto.
     - inv H1. eexists; split; eauto. inv H; now rewrite M.gss; eauto.
       destruct H as [z [H1 H2]]. inv H1.
       destruct (peq z x); subst.
       + exfalso; eauto.
       + eexists. rewrite M.gso; eauto.
   Qed.

   Lemma env_locs_set_Inlcuded S rho x l :
     env_locs (M.set x l rho) (Union _ S [set x]) \subset
     Union _ [set l] (env_locs rho S).
   Proof.
     intros l' H1.
     - destruct H1 as [z [H1 H2]].
       destruct (peq z x); subst.
       + rewrite M.gss in *. inv H2; eauto.
       + rewrite M.gso in *; eauto. right. eexists; split; eauto.
         inv H1; eauto. inv H. congruence.
   Qed.

   Lemma env_locs_def_funs_Included B l rho S :
     env_locs (def_funs B l rho)
              (Union M.elt S (name_in_fundefs B)) \subset
     Union _ (env_locs rho S) [set l].
   Proof.
     induction B; simpl.
     - eapply Included_trans.
       rewrite (Union_commut [set v]), Union_assoc.
       eapply env_locs_set_Inlcuded. rewrite Union_commut.
       eapply Union_Included; eauto with Ensembles_DB.
     - rewrite Union_Empty_set_neut_r; eauto with Ensembles_DB.
   Qed.

   Lemma env_locs_set_list_Included ys ls rho rho' S :
     setlist ys ls rho = Some rho'  ->
     env_locs rho'
              (Union M.elt S (FromList ys)) \subset
     Union _ (env_locs rho S) (FromList ls).
   Proof with now eauto with Ensembles_DB.
     revert rho' S ls; induction ys; intros rho' S ls Hset.
     - rewrite FromList_nil, Union_Empty_set_neut_r. inv Hset.
       destruct ls; try discriminate. inv H0...
     - destruct ls; try discriminate. simpl in *.
       destruct (setlist ys ls rho) eqn:Hset'; try discriminate.
       inv Hset. rewrite !FromList_cons.
       rewrite (Union_commut [set a]), !Union_assoc. 
       eapply Included_trans. eapply env_locs_set_Inlcuded.
       eapply Union_Included; eauto with Ensembles_DB. 
       eapply Included_trans. eapply IHys; eauto.
       now eauto with Ensembles_DB. 
   Qed.

   Lemma alloc_Same_set {A} H (v : A) l H' :
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




   Lemma post_Union H S1 S2 :
     post H (Union _ S1 S2) <--> Union _ (post H S1) (post H S2).
   Proof with now eauto with Ensembles_DB.
     split; intros l Hp.
     - destruct Hp as [l' [v [Hin [Hget Hin']]]].
       inv Hin; [left | right ]; repeat eexists; eauto.
     - destruct Hp as [ Hp | Hp ];
       eapply post_set_monotonic; eauto...
   Qed.

   Lemma post_n_Union n H S1 S2 :
     (post H ^ n) (Union _ S1 S2) <--> Union _ ((post H ^ n) S1) ((post H ^ n) S2).
   Proof with now eauto with Ensembles_DB.
     induction n;  try now firstorder.
     simpl. rewrite IHn, post_Union. reflexivity.
   Qed.

   Lemma reach'_Union H S1 S2 :
     reach' H (Union _ S1 S2) <--> Union _ (reach' H S1) (reach' H S2).
   Proof.
     split; intros l Hp.
     - destruct Hp as [n [HT Hp]].
       eapply post_n_Union in Hp. destruct Hp as [Hp | Hp ].
       now left; firstorder. now right; firstorder.
     - destruct Hp as [ l [n [HT Hp]] | l [n [HT Hp]] ];
       repeat eexists; eauto; eapply post_n_Union; eauto.
   Qed.

   Lemma post_n_heap_monotonic n (H1 H2 : heap val) (S : Ensemble loc) :
     H1 ⊑ H2 -> (post H1 ^ n) S \subset (post H2 ^ n) S.
   Proof.
     induction n; simpl; eauto with Ensembles_DB.
     intros Hsub. eapply Included_trans.
     eapply post_set_monotonic. now eauto.
     now eapply post_heap_monotonic.
   Qed.

   Lemma reach'_heap_monotonic (H1 H2 : heap val) (S : Ensemble loc) :
     H1 ⊑ H2 -> reach' H1 S \subset reach' H2 S.
   Proof.
     intros Hsub l [n [HT Hp]]. exists n; split; eauto.
     eapply post_n_heap_monotonic; eauto.
   Qed.

    Lemma post_alloc S H v l H'  :
     alloc v H = (l, H') ->
     post H' S \subset (Union _ (post H S) (locs v)).
    Proof.
     intros Ha l' Hp.
     destruct Hp as [l2 [v' [Hin2 [Hget Hin1]]]].
     destruct (loc_dec l l2); subst; eauto.
     + repeat eexists; eauto. erewrite gas in Hget; eauto.
       inv Hget. eauto.
     + left; repeat eexists; eauto. erewrite <-gao; eauto.
    Qed.

    Lemma post_n_alloc n S H v l H'  :
      alloc v H = (l, H') ->
      locs v \subset reach' H S ->
      (post H' ^ n) S \subset reach' H S.
    Proof.
      revert S.
      induction n; intros S Ha Hin; simpl; eauto with Ensembles_DB.
      - now apply reach'_extensive.
      - eapply Included_trans. eapply post_set_monotonic.
        now eauto. eapply Included_trans. now eapply post_alloc; eauto.
        eapply Union_Included. now eapply reach'_post_fixed_point_n with (n := 1).
        eapply Included_trans; eauto. reflexivity.
    Qed.

   Lemma reach'_alloc S H v l H'  :
     alloc v H = (l, H') ->
     locs v \subset reach' H S ->
     reach' H' S <--> reach' H S.
   Proof.
     intros Ha Hin.
     split.
     - intros l' [n [_ Hp]]. eapply post_n_alloc; eauto.
     - eapply reach'_heap_monotonic. now eapply alloc_subheap; eauto.
   Qed.

   Instance Proper_well_formed : Proper (Same_set _ ==> eq ==> iff) well_formed.
   Proof.
     intros s1 s2 hseq H1 h2 Heq; subst. firstorder.
   Qed.

   Lemma well_formed_antimon S1 S2 H :
     S1 \subset S2 ->
     well_formed S2 H ->
     well_formed S1 H.
   Proof.
     firstorder.
   Qed.

   Lemma post_Empty S H :
     Disjoint _ S (dom H) ->
     post H S <--> Empty_set _.
   Proof.
     intros Hd; split; eauto with Ensembles_DB.
     intros l [l' [v [Hin [Hget _]]]].
     exfalso. eapply Hd. constructor; eauto.
     eexists; eauto.
   Qed.

   Lemma post_n_Disjoint n S H :
     Disjoint _ S (dom H) ->
     (post H ^ n) S \subset S.
   Proof with now eauto with Ensembles_DB.
     revert S; induction n; intros S Hd; eauto with Ensembles_DB.
     replace (Datatypes.S n) with (n + 1) by omega.
     rewrite app_plus. simpl. unfold compose.
     eapply Included_trans. eapply proper_post_n.
     rewrite post_Empty; eauto. reflexivity.
     eapply Included_trans; [ eapply IHn | ]...
   Qed.

   Lemma reach'_Disjoint S H :
     Disjoint _ S (dom H) ->
     reach' H S <--> S.
   Proof.
     split.
     - intros l [n [_ Hp]]. eapply post_n_Disjoint; eauto.
     - apply reach'_extensive.
   Qed.

   Lemma well_formed_Union S1 S2 H :
     well_formed S1 H ->
     well_formed S2 H ->
     well_formed (Union _ S1 S2) H.
   Proof.
     intros Hwf1 Hwf2 l v Hin Hget; inv Hin; eauto.
   Qed.

   Lemma env_locs_Union rho S1 S2 :
     env_locs rho (Union _ S1 S2) <-->
     Union _ (env_locs rho S1) (env_locs rho S2).
   Proof.
     split; intros l.
     - intros [v [Hin Hget]]. inv Hin; firstorder.
       now left; repeat eexists; eauto.
       now right; repeat eexists; eauto.
     - intros [ l' [v [Hin Hget]] | l' [v [Hin Hget]] ];
       repeat eexists; eauto.
   Qed.

   Lemma well_formed_reach_alloc S H x l v H' rho :
     well_formed (reach' H (env_locs rho S)) H ->
     env_locs rho S \subset dom H ->
     alloc v H = (l, H') ->
     locs v \subset (reach' H (env_locs rho S)) ->
     well_formed (reach' H' (env_locs (M.set x l rho) (Union _ S [set x]))) H'.
   Proof with now eauto with Ensembles_DB.
     intros Hwf Hsub Ha Hin.
     eapply well_formed_antimon.
     eapply reach'_set_monotonic. now eapply env_locs_set_Inlcuded.
     rewrite reach'_alloc; eauto.
     - rewrite reach'_Union. eapply well_formed_Union.
       + rewrite reach'_Disjoint.
         * intros l' v' Hin' Hget. inv Hin'.
           erewrite gas in Hget; eauto. inv Hget.
           eapply Included_trans; eauto.
           eapply Included_trans;
             [| now eapply dom_subheap; eapply alloc_subheap; eauto ].
           eapply reachable_in_dom; eauto.
         * constructor. intros l' Hc. inv Hc. inv H0.
           destruct H1 as [v' Hget]. erewrite alloc_fresh in Hget; eauto.
           discriminate.
       + eapply well_formed_alloc; eauto.
         eapply Included_trans; eauto. eapply reachable_in_dom; eauto.
     - rewrite reach'_Union. eapply Included_Union_preserv_r.
       eassumption.
   Qed.

   Lemma well_formed_reach_set S H x l rho :
     well_formed (reach' H (env_locs rho S)) H ->
     well_formed (reach' H [set l]) H ->
     well_formed (reach' H (env_locs (M.set x l rho) (Union _ S [set x]))) H.
   Proof with now eauto with Ensembles_DB.
     intros Hwf  Hin.
     eapply well_formed_antimon.
     eapply reach'_set_monotonic. now eapply env_locs_set_Inlcuded.
     rewrite reach'_Union. eapply well_formed_Union; eauto.
   Qed.

   Lemma env_locs_Empty S :
     Empty_set _ <--> env_locs (M.empty _) S.
   Proof.
     split; eauto with Ensembles_DB.
     intros l [v [Hs Hp]]. rewrite M.gempty in Hp.
     discriminate.
   Qed.

   Lemma env_locs_singleton x l :
     [set l] <--> env_locs (M.set x l (M.empty _)) (Union _ (Empty_set _) [set x]).
   Proof.
     rewrite env_locs_set; eauto with Ensembles_DB.
     rewrite <- env_locs_Empty; eauto with Ensembles_DB.
   Qed.

    Lemma env_locs_singleton_Included x l rho S:
     [set l] \subset env_locs (M.set x l rho) (Union _ S [set x]).
   Proof.
     rewrite env_locs_set; eauto with Ensembles_DB.
   Qed.
     
   Lemma well_formed_reach_alloc_def_funs S H B l v H' rho :
     well_formed (reach' H (env_locs rho S)) H ->
     env_locs rho S \subset dom H ->
     alloc v H = (l, H') ->
     locs v \subset (reach' H (env_locs rho S)) ->
     well_formed (reach' H' (env_locs (def_funs B l rho) (Union _ S (name_in_fundefs B)))) H'.
   Proof with now eauto with Ensembles_DB.
     induction B; intros Hwf Hsub Ha Hin; simpl.
     - rewrite (Union_commut [set v0]), Union_assoc.
       eapply well_formed_reach_set.
       + eapply IHB; eauto.
       + eapply well_formed_antimon.
         eapply reach'_set_monotonic.
         now apply env_locs_singleton_Included with (x := v0).
         eapply well_formed_reach_alloc; eauto.
     - rewrite Union_Empty_set_neut_r.
       rewrite reach'_alloc; eauto.
       eapply well_formed_alloc; eauto.
       eapply Included_trans. eassumption.
       eapply reachable_in_dom; eauto.
   Qed.

  Lemma occurs_free_Econstr_Included' (x : var) (t : cTag) (ys : list var) (e : exp) :
    Setminus _ (occurs_free e) [set x] \subset
    occurs_free (Econstr x t ys e).
  Proof.
    eapply Setminus_Included_Included_Union.
    now apply occurs_free_Econstr_Included.
  Qed.

  Lemma FromList_env_locs xs ls rho S :
    getlist xs rho = Some ls ->
    FromList xs \subset S ->
    FromList ls \subset env_locs rho S.
  Proof with now eauto with Ensembles_DB.
    revert ls; induction xs; intros ls Hget Hs; simpl in *.
    - inv Hget. rewrite FromList_nil...
    - destruct (M.get a rho) eqn:Hgeta; try discriminate.
      destruct (getlist xs rho) eqn:Hgetl; try discriminate.
      inv Hget. rewrite !FromList_cons in Hs. rewrite !FromList_cons.
      eapply Union_Included.
      + intros l' Hin. inv Hin. repeat eexists; eauto.
      + eapply IHxs; eauto.
        eapply Included_trans...
  Qed.

  Lemma well_formed_heap_eq S H1 H2 :
    well_formed S H1 ->
    closed S H1 -> 
    S |- H1 ≡ H2 ->
    well_formed S H2.
  Proof.
    intros Hwf Hcl Heq x v Hin Hget l Hin'.
    rewrite <- Heq in Hget; eauto.
    destruct (Hwf x v Hin Hget l Hin') as [l' Hget'].
    rewrite -> Heq in Hget'; eauto. repeat eexists; eauto.
    edestruct Hcl as [v' [Hget'' Hin'']]; eauto.
    rewrite Hget in Hget''; inv Hget''; eauto.
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

  Lemma alloc_In_dom {A} H1 (v :A) l H2 :
    alloc v H1 = (l, H2) ->
    l \in dom H2.
  Proof.
    intros. eexists. erewrite gas; eauto.
  Qed.

  (** Lemmas about [getlist] *)
  Lemma getlist_In_val {A} (rho : M.t A) ys v vs :
    getlist ys rho = Some vs ->
    List.In v vs ->
    exists x, List.In x ys /\ M.get x rho = Some v.
  Proof.
    revert v vs. induction ys; intros x vs Hget H.
    - inv Hget. now inv H.
    - simpl in *.
      destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
      destruct (getlist ys rho) eqn:Heq'; try discriminate; eauto.
      inv Hget. inv H; eauto.
      edestruct IHys as [y [Hin Hget]]; eauto.
  Qed.

  Lemma heap_env_approx_Vfun S rho rho' rho1 rho2 H H' l l' f B :
    M.get f rho = Some l ->
    M.get f rho' = Some l' ->
    (l, H) ≈ (l', H') ->
    S |- (H, rho) ⩪ (H', rho') ->
    f \in S ->
    get l H = Some (Vfun rho1 B) ->
    get l' H' = Some (Vfun rho2 B) ->
    heap_env_approx (occurs_free_fundefs B) (H, rho1) (H', rho2).
  Proof.
    intros Hget1 Hget2 Heq Hheq Hin Hget1' Hget2' x1 l1 Hin' Hget.
    edestruct Heq with (n := 1) as [Heq1 Heq2]. 
    edestruct Heq1 as [v2 [Hget' Hv]]; eauto.
    destruct v2; try contradiction.
    destruct Hv as [HBeq Hlt]; subst. 
    destruct (Hlt 0 x1) as [[l1' [l2' [Hgetl1 [Hgetl2 _]]]] | [Hn1 Hn2]]; eauto;
    try congruence.
    rewrite Hget in Hgetl1; inv Hgetl1; rewrite Hget' in  Hget2'; inv Hget2'.
    eexists; split; eauto.
    intros n.
    edestruct Heq with (n := n + 1) as [Heqn1 Heqn2].
    split.
    - edestruct Heqn1 as [v2 [Hgetv Hv]]; eauto.
      destruct v2; try contradiction. destruct Hv as [HBeq Hlt']; subst. 
      destruct (Hlt' n x1) as [[l3' [l4' [Hgetl3 [Hgetl4 Hres]]]] | [Hn1 Hn2]]; eauto;
      try congruence.
      omega. rewrite Hgetv in Hget'; inv Hget'.
      rewrite Hget in Hgetl3; inv Hgetl3.
      rewrite Hgetl2 in Hgetl4; inv Hgetl4.
      rewrite <- res_approx_fuel_eq. eassumption.
    - edestruct Heqn2 as [v2 [Hgetv Hv]]; eauto.
      destruct v2; try contradiction. destruct Hv as [HBeq Hlt']; subst. 
      destruct (Hlt' n x1) as [[l3' [l4' [Hgetl3 [Hgetl4 Hres]]]] | [Hn1 Hn2]]; eauto;
      try congruence.
      omega. rewrite Hgetv in Hget1'; inv Hget1'.
      rewrite Hget in Hgetl4; inv Hgetl4.
      rewrite Hgetl2 in Hgetl3; inv Hgetl3.
      rewrite <- res_approx_fuel_eq. eassumption.
  Qed.

  Corollary heap_env_equiv_Vfun S rho rho' rho1 rho2 H H' l l' f B :
    M.get f rho = Some l ->
    M.get f rho' = Some l' ->
    (l, H) ≈ (l', H') ->
    S |- (H, rho) ⩪ (H', rho') ->
    f \in S ->
    get l H = Some (Vfun rho1 B) ->
    get l' H' = Some (Vfun rho2 B) ->
    (occurs_free_fundefs B) |- (H, rho1) ⩪ (H', rho2).
  Proof.
    intros. split.
    now eapply (heap_env_approx_Vfun _ rho rho' _ _ H H'); eauto.
    now eapply (heap_env_approx_Vfun _ rho' rho _ _ H' H); eauto; symmetry.
  Qed.

 End HeapDefs.
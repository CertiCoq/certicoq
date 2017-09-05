(* Heap definitions for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps cps_util eval List_util Ensembles_util functions
        identifiers Heap.heap.
Require Import compcert.lib.Coqlib.


Open Scope Ensembles_scope.

Module HeapDefs (H : Heap).
  
  Import H.

  (** * Heap definitions *)

  (** A value is a location plus or a location paired with a function pointer offset *)
  Inductive value : Type :=
  (* Just a location *)
  | Loc : loc -> value
  (* A location (that should point to a function pointer) plus an offset *)
  | FunPtr : loc -> var -> value.
  
  Definition env : Type := M.t value.
  
  (** A block in the heap *)
  Inductive block :=
  (* Constructed value *)
  | Vconstr : cTag -> list value -> block
  (* Function pointer *)
  | Vfun : env -> fundefs -> block.


  Definition res : Type := value * heap block.

(*

  (** Definitions for unboxed function pointers *)
  (* This solution is not that different from the one above. In essence the only
     difference is that the one above introduces an extra level of indirection *)

  Inductive value A : Type :=
  | Loc : loc -> value A
  | FunPtr : A -> fundefs -> var -> value A.
  
  (* Environment. Constructed values are boxed, function pointers are unboxed *)
  CoInductive environment : Type :=
  | Env : M.t (value environment) -> environment.

  Definition val := value environment.

  (** The result of the evaluation *)
  Definition res := (val * heap val)%type.

*)

  (** Approximation of results with fuel *)
  Fixpoint res_approx_fuel (n : nat) (r1 r2 : res) : Prop :=
    let '(v1, H1) := r1 in
    let '(v2, H2) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        forall c vs1,
          get l1 H1 = Some (Vconstr c vs1) ->
          exists vs2, 
            get l2 H2 = Some (Vconstr c vs2) /\
            forall i, (i < n)%nat ->
                 match n with
                   | 0%nat => True
                   | S n' =>
                     Forall2
                       (fun l1 l2 => res_approx_fuel (n'-(n'-i)) (l1, H1) (l2, H2)) vs1 vs2
                 end
      | FunPtr l1 off1, FunPtr l2 off2 =>
        off1 = off2 /\
        forall rho1 B,
          get l1 H1 = Some (Vfun rho1 B) ->
          exists rho2, get l2 H2 = Some (Vfun rho2 B) /\
                  (forall i, (i < n)%nat ->
                        match n with
                          | 0%nat => True
                          | S n' =>
                            forall x, x \in (occurs_free_fundefs B) ->
                                       (exists v1 v2, M.get x rho1 = Some v1 /\
                                                 M.get x rho2 = Some v2 /\
                                                 res_approx_fuel (n'-(n'-i)) (v1, H1) (v2, H2)) \/
                                       (M.get x rho1 = None /\ M.get x rho2 = None)
                        end)
      | _, _ => False
    end.



  (** Equivalent definition, unfolding the recursion *)
  Definition res_approx_fuel' (n : nat) (r1 r2 : res) : Prop :=
    let '(v1, H1) := r1 in
    let '(v2, H2) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        forall c vs1,
          get l1 H1 = Some (Vconstr c vs1) ->
          exists vs2, 
            get l2 H2 = Some (Vconstr c vs2) /\
            forall i, (i < n)%nat ->
                 Forall2 (fun v1 v2 => res_approx_fuel i (v1, H1) (v2, H2)) vs1 vs2
      | FunPtr l1 off1, FunPtr l2 off2 =>
        off1 = off2 /\
        forall rho1 B,
          get l1 H1 = Some (Vfun rho1 B) ->
          exists rho2, get l2 H2 = Some (Vfun rho2 B) /\
                  forall i x, (i < n)%nat -> 
                         x \in (occurs_free_fundefs B) ->
                               (exists v1 v2, M.get x rho1 = Some v1 /\
                                         M.get x rho2 = Some v2 /\
                                         res_approx_fuel i (v1, H1) (v2, H2)) \/
                               (M.get x rho1 = None /\ M.get x rho2 = None)
      | _, _ => False
    end.
  
  (** Equivalence of the two definitions *)
  Lemma res_approx_fuel_eq n r1 r2 :
    res_approx_fuel n r1 r2 <-> res_approx_fuel' n r1 r2.
  Proof.
    destruct n; destruct r1 as [[l1 | l1 o1] H1]; destruct r2 as [[l2 | l2 o2] H2]; simpl; try now eauto.
    - split.
      + intros H c vs1 Hget. destruct (H c vs1 Hget) as [vs2 [Hget' _]].
        eexists; split; eauto. intros; omega.
      + intros H c vs1 Hget. destruct (H c vs1 Hget) as [vs2 [Hget' _]].
        eexists; split; eauto.
    - split.
      + intros [Heq Hb]. subst; split; [ reflexivity |].
        intros rho1 B Hget. destruct (Hb rho1 B Hget) as [rho2 [Hget' _]].
        eexists; split; eauto. intros; omega.
      + intros [Heq Hb]. subst; split; [ reflexivity |].
        intros rho1 B Hget. destruct (Hb rho1 B Hget) as [rho2 [Hget' _]].
        eexists; split; eauto.
    - split.
      + intros H c vs1 Hget. destruct (H c vs1 Hget) as [vs2 [Hget' Hall]].
        eexists; split; eauto. intros i Hlt.
        assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite Heq.
        eauto.
      + intros H c vs1 Hget. destruct (H c vs1 Hget) as [vs2 [Hget' Hall]].
        eexists; split; eauto. intros i Hlt.
        assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite <- Heq.
        eauto.
    - split.
      + intros [Heq Hb]. subst; split; [ reflexivity |].
        intros rho1 B Hget. destruct (Hb rho1 B Hget) as [rho2 [Hget' HB]].
        eexists; split; eauto. intros i x Hlt.
        assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite Heq.
        eauto.
      + intros [Heq Hb]. subst; split; [ reflexivity |].
        intros rho1 B Hget. destruct (Hb rho1 B Hget) as [rho2 [Hget' HB]].
        eexists; split; eauto. intros i x Hlt.
        assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite <- Heq.
        eauto.
  Qed.

  Opaque res_approx_fuel.

  (** Result equivalence. Two results represent the exact same value *)
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

  (** Location of a value *)
  Definition val_loc (v : value) : loc :=
    match v with
      | Loc l => l
      | FunPtr l _ => l
    end.
  
  (** The image of the environment *)
  Definition env_locs (rho : env) S : Ensemble loc :=
    image' (fun x => match M.get x rho with
                    | Some v => Some (val_loc v)
                    | None => None
                  end) S.
  
  (** Size of heap blocks *)
  Definition size_val (v : block) : nat :=
    match v with
      | Vconstr t ls => (* The size of the constructor representation *)
        1 + length ls
      | Vfun rho B => 1 (* Constant size for function definitions -- just a function pointer *) 
    end.
  
  (** Size of the heap *)
  Definition size_heap (H : heap block) : nat :=
    size_with_measure size_val H.
  
  (** The locations that appear on a block *)
  Definition locs (v : block) : Ensemble loc :=
    match v with
      | Vconstr t ls => FromList (map val_loc ls)
      | Vfun rho B =>
        (* Take only the relevant part of the environment instead
           of its whole codomain *)
        env_locs rho (occurs_free_fundefs B)
    end.

  (** The location that are pointed by the locations in S *)
  Definition post (H : heap block) (S : Ensemble loc) :=
    [ set l : loc | exists l' v, l' \in S /\ get l' H = Some v /\ l \in locs v].  
  
  Close Scope Z_scope.

  (** Least fixed point *)
  Definition lfp {A} (f : Ensemble A -> Ensemble A) :=
    \bigcup_( n : nat ) ((f ^ n) (Empty_set A)).
  
  (** Least fixed point characterization of heap reachability. *)
  Definition reach (H : heap block) (Si : Ensemble loc) : Ensemble loc :=
    lfp (fun S => Union _ Si (post H S)).
  
  (** Alternative characterization of heap reachability. *)
  Definition reach' (H : heap block) (Si : Ensemble loc) : Ensemble loc :=
    \bigcup_( n : nat ) (((post H) ^ n) (Si)).
  
  (* The to definitions should be equivalent. TODO: Do the proof *)
  Lemma reach_equiv H Si :
    reach H Si <--> reach' H Si.
  Proof.
  Abort.
  
  (** A heap is well-formed if there are not dangling pointers in the stored values *)
  Definition well_formed (S : Ensemble loc) (H : heap block) :=
    forall l v, l \in S -> get l H = Some v -> locs v \subset dom H.
  
  (** Well-formedness lifted to the environments. NOT USED *)
  Definition well_formed_env (S: Ensemble var) (H : heap block) (rho : env):=
    forall x v,
      x \in S -> M.get x rho = Some v -> (val_loc v) \in dom H.
  
  (** A heap is closed in S if the locations of its image on S remain in S *)
  Definition closed (S : Ensemble loc) (H : heap block) : Prop :=
    forall l, l \in S -> exists v, get l H = Some v /\ locs v \subset S.

  
  (** Using S as the set of roots, garbage collect H1 *) 
  Definition collect (S : Ensemble loc) (H1 H2 : heap block) : Prop :=
    (* H2 is a subheap of H1 *)
    H2 ⊑ H1 /\
    (* the domain of H2 includes everything that is reachable *)
    (reach' H1 S :&: dom H1) \subset dom H2.  
  
  (** [live S H1 H2] iff H2 is the live portion of H1, using S as roots *)
  Definition live (S : Ensemble loc) (H1 H2 : heap block) : Prop :=
    H2 ⊑ H1 /\
    dom H2 <--> (reach' H1 S :&: dom H1).

  (** The size of the reachable portion of the heap *)
  Definition size_reach (H : heap block) (S : Ensemble loc) (n : nat) : Prop :=
    forall H', live S H H' -> size_heap H' = n. 

  (** Add a block of function definitions in the environment *)
  Fixpoint def_funs (B : fundefs) (l : loc) (rho : env) {struct B}
  : env :=
    match B with
      | Fcons f _ _ _ B' =>
        M.set f (FunPtr l f) (def_funs B' l rho)
      | Fnil => rho
    end.
  
  (** * Lemmas about [collect] *)
  
  (** The reachable part of the heap before and after collection are the same *)
  Lemma collect_heap_eq S H1 H2 :
    collect S H1 H2 ->
    (reach' H1 S) |- H1 ≡ H2.
  Proof.
    intros [Hc1 Hc2] l Hin.
    destruct (get l H1) eqn:Hget.
    edestruct Hc2 as [v2 Hget2].
    - constructor; eauto. firstorder.
    - specialize (Hc1 _ _ Hget2). congruence.
    - destruct (get l H2) eqn:Hget2; eauto.
      specialize (Hc1 _ _ Hget2). congruence.
  Qed.
  
 
  (** * Lemmas about [post] and [reach'] *)


  (** Set monotonicity lemmas *)
  
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

  (** Heap monotonicity lemmas *)

  Lemma post_n_heap_monotonic n (H1 H2 : heap block) (S : Ensemble loc) :
    H1 ⊑ H2 -> (post H1 ^ n) S \subset (post H2 ^ n) S.
  Proof.
    induction n; simpl; eauto with Ensembles_DB.
    intros Hsub. eapply Included_trans.
    eapply post_set_monotonic. now eauto.
    now eapply post_heap_monotonic.
  Qed.
  
  Lemma reach'_heap_monotonic (H1 H2 : heap block) (S : Ensemble loc) :
    H1 ⊑ H2 -> reach' H1 S \subset reach' H2 S.
  Proof.
    intros Hsub l [n [HT Hp]]. exists n; split; eauto.
    eapply post_n_heap_monotonic; eauto.
  Qed.

  (** [reach'] is extensive *)
  Lemma reach'_extensive H S :
    S \subset reach' H S.
  Proof.
    intros x Hin. exists 0; split; eauto.
    now constructor.
  Qed.

  (** [reach'] includes [post] *)
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

  (* Lemma reach'_env_set S H v rho x : *)
  (*   val_loc v \in reach' H (env_locs rho (S \\ [set x])) -> *)
  (*   reach' H (env_locs rho (S \\ [set x])) <--> *)
  (*   reach' H (env_locs (M.set x v rho) S). *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   intros Hin. *)
  (* Abort. *)

  (* TODO better name for this? *)
  Lemma reach_spec H S S' :
    S \subset S' ->
    S' \subset reach' H S ->
    reach' H S <--> reach' H S'.
  Proof.
    intros Hsub1 Hsub2. split.
    - eapply reach'_set_monotonic. eassumption.
    - rewrite (reach'_idempotent H S).
      apply reach'_set_monotonic. eassumption.
  Qed.
  

  (** Proper instances and the like *)

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
  
  (** Union lemmas *)

  Lemma post_Union H S1 S2 :
    post H (Union _ S1 S2) <--> Union _ (post H S1) (post H S2).
  Proof with now eauto with Ensembles_DB.
    split; intros l Hp.
    - destruct Hp as [l' [v [Hin [Hget Hin']]]].
      inv Hin; [left | right ]; repeat eexists; eauto.
    - destruct Hp as [ Hp | Hp ];
      eapply post_set_monotonic; eauto...
  Qed.

  Lemma post_Singleton (H1 : heap block) (l : loc) (b : block) :
    get l H1 = Some b ->
    post H1 [set l] <--> locs b.
  Proof.
    intros Hget; split; intros l1.
    - intros [l2 [b2 [Hin [Hget' Hin']]]]. inv Hin.
      rewrite Hget in Hget'. inv Hget'; eauto.
    - intros Hin. repeat eexists; eassumption.
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

  (** Disjointedness lemmas *)

  Lemma post_Disjoint S H :
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
     rewrite post_Disjoint; eauto. reflexivity.
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

  (** allocation lemmas *)
   
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

  Lemma post_alloc' H v l H'  :
    alloc v H = (l, H') ->
    post H' [set l] \subset locs v.
  Proof.
    intros Ha l' Hp.
    destruct Hp as [l2 [v' [Hin2 [Hget Hin1]]]].
    inv Hin2.
    repeat eexists; eauto. erewrite gas in Hget; eauto.
    inv Hget. eauto.
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

  (** TODO implement BFS in the heap to find reachable locs *)
  Lemma Decidable_reach' (S : Ensemble loc) (H : heap block) :
    Decidable S ->
    Decidable (reach' H S).
  Admitted.

  (** * Lemmas about [env_locs] *)

  (** Set monotonicity *)
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

  (** Environment extension lemmas *)
  
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
  
  Lemma env_locs_set_In S rho x v :
    x \in S ->
    env_locs (M.set x v rho) S <-->
    Union _ [set (val_loc v)] (env_locs rho (Setminus _ S [set x])).
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
  
  Lemma env_locs_set_Inlcuded S rho x v :
    env_locs (M.set x v rho) (Union _ S [set x]) \subset
    Union _ [set (val_loc v)] (env_locs rho S).
  Proof.
    intros l' H1.
    - destruct H1 as [z [H1 H2]].
      destruct (peq z x); subst.
      + rewrite M.gss in *. inv H2; eauto.
      + rewrite M.gso in *; eauto. right. eexists; split; eauto.
        inv H1; eauto. inv H; congruence.
   Qed.
  
  Lemma env_locs_set_Inlcuded' S rho x v :
    env_locs (M.set x v rho) S \subset
    Union _ [set (val_loc v)] (env_locs rho (Setminus _ S [set x])).
  Proof.
    intros l' H1.
    - destruct H1 as [z [H1 H2]].
      destruct (peq z x); subst.
      + rewrite M.gss in *. inv H2; eauto.
      + rewrite M.gso in *; eauto. right. eexists; split; eauto.
        constructor; eauto. intros Heq. inv Heq; congruence. 
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
  
  Lemma env_locs_setlist_Included ys ls rho rho' S :
    setlist ys ls rho = Some rho'  ->
    env_locs rho'
             (Union M.elt S (FromList ys)) \subset
    Union _ (env_locs rho S) (FromList (map val_loc ls)).
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

  Lemma val_dec (v1 v2 : value): {v1 = v2} + {v1 <> v2}.
    decide equality.
    now apply loc_dec.
    now apply var_dec.
    now apply loc_dec.
  Qed.

  Lemma Decidable_env_locs rho S :
    Decidable S ->
    Decidable (env_locs rho S).
  Proof.
    intros HD. unfold env_locs, image'.
    inv HD. constructor.
    assert (forall l : loc,
              (exists (x : M.elt) v, In M.elt S x /\
                                val_loc v = l /\
                                List.In (x, v) (M.elements rho)) \/
              ~ (exists (x : M.elt) v, In M.elt S x /\
                                  val_loc v = l /\
                                  List.In (x, v) (M.elements rho))).
    { generalize (M.elements rho) as el.
      induction el as [| [x v] el IHel]; simpl; intros l1.
      - right. firstorder.
      - destruct (Dec x).
        + destruct (loc_dec (val_loc v) l1); subst.
          * left. do 2 eexists; repeat split; eauto.
          * destruct (IHel l1) as [[x2 [v2 [H1 [H2 H3]]]] | H2].
            left. now do 2 eexists; repeat split; eauto.
            right. intros [x2 [v2 [Hc1 [Hc2 Hc3]]]]. inv Hc3; try congruence.
            now eapply H2; eauto.
        + destruct (IHel l1) as [[x2 [v2 [H1 [H2 H3]]]] | H2].
          left. now do 2 eexists; repeat split; eauto.
          right. intros [x2 [v2 [Hc1 [Hc2 Hc3]]]]. inv Hc3.
          inv H0; try contradiction.
          now eapply H2; eauto. }
    intros l. destruct (H l) as [[x [v [Hl1 [Hl2 Hl3]]]] | Hr].
    - left. eexists; split; eauto. eapply M.elements_complete in Hl3.
      rewrite Hl3. congruence.
    - right. intros [x [H1 H2]].
      destruct (M.get x rho) eqn:Hget; try congruence. inv H2.
      eapply Hr; do 2 eexists; repeat split; eauto.
      eapply M.elements_correct; eassumption.
  Qed.
  
  (* Set lemmas *)
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

  Lemma env_locs_Empty S :
    Empty_set _ <--> env_locs (M.empty _) S.
  Proof.
    split; eauto with Ensembles_DB.
    intros l [v [Hs Hp]]. rewrite M.gempty in Hp.
    discriminate.
  Qed.

  Lemma env_locs_Singleton x rho v :
    M.get x rho = Some v ->
    env_locs rho [set x] <--> [set (val_loc v)].
  Proof.
    intros Hget; split; intros l.
    - intros [y [Hin Hget']]. inv Hin.
      rewrite Hget in Hget'. inv Hget'; eauto.
    - intros Hin; inv Hin. eexists; split.
      reflexivity. rewrite Hget; eauto.
  Qed.

  (* TODO change name *)
  Lemma env_locs_singleton (x : var) (v : value) :
    [set (val_loc v)] <--> env_locs (M.set x v (M.empty _)) [set x].
  Proof.
    rewrite env_locs_set_In; eauto with Ensembles_DB.
    rewrite <- env_locs_Empty; eauto with Ensembles_DB.
  Qed.
  
  Lemma env_locs_singleton_Included (x : var) (v : value) (rho : env)
        (S : Ensemble var):
    [set (val_loc v)] \subset env_locs (M.set x v rho) (Union _ S [set x]).
  Proof.
    rewrite env_locs_set_In; eauto with Ensembles_DB.
  Qed.

  Lemma env_locs_Empty_set (rho : env) :
    env_locs rho (Empty_set _) <--> Empty_set _.
  Proof.
    unfold env_locs. rewrite image'_Empty_set.
    reflexivity.
  Qed.

  Lemma env_locs_FromList (rho : env) (xs : list var) (vs : list value) :
    getlist xs rho = Some vs ->
    env_locs rho (FromList xs) <--> (FromList (map val_loc vs)).
  Proof.
    revert vs. induction xs; intros vs Hgetl; simpl in Hgetl.
    + inv Hgetl. simpl; rewrite !FromList_nil.
      rewrite env_locs_Empty_set. reflexivity.
    + destruct (M.get a rho) eqn:Hgeta; try discriminate.
      destruct (getlist xs rho) eqn:Hgetl'; try discriminate.
      inv Hgetl.
      simpl. rewrite !FromList_cons.
      rewrite env_locs_Union. eapply Same_set_Union_compat.
      eapply env_locs_Singleton. eassumption.
      eapply IHxs. reflexivity.
  Qed.

  (* Lemma reach_env_locs_alloc (S : Ensemble var) (H H' : heap block) (rho : env) *)
  (*       (x : var) (v : value) (b : block) : *)
  (*   alloc b H = (l, H') -> *)
  (*   locs v \subset (reach' H (env_locs rho S)) -> *)
  (*   reach' H' (env_locs (M.set x l rho) (Union _ S [set x])) \subset *)
  (*   Union _ [set (val_loc l)] (reach' H (env_locs rho S)). *)
  (* Proof. *)
  (*   intros Hal Hsub l1 Hr. *)
  (*   eapply reach'_set_monotonic in Hr; *)
  (*     [ | now eapply env_locs_set_Inlcuded ]. *)
  (*   rewrite reach'_Union in Hr. inv Hr. *)
  (*   - rewrite reach_unfold in H0. inv H0; eauto. *)
  (*     right. *)
  (*     eapply reach'_set_monotonic in H1; [| now eapply post_alloc'; eauto ]. *)
  (*     rewrite reach'_alloc in H1; try eassumption. *)
  (*     eapply reach'_set_monotonic in H1; [| eassumption ]. *)
  (*     now rewrite <- reach'_idempotent in H1. *)
  (*     eapply reach'_extensive. *)
  (*   - right. rewrite <- reach'_alloc; eauto. *)
  (* Qed. *)

  Lemma FromList_env_locs (S : Ensemble var) (rho : env)
        (xs : list var) (ls : list value) :
    getlist xs rho = Some ls ->
    FromList xs \subset S ->
    FromList (map val_loc ls) \subset env_locs rho S.
  Proof with now eauto with Ensembles_DB.
    revert ls; induction xs; intros ls Hget Hs; simpl in *.
    - inv Hget. rewrite FromList_nil...
    - destruct (M.get a rho) eqn:Hgeta; try discriminate.
      destruct (getlist xs rho) eqn:Hgetl; try discriminate.
      inv Hget. rewrite !FromList_cons in Hs. simpl.
      rewrite !FromList_cons.
      eapply Union_Included.
      + intros l' Hin. inv Hin. repeat eexists; eauto.
        rewrite Hgeta. reflexivity.
      + eapply IHxs; eauto.
        eapply Included_trans...
  Qed.
  
  (** * Lemmas about locs *)

  (* TODO move *)
  Instance Decidable_FromList A
           (H : forall (x y : A), {x = y} + {x <> y}) (l : list A) :
    Decidable (FromList l).
  Proof.
    constructor. intros x. induction l. 
    - right. intros H1. inv H1. 
    - destruct (H a x); subst.
      + left. constructor. eauto.
      + destruct IHl. left. now constructor 2.
        right. intros Hc. inv Hc; eauto.
  Qed.
  
  Instance Decidable_locs v : Decidable (locs v).
  Proof.
    constructor. intros l1.
    destruct v; simpl.
    - eapply (Decidable_FromList loc loc_dec). 
    - eapply Decidable_env_locs; typeclasses eauto.
  Qed.
  
  (** * Lemmas about [live] *)
  
  Lemma live_exists S H :
    Decidable S ->
    exists H', live S H H'.
  Proof.
  Admitted.

  Lemma live_heap_eq (S : Ensemble loc) (H1 H1' H2 : heap block) :
    reach' H1 S |- H1 ≡ H1' ->
    live S H1 H2 ->
    live S H1' H2.
  Proof.
    intros Heq [Hs Hl]. split.
    - intros l b Hget1. rewrite <- Heq.
      now edestruct Hs as [b' Hget']; eauto. 
      assert (Hin : l \in dom H2) by (eexists; eauto).
      eapply Hl in Hin. now inv Hin.
    - rewrite Hl. split; intros l Hin.
      + inv Hin. destruct H0 as [v1 Hget1].
        constructor. rewrite <- reach'_heap_eq; try eassumption.
        rewrite Heq in Hget1; eauto. eexists; eauto.
      + inv Hin. destruct H0 as [v1 Hget1].
        rewrite <- reach'_heap_eq in H; eauto.
        constructor; try eassumption.
        rewrite <- Heq in Hget1; eauto. eexists; eauto.
  Qed.

  Lemma live_collect S H1 H2 :
    live S H1 H2 ->
    collect S H1 H2.
  Proof.
    firstorder.
  Qed.

  Lemma live_idempotent (S : Ensemble loc) (H1 H2 : heap block) :
    live S H1 H2 ->
    live S H2 H2.
  Proof.
    intros Hl.
    assert (Hc := live_collect _ _ _ Hl).
    destruct Hl as [Hyp1 Hyp2]. split.
    now apply subheap_refl.
    split; intros l Hin.
    + constructor; eauto.
      rewrite <- reach'_heap_eq; [| eapply collect_heap_eq; eassumption ].
      eapply Hyp2 in Hin. now inv Hin.
    + now inv Hin.
  Qed.

  Instance Proper_live : Proper (Same_set _ ==> eq ==> eq ==> iff) live.
  Proof.
    constructor; subst; intros [Hl1 Hl2].
    split; eauto. now rewrite <- H.
    split; eauto. now rewrite H.
  Qed.

  (** * Lemmas about [reach_size] *)

  Lemma size_reach_heap_eq (S : Ensemble loc) (H1 H1' : heap block) (m : nat) :
    reach' H1 S |- H1 ≡ H1' ->
    size_reach H1 S m ->
    size_reach H1' S m.
  Proof.
    intros Heq Hs H2 Hl. eapply Hs.
    eapply live_heap_eq; eauto. rewrite <- reach'_heap_eq; eauto.
    now symmetry.
  Qed.
  
  (** * Lemmas about [closed] *)

  Lemma in_dom_closed (S : Ensemble loc) (H : heap block) :
    closed (reach' H S) H ->
    (reach' H S) \subset dom H.
  Proof. 
    intros Hc l1 Hr.
    edestruct Hc as [v2 [Hget' Hdom]]; eauto.
    repeat eexists; eauto.
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

  Lemma closed_alloc H H' l v :
    closed (dom H) H ->
    locs v \subset dom H ->
    alloc v H = (l, H') ->
    closed (dom H') H'.
  Proof with now eauto with Ensembles_DB.
    intros Hcl Hin Ha l1 Hin'.
    destruct (loc_dec l1 l); subst.
    - eexists. erewrite gas; eauto.
      split. reflexivity.
      eapply Included_trans. eassumption.
      rewrite (alloc_dom _ _ _ _ Ha)...
    - rewrite (alloc_dom _ _ _ _ Ha) in Hin'.
      inv Hin'. inv H0. congruence.
      edestruct Hcl as [l2 [Hget Hsub]]; try eassumption.
      eexists. erewrite gao; eauto; split; eauto.
      eapply Included_trans. eassumption.
      rewrite (alloc_dom _ _ _ _ Ha)...
  Qed.

  Instance Proper_closed : Proper (Same_set _ ==> eq ==> iff) closed.
  Proof.
    intros S1 S2 Heq x1 x2 Heq'; split; intros Hc x Hin; eapply Heq in Hin;
    subst; eauto.
    - setoid_rewrite <- Heq; eauto.
    - setoid_rewrite Heq; eauto.
  Qed.

  Lemma closed_Union (S1 S2 : Ensemble loc) (H : heap block) :
    closed S1 H ->
    closed S2 H ->
    closed (Union _ S1 S2) H.
  Proof with now eauto with Ensembles_DB.
    intros Hc1 Hc2 l Hin.
    inv Hin.
    - edestruct Hc1 as [c [Hget Hinv]]; eauto.
      eexists; split; eauto...
    - edestruct Hc2 as [c [Hget Hinv]]; eauto.
      eexists; split; eauto...
  Qed.

  (** * Lemmas about [well_formed] and [well_formed_env] *)
  
  (** Monotonicity lemmas *)

  Lemma well_formed_antimon S1 S2 H :
    S1 \subset S2 ->
    well_formed S2 H ->
    well_formed S1 H.
  Proof.
    firstorder.
  Qed.

  Lemma well_formed_env_antimon S1 S2 H rho :
    well_formed_env S1 H rho ->
    S2 \subset S1 ->
    well_formed_env S2 H rho.
  Proof.
    firstorder.
  Qed.

  Lemma well_formed'_closed (S : Ensemble loc) (H : heap block) :
    closed (reach' H S) H ->
    well_formed (reach' H S) H.
  Proof. 
    intros Hc l1 v1 Hin Hget.
    edestruct Hc as [v2 [Hget' Hdom]]; eauto.
    rewrite Hget in Hget'. inv Hget'.
    eapply Included_trans. eassumption.
    eapply in_dom_closed; eauto.
  Qed.

  (** Proper instances *)

  Instance Proper_well_formed : Proper (Same_set _ ==> eq ==> iff) well_formed.
  Proof.
    intros s1 s2 hseq H1 h2 Heq; subst. firstorder.
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

  (** Set lemmas *)

  Lemma well_formed_Union S1 S2 H :
    well_formed S1 H ->
    well_formed S2 H ->
    well_formed (Union _ S1 S2) H.
  Proof.
    intros Hwf1 Hwf2 l v Hin Hget; inv Hin; eauto.
  Qed.
  
  Lemma well_formed_Empty_set H:
    well_formed (Empty_set _) H.
  Proof.
    firstorder.
  Qed.
  
  (** Reachable locations are in the domain of the heap *)
  Lemma reachable_in_dom H S :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    reach' H S \subset dom H.
  Proof.
    intros H1 Hs l [n [_ Hr]]. destruct n; eauto.
    simpl in Hr. destruct Hr as [l' [v' [Hin [Hget Hin']]]].
    eapply H1; eauto. eexists; split; eauto. now constructor; eauto.
  Qed.

  (** The heap is closed in the set of the reachable locations *)
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
  
  
  Lemma getlist_in_dom (S : Ensemble var) (H : heap block) (rho : env)
        (ys : list var) (vs : list value) :
    well_formed_env S H rho ->
    getlist ys rho = Some vs ->
    FromList ys \subset S ->
    FromList (map val_loc vs) \subset dom H. 
  Proof.
    revert vs; induction ys; intros ls Hwf Hget Hin; destruct ls; simpl in *; try discriminate.
    - now eauto with Ensembles_DB.
    - now eauto with Ensembles_DB.
    - rewrite !FromList_cons in Hin. rewrite FromList_cons.
      destruct (M.get a rho) eqn:Hgeta; try discriminate.
      destruct (getlist ys rho) eqn:Hgetys; try discriminate.
      inv Hget. eapply Union_Included.
      eapply Singleton_Included. eapply Hwf; eauto. 
      eapply IHys; eauto. eapply Included_trans; now eauto with Ensembles_DB.
  Qed.

  (** Well-formedness preservation under enviroment and heap extensions *)

  (** Allocation lemmas *)

  Lemma closed_set_alloc_alt S H H' b v rho x :
    closed (reach' H (env_locs rho (S \\ [set x]))) H ->
    locs b \subset (reach' H (env_locs rho (S \\ [set x]))) ->
    alloc b H = (val_loc v, H') ->
    closed (reach' H' (env_locs (M.set x v rho) S)) H'.
  Proof with now eauto with Ensembles_DB.
    intros Hcl Hin Ha l1 Hin'.
    destruct (loc_dec l1 (val_loc v)); subst.
    - eexists. erewrite gas; eauto.
      split. reflexivity.
      eapply Included_trans. eassumption.
      eapply Included_trans.
      eapply reach'_heap_monotonic.
      now eapply alloc_subheap; eauto.
      eapply reach'_set_monotonic.
      rewrite <- env_locs_set_not_In.
      eapply env_locs_monotonic...
      intros Hinx. now inv Hinx; eauto.
    - eapply reach'_set_monotonic in Hin';
      [| now eapply env_locs_set_Inlcuded'].
      rewrite reach'_Union in Hin'.
      rewrite reach_unfold in Hin'.
      rewrite post_Singleton in Hin'; [| now erewrite gas; eauto ].
      inv Hin'.
      + inv H0.
        * inv H1. congruence.
        * edestruct Hcl as [b1 [Hget1 Hsub]]; eauto.
          rewrite <- reach'_alloc; try eassumption.
          rewrite reach'_idempotent.
          eapply reach'_set_monotonic; [| eassumption ].
          eapply Included_trans. eassumption.
          eapply reach'_heap_monotonic.
          eapply alloc_subheap. eassumption.
          eexists; split; eauto.
          
          now erewrite gao; eauto.
          
          eapply Included_trans. eassumption.
          eapply Included_trans. eapply reach'_heap_monotonic.
          eapply alloc_subheap. eassumption.
          eapply reach'_set_monotonic. 
          rewrite <- env_locs_set_not_In.
          eapply env_locs_monotonic...
          intros Hc. inv Hc; eauto.            
      + edestruct Hcl as [b1 [Hget1 Hsub]]; eauto.
        rewrite <- reach'_alloc; try eassumption.
        eexists.
        erewrite gao; eauto; split; eauto.
        eapply Included_trans. eassumption.
        eapply Included_trans. eapply reach'_heap_monotonic.
        eapply alloc_subheap. eassumption.
        eapply reach'_set_monotonic. 
        rewrite <- env_locs_set_not_In.
        eapply env_locs_monotonic...
        intros Hc. inv Hc; eauto.
  Qed.
  
  Lemma well_formed_alloc (S : Ensemble loc) (H H' : heap block)
             (b : block) (l : loc) :
    well_formed S H ->
    alloc b H = (l, H') ->
    locs b \subset dom H ->
    well_formed S H'.
  Proof with now eauto with Ensembles_DB.
    intros Hwf ha Hsub l' v' Sin Hget. destruct (loc_dec l l'); subst.
    - erewrite gas in Hget; eauto. inv Hget.
      eapply Included_trans. eassumption.
      rewrite (alloc_dom H _ _ _ ha)...
    - erewrite gao in Hget; eauto.
      eapply Included_trans. now eauto.
      rewrite (alloc_dom H _ _ _ ha)...
  Qed.

  Lemma well_formed_env_alloc_extend (S : Ensemble var) (H H' : heap block)
             (rho : env) (x : var) (b : block) (v : value) :
    well_formed_env (Setminus _ S (Singleton _ x)) H rho ->
    alloc b H = (val_loc v, H') ->
    locs b \subset (dom H) ->
    well_formed_env S H' (M.set x v rho).
  Proof with now eauto with Ensembles_DB.
    intros Hwf Ha Hsub x' v' Hin Hget. destruct (peq x x'); subst.
    - rewrite M.gss in Hget. inv Hget.
      eexists. eapply gas. eauto.
    - rewrite M.gso in Hget; eauto.
      rewrite (alloc_dom H _ _ _ Ha).
      right. eapply Hwf; eauto.
      constructor; eauto. intros Hc; inv Hc; congruence.
  Qed.  
  
  Lemma well_formed_reach_alloc (S : Ensemble var) (H H' : heap block)
        (rho : env) (x : var) (b : block) (v : value) :
    well_formed (reach' H (env_locs rho S)) H ->
    env_locs rho S \subset dom H ->
    alloc b H = (val_loc v, H') ->
    locs b \subset (reach' H (env_locs rho S)) ->
    well_formed (reach' H' (env_locs (M.set x v rho) (Union _ S [set x]))) H'.
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

  Lemma well_formed_reach_set (S : Ensemble var) (H : heap block) (rho : env)
        (x : var) (v : value) :
    well_formed (reach' H (env_locs rho S)) H ->
    well_formed (reach' H [set (val_loc v)]) H ->
    well_formed (reach' H (env_locs (M.set x v rho) (Union _ S [set x]))) H.
  Proof with now eauto with Ensembles_DB.
    intros Hwf  Hin.
    eapply well_formed_antimon.
    eapply reach'_set_monotonic. now eapply env_locs_set_Inlcuded.
    rewrite reach'_Union. eapply well_formed_Union; eauto.
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

  Lemma well_formed_reach_setlist  (S : Ensemble M.elt) (H : heap block) 
        (rho rho' : env)  (xs : list M.elt) (vs : list value) :
    well_formed (reach' H (env_locs rho S)) H ->
    well_formed (reach' H (FromList (map val_loc vs))) H ->
    setlist xs vs rho = Some rho' -> 
    well_formed
      (reach' H (env_locs rho' (Union M.elt S (FromList xs)))) H.
  Proof.
    revert rho' vs. induction xs; intros rho' ls Hwf1 Hwf2 Hsetl.
    - destruct ls; try discriminate. inv Hsetl.
      rewrite FromList_nil, Union_Empty_set_neut_r. eassumption.
    - simpl. rewrite FromList_cons in *.
      simpl in Hsetl. destruct ls; try discriminate.
      destruct (setlist _ _ _) eqn:Hsetl'; try discriminate.
      inv Hsetl. rewrite (Union_commut [set a]), Union_assoc.
      eapply well_formed_reach_set.
      + eapply IHxs. eassumption.
        eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic.
        intros x Hin. eapply FromList_cons. right. eassumption.
        eassumption.
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. simpl. rewrite FromList_cons.
        now eauto with Ensembles_DB.
  Qed.

  Lemma well_formed_reach_setlist_cor  (S : Ensemble M.elt) (H : heap block) 
        (rho rho' : env) (xs : list M.elt) (vs : list value) :
    well_formed (reach' H (env_locs rho S)) H ->
    FromList (map val_loc vs) \subset (reach' H (env_locs rho S)) ->
    setlist xs vs rho = Some rho' -> 
    well_formed
      (reach' H (env_locs rho' (Union M.elt S (FromList xs)))) H.
  Proof.
    intros. eapply well_formed_reach_setlist; [ eassumption | | eassumption ].
    eapply well_formed_antimon.
    eapply reach'_set_monotonic. eassumption.
    rewrite <- reach'_idempotent. eassumption.
  Qed.   

  (* TODO move? *)
  Lemma closed_set_alloc S H H' b v rho x :
    closed (reach' H (locs b :|: (env_locs rho (S \\ [set x])))) H ->
    alloc b H = (val_loc v, H') ->
    closed (reach' H' (env_locs (M.set x v rho) S)) H'.
  Proof with now eauto with Ensembles_DB.
    intros Hcl Ha.
    eapply reach'_closed.
    - eapply well_formed_antimon.
      eapply reach'_set_monotonic. eapply env_locs_monotonic.
      eapply Included_Union_Setminus with (s2 := [set x]); typeclasses eauto.
      rewrite env_locs_Union.
      rewrite env_locs_set_not_In.
      + rewrite env_locs_Singleton; [| now rewrite M.gss ].
        rewrite reach'_Union. 
        rewrite (reach_unfold H' [set val_loc v]).
        rewrite post_Singleton; [| now erewrite gas; eauto ].
        rewrite Union_commut, <- Union_assoc.
        eapply well_formed_Union.
        * intros l1 b1 Hin Hget. inv Hin.
          erewrite gas in Hget; eauto. inv Hget.
          eapply Included_trans.
          eapply in_dom_closed in Hcl.
          eapply Included_trans; [| eassumption ].
          eapply Included_trans; [| eapply reach'_extensive ]...
          eapply dom_subheap. eapply alloc_subheap; now eauto.
        * rewrite <- reach'_Union.
          eapply well_formed_alloc; try eassumption.
          rewrite reach'_alloc; try eassumption.
          eapply well_formed'_closed in Hcl.
          eassumption.
          eapply Included_trans; [| now eapply reach'_extensive ]...
          eapply in_dom_closed in Hcl. eapply Included_trans; [| eassumption ].
          eapply Included_trans; [| now eapply reach'_extensive ]...
      + intros Hc. inv Hc; eauto.
    - eapply Included_trans. eapply env_locs_set_Inlcuded'.
      eapply Union_Included.
      + eapply Singleton_Included. eexists b.
        erewrite gas; eauto.
      + eapply Included_trans;
        [| eapply dom_subheap; eapply alloc_subheap; now eauto ].
        eapply in_dom_closed in Hcl.
        eapply Included_trans; [| eassumption ].
        eapply Included_trans; [| now eapply reach'_extensive ]...
  Qed.    

  (** * Lemmas about [res_approx] and [res_equiv] *)

  (** Preorder and equivalence properties of [res_approx] and [res_equiv] *)
  
  Lemma reach_res_approx (S : Ensemble loc) (H1 H2 : heap block)
        (v : value) (n : nat) :
    (reach' H1 S) |- H1 ≡ H2  ->
    (val_loc v) \in S -> 
    res_approx_fuel n (v, H1) (v, H2).
  Proof.
    intros Hsub Hin .
    assert (Hr : reach' H1 S <--> reach' H2 S).
    { eapply reach'_heap_eq. eauto. }
    revert H1 H2 S v Hr Hsub Hin.
    induction n using lt_wf_rec1; intros H1 H2 S v Hr Hsub Hin.
    destruct n; destruct v.
    - rewrite res_approx_fuel_eq. intros c vs Hget.
      rewrite Hsub in Hget. eexists; split; eauto. intros; omega.
      eapply reach'_extensive. eassumption.
    - rewrite res_approx_fuel_eq; split; [ reflexivity |]; intros rho B Hget.
      rewrite Hsub in Hget.
      eexists; split; eauto. intros; omega. now eapply reach'_extensive.
    - rewrite res_approx_fuel_eq. intros c vs Hget.
      assert (Hget1 := Hget).
      rewrite Hsub in Hget; [| now eapply reach'_extensive ].
      eexists; split; eauto. intros i Hlt.
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
      right. exists l. eexists. repeat split; eauto.
      unfold locs. rewrite FromList_map_image_FromList. eexists.
      split; eauto.
    - rewrite res_approx_fuel_eq; split; [ reflexivity |]; intros rho B Hget.
      assert (Hget1 := Hget).
      rewrite Hsub in Hget; [| now apply reach'_extensive ].
      eexists; split; eauto. intros i x Hlt Hin'.
      destruct (M.get x rho) eqn:Heq.
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
        exists x. split; eauto. rewrite Heq. reflexivity.
      * right; eauto.
  Qed.
  
  Corollary reach_res_equiv (S : Ensemble loc) (H1 H2 : heap block)
            (v : value) :
    (reach' H1 S) |- H1 ≡ H2 ->
    val_loc v \in S -> 
    (v, H1) ≈ (v, H2).
  Proof.
    intros Hsub Hin n; split; rewrite <- res_approx_fuel_eq;
    eapply reach_res_approx; eauto. rewrite <- reach'_heap_eq.
    symmetry. eassumption. eassumption.
  Qed.
  
  Lemma Preorder_res_equiv_fuel i : preorder res (res_approx_fuel i).
  Proof.
    constructor.
    - induction i as [i IHi] using lt_wf_rec.
      intros [v H1]. rewrite res_approx_fuel_eq. destruct v.
      + intros c vs Hget.
        eexists; split; eauto. intros i' Hlt.
        eapply Forall2_refl; intros l'. eapply IHi. eassumption.
      + split; [ reflexivity |]. intros rho1 B Hget.
        eexists; split; eauto. intros i' x Hlt Hin.
        destruct (M.get x rho1) eqn:heq; eauto.
        left. do 2 eexists; repeat split; eauto.
        eapply IHi; eauto.
    - induction i as [i IHi]  using lt_wf_rec1.
      intros [l1 H1] [l2 H2] [l3 H3] Hap1 Hap2. rewrite res_approx_fuel_eq in *.
      destruct l1; destruct l2; destruct l3; try contradiction.
      + intros c vs Hget. edestruct (Hap1 c vs Hget) as [vs2 [Hget2 Hall2]].
        edestruct (Hap2 c vs2 Hget2) as [vs3 [Hget3 Hall3]].
        eexists; split; eauto.
        intros i' Hlt.
        eapply Forall2_trans_strong; eauto. intros v1 v2 v3 Hv1 Hv2.
        eapply IHi. eassumption. simpl in Hv1. eassumption.
        simpl in Hv2. eassumption.
      + edestruct Hap1 as [Heq1 HB1]; edestruct Hap2 as [Heq2 HB2]; subst.
        split; eauto. intros rho1 B Hget.
        edestruct (HB1 rho1 B Hget) as [rho2 [Hget2 Hi2]].
        edestruct (HB2 rho2 B Hget2) as [rho3 [Hget3 Hi3]].
        eexists; split; eauto. intros i' x Hlt Hf.
        edestruct (Hi2 i' x Hlt Hf)
          as [[v1' [v2' [Hget1' [Hget2' Hres]]]] | [Hget1' Hget2']];
        edestruct (Hi3 i' x Hlt Hf)
          as [[v2'' [v3' [Hget2'' [Hget3' Hres']]]] | [Hget2'' Hget3']];
          try congruence.
        * left; repeat eexists; eauto.
          rewrite Hget2' in Hget2''. inv Hget2''.
          eapply IHi; eauto.
        * right; split; eauto.
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
  
  (** [heap_env_approx] and [heap_env_equiv] equivalence properties *)
  Lemma reach_approx (S : Ensemble var) (H1 H2 : heap block) (rho : env) : 
    (reach' H1 (env_locs rho S)) |- H1 ≡ H2 -> 
    heap_env_approx S (H2, rho) (H1, rho).
  Proof.
    intros Hreach x l Hin Hget. 
    exists l. split. eassumption.
    eapply reach_res_equiv. symmetry.
    rewrite <- reach'_heap_eq; eassumption.
    eexists. split; eauto. rewrite Hget.
    reflexivity.
  Qed.   

  Corollary reach_heap_env_equiv (S : Ensemble var) (H1 H2 : heap block)
            (rho : env) :
    (reach' H1 (env_locs rho S)) |- H1 ≡ H2 -> 
    S |- (H1, rho) ⩪ (H2, rho).
  Proof.
    intros. split; eapply reach_approx; simpl; try eassumption.
    symmetry. rewrite <- reach'_heap_eq; eassumption.
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
  
  (** Proper instances *)

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

  (** Monotonicity properties *)

  Lemma heap_env_equiv_antimon S1 S2 H1 H2 rho1 rho2 :
    S1 |- (H1, rho1) ⩪ (H2, rho2) ->
    S2 \subset S1 ->
    S2 |- (H1, rho1) ⩪ (H2, rho2).
  Proof.
    firstorder.
  Qed.

  (** Weakening lemmas *)
  
  Lemma res_approx_weakening (S1 S2 : Ensemble loc) (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) (i : nat) :
    closed S1 H1 -> closed S2 H2 ->
    res_approx_fuel' i (v1, H1) (v2, H2) ->
    H1 ⊑ H1' -> 
    H2 ⊑ H2' ->
    val_loc v1 \in S1 -> val_loc v2 \in S2 -> 
    res_approx_fuel' i (v1, H1') (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2.
    revert v1 v2 Heq; induction i using lt_wf_rec1;
    intros v1 v2 Heq Hdom1 Hdom2.
    destruct v1; destruct v2; try contradiction.
    - intros c v1 Hget1. edestruct (Hwf1 _ Hdom1) as [v1' [Hget1' Hsub1']].
      edestruct (Hwf2 _ Hdom2) as [v2' [Hget2' Hsub2']].
      specialize (Hsub1 _ _ Hget1'). simpl in Hsub1.
      rewrite Hsub1 in Hget1; inv Hget1.
      specialize (Hsub2 _ _ Hget2').
      edestruct Heq as [v2 [Hget2 Hm]]; eauto.
      simpl in Hget2'. rewrite Hget2 in Hget2'; inv Hget2'.
      eexists; split; [ now eauto |]. intros i' Hlt.
      eapply Forall2_monotonic_strong
      with (R :=
              fun l3 l4 =>
                val_loc l3 \in S1 ->
                val_loc l4 \in S2 -> res_approx_fuel i' (l3, H1) (l4, H2)).
      * intros l1' l2' Hin1 Hin2 Hyp.
        simpl in Hsub1'; rewrite FromList_map_image_FromList in Hsub1'.
        simpl in Hsub2'; rewrite FromList_map_image_FromList in Hsub2'.
        rewrite res_approx_fuel_eq. eapply H; eauto.
        rewrite <- res_approx_fuel_eq. eapply Hyp; eauto.
        eapply Hsub1'. now eexists; split; eauto.
        eapply Hsub2'. now eexists; split; eauto.
        eapply Hsub1'. now eexists; split; eauto.
        eapply Hsub2'. now eexists; split; eauto.
      * eapply Forall2_monotonic; [| eauto ].
        intros. eassumption.
    - simpl in Hdom1, Hdom2. destruct Heq as [Heq HB]; subst.
      split; [ reflexivity |]. intros rho1 B Hget.
      edestruct (Hwf1 _ Hdom1) as [v1' [Hget1' Hsub1']].
      edestruct (Hwf2 _ Hdom2) as [v2' [Hget2' Hsub2']].
      specialize (Hsub1 _ _ Hget1'). 
      rewrite Hsub1 in Hget; inv Hget.
      specialize (Hsub2 _ _ Hget2').
      edestruct (HB rho1 B Hget1') as [rho2 [Hget2 Hlt]].
      rewrite Hget2 in Hget2'; inv Hget2'.
      eexists; split; eauto. intros i' x Hlt' Hfv.
      specialize (Hlt i' x Hlt' Hfv).
      inversion Hlt as [[l3 [l4 [Hget3 [Hget4 Hres]]]] | H3']; eauto.
      left. exists l3, l4. split; [| split ]; eauto.
      rewrite res_approx_fuel_eq. eapply H; eauto.
      rewrite <- res_approx_fuel_eq. eassumption.
      eapply Hsub1'; eauto. eexists. split; eauto.
      rewrite Hget3; reflexivity.
      eapply Hsub2'; eauto. eexists. split; eauto.
      rewrite Hget4; reflexivity. 
  Qed.
  
  Corollary res_equiv_weakening (S1 S2 : Ensemble loc) (H1 H2 H1' H2' : heap block)
            (v1 v2 : value) :
    closed S1 H1 -> closed S2 H2 ->
    (v1, H1) ≈ (v2, H2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    val_loc v1 \in S1 -> val_loc v2 \in S2 -> 
    (v1, H1') ≈ (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2 Hin1 Hin2 n. destruct (Heq n) as [Heq1 He2].
    split. now eapply (res_approx_weakening S1 S2 H1 H2 H1' H2'); eauto.
    now eapply (res_approx_weakening S2 S1 H2 H1 H2' H1'); eauto.
  Qed.

  Lemma heap_env_approx_weakening S H1 H2 H1' H2' rho1 rho2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    well_formed (reach' H2 (env_locs rho2 S)) H2 ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2 ->
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    heap_env_approx S (H1', rho1) (H2', rho2).
  Proof.
    intros Hwf1 Hwf2 He1 He2  [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
    edestruct Heq1 as [x' [Hget' Heq']]; eauto.
    eexists; split; eauto.
    eapply (res_equiv_weakening _ _ H1 H2).
    eapply reach'_closed. now apply Hwf1. eassumption.
    eapply reach'_closed. now apply Hwf2. eassumption.
    eassumption. eassumption. eassumption.
    eapply reach'_extensive. eexists; split; eauto.
    rewrite Hget. reflexivity.
    eapply reach'_extensive. eexists; split; eauto.
    rewrite Hget'. reflexivity.
  Qed.
  
  Corollary heap_env_equiv_weaking_cor S H1 H2 H1' H2' rho1 rho2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    well_formed (reach' H2 (env_locs rho2 S)) H2 ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2 ->
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    S |- (H1', rho1) ⩪ (H2', rho2).
  Proof.
    intros. split.
    now eapply (heap_env_approx_weakening _ H1 H2); eauto.
    now eapply (heap_env_approx_weakening _ H2 H1); eauto; symmetry.
  Qed.

  Lemma heap_env_approx_weakening' S S1 S2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset S1 ->
     env_locs rho2 S \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     heap_env_approx S (H1', rho1) (H2', rho2).
   Proof.
     intros Hwf1 Hwf2 He1 He2  [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
     edestruct Heq1 as [x' [Hget' Heq']]; eauto.
     eexists; split; eauto.
     eapply (res_equiv_weakening _ _ H1 H2); eauto.
     eapply He1. eexists; split; eauto.
     rewrite Hget; reflexivity.
     eapply He2. eexists; split; eauto.
     rewrite Hget'; reflexivity.
   Qed.
   
   Corollary heap_env_equiv_weaking' S S1 S2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset S1 ->
     env_locs rho2 S \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     S |- (H1', rho1) ⩪ (H2', rho2).
   Proof.
     intros. split.
     now eapply (heap_env_approx_weakening' _ _ _ H1 H2); eauto.
     now eapply (heap_env_approx_weakening' _ _ _ H2 H1); eauto; symmetry.
   Qed.
  
  (** [heap_env_approx] and [heap_env_equiv] preservation under store and heap extension *)
   
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


  Lemma heap_env_equiv_setlist S H1 H2 xs ls1 ls2 rho1 rho2 rho1' rho2' :
    Setminus _ S (FromList xs) |- (H1, rho1) ⩪ (H2, rho2) ->
    setlist xs ls1 rho1 = Some rho1' -> setlist xs ls2 rho2 = Some rho2' ->
    Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) ls1 ls2  ->
    S |- (H1, rho1') ⩪ (H2, rho2').
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

  Lemma res_approx_fuel_offset_indep (H1 H2 : heap block) (l1 l2 : loc)
        (f f' : var) (i : nat) :
    res_approx_fuel i (FunPtr l1 f, H1) (FunPtr l2 f, H2) ->
    res_approx_fuel i (FunPtr l1 f', H1) (FunPtr l2 f', H2).
  Proof.
    rewrite !res_approx_fuel_eq. intros [_ H].
    split; eauto.
  Qed.

  Lemma res_equiv_fuel_offset_indep (H1 H2 : heap block) (l1 l2 : loc)
        (f f' : var) :
    (FunPtr l1 f, H1) ≈ (FunPtr l2 f, H2) ->
    (FunPtr l1 f', H1) ≈ (FunPtr l2 f', H2).
  Proof.
    intros Hyp n. destruct (Hyp n) as [Hyp1 Hyp2].
    split; rewrite <- !res_approx_fuel_eq in *;
    now eapply res_approx_fuel_offset_indep; eauto.
  Qed.

  Lemma heap_env_equiv_def_funs S H1 H2 rho1 rho2 B l1 l2 f :
    Setminus _ S (name_in_fundefs B) |- (H1, rho1) ⩪ (H2, rho2) ->
    (FunPtr l1 f, H1) ≈ (FunPtr l2 f, H2) ->
    S  |- (H1, def_funs B l1 rho1) ⩪ (H2, def_funs B l2 rho2).
  Proof with (now eauto with Ensembles_DB).
    revert S; induction B;
    intros S Heq Hreq.
    - simpl. eapply heap_env_equiv_set; eauto.
      eapply IHB; eauto. eapply heap_env_equiv_antimon; eauto.
      simpl. rewrite Setminus_Union... eapply res_equiv_fuel_offset_indep.
      eassumption.
    - simpl. rewrite Setminus_Empty_set_neut_r in Heq.
      eassumption.
  Qed.

    Lemma res_equiv_get_Vconstr (H1 H2 : heap block)
        (l1 l2 : loc) (c : cTag) (vs1 : list value) :
    (Loc l1, H1) ≈ (Loc l2, H2) ->
    get l1 H1 = Some (Vconstr c vs1) ->
    exists vs2,
      get l2 H2 = Some (Vconstr c vs2) /\
      Forall2 (fun v1 v2 => (v1, H1) ≈ (v2, H2)) vs1 vs2.
  Proof.
    intros Hres Hget. 
    assert (Hres1 := (Hres 1)). destruct Hres1 as [Hl Hr]. 
    specialize (Hl _ _ Hget). destruct Hl as [vs2 [Hget2 _]].
    eexists; split; eauto.
    eapply Forall2_forall.
    constructor. exact 0.
    intros k.
    destruct (Hres (k + 1)) as [Hl' Hr'].
    edestruct Hl' as [vs2' [Hget2' Happrox]]; eauto.
    rewrite Hget2 in Hget2'. inv Hget2'.
    edestruct Hr' as [vs1' [Hget1' Happrox']]; eauto.
    rewrite Hget in Hget1'. inv Hget1'.
    eapply Forall2_conj.
    - eapply Forall2_monotonic.
      + intros. rewrite <- res_approx_fuel_eq. eapply H.
      + eapply Happrox. omega.
    - eapply Forall2_monotonic.
      + intros. rewrite <- res_approx_fuel_eq. eapply H.
      + eapply Forall2_flip. eapply Happrox'. omega.
  Qed.

  Lemma heap_env_equiv_env_get (S : Ensemble var) (H1 H2 : heap block)
        (rho1 rho2 : env) (x : var) (l : value) :
    M.get x rho1 = Some l ->
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    x \in S ->
    exists l',
      M.get x rho2 = Some l' /\
      (l, H1) ≈ (l', H2).
  Proof.
    intros Hget Heq Hin.
    eapply Heq in Hget; eassumption.
  Qed.
  
  Lemma heap_env_equiv_env_getlist (S : Ensemble var) (H1 H2 : heap block)
        (rho1 rho2 : env) (xs : list var) (ls : list value) :
    getlist xs rho1 = Some ls ->
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    (FromList xs) \subset S ->
    exists ls',
      getlist xs rho2 = Some ls' /\
      Forall2 (fun l l' => (l, H1) ≈ (l', H2)) ls ls'.
  Proof with now eauto with Ensembles_DB.
    revert ls; induction xs; intros ls Hget Heq Hin.
    - inv Hget.
      eexists; split; eauto. reflexivity.
    - simpl in Hget.
      destruct (M.get a rho1) as [l1 | ] eqn:Hgetl1; try discriminate.
      destruct (getlist xs rho1) as [ls1 | ] eqn:Hetls1; try discriminate.
      inv Hget.
      edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Heq']]; eauto.
      eapply Hin. rewrite FromList_cons...
      edestruct IHxs as [ls2 [Hgetls2 Hall2]]; eauto.
      eapply Included_trans; try eassumption. 
      rewrite FromList_cons...
      eexists; split. simpl. rewrite Hgetl2, Hgetls2.
      reflexivity. constructor; eauto.
  Qed.

  Lemma heap_env_approx_set_alloc_Vconstr (S : Ensemble var) (S1 S2 : Ensemble loc)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (x : var) (t : cTag)
        (vs vs' : list value) (l1 l2 : loc):
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S (Singleton _ x)) \subset S1 ->
    env_locs rho2 (Setminus _ S (Singleton _ x)) \subset S2 ->
    FromList (map val_loc vs) \subset S1 ->
    FromList (map val_loc vs') \subset S2 -> 
    heap_env_approx (Setminus _ S (Singleton _ x)) (H1, rho1) (H2, rho2) ->
    alloc (Vconstr t vs) H1 = (l1, H1') ->
    alloc (Vconstr t vs') H2 = (l2, H2') ->
    Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) vs vs' ->
    heap_env_approx S (H1', (M.set x (Loc l1) rho1)) (H2', (M.set x (Loc l2) rho2)).
  Proof.
    intros Hwf1 Hwf2 He1 He2 Hl1 Hl2 Heq Hal1 Hal2 Hall; simpl; intros y l Hin Hget.
    destruct (peq x y); subst.
    + rewrite M.gss in *. inv Hget. eexists; split; eauto. split.
      * intros c vs1 Hget. erewrite gas in *; eauto. inv Hget.
        eexists; split; eauto. intros i Hlt.
        eapply Forall2_monotonic_strong
        with (R :=  fun l3 l4 =>
                      val_loc l3 \in S1 -> val_loc l4 \in S2 ->
                      res_approx_fuel i (l3, H1') (l4, H2')).
        intros l1' l2' Hin1 Hin2 Hyp. eapply Hyp; eauto.
        eapply Hl1. rewrite FromList_map_image_FromList.
        now eexists; split; eauto.
        eapply Hl2. rewrite FromList_map_image_FromList.
        now eexists; split; eauto.
        eapply Forall2_monotonic; [| eauto ].
        intros. rewrite res_approx_fuel_eq.
        eapply (res_approx_weakening _ _ H1 H2); eauto.
        eapply H; eauto. now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
      * intros c vs1 Hget. erewrite gas in *; eauto. inv Hget.
        eexists; split; eauto. intros i Hlt.
        eapply Forall2_monotonic_strong
        with (R :=  fun l3 l4 =>
                      val_loc l3 \in S2 -> val_loc l4 \in S1 ->
                      res_approx_fuel i (l3, H2') (l4, H1')).
        intros l1' l2' Hin1 Hin2 Hyp. eapply Hyp; eauto.
        eapply Hl2. rewrite FromList_map_image_FromList.
        now eexists; split; eauto.
        eapply Hl1. rewrite FromList_map_image_FromList.
        now eexists; split; eauto.
        eapply Forall2_symm_strong
        with (R2 := (fun l1 l2 => (l1, H2) ≈ (l2, H1))) in Hall.
        eapply Forall2_monotonic; [| eauto ].
        intros. rewrite res_approx_fuel_eq.
        eapply (res_approx_weakening _ _ H2 H1); eauto.
        eapply H; eauto. now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
        intros; now symmetry.
    + rewrite M.gso in *; eauto. assert (Hget1 := Hget). eapply Heq in Hget.
      destruct Hget as [l' [Hget' Heq']]. eexists; split; eauto.
      eapply (res_equiv_weakening _ _ H1 H2  H1' H2'); eauto; simpl in *.
      now eapply alloc_subheap; eauto.
      now eapply alloc_subheap; eauto.
      eapply He1; eauto. repeat eexists; eauto.
      intros Hc; inv Hc. congruence. now rewrite Hget1.
      eapply He2; eauto. repeat eexists; eauto.
      intros Hc; inv Hc. congruence. now rewrite Hget'.
      econstructor; eauto. intros Hc; inv Hc; congruence.
  Qed.

  Corollary heap_env_equiv_set_alloc_Vconstr (S : Ensemble var) (S1 S2 : Ensemble loc)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (x : var) (t : cTag)
        (vs vs' : list value) (l1 l2 : loc) :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S (Singleton _ x)) \subset S1 ->
    env_locs rho2 (Setminus _ S (Singleton _ x)) \subset S2 ->
    FromList (map val_loc vs) \subset S1 ->
    FromList (map val_loc vs') \subset S2 ->
    Setminus _ S (Singleton _ x) |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc (Vconstr t vs) H1 = (l1, H1') ->
    alloc (Vconstr t vs') H2 = (l2, H2') ->
    Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) vs vs' ->
    S |- (H1', M.set x (Loc l1) rho1) ⩪ (H2', M.set x (Loc l2) rho2).
  Proof.
    intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hl1 Hl2 [Heq1 Heq2] Hal1 Hal2 Hall; split.
    now eapply (heap_env_approx_set_alloc_Vconstr _ _ _ H1 H2); eauto.
    eapply (heap_env_approx_set_alloc_Vconstr _ _ _ H2 H1); eauto.
    eapply Forall2_symm_strong; [| eassumption ]. intros; now symmetry; eauto.
  Qed.

  Lemma heap_env_approx_set_alloc_Vfun (S : Ensemble var) (S1 S2 : Ensemble loc)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (x x' : var) (B : fundefs)
        (l1 l2 : loc) :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S [set x]) \subset S1 ->
    env_locs rho2 (Setminus _ S [set x]) \subset S2 ->
    (occurs_free_fundefs B) \subset (Setminus _ S [set x]) ->
    Setminus _ S [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc (Vfun rho1 B) H1 = (l1, H1') -> alloc (Vfun rho2 B) H2 = (l2, H2') ->
    heap_env_approx S (H1', (M.set x (FunPtr l1 x') rho1)) (H2', (M.set x (FunPtr l2 x') rho2)).
  Proof.
    intros Hwf1 Hwf2 He1 He2 Hsub [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
    destruct (peq x y); subst.
    - rewrite M.gss in *. inv Hget. eexists; split; eauto. split.
      + split; eauto. intros rho B' Hget.
        erewrite gas in *; eauto. inv Hget. eexists; split; eauto.
        intros i x Hlt Hin'.
        destruct (M.get x rho) eqn:Hget.
        * edestruct Heq1 as [v' [Hget' Heq']]; eauto.
          left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
          eapply (res_approx_weakening _ _ H1 H2); eauto.
          now destruct (Heq' i); eauto. 
          now eapply alloc_subheap; eauto.
          now eapply alloc_subheap; eauto. 
          eapply He1. eexists; split; eauto.
          rewrite Hget. reflexivity.
          eapply He2. eexists; split; eauto.
          rewrite Hget'. reflexivity.
        * right; split; eauto.
          destruct (M.get x rho2) eqn:Hget'; eauto.
          edestruct Heq2 as [v' [Hget'' Heq']]; eauto; congruence.
      + split; eauto. intros rho B' Hget. erewrite gas in *; eauto.
        inv Hget. eexists; split; eauto.
        intros i x Hlt Hin'.
        destruct (M.get x rho1) eqn:Hget.
        * edestruct Heq1 as [v' [Hget' Heq']]; eauto.
          left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
          symmetry in Heq'. eapply (res_approx_weakening _ _ H2 H1); eauto.
          now destruct (Heq' i); eauto. 
          now eapply alloc_subheap; eauto.
          now eapply alloc_subheap; eauto. 
          eapply He2. eexists; split; eauto.
          rewrite Hget'. reflexivity.
          eapply He1. eexists; split; eauto.
          rewrite Hget. reflexivity.
        * right; split; eauto.
          destruct (M.get x rho) eqn:Hget'; eauto.
          edestruct Heq2 as [v' [Hget'' Heq']]; eauto; congruence.
    - rewrite M.gso in *; eauto. assert (Hget1 := Hget). eapply Heq1 in Hget.
      destruct Hget as [l' [Hget' Heq']]. eexists; split; eauto.
      eapply (res_equiv_weakening _ _ H1 H2  H1' H2'); eauto; simpl in *.
      now eapply alloc_subheap; eauto.
      now eapply alloc_subheap; eauto.
      eapply He1; eauto. repeat eexists; eauto.
      intros Hc; inv Hc. congruence. now rewrite Hget1.
      eapply He2; eauto. repeat eexists; eauto.
      intros Hc; inv Hc. congruence. now rewrite Hget'.
      econstructor; eauto. intros Hc; inv Hc; congruence.
  Qed.

  Corollary heap_env_equic_set_alloc_Vfun (S : Ensemble var) (S1 S2 : Ensemble loc)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (x x' : var) (B : fundefs)
        (l1 l2 : loc) :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S [set x]) \subset S1 ->
    env_locs rho2 (Setminus _ S [set x]) \subset S2 ->
    (occurs_free_fundefs B) \subset (Setminus _ S [set x]) ->
    Setminus _ S [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc (Vfun rho1 B) H1 = (l1, H1') ->
    alloc (Vfun rho2 B) H2 = (l2, H2') ->
    S |- (H1', (M.set x (FunPtr l1 x') rho1)) ⩪ (H2', (M.set x (FunPtr l2 x') rho2)).
  Proof.
    intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hsub Heq Hal1 Hal2; split.
    now eapply (heap_env_approx_set_alloc_Vfun _ _ _ H1 H2); eauto.
    now eapply (heap_env_approx_set_alloc_Vfun _ _ _ H2 H1); eauto.
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
    eapply He1. eexists; split; eauto.
    now rewrite Hget.
    eapply He2. eexists; split; eauto.
    now rewrite Hget'.
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
  
  Lemma heap_env_equiv_def_funs_alloc S S1 S2 H1 H2 H1' H2' rho1 rho2
        B B' l1 l2 :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S (name_in_fundefs B)) \subset S1 ->
    env_locs rho2 (Setminus _ S (name_in_fundefs B)) \subset S2 ->
    (occurs_free_fundefs B') \subset (Setminus _ S (name_in_fundefs B)) -> 
    (Setminus _ S (name_in_fundefs B)) |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc (Vfun rho1 B') H1 = (l1, H1') ->
    alloc (Vfun rho2 B') H2 = (l2, H2') ->
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
        { split. reflexivity. intros rho' B1 Hget.
          erewrite !gas in *; eauto. inv Hget.
          eexists; split; eauto. intros i x Hlt Hin.
          destruct (M.get x rho') eqn:Hget.
          - edestruct Heq1 as [x' [Hget' Heq']]; eauto.
            left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
            eapply (res_approx_weakening _ _ H1 H2); eauto.
            now destruct (Heq' i); eauto. 
            now eapply alloc_subheap; eauto.
            now eapply alloc_subheap; eauto. 
            eapply He1. eexists; split; eauto.
            now rewrite Hget.
            eapply He2. eexists; split; eauto.
            now rewrite Hget'.
          - right; split; eauto.
            destruct (M.get x rho2) eqn:Hget'; eauto.
            edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence. }
        { split. reflexivity. erewrite !gas; eauto.
          intros rho' B1 Hget. inv Hget. eexists; split; eauto.
          intros i x Hlt Hin.
          destruct (M.get x rho1) eqn:Hget.
          - edestruct Heq1 as [x' [Hget' Heq']]; eauto.
            left. repeat eexists; eauto. rewrite res_approx_fuel_eq.
            symmetry in Heq'. eapply (res_approx_weakening _ _ H2 H1); eauto.
            now destruct (Heq' i); eauto. 
            now eapply alloc_subheap; eauto.
            now eapply alloc_subheap; eauto. 
            eapply He2. eexists; split; eauto.
            now rewrite Hget'.
            eapply He1. eexists; split; eauto.
            now rewrite Hget.
          - right; split; eauto.
            destruct (M.get x rho') eqn:Hget'; eauto.
            edestruct Heq2 as [x' [Hget'' Heq']]; eauto; congruence. }
    - simpl in *. rewrite !Setminus_Empty_set_neut_r in He1, He2, Heq.
      eapply (heap_env_equiv_alloc_Vfun _ _ _ H1 H2); eauto.
  Qed.

  Lemma heap_env_equiv_getlist_Forall2 S H1 H2 ys vs1 vs2 rho1 rho2 :
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    FromList ys \subset S ->
    getlist ys rho1 = Some vs1 ->
    getlist ys rho2 = Some vs2 ->
    Forall2 (fun l1 l2 => (l1, H1) ≈ (l2, H2)) vs1 vs2.
  Proof.
    revert vs1 vs2; induction ys; intros vs1 vs2 Heq Hin Hg1 Hg2;
    destruct vs1; destruct vs2; simpl in *; try discriminate; try now constructor.
    - destruct (M.get a rho1) eqn:Heqa;
      destruct (getlist ys rho1) eqn:Heqys; try discriminate.
    - destruct (M.get a rho2) eqn:Heqa;
      destruct (getlist ys rho2) eqn:Heqys; try discriminate.
    - rewrite FromList_cons in Hin.
      destruct (M.get a rho1) eqn:Heqa;
        destruct (getlist ys rho1) eqn:Heqys; try discriminate. inv Hg1.
      eapply Heq in Heqa. destruct Heqa as [l' [Hget Heq']].
      rewrite Hget in Hg2.
      destruct (getlist ys rho2) eqn:Heqys'; try discriminate. inv Hg2.
      constructor; eauto. eapply IHys; eauto.
      eapply Included_trans; now eauto with Ensembles_DB.
      eapply Included_trans; now eauto with Ensembles_DB.
  Qed.
  

  Lemma reach_env_locs_alloc_not_In S H H' rho x b v :
    alloc b H = (val_loc v, H') ->
    locs b \subset (reach' H (env_locs rho S)) ->
    ~ x \in S ->
    Union _ [set (val_loc v)] (reach' H (env_locs rho S)) \subset
    reach' H' (env_locs (M.set x v rho) (Union _ S [set x])).
  Proof.
    intros Hal Hsub Hnin l1 Hin.
    rewrite <- (env_locs_set_not_In) with (l := v) in Hin; eauto.
    rewrite env_locs_Union, reach'_Union. inv Hin.
    - inv H0. right. exists 0. split. 
      now constructor. simpl. eexists. split; eauto.
      now rewrite M.gss.
    - left. eapply reach'_heap_monotonic; eauto.
      eapply alloc_subheap. eassumption.
  Qed.
  
  Lemma heap_env_approx_Vfun S H H'  rho rho' rho1 rho2 l l' f f' B :
    M.get f rho = Some (FunPtr l f') ->
    M.get f rho' = Some (FunPtr l' f') ->
    (FunPtr l f', H) ≈ (FunPtr l' f', H') ->
    S |- (H, rho) ⩪ (H', rho') ->
    f \in S ->
    get l H = Some (Vfun rho1 B) ->
    get l' H' = Some (Vfun rho2 B) ->
    heap_env_approx (occurs_free_fundefs B) (H, rho1) (H', rho2).
  Proof.
    intros Hget1 Hget2 Heq Hheq Hin Hget1' Hget2' x1 l1 Hin' Hget.
    edestruct Heq with (n := 1) as [[_ Heq1] [_ Heq2]]. 
    edestruct Heq1 as [rho2' [Hget' Hlt]]; eauto.
    destruct (Hlt 0 x1) as [[l1' [l2' [Hgetl1 [Hgetl2 _]]]] | [Hn1 Hn2]]; eauto;
    try congruence.
    rewrite Hget in Hgetl1; inv Hgetl1. rewrite Hget2' in Hget'. inv Hget'.
    eexists; split; eauto.
    intros n.
    edestruct Heq with (n := n + 1) as [[_ Heqn1] [_ Heqn2]].
    split.
    - edestruct Heqn1 as [rho2 [Hget' Hlt']]; eauto.
      rewrite Hget2' in Hget'; inv Hget'.
      destruct (Hlt' n x1) as [[l3' [l4' [Hgetl3 [Hgetl4 Hres]]]] | [Hn1 Hn2]]; eauto;
      try congruence.
      omega.
      rewrite Hgetl3 in Hget; inv Hget.
      rewrite Hgetl4 in Hgetl2; inv Hgetl2.
      rewrite <- res_approx_fuel_eq. eassumption.
    - edestruct Heqn2 as [rho2 [Hget' Hlt']]; eauto.
      rewrite Hget1' in Hget'; inv Hget'.
      destruct (Hlt' n x1) as [[l3' [l4' [Hgetl3 [Hgetl4 Hres]]]] | [Hn1 Hn2]]; eauto;
      try congruence.
      omega.
      rewrite Hgetl3 in Hgetl2; inv Hgetl2.
      rewrite Hgetl4 in Hget; inv Hget.
      rewrite <- res_approx_fuel_eq. eassumption.
  Qed.

  Corollary heap_env_equiv_Vfun S rho rho' rho1 rho2 H H' l l' f f' B :
    M.get f rho = Some (FunPtr l f') ->
    M.get f rho' = Some (FunPtr l' f') ->
    (FunPtr l f', H) ≈ (FunPtr l' f', H') ->
    S |- (H, rho) ⩪ (H', rho') ->
    f \in S ->
    get l H = Some (Vfun rho1 B) ->
    get l' H' = Some (Vfun rho2 B) ->
    (occurs_free_fundefs B) |- (H, rho1) ⩪ (H', rho2).
  Proof.
    intros. split.
    now eapply (heap_env_approx_Vfun _ H H' rho rho'); eauto.
    now eapply (heap_env_approx_Vfun _ H' H rho' rho); eauto; symmetry.
  Qed.

 End HeapDefs.
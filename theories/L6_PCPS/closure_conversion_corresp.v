Require Import cps cps_util set_util identifiers ctx hoare Ensembles_util
        List_util closure_conversion closure_conversion_correct functions.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.


(** * Correspondance of the relational and the computational definitions of  closure conversion *)

Section CC_correct.
  Variable (clo_tag : cTag).


  Open Scope ctx_scope.

  (** All the variables greater or equal to x are in S (i.e. the "fresh" set) *)
  Definition fresh (S : Ensemble var) (x : var) :=
    forall y, (x <= y)%positive -> In _ S y.

  (** Free variable map invariant *)
  Definition FVmap_inv (FVmap : VarInfoMap) Scope Funs FVs : Prop :=
    Same_set _ Scope (fun x => M.get x FVmap = Some BoundVar) /\
    Same_set _ (Setminus _ Funs Scope)
             (fun x => exists x', M.get x FVmap = Some (MRFun x')) /\
    forall N x, (nthN FVs N = Some x /\ ~ In _ Scope x /\ ~ In _ Funs x) <->
           (M.get x FVmap = Some (FVar N)).

  (** Function names substitution *)
  Definition subst (FVmap : VarInfoMap) x : var :=
    match M.get x FVmap with
      | Some (MRFun x') => x'
      | _ => x
    end.

  (** A function that corresponds to an evaluation context *)
  Definition is_exp_ctx (f : exp -> exp) C : Prop := 
    forall e, f e = app_ctx_f C e. 

  (** Set of variables not in the map *)
  Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) := 
    forall x : M.elt, In M.elt S x -> M.get x map = None.

  (** Spec for [get_name] *)
  Lemma get_name_fresh S :
    {{ fun s => fresh S (next_var s) }}
      get_name
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (next_var s') }}.  
  Proof.   
    eapply pre_post_mp_l.
    eapply bind_triple. eapply get_triple.
    intros[x c i e] [x' c' i' e'].
    eapply pre_post_mp_l. eapply bind_triple.
    eapply put_triple. intros u [x'' c'' i'' e'']. eapply return_triple. 
    intros [x''' c''' i''' e'''] Heq1 [Heq2 Heq3] H; subst. inv Heq1. inv Heq2. inv Heq3. 
    split; eauto. intros y Hleq.
    constructor.
    - eapply H. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. eapply Pos.le_nlt in Hleq.
      eapply Hleq. zify. omega.
  Qed.
  
  Lemma fresh_monotonic S S' x :
    Included _ S S' ->
    fresh S x ->
    fresh S' x.
  Proof.
    intros Hinc Hf x' Hleq. eapply Hinc. eapply Hf. eassumption.
  Qed.  
  
  Lemma FVmap_inv_set_bound FVmap Scope Funs FVs x :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x BoundVar FVmap) (Union _ (Singleton _ x) Scope) Funs FVs.
  Proof. 
    intros [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + unfold In. now rewrite M.gss.
      + inv Hin. inv H; congruence.
        eapply H1 in H. edestruct H as [t' Heq].
        unfold In. rewrite M.gso; now eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + eauto.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        right. eapply H1. eauto.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + exfalso. eauto.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x' Heq].
        * constructor; eauto.
        * eexists. rewrite M.gso; eauto.
    - eapply H2. destruct H as [x' Heq].
      destruct (Coqlib.peq x x0); subst.
      + rewrite M.gss in Heq. congruence.
      + repeat eexists. rewrite M.gso in Heq; eauto.
    - intros Hc. destruct H as [x' Heq].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + inv Hc. inv H; congruence.
        eapply H2; eauto. repeat eexists.
        rewrite M.gso in Heq; eauto.
    - intros [Hnth [Hnin Hnin']].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto. 
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto.
        rewrite M.gso in H; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. inv Hc. inv H0; congruence.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [Hc _]]].
        eapply H3 in H0; eauto. contradiction.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ Hc']]].
        eapply H3 in Hc; eauto. contradiction.
  Qed.

  Lemma FVmap_inv_set_funs FVmap Scope Funs FVs x x' :
    ~ In _ Scope x ->
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x (MRFun x') FVmap) Scope (Union _ (Singleton _ x) Funs) FVs.
  Proof. 
    intros Hnin [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + contradiction.
      + eapply H1 in Hin. edestruct Hin as [t'' Heq].
        unfold In. rewrite M.gso; eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + unfold In in Hin. rewrite M.gss in Hin; congruence.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        now eapply H1.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + repeat eexists. rewrite M.gss. reflexivity.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x'' Heq].
        inv H. inv H4; congruence. constructor; eassumption.
        repeat eexists. rewrite M.gso; eassumption.
    - destruct (Coqlib.peq x0 x); subst; eauto. right.
      eapply H2. edestruct H as [x'' Hget].
      rewrite M.gso in Hget; [| now eauto ].
      repeat eexists; eauto. 
    - destruct H as [x'' Hget].
      destruct (Coqlib.peq x0 x); subst; eauto.
      rewrite M.gso in Hget; [| now eauto ].
      intros Hc. apply H1 in Hc. congruence.
    - intros [Hnth [Hnin1 Hnin2]].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto.
        rewrite M.gso in H; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto. eapply H1 in Hc. 
        congruence.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        inv Hc. inv H0; congruence.
        edestruct H2 as [H2' _].  edestruct (H2' x0) as [y Hge'].
        constructor. eauto. intros Hc. eapply H1 in Hc. 
        congruence. congruence.
  Qed.

  (** Spec for [get_var] *)
  Lemma get_var_project_var_sound Scope Funs c Γ FVs FVmap S x :
    binding_in_map (Singleton _ x) FVmap ->
    (* binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap -> *)
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (next_var s') /\
           let '(x', f) := t in
           project_var clo_tag Scope Funs (subst FVmap) c Γ FVs S x x' C S' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hin Minv. destruct Minv as [Minv1 [Minv2 Minv3]]. 
    unfold get_var. edestruct (Hin x) as [inf Hget]; eauto. 
    destruct inf; rewrite Hget. 
    - eapply bind_triple.
      + eapply get_name_fresh.     
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        eexists (Eproj_c x' _ n Γ Hole_c). repeat eexists. 
        * eassumption.
        * edestruct Minv3 as [H1 [H2 [H3 H4]]]. now repeat eexists; eauto.
          econstructor 3; eauto.
          eapply Hf. zify; omega.
    - eapply bind_triple.
      + eapply get_name_fresh.  
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        edestruct Minv2 as [H1 H2]; eauto. 
        exists (Econstr_c x' clo_tag [v; Γ] Hole_c). repeat eexists.
        * eassumption.
        * replace v with ((subst FVmap) x)
            by (unfold subst; rewrite Hget; reflexivity). 
          econstructor; eauto.
          intros Hc. eapply Minv1 in Hc. congruence.
          eapply H2. repeat eexists; eauto.
          eapply Hf. zify; omega.    
    - eapply return_triple. intros [s d] Hin'.      
      exists Hole_c. repeat eexists. 
      + eassumption. 
      + constructor. eapply Minv1. eauto.
  Qed.
  
  (** Spec for [get_vars] *)
  Lemma get_vars_project_vars_sound Scope Funs c Γ FVs FVmap S xs :
    binding_in_map (FromList xs) FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (next_var s') /\
           let '(xs', f) := t in
           project_vars clo_tag Scope Funs (subst FVmap) c Γ FVs S xs xs' C S' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hb Hfv. eapply pre_post_mp_l.
    revert S Hb Hfv. induction xs; intros S Hb Hfv. 
    - eapply return_triple. intros [x' d'] _ Hf.
      eexists Hole_c. repeat eexists; eauto.
      constructor.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; eauto.
        intros x Hin. eapply Hb. 
        inv Hin. constructor. eauto.
      + intros [x f] [x1 c1 f1 e1]. eapply pre_eq_state.
        intros [x2 c2 f2 e2] [C [S' [Hf [Hproj Hctx]]]].
        eapply pre_post_mp_l. eapply bind_triple.
        eapply (IHxs S'); eauto.
        intros y Hin. eapply Hb. 
        constructor 2. eassumption.
        intros [xs' f'] [x4 c4 f4 e4]. eapply return_triple.  
        intros s5 Hyp Heq'. inversion Heq'.
        destruct Hyp as [C' [S'' [Hf' [Hproj' Hctx']]]]; eauto.
        now rewrite <- H0; eauto.
        exists (comp_ctx_f C C'), S''.
        split; [ eassumption |].
        split. now econstructor; eauto.
        intros e. rewrite <- app_ctx_f_fuse. congruence.
  Qed.
  
  Lemma subst_BoundVar_f_eq_subdomain FVmap x S :
    f_eq_subdomain S ((subst FVmap) {x ~> x}) (subst (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold subst, extend. rewrite M.gsspec.
    destruct (Coqlib.peq x' x). now eauto.
    reflexivity. 
  Qed.

  Lemma subst_BoundVar_f_eq FVmap x :
    f_eq ((subst FVmap) {x ~> x}) (subst (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold subst, extend. rewrite M.gsspec.
    destruct (Coqlib.peq x' x). now eauto.
    reflexivity. 
  Qed.

  Lemma Disjoint_free_set FVmap Scope Funs FVs S :
    binding_not_in_map S FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    Disjoint _ S (Union var Scope
                        (Union var Funs (FromList FVs))).
  Proof.             
    intros Hb [Hinv1 [Hinv2 Hinv3]].
    constructor. intros x Hc. inv Hc. 
    assert (Hdec1 : Decidable Scope).
    { eapply Decidable_Same_set.
      apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros; congruence. 
      - right. intros; congruence. }
    assert (Hdec2 : Decidable (Setminus _ Funs Scope)).
    { eapply Decidable_Same_set.
      apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [y Hc]; congruence. 
      - right. intros [y Hc]; congruence. }
    destruct Hdec1, Hdec2.
    destruct (Dec x). 
    - eapply Hinv1 in H1.
      unfold In in H1. rewrite Hb in H1; eauto. congruence.
    - destruct (Dec0 x).
      + eapply Hinv2 in H2. destruct H2 as [y Heq].
        rewrite Hb in Heq; eauto. congruence.
      + inv H0; try contradiction.
        inv H3. eapply H2; constructor; eauto.
        unfold In, FromList in H0.        
        edestruct In_nthN as [N Hnth]; [ eassumption |].
        edestruct Hinv3 as [H' _].
        assert (H3 : ~ Funs x) by (intros Hc; eapply H2; constructor; eauto).
        specialize (H' (conj Hnth (conj H1 H3))). rewrite Hb in H'; congruence.
  Qed.
  
  Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
    Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
  Proof. 
    intros Hin Hb x Hin'. eauto.
  Qed.

  Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
    binding_not_in_map S map ->
    ~ In _ S x ->
    binding_not_in_map S (M.set x v map). 
  Proof. 
    intros HB Hnin x' Hin.
    rewrite M.gsspec. destruct (Coqlib.peq x' x); subst; try contradiction. 
    eauto. 
  Qed.

  Import MonadNotation.

  Transparent bind ret.

  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase {S} m1 (m2 : state S (var * (exp -> exp))) y :
    st_eq
      (ys <- m1 ;; 
       ys' <- ret (y :: ys) ;;
       t1 <- m2 ;;
       let '(x, f) := t1 in
       ret (Ecase x ys', f))
      (fe <- (ys <- m1 ;;
             t1 <- m2 ;;
             let '(x, f1) := t1 in    
             ret (Ecase x ys, f1)) ;;
       match fe with
         | (Ecase x ys, f) =>
           ret (Ecase x (y :: ys), f)
         | _ => ret fe
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s).
    destruct (runState m2 s0). destruct p as [x f].
    reflexivity.
  Qed.

  Opaque bind ret.

  Global Instance FVmap_inv_Scope_Proper :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq2.
      intros H. rewrite <- Heq2. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq2.
      intros H. rewrite Heq2. eapply H3. eassumption. 
  Qed.

  Global Instance FVmap_inv_Funs_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq3; eauto.
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq3.
      intros H. rewrite <- Heq3. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq3; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq3.
      intros H. rewrite Heq3. eapply H3. eassumption. 
  Qed.

  Lemma FVmapInv_add_params FVmap xs Scope Funs FVs :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (add_params xs FVmap) (Union _ Scope (FromList xs)) Funs FVs. 
  Proof. 
    revert FVmap Scope. induction xs; intros FVmap Scope Hinv.
    - rewrite FromList_nil, Union_Empty_set_l. eauto.
    - rewrite FromList_cons.
      rewrite Union_assoc; rewrite Union_sym with (s2 := Singleton M.elt a), <- Union_assoc. 
      eapply FVmap_inv_set_bound; eauto.
  Qed.

  Lemma binding_in_map_add_params S FVmap xs :
    binding_in_map S FVmap ->
    binding_in_map (Union _ S  (FromList xs)) (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb.
    - intros x. rewrite FromList_nil, Union_Empty_set_l. eauto.
    - intros x. rewrite FromList_cons.
      rewrite Union_sym with (s2 := FromList xs), Union_assoc.
      simpl. eapply binding_in_map_set; eauto. 
  Qed.

  Lemma binding_not_in_map_add_params S FVmap xs :
    binding_not_in_map S FVmap ->
    Disjoint _ S (FromList xs) ->
    binding_not_in_map S (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb Hd.
    - eauto.
    - rewrite FromList_cons in Hd.
      eapply binding_not_in_map_set_not_In_S; eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
  Qed.
  
  Lemma FVmap_inv_empty :
    FVmap_inv (Maps.PTree.empty VarInfo) (Empty_set M.elt) (Empty_set M.elt) [].
  Proof.
    repeat split; (try now intros Hc; inv Hc); (try now intros x Hc; inv Hc). 
    intros x Hx. unfold In in Hx. rewrite M.gempty in Hx. now inv Hx.
    destruct H as [x' Hget]. rewrite M.gempty in Hget. now inv Hget.
    rewrite M.gempty in H. now inv H.
  Qed.
    
  Lemma FVmap_inv_set_free_var FVmap Scope Funs FVs x n:
    FVmap_inv FVmap Scope Funs FVs ->
    N.of_nat (length FVs) = n ->
    ~ In _ Scope x -> ~ In  _ Funs x -> ~ List.In x FVs ->
    FVmap_inv (Maps.PTree.set x (FVar n) FVmap) Scope Funs (FVs ++ [x]). 
  Proof.  
    intros [H1 [H2 H3]] Hlen Hnin1 Hnin2.
    split; [| split ]. 
    - split.
      + intros x' Hin. assert (Hin' := Hin).
        eapply H1 in Hin.
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        unfold In. rewrite M.gso; eauto.
      + intros x' Hget. eapply H1. 
        unfold In in Hget. rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence. now eauto.
    - split.
      + intros x' Hin. assert (Hin' := Hin). inv Hin'. 
        eapply H2 in Hin. edestruct Hin as [y Heq].
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [y Hget]. eapply H2. 
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence.
        now eauto.
    - intros N x'. split.
      + intros [Hnth [Hnin1' Hnin2']].
        destruct (nthN_app FVs [x] N) as [Hn | [Hn Hlen']].
        * destruct (Coqlib.peq x' x); subst.
          exfalso. eapply H. eapply nthN_In. rewrite <- Hnth. now eauto.
          edestruct H3 as [Hget _].
          rewrite M.gso; eauto. eapply Hget. repeat split; eauto.
          rewrite <- Hnth. now eauto.
        * subst. rewrite Hnth in Hn. eapply nthN_is_Some_length in Hnth.
          rewrite app_length in Hnth. simpl length in *.
          destruct (N - N.of_nat (length FVs))%N eqn:Heq; simpl in Hn; try congruence.
          inv Hn. rewrite M.gss; eauto.
          repeat f_equal. zify. omega. 
      + subst. intros Hget.
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        * subst. inv Hget. repeat split; eauto.
          rewrite nthN_app_geq. rewrite N.sub_diag. reflexivity. 
          zify; omega. 
        * edestruct H3 as [_ [H1' [H2' H3']]].
          eassumption.
          repeat split; eauto. apply nthN_is_Some_app. eassumption.
  Qed.

  Lemma make_record_cTag_preserves_prop n P :
    {{ fun s => P (next_var s) }} make_record_cTag n {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1] [x2 c2 f2 e2].
    apply pre_post_mp_l. eapply bind_triple. now apply put_triple.
    intros x s. eapply return_triple. intros s' [[H1 H3] H2]; subst. inv H1.
    eassumption.
  Qed.
  
  Lemma make_env_spec fv FVmap_o c Γ_n Γ_o Scope Funs FVs S :
    binding_in_map (FromList (PS.elements fv)) FVmap_o ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ_o)) FVmap_o ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      make_env clo_tag fv (Maps.PTree.empty VarInfo) FVmap_o c Γ_n Γ_o 
    {{ fun s t  s' =>
         let '(c', FVmap_n, f) := t in
         exists C S' FVs',
           fresh S' (next_var s') /\
           project_vars clo_tag Scope Funs (subst FVmap_o) c Γ_o FVs S (PS.elements fv) FVs' C S' /\
           is_exp_ctx f (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c)) /\
           binding_in_map (FromList (PS.elements fv)) FVmap_n /\
           binding_not_in_map (Complement _ (FromList (PS.elements fv))) FVmap_n /\
           FVmap_inv FVmap_n (Empty_set _) (Empty_set _) (PS.elements fv)
     }}.
  Proof.
    intros Hb1 Hb2 Minv. unfold make_env.
    destruct ((fix
                 add_fvs (l : list Maps.PTree.elt) (n : N) (map : Maps.PTree.t VarInfo)
                 {struct l} : Maps.PTree.t VarInfo * N :=
                 match l with
                   | [] => (map, n)
                   | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                 end)
                (PS.elements fv) 0%N (Maps.PTree.empty VarInfo)) as [map_new n] eqn:Heq.
    eapply bind_triple.
    - eapply get_vars_project_vars_sound; eauto.
    - intros [xs f] s1.
      eapply pre_existential. intros C1. eapply pre_existential. intros S'.
      eapply pre_uncurry_r. intros [Hvars Hctx].
      eapply bind_triple. now eapply make_record_cTag_preserves_prop.
      intros tau s2. eapply return_triple.
      intros s3 Hf. do 3 eexists. 
      repeat (split; [ eassumption |]). split.
      + intros e. rewrite Hctx. rewrite <- app_ctx_f_fuse.
        now f_equal.
      + replace map_new with
        (fst ((fix
                add_fvs (l : list Maps.PTree.elt) (n : N)
                (map : Maps.PTree.t VarInfo) {struct l} :
                Maps.PTree.t VarInfo * N :=
                match l with
                  | [] => (map, n)
                  | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                end) (PS.elements fv) 0%N (Maps.PTree.empty VarInfo)))
          by (rewrite Heq; eauto).
        clear.
        assert (He : FVmap_inv (Maps.PTree.empty VarInfo)
                               (Empty_set M.elt) (Empty_set M.elt) (@nil PS.elt))
          by apply FVmap_inv_empty.
        assert (Hb : binding_in_map (FromList (@nil PS.elt)) (Maps.PTree.empty VarInfo))
          by (intros x H; inv H).
        assert (Hb' : binding_not_in_map (Complement _ (FromList ((@nil PS.elt))))
                                         (Maps.PTree.empty VarInfo))
          by (intros x H; rewrite Maps.PTree.gempty; reflexivity).
        assert (Hlen : N.of_nat (@length PS.elt []) = 0%N) by eauto.
        assert (Hnin : forall x, List.In x (PS.elements fv) -> ~ List.In x (@nil PS.elt))
          by (intros x H1 H2; inv H2).
        assert (Hdup :  NoDupA eq (PS.elements fv)) by apply PS.elements_spec2w.
        replace (PS.elements fv) with ([] ++ PS.elements fv) at 1 3 6 by reflexivity.
        revert Hlen He Hb Hb' Hnin Hdup. generalize (Maps.PTree.empty VarInfo) as FVmap_i.
        generalize (@nil PS.elt). generalize 0%N. 
        induction (PS.elements fv); intros n vars FVmap_i Hlen Hinv Hb Hb' Hnin Hdup.
        * simpl. rewrite app_nil_r. simpl. eauto.
        * simpl. replace (vars ++ a :: l) with ((vars ++ [a]) ++ l). simpl.
          eapply IHl. rewrite app_length. simpl. zify. omega.
          eapply FVmap_inv_set_free_var. now eauto. eassumption. 
          now intros Hc; inv Hc. now intros Hc; inv Hc. 
          eapply Hnin. constructor. reflexivity.
          intros x H. eapply binding_in_map_set. eassumption.
          rewrite FromList_app, FromList_cons, FromList_nil, Union_Empty_set_l in H.
          eassumption.
          eapply binding_not_in_map_set_not_In_S.
          eapply binding_not_in_map_antimon; [| eassumption ]. 
          eapply Complement_antimon. rewrite FromList_app. now apply Included_Union_l.
          intros Hc. eapply Hc. rewrite FromList_app, FromList_cons, FromList_nil. now eauto.
          intros x Hin Hc. eapply Hnin.
          now constructor 2; eauto. inv Hdup.
          apply Coqlib.in_app in Hc. inv Hc; eauto. inv H. 
          exfalso. eapply H1. eapply In_InA. eauto. now eapply Pos.eq_equiv. 
          eassumption. now inv H0. now inv Hdup.
          rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma subst_MRFun_f_eq (FVmap : VarInfoMap) (x x' : var) :
    f_eq ((subst FVmap) {x ~> x'}) (subst (M.set x (MRFun x') FVmap)).
  Proof.
    unfold subst. intros y. unfold extend.
    rewrite M.gsspec. destruct (Coqlib.peq y x); eauto.
  Qed.


  Lemma make_full_closure_spec B FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2' :
    binding_in_map S1 FVmap_o -> 
    binding_in_map S2 FVmap_n ->
    binding_not_in_map S1' FVmap_o -> 
    binding_not_in_map S2' FVmap_n ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    FVmap_inv FVmap_n (Empty_set _) (Empty_set _) FVs' ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B FVmap_n FVmap_o Γ
    {{ fun s t s' =>
         let '(FVmap_n', FVmap_o', f) := t in
         exists C S',
           fresh S' (next_var s') /\
           make_closures clo_tag B S Γ C (subst FVmap_n') S' /\
           is_exp_ctx f C /\
           f_eq_subdomain (Setminus _ Funs (Union _ Scope (name_in_fundefs B)))
                          (subst FVmap_o) (subst FVmap_o') /\
           binding_in_map (Union _ S1 (name_in_fundefs B)) FVmap_o' /\
           binding_in_map (Union _ S2 (name_in_fundefs B)) FVmap_n' /\
           binding_not_in_map (Setminus _ S1' (name_in_fundefs B)) FVmap_o' /\
           binding_not_in_map (Setminus _ S2' (name_in_fundefs B)) FVmap_n' /\
           FVmap_inv FVmap_o' (Union _ (name_in_fundefs B) Scope) Funs FVs /\
           FVmap_inv FVmap_n' (Empty_set _) (name_in_fundefs B) FVs'
     }}.
  Proof.
    revert FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2'.
    induction B;
      intros FVmap_n FVmap_o Γ Scope Funs FVs FVs' S
             S1 S2 S1' S2' Hb1 Hb2 Hb1' Hb2'  Minv_o Minv_n. 
    - eapply bind_triple; [ now apply get_name_fresh |].
      intros x s1. eapply pre_uncurry_l. intros Hx.
      eapply bind_triple; [ eapply IHB; eassumption |].
      intros [[FVmap_n' FVmap_o'] f'] _.
      eapply pre_existential. intros C. eapply pre_existential. intros S'.
      eapply pre_uncurry_r. intros [Hclo [Hctx [Hfeq [Hbn [Hbo [Hbn' [Hbo' [Minv_o' Minv_n']]]]]]]].
      apply return_triple. 
      intros s3 Hf. do 2 eexists.
      split. eassumption. 
      split. econstructor. eassumption. eapply Hx. zify; omega.
      rewrite <- subst_MRFun_f_eq. reflexivity.
      split. intros e'. simpl. rewrite Hctx. reflexivity.
      split. rewrite <- subst_BoundVar_f_eq.
      apply f_eq_subdomain_extend_not_In_S_r.
      intros Hc. inv Hc. eapply H0. right. left. now eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      apply Included_Union_compat. now apply Included_refl.
      now apply Included_Union_r.
      split. eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      simpl. rewrite (Union_sym (Singleton _ v)), Union_assoc. now apply Included_refl.
      split.  eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      simpl. rewrite (Union_sym (Singleton _ v)), Union_assoc. now apply Included_refl.
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ]. 
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. simpl. rewrite <- Union_assoc. eapply FVmap_inv_set_bound.
      eassumption.
      simpl. apply FVmap_inv_set_funs. now apply not_In_Empty_set.
      eassumption. 
    - eapply return_triple. intros s Hs. do 2 eexists.
      split. eassumption. split. now constructor.
      split. intros e. reflexivity.
      split. intros x H. reflexivity.
      split. intros x H. eapply Hb1. now rewrite Union_Empty_set_l in H.
      split. intros x H. eapply Hb2. now rewrite Union_Empty_set_l in H.
      split. eapply binding_not_in_map_antimon; [| eassumption ].
      now apply Subset_Setminus.
      split. eapply binding_not_in_map_antimon; [| eassumption ].
      now apply Subset_Setminus.
      split. rewrite Union_Empty_set_r. eassumption.
      eassumption. 
  Qed.

  (* Rewrite does not exactly works for these two, but they are still useful as lemmas *)
  Global Instance project_var_Proper Scope Funs :
    Proper
      (f_eq_subdomain (Setminus _ Funs Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_var clo_tag Scope Funs).
  Proof. 
    constructor; subst; intros Hproj; inv Hproj; try (now constructor; eauto).
    - rewrite H; now econstructor; eauto.
    - rewrite <- H; now econstructor; eauto.
  Qed.
  
  Global Instance project_vars_Proper Scope Funs :
    Proper
      (f_eq_subdomain (Setminus _ Funs Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_vars clo_tag Scope Funs).
  Proof. 
      constructor; subst; intros Hproj; induction Hproj; try (now constructor; eauto).
      - econstructor. eapply project_var_Proper; eauto.
        now symmetry. now eauto.
      - econstructor. now eapply project_var_Proper; eauto. now eauto.
  Qed.

  Lemma Closure_conversion_f_eq_subdomain_mut :
    (forall e Scope Funs σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs σ' c Γ FVs e e' C) /\
    (forall B Funs σ σ' c FVs B'
       (Hinc : Included _ (name_in_fundefs B) Funs)
       (Hcc : Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hfeq : f_eq_subdomain Funs σ σ'),
       Closure_conversion_fundefs clo_tag Funs σ' c FVs B B').
  Proof. 
    eapply exp_def_mutual_ind; intros; inv Hcc.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      inv H11. constructor.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      inv H13. inv H4. simpl in H1; subst. destruct H2 as [C' [e' [Heq Hcc]]].
      constructor. now split; eauto.
      assert (Hcc' : Closure_conversion clo_tag Scope Funs σ' c0 Γ FVs (Ecase v l)  (Ecase x' l') C).
      { eapply H0. econstructor; eauto. eassumption. }
      now inv Hcc'.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
    - econstructor; try reflexivity. eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption. eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption. eassumption. eapply H.
      now apply Included_refl. eassumption. reflexivity.
      eapply H0. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
    - econstructor; try reflexivity; try eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; [| eassumption ].
      eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
      apply Included_Setminus_compat. now apply Included_refl.
      now apply Included_Union_r.
    - rewrite Hfeq. econstructor; try eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ]. eassumption.
      eapply H0; [| now eauto | now eauto ].
      eapply Included_trans; [| eassumption ]. now apply Included_Union_r.
      eapply H. eassumption.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      now apply Subset_Setminus.
      eapply Hinc. left. eauto.
    - constructor. 
  Qed.

  Corollary Closure_conversion_f_eq_subdomain :
    forall e Scope Funs σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
      Closure_conversion clo_tag Scope Funs σ' c Γ FVs e e' C.
  Proof.
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

  Corollary Closure_conversion_fundefs_f_eq_subdomain :
  (forall B Funs σ σ' c FVs B'
       (Hinc : Included _ (name_in_fundefs B) Funs)
       (Hcc : Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hfeq : f_eq_subdomain Funs σ σ'),
       Closure_conversion_fundefs clo_tag Funs σ' c FVs B B').
  Proof. 
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.
  

  Lemma subst_add_params_f_eq_subdomain S l FVmap :
    Disjoint _ (FromList l) S ->
    f_eq_subdomain S
     (subst (add_params l FVmap)) (subst FVmap).
  Proof.
    intros Hd. induction l.
    - simpl. reflexivity.
    - simpl.
      rewrite <- subst_BoundVar_f_eq_subdomain.
      eapply f_eq_subdomain_extend_not_In_S_l.
      intros H. eapply Hd. constructor. rewrite FromList_cons.
      now left. eassumption.
      eapply IHl. eapply Disjoint_Included_l; [| eassumption ].
      rewrite FromList_cons. now apply Included_Union_r.
  Qed.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs c Γ FVs FVmap S
       (* The invariant the relates [FVmap] and [Scope], [Funs], [FV] *)
       (Minv : FVmap_inv FVmap Scope Funs FVs)
       (* [FVmap] contains all the free variables *)
       (Hbin1 : binding_in_map (occurs_free e) FVmap)
       (* [FVmap] does not contain the variables in [S] or [Γ] *)
       (Hbin2 : binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap)
       (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
       (HD1 : Disjoint _ S (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                                  (Union _ (bound_var e)
                                         (Union _ (occurs_free e) (Singleton _ Γ)))))
       (* The current environment argument is fresh *)
       (HD2 : ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ),
       {{ fun s => True }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            fresh S (next_var s) ->
            exists C, is_exp_ctx (snd ef) C /\
                 Closure_conversion clo_tag Scope Funs (subst FVmap) c Γ FVs e (fst ef) C /\
                 fresh S (next_var s')
       }}) /\
    (forall B FVmap Funs FVs S c
       (Minv : FVmap_inv FVmap (Empty_set _) Funs FVs)
       (Hbin1 : binding_in_map (Union _ (occurs_free_fundefs B) (name_in_fundefs B)) FVmap)
       (Hbin2 : binding_not_in_map S FVmap)
       (HD1 : Disjoint _ S (Union _ (image (subst FVmap) Funs)
                                  (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))))
       (Hinc : Included _ (name_in_fundefs B) Funs),
       {{ fun s => True }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
            fresh S (next_var s) ->       
            Closure_conversion_fundefs clo_tag Funs (subst FVmap) c FVs B B' /\
            fresh S (next_var s')
       }}).
  Proof.
    eapply exp_def_mutual_ind; intros.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_eq_state.
        intros [? ? ? ? ] [C [S' [Hf [Hproj Hctx]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Econstr_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat. eapply project_vars_free_set_Included; now eauto. 
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l. eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite <- subst_BoundVar_f_eq.
          rewrite Union_sym, <- Setminus_Union. now eapply image_Setminus_extend.
          rewrite !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Econstr_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Econstr, occurs_free_Econstr. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst.
          edestruct (Hf' Hf) as [C' [Hctx' [Hcc Hf'']]]; eauto.
          do 2 eexists. eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor. eapply Disjoint_free_set in Minv.  
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. apply Included_Union_mon_r.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
          now apply Included_refl.
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eassumption.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple with (post' := fun _ l i => l = [] /\ fresh S (next_var i)).
      + eapply return_triple; eauto. 
      + intros pats' s2.
        eapply bind_triple.
        * eapply frame_rule. eapply get_var_project_var_sound; eauto.
          intros x Hx. eapply Hbin1. rewrite occurs_free_Ecase_nil. eassumption.
        * intros [x f] s. eapply return_triple.
          intros s' [Heq [C [S' [Hf [Hproj Hctx]]]]]. rewrite Heq.
          eexists. split; eauto. split. econstructor; [| eassumption |].
          eapply Disjoint_free_set in Minv.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. apply Included_Union_mon_r.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
          now apply Included_refl.
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          now constructor.
          eapply fresh_monotonic. now eapply project_var_free_set_Included; eauto.
          eassumption.
    - unfold exp_closure_conv. setoid_rewrite assoc.
      eapply bind_triple.
      + eapply H; [ eassumption | | eassumption | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite !Union_assoc. apply Included_Union_compat; [| now apply Included_refl ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor. 
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. 
        eapply pre_post_mp_l. eapply bind_triple. 
        eapply H0 with (FVmap := FVmap) (Γ := Γ) (c := c0);
          [ eassumption | | eassumption | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Ecase_cons. apply Included_Union_mon_r.
          now apply Included_Union_r.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite !Union_assoc. apply Included_Union_compat; [| now apply Included_refl ].
          eapply bound_var_occurs_free_Ecase_cons_Included.
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
        * intros [e'' f s''].   
          edestruct e''; eapply return_triple; intros s''' Hcc1 Hcc2 Hf;
          edestruct (Hcc2 Hf) as [C2 [Hctx2 [Hcc2'  Hf2]]];
          edestruct (Hcc1 Hf2) as [C1 [Hctx1 [Hcc1' Hf1]]]; inv Hcc1'.
          eexists. repeat split.
          eassumption.
          simpl. econstructor; [ eassumption | eassumption | now constructor; eauto ].
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; [ | eassumption ].
        intros x Hx. inv Hx. eapply Hbin1. eauto.
      + intros [x f] s. eapply pre_eq_state.
        intros [? ? ? ?] [C [S' [Hf [Hproj Hctx]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eproj_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l. eapply project_var_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite <- subst_BoundVar_f_eq.
          rewrite Union_sym, <- Setminus_Union. now eapply image_Setminus_extend.
          rewrite !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Eproj_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eproj, occurs_free_Eproj. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst.
          edestruct (Hf' Hf) as [C' [Hctx' [Hcc Hf'']]]; eauto.
          do 2 eexists. eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor. eapply Disjoint_free_set in Minv.  
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. apply Included_Union_mon_r.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
          now apply Included_refl.
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eassumption.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic. now eapply project_var_free_set_Included; eauto.
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple; [ now eapply get_name_fresh |].
      intros Γ' s1. eapply pre_uncurry_l. intros Hf1.
      eapply bind_triple.
      + eapply make_env_spec. eapply binding_in_map_antimon; [| eassumption ].
        * intros x Hfv. eapply occurs_free_Efun. left.
          eapply fundefs_fv_correct. eassumption. 
        * eapply binding_not_in_map_antimon; [| eassumption ].
          eapply Included_Union_compat. now apply Subset_Setminus.
          now apply Included_refl.
        * eassumption.
      + intros [[c' FVmap'] f] _. eapply pre_existential; intros C1.
        eapply pre_existential; intros S2. eapply pre_existential; intros FVs'.
        eapply pre_uncurry_r. intros [Hproj [Hctx1 [Hb1 [Hb1' Minv1]]]].
        eapply bind_triple; [ eapply make_full_closure_spec; eassumption |].
        intros [[FVmap_n FVmap_o] f'] s2. eapply pre_existential; intros C2.
        eapply pre_existential; intros S3. eapply pre_uncurry_r.
        intros [Hmc [Hctx2 [Hfeq [Hb2 [Hb2' [Hb3 [Hb3' [Minv_n Minv_o]]]]]]]].
        eapply pre_post_mp_l. eapply bind_triple.
        * eapply H0 with (S := S3) ; [ eassumption | | | | ].
          eapply binding_in_map_antimon; [| eassumption ].
          now apply occurs_free_Efun_Included.
          eapply binding_not_in_map_antimon; [| eassumption ].
          rewrite <- Included_Setminus_Disjoint.
          eapply Included_Union_compat.
          eapply Included_trans. eapply Included_trans. now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto. now apply Subset_Setminus.
          now apply Included_refl.
          eapply Disjoint_Union.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_mon_r. apply Included_Union_mon_l.
          rewrite bound_var_Efun. apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
          apply Disjoint_sym. eapply Disjoint_Singleton. intros Hc. eapply HD2.
          left. rewrite bound_var_Efun. left. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [| eassumption ] ].
          eapply Included_Union_compat. rewrite Union_sym. rewrite <- image_f_eq_subdomain. 
          apply image_monotonic. apply Included_Setminus_compat. now apply Included_refl.
          now apply Included_Union_l. eassumption. 
          rewrite !Union_assoc. eapply Included_Union_compat.
          now apply bound_var_occurs_free_Efun_Included. now apply Included_refl.
          eapply Included_trans. eapply Included_trans. now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto. now apply Subset_Setminus.
          intros H'. eapply HD2. now eapply bound_var_occurs_free_Efun_Included.
        * intros [e' f''] s3. eapply pre_post_mp_l.
          eapply bind_triple.
          eapply H. eassumption. eapply binding_in_map_antimon; [| eassumption ].
          apply Included_Union_compat. rewrite fundefs_fv_correct.
          now apply Included_refl. now apply Included_refl.          
          eapply binding_not_in_map_antimon with (S' := S3); [| eassumption ].
          eapply Included_trans. eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto.          
          now apply Subset_Setminus.
          intros x H'. constructor. intros Hc.
          eapply HD1. constructor. now eauto. do 2 right. left. rewrite occurs_free_Efun.
          left. eapply fundefs_fv_correct. eassumption. intros Hc. eapply HD1. constructor. now eauto.
          right. left. rewrite bound_var_Efun. left. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_sym. eapply Disjoint_Union.
          eapply make_closures_image_Disjoint. eassumption.  
          apply Disjoint_sym.
          eapply Disjoint_Included_l. now eapply make_closures_free_set_Included; eauto.
          eapply Disjoint_Included_l. now eapply project_vars_free_set_Included; eauto.
          eapply Disjoint_Included_l. now eapply Subset_Setminus.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_mon_r. rewrite Union_assoc.
          apply Included_Union_mon_l. now apply bound_var_occurs_free_fundefs_Efun_Included.
          now apply Included_refl.
          intros B s4. apply return_triple. intros s5 H1 H2 H3.
          edestruct (H2 H3) as [C'' [Hctx'' [Hcc'' Hf'']]]; eauto.
          edestruct (H1 Hf'') as [Hcc' Hf']; eauto.
          eexists.  split. eassumption. 
          split. simpl. rewrite Hctx'', Hctx2.
          assert (HD3 :
                    Disjoint M.elt S
                             (Union var (bound_var_fundefs f2)
                                    (Union var Scope
                                           (Union var (image (subst FVmap) (Setminus var Funs Scope))
                                                  (Union var (FromList FVs) (Singleton var Γ)))))).
          { eapply Disjoint_free_set in Minv.  
            eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
            eapply Disjoint_Included_r; [| now eapply HD1 ]. 
            apply Included_Union_mon_r. apply Included_Union_mon_l.
            rewrite bound_var_Efun. now apply Included_Union_l.
            eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
            eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
            eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
            eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
            eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
            eapply Disjoint_Included_r; [|  eassumption ]. apply Included_Union_mon_r.
            now apply Included_Union_r.
            eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
            now apply Included_refl.
            eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l. }
          econstructor; [ |  | eassumption | | |  | eassumption | eassumption | ]. 
          now eapply fundefs_fv_correct.
          eapply Disjoint_Included_l. now apply Subset_Setminus. 
          eapply Disjoint_Included_r; [| eassumption ].
          now apply Included_Union_r.
          eapply Disjoint_Included_l with (s8 := S).
          intros x Hin. eapply Hin. eapply Disjoint_Included_r; [| eassumption ]. 
          eapply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          now apply Included_refl.
          eapply Hf1. zify; omega.
          rewrite Union_assoc, (Union_sym _ (Singleton var Γ')), <- Union_assoc.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_l.
          eapply project_vars_free_set_Included; eassumption.
          eapply Disjoint_Setminus. now apply Included_refl.
          eapply Disjoint_Included_l.
          eapply Included_trans. eapply project_vars_free_set_Included; eassumption.
          now apply Subset_Setminus. eassumption.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite Union_sym. symmetry. eassumption.
          eapply fresh_monotonic; [ | eassumption ].
          eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto. now apply Subset_Setminus.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; [  | eassumption ].
        eapply binding_in_map_antimon; [| eassumption ].
        rewrite occurs_free_Eapp. apply Included_Union_mon_r.
        now apply Included_refl.
      + intros [x f] s1. eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_uncurry_r. intros [Hvar Hctx1].
        eapply bind_triple.
        * eapply get_vars_project_vars_sound; [ | eassumption ].
          eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Eapp. apply Included_Union_mon_l.
          now apply Included_refl.
        * intros [xs f'] s2. eapply pre_existential. intros C2.
          eapply pre_existential. intros S''.
          eapply pre_uncurry_r. intros [Hvars  Hctx2]. eapply bind_triple.
          eapply get_name_fresh.
          intros x' i. eapply pre_uncurry_l. intros Hf1.
          eapply bind_triple.
          now eapply get_name_fresh. 
          intros x'' s3. eapply pre_uncurry_l. intros Hf2. 
          eapply return_triple.
          intros s5 Hf5. simpl. exists (comp_ctx_f C1 C2).
          split. intros e. rewrite <- app_ctx_f_fuse. congruence.
          split; eauto.
          econstructor;
            [ | econstructor; eassumption | eapply Hf1; now apply Pos.le_refl
              | eapply Hf2; now apply Pos.le_refl
              | intros Hc; subst x';  eapply Hf2;
                [ now apply Pos.le_refl | now eauto ]].
          eapply Disjoint_free_set in Minv.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. apply Included_Union_mon_r.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
          now apply Included_refl.
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply fresh_monotonic; [| eassumption ].
          do 2 (eapply Included_trans; [ now apply Subset_Setminus |]).
          eapply Included_trans. now eapply project_vars_free_set_Included; eauto.
          eapply Included_trans. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_eq_state.
        intros [x'' d''] [C [S' [Hf [Hproj Hctx]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eprim_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat. eapply project_vars_free_set_Included; now eauto. 
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l. eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite <- subst_BoundVar_f_eq.
          rewrite Union_sym, <- Setminus_Union. now eapply image_Setminus_extend.
          rewrite !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Eprim_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eprim, occurs_free_Eprim. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst.
          edestruct (Hf' Hf) as [C' [Hctx' [Hcc Hf'']]]; eauto.
          do 2 eexists. eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor. eapply Disjoint_free_set in Minv.  
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| now apply HD1 ]. now apply Included_Union_l.
          eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eassumption ]. apply Included_Union_mon_r.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| now apply HD1 ]. do 3 apply Included_Union_mon_r.
          now apply Included_refl.
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eassumption.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - assert (Hincl : Included var (Union var (bound_var e) (occurs_free e))
                               (Union var (bound_var_fundefs (Fcons v t l e f5))
                                      (occurs_free_fundefs (Fcons v t l e f5)))).
      { rewrite bound_var_fundefs_Fcons.
        rewrite !Union_assoc,
        Union_sym with (s2 := FromList l), Union_sym with (s2 := bound_var e), <- !Union_assoc.
        apply Included_Union_compat. now apply Included_refl.
        eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e f5).
        econstructor. now eauto. apply Included_Union_compat. now apply Included_refl. 
        simpl. rewrite <- Union_assoc. apply Included_Union_compat. now apply Included_refl. 
        apply Included_Union_compat; [| now apply Included_refl ].
        now eapply name_in_fundefs_bound_var_fundefs. }
      eapply pre_post_mp_r. eapply bind_triple. now apply get_name_fresh.
      intros x s2. apply pre_uncurry_l. intros Hf1. 
      eapply pre_post_mp_l. eapply bind_triple.
      eapply H with (Scope := FromList l) (Funs := Funs) (FVs := FVs) (S := Setminus _ S (Singleton _ x)).
      + rewrite <- Union_Empty_set_r with (s := FromList l). eapply FVmapInv_add_params.
        eassumption.
      + eapply binding_in_map_antimon; [| eapply binding_in_map_add_params; eassumption ].
        rewrite Union_sym. rewrite Union_sym with (s1 := occurs_free_fundefs _).
        eapply occurs_free_in_fun. constructor. eauto.
      + intros x'. rewrite <- (@Union_Setminus _ _ _ _), Union_Included_Same_set. 
        eapply binding_not_in_map_add_params. eassumption.
        constructor. intros y Hc. inv Hc. eapply HD1. constructor; eauto. now right; eauto.
        intros x'' Hc; inv Hc. eapply Hf1. zify; omega.
      + rewrite !Union_assoc. apply Disjoint_sym. apply Disjoint_Union; apply Disjoint_sym.
        eapply Disjoint_Included_l. now apply Subset_Setminus.
        eapply Disjoint_Included_r; [| eassumption ]. rewrite <- !Union_assoc.
        apply Included_Union_compat. rewrite image_f_eq_subdomain.
        apply image_monotonic. now apply Subset_Setminus.
        apply subst_add_params_f_eq_subdomain. eapply Disjoint_sym. eapply Disjoint_Setminus.
        now apply Included_refl. eassumption.
        now eapply Disjoint_Setminus.
      + intros Hc. eapply HD1. inv Hc.
        constructor; [ | now eauto ]; eapply Hf1; zify; omega.
        constructor. eapply Hf1; zify; omega. right.
        eapply occurs_free_in_fun with (B := Fcons v t l e f5) in H1; [| econstructor; now eauto ].
        inv H1; eauto. inv H2; eauto. left. now eapply name_in_fundefs_bound_var_fundefs. 
      + intros [e' f] s3. eapply pre_post_mp_l. eapply bind_triple.
        eapply H0 with (S := Setminus _ S (Singleton _ x)); [ eassumption | | | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          simpl. rewrite Union_assoc. apply Included_Union_compat.
          now apply occurs_free_fundefs_Fcons_Included. now apply Included_refl.
        * eapply binding_not_in_map_antimon. now apply Subset_Setminus.
          eassumption.
        * eapply Disjoint_Included_l. now apply Subset_Setminus.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite bound_var_fundefs_Fcons. rewrite Union_sym with (s1 := Singleton var v).
          do 2 rewrite <- Union_assoc. rewrite Union_sym with (s1 := Singleton var v).
          apply Included_Union_mon_r. (* TODO lemma *)
          apply Included_Union_compat. now apply Included_Union_r.
          now apply occurs_free_fundefs_Fcons_Included.
        * eapply Included_trans; [| eassumption ]. now apply Included_Union_r.
        * intros B' s5.
          assert (Ha: exists v', Maps.PTree.get v FVmap = Some (MRFun v')).
          { destruct Minv as [_ [HM _]]. eapply HM. rewrite Setminus_Empty_set_Same_set.
            eapply Hinc. left; eauto. }
          destruct Ha as [v' Ha']. rewrite Ha'.
          eapply return_triple. intros s6 Hcc1 Hcc2 Hf. 
          edestruct (Hcc2 Hf) as [C1 [Hctx1 [Hcc1' Hf1']]].
          destruct (Hcc1 Hf1') as [Hcc2' Hf2'].
          split; [| eapply fresh_monotonic; [ now apply Subset_Setminus | eassumption ]].
          simpl. rewrite Hctx1.
          replace v' with ((subst FVmap) v) by (unfold subst; rewrite Ha'; reflexivity).
          econstructor; [| eassumption | eassumption |].
          eapply (Disjoint_Included_l _ _ S). intros x' Hx'. eapply Hx'. zify; omega.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          apply Included_Union_mon_l. rewrite bound_var_fundefs_Fcons.
          apply Included_Union_mon_r. apply Included_Union_compat. now apply Included_refl.
          now apply Included_Union_l.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          eapply subst_add_params_f_eq_subdomain.
          eapply Disjoint_sym. eapply Disjoint_Setminus. now apply Included_refl.
    - eapply return_triple. intros Hc _ Hf.
      split; [| eassumption ]. constructor.
  Qed.

End CC_correct.

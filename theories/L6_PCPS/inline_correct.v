Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Classes.Morphisms.
Require Import compcert.lib.Maps compcert.lib.Coqlib.
Require Import L6.cps L6.state L6.freshen L6.cps_util L6.cps_show L6.ctx L6.hoare L6.inline L6.rename L6.identifiers
        L6.Ensembles_util L6.alpha_conv L6.functions L6.logical_relations L6.tactics L6.eval L6.map_util.
Require Import Common.compM Common.Pipeline_utils Libraries.CpdtTactics Libraries.maps_util.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import Coq.Structures.OrdersEx.

Import MonadNotation.
Import ListNotations.
Open Scope monad_scope.
Open Scope ctx_scope.
Open Scope fun_scope.

Section Inline_Eq.
  
  Context (St : Type) (IH : InlineHeuristic St).
  
  Definition beta_contract' (d : nat) (e : exp) (sig : r_map) (fm:fun_map) (s:St) : inlineM exp :=
    match e with
    | Econstr x t ys e =>
      let ys' := apply_r_list sig ys in
      x' <- get_name x "" ;;
      e' <- beta_contract _ IH d e (M.set x x' sig) fm s;;
      ret (Econstr x' t ys' e')
    | Ecase v cl =>
      let v' := apply_r sig v in
      cl' <- (fix beta_list (br: list (ctor_tag*exp)) : inlineM (list (ctor_tag*exp)) :=
                match br with
                | nil => ret ( nil)
                | (t, e)::br' =>
                  e' <- beta_contract _ IH d e sig fm s;;
                  br'' <- beta_list br';;
                  ret ((t, e')::br'')
                end) cl;;
      ret (Ecase v' cl')
    | Eproj x t n y e =>
      let y' := apply_r sig y in
      x' <- get_name x "" ;;
      e' <- beta_contract _ IH d e (M.set x x' sig) fm s;;
      ret (Eproj x' t n y' e')
    | Eletapp x f t ys ec =>
      let f' := apply_r sig f in
      let ys' := apply_r_list sig ys in
      let (s' , inl) := update_letApp _ IH f' t ys' s in
      (match (inl, M.get f fm, d) with
       | (true, Some (t, xs, e), S d') =>
         let sig' := set_list (combine xs ys') sig  in            
         e' <- beta_contract _ IH d' e sig' fm s' ;;
         match inline_letapp e' x with
         | Some (C, x') =>
           ec' <- beta_contract _ IH d' ec (M.set x x' sig) fm s' ;;
           ret (C |[ ec' ]|)
         | None =>
           x' <- get_name x "" ;;
           ec' <- beta_contract _ IH d ec (M.set x x' sig) fm s' ;;
           ret (Eletapp x' f' t ys' ec')
         end
       | _ =>
         x' <- get_name x "" ;;
         ec' <- beta_contract _ IH d ec (M.set x x' sig) fm s' ;;
         ret (Eletapp x' f' t ys' ec')
       end)
    | Efun fds e =>
      let fm' := add_fundefs fds fm in
      let (s1, s2) := update_funDef _ IH fds sig s in
      let names := all_fun_name fds in
      names' <- get_names_lst names "" ;;
      let sig' := set_list (combine names names') sig in
      fds' <- (fix beta_contract_fds (fds:fundefs) (s:St) : inlineM fundefs :=
                 match fds with
                 | Fcons f t xs e fds' =>
                   let s' := update_inFun _ IH f t xs e sig s in
                   let f' := apply_r sig' f in
                   xs' <- get_names_lst xs "" ;;
                   e' <- beta_contract _ IH d e (set_list (combine xs xs') sig') fm' s' ;;
                   fds'' <- beta_contract_fds fds' s ;;
                   ret (Fcons f' t xs' e' fds'')
                 | Fnil => ret Fnil
                 end) fds s2 ;;
      e' <- beta_contract _ IH d e sig' fm' s1;;
      ret (Efun fds' e')
    | Eapp f t ys =>
      let f' := apply_r sig f in
      let ys' := apply_r_list sig ys in
      let (s', inl) := update_App _ IH f' t ys' s in
      (match (inl, M.get f fm, d) with
       | (true, Some (t, xs, e), S d') =>
         let sig' := set_list (combine xs ys') sig  in
         beta_contract _ IH d' e sig' fm  s'
       | _ => ret (Eapp f' t ys')
       end)
    | Eprim x t ys e =>
      let ys' := apply_r_list sig ys in
      x' <- get_name x "" ;;
      e' <- beta_contract _ IH d e (M.set x x' sig) fm s;;
      ret (Eprim x' t ys' e')
    | Ehalt x =>
      let x' := apply_r sig x in
      ret (Ehalt x')
    end.
  
  
  Lemma beta_contract_eq (d : nat) (e : exp) (sig : r_map) (fm:fun_map) (s:St) : 
    beta_contract _ IH d e sig fm s = beta_contract' d e sig fm s.
  Proof.
    destruct d; destruct e; try reflexivity.
  Qed.

End Inline_Eq. 

Opaque bind ret.

 
(** Spec for [get_name] *)
Lemma get_name_fresh A S y str :
  {{ fun _ (s : comp_data * A) => fresh S (next_var (fst s)) }}
    get_name y str
  {{ fun (r: unit) _ x s' =>
       x \in S /\ fresh (S \\ [set x]) (next_var (fst s')) }}.  
Proof. 
  eapply pre_post_mp_l.
  eapply bind_triple. now eapply get_triple.  
  intros [[] w1] [[] w2].
  eapply pre_post_mp_l. simpl.
  eapply bind_triple. now eapply put_triple.
  intros x [r3 w3].
  eapply return_triple. 
  intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
  split. eapply H. reflexivity. 
  simpl. intros z Hin. constructor. eapply H; eauto. zify. omega.
  intros Hc. inv Hc. zify; omega.
Qed.


Section Inline_correct.

  Context (St : Type) (IH : InlineHeuristic St) (cenv : ctor_env) (P1 : PostT) (PG : PostGT).


  Variable (HPost_con : post_constr_compat P1 P1)
           (HPost_proj : post_proj_compat P1 P1)
           (HPost_fun : post_fun_compat P1 P1)
           (HPost_case_hd : post_case_compat_hd P1 P1)
           (HPost_case_tl : post_case_compat_tl P1 P1)
           (HPost_app : post_app_compat P1 PG)
           (HPost_letapp : post_letapp_compat cenv P1 P1 PG)
           (HPost_letapp_OOT : post_letapp_compat_OOT P1 PG)
           (HPost_OOT : post_OOT P1)
           (Hpost_base : post_base P1)
           (HGPost : inclusion P1 PG)
           (Hpost_zero : forall e rho, post_zero e rho P1).

           (* (HPost_conG : post_constr_compat PG PG) *)
           (* (HPost_projG : post_proj_compat PG PG) *)
           (* (HPost_funG : post_fun_compat PG PG) *)
           (* (HPost_case_hdG : post_case_compat_hd PG PG) *)
           (* (HPost_case_tlG : post_case_compat_tl PG PG) *)
           (* (HPost_appG : post_app_compat PG PG) *)
           (* (HPost_letappG : post_letapp_compat cenv PG PG PG) *)
           (* (HPost_letapp_OOTG : post_letapp_compat_OOT PG PG) *)
           (* (HPost_OOTG : post_OOT PG) *)
           (* (Hpost_baseG : post_base PG) *)
           (* (Hless_steps_letapp : remove_steps_letapp cenv P1 P1 P1) *)
           (* (Hless_steps_letapp' : remove_steps_letapp' cenv P1 P1 P1) *)
           (* (Hless_steps_letapp_OOT : remove_steps_letapp_OOT cenv P1 P1) *)
           (* (Hless_steps_letapp_OOT' : remove_steps_letapp_OOT' cenv P1 P1) *)
           (* (Hpost_zero : forall e rho, post_zero e rho P1). *)

  Definition fun_map_fv (fm : fun_map) : Ensemble var :=
    fun v => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ v \in occurs_free e.

  Definition fun_map_bv (fm : fun_map) : Ensemble var :=
    fun v => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ v \in bound_var e.

  Definition funs_in_env (rho : env) : Ensemble var :=
    fun v => exists r B f, rho!v = Some (Vfun r B f).

  Definition occurs_free_in_val (v : val) : Ensemble var :=
    match v with
    | Vfun rho B f => occurs_free_fundefs B
    | _ => Empty_set _
    end.
    
  Definition occurs_free_in_env (rho : env) : Ensemble var :=
    fun v => exists x r B f, rho!x = Some (Vfun r B f) /\ v \in occurs_free_fundefs B.

  Definition fun_bindings_val (v : val) :=
    match v with
    | Vint _
    | Vconstr _ _ => Empty_set _ 
    | Vfun rho B _ => name_in_fundefs B :|: funs_in_env rho
    end.      

  Definition fun_bindings_env (rho : env) : Ensemble var :=
    fun f => exists x v, rho!x = Some v /\ f \in fun_bindings_val v.

  Lemma fun_bindings_env_set (rho : env) x v :
    fun_bindings_env (M.set x v rho) \subset fun_bindings_val v :|: fun_bindings_env rho.
  Proof.
    intros z Hin. unfold Ensembles.In, fun_bindings_env in *.
    destructAll. destruct (peq x x0); subst.
    - rewrite M.gss in H. inv H. now left; eauto.
    - rewrite M.gso in H; eauto. right. do 2 eexists. split; eauto.
  Qed.
  
  Lemma fun_bindings_env_set_lists (rho rho' : env) xs vs :
    set_lists xs vs rho = Some rho' ->    
    fun_bindings_env rho' \subset \bigcup_(v in FromList vs) (fun_bindings_val v) :|: fun_bindings_env rho.
  Proof.
    revert rho' vs. induction xs; intros rho' vs Hset; destruct vs; try now inv Hset.
    - inv Hset. normalize_sets. rewrite big_cup_Empty_set. sets.
    - normalize_sets. rewrite Union_big_cup.
      simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset'; inv Hset.
      eapply Included_trans. eapply fun_bindings_env_set.
      rewrite big_cup_Singleton. rewrite <- Union_assoc. eapply Included_Union_compat. now sets.
      eauto.
  Qed.
  
  Lemma fun_bindings_env_get (rho : env) x v :
    rho ! x = Some v ->
    fun_bindings_val v \subset fun_bindings_env rho.
  Proof.
    intros Hget z Hin. do 2 eexists. split. eassumption. eassumption.
  Qed.

  Lemma fun_bindings_env_get_list (rho : env) xs vs :
    get_list xs rho = Some vs ->
    \bigcup_(v in FromList vs) (fun_bindings_val v) \subset fun_bindings_env rho.
  Proof.
    revert vs. induction xs; intros vs Hget.
    - destruct vs; try now inv Hget. normalize_sets. rewrite big_cup_Empty_set. sets.
    - simpl in Hget. destruct (rho!a) eqn:Hgeta; try now inv Hget.
      destruct (get_list xs rho) eqn:Hgetl; try now inv Hget. inv Hget.
      normalize_sets. rewrite Union_big_cup. rewrite big_cup_Singleton.
      eapply Union_Included; eauto.
      eapply fun_bindings_env_get. eassumption.
  Qed.

  Lemma fun_bindings_env_def_funs (rho rhoc : env) B0 B :
    fun_bindings_env (def_funs B0 B rhoc rho) \subset name_in_fundefs B0 :|: funs_in_env rhoc :|: fun_bindings_env rho.
  Proof.
    revert rho; induction B; intros rho x HIn. simpl in HIn.
    - eapply fun_bindings_env_set in HIn. simpl in HIn. inv HIn; eauto.
      eapply IHB. eassumption.
    - simpl in HIn. now right.
  Qed.

  Fixpoint fun_map_inv' (k : nat) (S : Ensemble var) (fm : fun_map) (rho : env) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      eq_env_P (occurs_free_fundefs B) rho rhoc /\      
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free_fundefs B) fm (def_funs B B rhoc rhoc)
      end.

  Definition fun_map_inv (k : nat) (S : Ensemble var) (fm : fun_map) (rho : env) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      eq_env_P (occurs_free_fundefs B) rho rhoc /\      
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free_fundefs B) fm (def_funs B B rhoc rhoc)
      end.
    
  Lemma fun_map_inv_eq k fm rho :
    fun_map_inv k fm rho = fun_map_inv' k fm rho.
  Proof.
    destruct k; reflexivity.
  Qed.
  
  Lemma fun_map_inv_mon k k' S fm rho :
    fun_map_inv k S fm rho ->
    (k' <= k)%nat ->
    fun_map_inv k' S fm rho.
  Proof.
    revert S k fm rho. induction k' as [k' IHk] using lt_wf_rec1; intros.
    destruct k'.
    - unfold fun_map_inv in *. intros. edestruct H as [Hf [Heq [Heq' Hm]]]; eauto. 
    - destruct k; [ omega | ].
      intro; intros. edestruct H as [Hf [Heq [Heq' Hm]]]; eauto. 
      split; eauto. split; eauto. split; eauto. rewrite <- fun_map_inv_eq. eapply IHk. 
      omega. rewrite fun_map_inv_eq. eassumption. omega. 
  Qed.
  
  Lemma fun_map_inv_set k S fm rho x v :
    fun_map_inv k S fm rho ->
    ~ x \in Dom_map fm :|: occurs_free_in_env rho  ->
    fun_map_inv k (x |: S) fm (M.set x v rho).           
  Proof.
    intros Hinv Hnin. intro; intros.
    rewrite M.gso in *.
    2:{ intros Heq; subst. eapply Hnin. left. eexists; eauto. }
    inv H.
    - inv H2. exfalso. eapply Hnin. left. eexists; eauto.
    - edestruct Hinv; eauto.
      destructAll. split; [| split; [| split ]]; eauto.
      eapply eq_env_P_set_not_in_P_l. eassumption.
      intros Hc. eapply Hnin. right. do 4 eexists. split; eauto.    
  Qed.

  (* Lemma occurs_free_in_env_set_compat rho rho' x v : *)
  (*   occurs_free_in_env rho' \subset occurs_free_in_env rho -> *)
  (*   occurs_free_in_env (M.set x v rho') \subset occurs_free_in_env (M.set x v rho). *)
  (* Proof. *)
  (*   intros Hc z [y Hin]. destructAll. *)
  (*   destruct (peq x y); subst. *)
  (*   - rewrite M.gss in H. inv H.  *)
  (*     do 4 eexists; split; eauto. rewrite M.gss. reflexivity. *)
  (*   - rewrite M.gso in H; eauto. edestruct Hc. now do 4 eexists; split; eauto. *)
  (*     destructAll. do 4 eexists; split; eauto. rewrite M.gso. eassumption. reflexivity. *)
  (*   rewrite M.gso. eassumption. *)
  (*   intros Hd. eapply Hc. subst. eexists. eassumption. *)
  (* Qed. *)
      
  Lemma occurs_free_in_env_set rho x v :
    occurs_free_in_env (M.set x v rho) \subset occurs_free_in_val v :|: occurs_free_in_env rho.
  Proof.
    intros z [y Hin]. destructAll. destruct (peq x y); subst.
    - rewrite M.gss in H. inv H. now left; eauto.
    - rewrite M.gso in H; eauto. right.
      do 4 eexists; split; eauto.
  Qed.

  Lemma occurs_free_in_env_set_lists_not_In rho rho' xs vs :
    set_lists xs vs rho = Some rho' ->
    occurs_free_in_env rho' \subset \bigcup_(v in FromList vs) (occurs_free_in_val v) :|: occurs_free_in_env rho.
  Proof.
    revert rho' vs. induction xs; intros rho' vs Hset; destruct vs; try now inv Hset.
    - inv Hset. normalize_sets. rewrite big_cup_Empty_set. sets.
    - normalize_sets. rewrite Union_big_cup.
      simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset'; inv Hset.
      eapply Included_trans. eapply occurs_free_in_env_set.
      rewrite big_cup_Singleton. rewrite <- Union_assoc. eapply Included_Union_compat. now sets.
      eauto.
  Qed.

  Instance fm_map_Proper k : Proper (Same_set _ ==> eq ==> eq ==> iff) (fun_map_inv k).
  Proof.
    repeat (intro; intros). subst. split; intros.
    intro; intros. rewrite <- H in H1. eauto.
    intro; intros. rewrite H in H1. eauto.
  Qed.
  
  Lemma fun_map_inv_set_lists k S fm rho rho' xs vs :
    fun_map_inv k S fm rho ->
    \bigcup_(v in FromList vs) (occurs_free_in_val v) \subset occurs_free_in_env rho ->
    Disjoint _ (FromList xs) (Dom_map fm :|: occurs_free_in_env rho) ->
    set_lists xs vs rho = Some rho' ->
    fun_map_inv k (FromList xs :|: S) fm rho'.
  Proof.
    revert S rho rho' vs; induction xs; intros S rho rho' vs Hfm Hs Hdis Hset.
    - destruct vs; inv Hset; eauto. repeat normalize_sets. eauto.
    - destruct vs; try now inv Hset. simpl in Hset.
      destruct (set_lists xs vs rho) eqn:Hset'; inv Hset.
      repeat normalize_sets. rewrite <- Union_assoc. eapply fun_map_inv_set.
      eapply IHxs; eauto.
      + eapply Included_trans; [| eassumption ]. eapply Included_big_cup. reflexivity.
        sets.
      + sets.
      + intros Hc. eapply Hdis. constructor. now left. inv Hc; eauto.
        eapply occurs_free_in_env_set_lists_not_In in H; [| now eauto ]. inv H; eauto.
        right. eapply Hs. eapply Included_big_cup; [| | eassumption ]. reflexivity. sets.
  Qed.
  
  Lemma add_fundefs_in fm f B ft xs e:
    find_def f B = Some (ft, xs, e) -> 
    (add_fundefs B fm) ! f = Some (ft, xs, e). 
  Proof.
    induction B.
    - simpl. intros Hdef. destruct (M.elt_eq f v); subst.
      + inv Hdef. simpl. rewrite M.gss. reflexivity.
      + simpl. rewrite M.gso; eauto.
    - intros H. inv H.
  Qed.

  Lemma add_fundefs_not_in fm f B :
    ~ f \in name_in_fundefs B -> 
    (add_fundefs B fm) ! f = fm ! f.
  Proof.
    intros Hnin. induction B.
    - simpl. rewrite M.gso. eapply IHB.
      intros Hc. eapply Hnin. simpl. now right; eauto.
      intros Hc. eapply Hnin. simpl. subst; eauto.
    - reflexivity.
  Qed.

  Lemma Dom_map_add_fundefs fm B :
    Dom_map (add_fundefs B fm) <--> name_in_fundefs B :|: Dom_map fm.
  Proof.
    induction B; simpl; [| now sets ].
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.

  Lemma fun_map_inv_def_funs k fm rho B :
    fun_map_inv k fm rho ->
    Disjoint _ (name_in_fundefs B) (fun_bindings_env rho) ->
    fun_map_inv k (add_fundefs B fm) (def_funs B B rho rho).
  Proof.
    revert fm rho B. induction k as [k IHk] using lt_wf_rec1. intros fm rho B Hf Hdis.
    intros f ft xs e rhoc B' f' Heq1 Heq2.  
    destruct (Decidable_name_in_fundefs B) as [Dec]. destruct (Dec f).
    - rewrite def_funs_eq in Heq2; eauto. inv Heq2.
      edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in Heq1; [| eassumption ]. inv Heq1. split; eauto.
      split; eauto. destruct k; eauto. rewrite <- fun_map_inv_eq. eapply IHk. omega.
      eapply fun_map_inv_mon. eassumption. omega.
      eassumption.
    - rewrite def_funs_neq in Heq2; eauto.
      rewrite add_fundefs_not_in in Heq1; [| eassumption ].
      edestruct Hf. eassumption. eassumption. destructAll. split; eauto. split; eauto. 
      destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      assert (Hdis' : Disjoint _ (name_in_fundefs B) (name_in_fundefs B' :|: funs_in_env rhoc)).
      { eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_trans; [| eapply fun_bindings_env_get ]; [| eassumption ].
        reflexivity. }      
      clear Dec H Hf Heq2 Hdis. 
      revert rhoc B' B n H1 Hdis'. induction k as [k IHk2] using lt_wf_rec1; intros.
      intro; intros.
      rewrite add_fundefs_not_in in H; eauto. 
      edestruct H1. eassumption. eassumption. destructAll. split; eauto. split; eauto.
      destruct k; eauto. rewrite <- fun_map_inv_eq in *. 
      eapply IHk2. omega. now eauto. eassumption. eassumption. admit. eassumption. 
      { intros Hc.
        eapply Hdis. constructor. eassumption. SearchAbout rho.
        destruct (Decidable_name_in_fundefs B') as [Dec]. destruct (Dec f).
        

        intros Hin. eapply Hdis. constructor. eassumption. eapply H1. eassumption.
  Qed.

(*   
  Definition fun_map_inv (fm : fun_map) (rho : env) (* (sig : subst) *) :=
    forall f ft xs e,
      fm ! f = Some (ft, xs, e) ->
      exists rhoc B, rho ! f = Some (Vfun rhoc B f) /\
                     find_def f B = Some (ft, xs, e) /\
                     (forall g, g \in name_in_fundefs B ->
                                rho ! g = Some (Vfun rhoc B g) /\ g \in Dom_map fm).
  
  Lemma fun_map_inv_set fm rho x v :
    fun_map_inv fm rho ->
    ~ x \in Dom_map fm ->
    fun_map_inv fm (M.set x v rho).           
  Proof.
    intros Hinv Hnin f ft xs e Hget.
    rewrite M.gso.
    - eapply Hinv in Hget. destructAll. do 2 eexists. split; eauto. split; eauto.
      intros. rewrite M.gso. eauto. intro; subst. eapply H1 in H2.
      inv H2. contradiction.
    - intros Heq; subst. eapply Hnin.
      eexists; eauto.
  Qed.
    
  Lemma fun_map_inv_set_lists fm rho rho' xs vs :
    fun_map_inv fm rho ->
    Disjoint _ (FromList xs) (Dom_map fm) ->
    set_lists xs vs rho = Some rho' ->
    fun_map_inv fm rho'.
  Proof.
    revert rho rho' vs; induction xs; intros rho rho' vs Hfm Hdis Hset.
    - destruct vs; inv Hset; eauto.
    - destruct vs; try now inv Hset. simpl in Hset.
      destruct (set_lists xs vs rho) eqn:Hset'; inv Hset.
      repeat normalize_sets.
      eapply fun_map_inv_set. eapply IHxs; eauto.
      now sets. intros Hc. eapply Hdis. constructor. now left.
      eassumption.
  Qed.
  
  Lemma add_fundefs_in fm f B ft xs e:
    find_def f B = Some (ft, xs, e) -> 
    (add_fundefs B fm) ! f = Some (ft, xs, e). 
  Proof.
    induction B.
    - simpl. intros Hdef. destruct (M.elt_eq f v); subst.
      + inv Hdef. simpl. rewrite M.gss. reflexivity.
      + simpl. rewrite M.gso; eauto.
    - intros H. inv H.
  Qed.

  Lemma add_fundefs_not_in fm f B :
    ~ f \in name_in_fundefs B -> 
    (add_fundefs B fm) ! f = fm ! f.
  Proof.
    intros Hnin. induction B.
    - simpl. rewrite M.gso. eapply IHB.
      intros Hc. eapply Hnin. simpl. now right; eauto.
      intros Hc. eapply Hnin. simpl. subst; eauto.
    - reflexivity.
  Qed.

  Lemma Dom_map_add_fundefs fm B :
    Dom_map (add_fundefs B fm) <--> name_in_fundefs B :|: Dom_map fm.
  Proof.
    induction B; simpl; [| now sets ].
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.

  Lemma fun_map_inv_def_funs fm rho B :
    fun_map_inv fm rho ->
    Disjoint _ (name_in_fundefs B) (Dom_map fm) ->
    fun_map_inv (add_fundefs B fm) (def_funs B B rho rho).
  Proof.
    intros Hf Hd. intros f ft xs e Hget.
    destruct (Decidable_name_in_fundefs B) as [Dec]. destruct (Dec f).
    - do 2 eexists. split; [| split; [| split ]].
      + eapply def_funs_eq in n. eassumption.
      + edestruct name_in_fundefs_find_def_is_Some. eassumption.
        destructAll. rewrite H. eapply add_fundefs_in in H. rewrite H in Hget.
        inv Hget. reflexivity.
      + rewrite def_funs_eq. reflexivity. eassumption.
      + rewrite Dom_map_add_fundefs. sets.
    - rewrite add_fundefs_not_in in Hget; [| eassumption ]. rewrite def_funs_neq; eauto.
      eapply Hf in Hget. destructAll. do 2 eexists. split; eauto. split; eauto.
      intros. rewrite def_funs_neq; eauto. split; eauto. eapply H1. eassumption.
      rewrite Dom_map_add_fundefs. right. eapply H1; eauto.
      intros Hin. eapply Hd. constructor. eassumption. eapply H1. eassumption.
  Qed.
*)
  (* Lemma fun_map_inv_redef_funs fm rho B ft xs e rhoc f  : *)
  (*   fun_map_inv fm rho -> *)
  (*   fm ! f = Some (ft, xs, e) -> *)
  (*   rho ! f = Some (Vfun rhoc B f) -> *)
  (*   fun_map_inv fm (def_funs B B rho rho). *)
  (* Proof. *)
  (*   intros Hf Hg1 Hg2. intros g ft' xs' e' Hget. *)
  (*   destruct (Decidable_name_in_fundefs B) as [Dec]. destruct (Dec g). *)
  (*   - assert (Hg1' := Hg1). eapply Hf in Hg1. destructAll.  *)
  (*     rewrite Hg2 in H. inv H. erewrite def_funs_eq; eauto. *)
  (*     do 2 eexists. split. reflexivity. *)
  (*     eapply H1 in n. destructAll. destruct H2. destruct x1 as [[? ? ] ?]. rewrite Hget in H2; inv H2.  *)
  (*     eapply Hf in Hget. destructAll. rewrite H2 in H. inv H. split. eassumption. *)
  (*     intros. rewrite def_funs_eq; eauto. split. reflexivity. eapply H4. eassumption. *)
  (*   - rewrite def_funs_neq; eauto. *)
  (*     eapply Hf in Hget. destructAll. do 2 eexists. split; eauto. split; eauto. *)

  (*     intros g1 Hc. destruct (Decidable_name_in_fundefs B) as [Dec']. destruct (Dec' g1). clear Dec Dec'. *)
  (*     + eapply Hf in Hg1. destructAll. repeat subst_exp.  *)
  (*       eapply H4 in n0. destructAll.  *)
  (*       eapply H1 in Hc. destructAll. repeat subst_exp.  *)
  (*       rewrite def_funs_eq; eauto. *)
        
  (*       split. reflexivity. *)
  (*     repeat subst_exp. do 10 subst_exp.  *)
      (*   destruct (Decidable_name_in_fundefs B) as [Dec]. destruct (Dec f). *)
  (*   - do 3 eexists. split. *)
  (*     + eapply def_funs_eq in n. eassumption. *)
  (*     + edestruct name_in_fundefs_find_def_is_Some. eassumption. *)
  (*       destructAll. rewrite H. eapply add_fundefs_in in H. rewrite H in Hget. *)
  (*       inv Hget. reflexivity. *)
  (*   - rewrite add_fundefs_not_in in Hget; [| eassumption ]. rewrite def_funs_neq; eauto. *)
  (* Qed. *)
  (* Abort. *)
  
  Opaque preord_exp'.
  
  Lemma inline_correct d e sig fm st S :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    Disjoint _ S (bound_var e :|: image (apply_r sig) (occurs_free e)) ->
    Disjoint _ (Dom_map fm) (bound_var e) ->       
    {{ fun _ s => fresh S (next_var (fst s)) }}
      beta_contract St IH d e sig fm st
    {{ fun _ _ e' s' =>
         fresh S (next_var (fst s')) /\
         (* unique bindings is preserved *)
         unique_bindings e' /\
         occurs_free e' \subset image (apply_r sig) (occurs_free e) /\
         bound_var e' \subset S /\
         (* Disjointedness is preserved *)
         (* Disjoint _ (bound_var e') (occurs_free e') /\ *)
         (* FV are preserved *)
         (* semantics are preserved *)
         (forall rho1 rho2 k,
             preord_env_P_inj cenv PG (occurs_free e) k (apply_r sig) rho1 rho2 ->
             fun_map_inv fm rho1 ->
             preord_exp cenv P1 PG k (e, rho1) (e', rho2))

    }}.
  Proof.
    revert e sig fm st S. induction d as [d IHd] using lt_wf_rec1.
    induction e using exp_ind'; intros sig fm st S Hun Hdis1 Hdis2 Hdis3; inv Hun; rewrite beta_contract_eq.
    - (* constr *)
      eapply bind_triple. now eapply get_name_fresh. 
      intros x w1. eapply pre_curry_l. intros Hinx.
      eapply bind_triple. eapply IHe with (S := S \\ [set x]).
      + eassumption. 
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1]; now sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply Included_Union_compat. reflexivity.
        eapply image_apply_r_set. 
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ]. rewrite image_Union. now sets.
        now sets.
      + repeat normalize_bound_var_in_ctx. sets.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf [Hun [Hsub [Hsub' Hsem]]]].
        split; [| split; [| split; [| split ]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * constructor.
          intros Hc. eapply Hsub' in Hc. now inv Hc; eauto. eassumption. 
        * repeat normalize_occurs_free. rewrite image_Union.
          rewrite <- FromList_apply_list. eapply Included_Union_compat. reflexivity. 
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption. now sets.
          eapply Singleton_Included. eassumption.
        * intros r1 r2 k Henv Hfm. eapply preord_exp_const_compat.
          admit. admit. admit.
          intros. eapply Hsem. 
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free. sets.
          -- rewrite preord_val_eq. split. reflexivity.
             eapply Forall2_Forall2_asym_included. eassumption.
          -- intros Hc. eapply Hdis2. constructor. eassumption.
             right. normalize_occurs_free. rewrite image_Union. right. eassumption.
          -- eapply fun_map_inv_set. eassumption.
             eapply Disjoint_Singleton_In. tci. repeat normalize_bound_var_in_ctx. sets.
    - (* Ecase [] *)
      admit.
    - (* Ecase (_ :: _) *)
      admit.
    - (* Eproj *)
      admit.
    - (* Eletapp *)
      admit.
    - (* Efun *)
      admit.
    - (* Eapp *)
      simpl. destruct (update_App St IH (apply_r sig v) t (apply_r_list sig l) st) as [s b] eqn:Hup. 
      + destruct b.
        * destruct (fm ! v) as [[[ft xs] e] |] eqn:Heqf.
          destruct d.
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split ]]]; try eassumption.
             ++ constructor.
             ++ simpl. repeat normalize_occurs_free. rewrite image_Union, image_Singleton.
                rewrite FromList_apply_list. reflexivity.
             ++ normalize_bound_var. sets.
             ++ intros. eapply preord_exp_app_compat.
                assumption. assumption.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.
          -- eapply post_weakening; [| eapply IHd ].
             ++ simpl. intros. destructAll. 
                split; [| split; [| split; [| split ]]]; try eassumption.
                ** eapply Included_trans. eassumption.
                   (* eapply Included_trans. eapply image_apply_r_set_list.  eassumption.  *)
                   admit. (* change FV subset to include fvs in fm *)
                ** intros. eapply preord_exp_app_l.
                   --- admit.
                   --- admit. 
                   --- intros. assert (Heqf' := Heqf). eapply H6 in Heqf. destructAll.
                       do 2 subst_exp. eapply H4.
                       admit. 
                       eapply fun_map_inv_set_lists.
                       eapply  fun_map_inv_def_funs.
                       eassumption.
                       admit.
                       (* eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ]. *)
                       
                       normalize_bound_var. 
                       H4. 
                normalize_occurs_free; sets.
             split.
             
      simpl. 
       eapply bind_triple.
          pre
          reflexivity. 
        rewrite Union_Setminus with (S1 := occurs_free e) (S2 := [set v]).
        2:{ 

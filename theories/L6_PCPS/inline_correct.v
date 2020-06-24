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

  Definition beta_contract_fundefs (d : nat) (sig sig' : subst) (fm' : fun_map) :=
    (fix beta_contract_fds (fds:fundefs) (s:St) : inlineM fundefs :=
       match fds with
       | Fcons f t xs e fds' =>
         let s' := update_inFun _ IH f t xs e sig s in
         let f' := apply_r sig' f in
         xs' <- get_names_lst xs "" ;;
         e' <- beta_contract _ IH d e (set_list (combine xs xs') sig') fm' s' ;;
         fds'' <- beta_contract_fds fds' s ;;
         ret (Fcons f' t xs' e' fds'')
       | Fnil => ret Fnil
       end).
  
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
         match inline_letapp e' x, Nat.eqb (List.length xs) (List.length ys) with
         | Some (C, x'), true =>
           ec' <- beta_contract _ IH d' ec (M.set x x' sig) fm s' ;;
           ret (C |[ ec' ]|)
         | _, _ =>
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
      fds' <-  beta_contract_fundefs d sig sig' fm' fds s2 ;;
      e' <- beta_contract _ IH d e sig' fm' s1;;
      ret (Efun fds' e')
    | Eapp f t ys =>
      let f' := apply_r sig f in
      let ys' := apply_r_list sig ys in
      let (s', inl) := update_App _ IH f' t ys' s in
      (match (inl, M.get f fm, d) with
       | (true, Some (ft, xs, e), S d') =>
         if Nat.eqb (List.length xs) (List.length ys) then
           let sig' := set_list (combine xs ys') sig  in
           beta_contract _ IH d' e sig' fm  s'
         else ret (Eapp f' t ys')
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

Lemma get_names_lst_fresh A S ns str :
  {{ fun _ (s : comp_data * A) => fresh S (next_var (fst s)) }}
     get_names_lst ns str
  {{ fun (r: unit) _ xs s' =>
       FromList xs \subset S /\ NoDup xs /\ fresh (S \\ FromList xs) (next_var (fst s')) }}.  
Proof.
  unfold get_names_lst. revert S; induction ns; intros S.
  - simpl. eapply return_triple.
    intros. repeat normalize_sets. split; eauto. sets. split; eauto.
    now constructor.
  - simpl. eapply bind_triple. eapply get_name_fresh.
    intros x w. eapply pre_curry_l. intros Hin.
    eapply bind_triple. eapply IHns.
    intros xs w'. eapply return_triple. intros. destructAll.
    repeat normalize_sets. split; [| split ].
    + eapply Union_Included. now sets. eapply Included_trans. eassumption. sets.
    + constructor; eauto. intros hc. eapply H. eassumption. sets.
    + rewrite <- Setminus_Union. eassumption.
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
    | Vfun rho B f => occurs_free_fundefs B :|: name_in_fundefs B
    | _ => Empty_set _
    end.
    
  Definition occurs_free_in_env (rho : env) : Ensemble var :=
    fun v => exists x r B f, rho!x = Some (Vfun r B f) /\ v \in occurs_free_fundefs B :|: name_in_fundefs B.

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

  Fixpoint fun_map_inv' (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (name_in_fundefs B :|: occurs_free_fundefs B) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      sub_map (def_funs B B rhoc rhoc) rho1 /\
      Disjoint _ (bound_var e) (name_in_fundefs B :|: FromList xs :|: occurs_free_in_env rho1 :|: Dom_map rhoc) /\
      Disjoint _ (FromList xs) (name_in_fundefs B :|: occurs_free_in_env rho1 :|: Dom_map rhoc :|: Dom_map fm) /\
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free_in_env rho1) fm (def_funs B B rhoc rhoc) rho2 i sig
      end.

  Definition fun_map_inv (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (name_in_fundefs B :|: occurs_free_fundefs B) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      sub_map (def_funs B B rhoc rhoc) rho1 /\
      Disjoint _ (bound_var e) (name_in_fundefs B :|: FromList xs :|: occurs_free_in_env rho1 :|: Dom_map rhoc) /\
      Disjoint _ (FromList xs) (name_in_fundefs B :|: occurs_free_in_env rho1 :|: Dom_map rhoc :|: Dom_map fm) /\
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free_in_env rho1) fm (def_funs B B rhoc rhoc) rho2 i sig
      end.

  Lemma fun_map_inv_eq k S fm rho1 rho2 n sig :
    fun_map_inv k S fm rho1 rho2 n sig = fun_map_inv' k S fm rho1 rho2 n sig.
  Proof.
    destruct k; reflexivity.
  Qed.
  
  Lemma fun_map_inv_mon k k' S fm rho1 rho2 i sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    (k' <= k)%nat ->
    fun_map_inv k' S fm rho1 rho2 i sig.
  Proof.
    revert S k fm rho1 rho2 i sig. induction k' as [k' IHk] using lt_wf_rec1; intros.
    destruct k'.
    - unfold fun_map_inv in *. intros. edestruct H; eauto. destructAll.
      repeat (split; eauto).
    - destruct k; [ omega | ].
      intro; intros. edestruct H; eauto. destructAll. 
      split; eauto. split; eauto. split; eauto. split; eauto. split; eauto. split; eauto.
      rewrite <- fun_map_inv_eq. eapply IHk. 
      omega. rewrite fun_map_inv_eq. eassumption. omega. 
  Qed.

  Lemma fun_map_inv_i_mon k S fm rho1 rho2 i i' sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    (i' <= i)%nat ->
    fun_map_inv k S fm rho1 rho2 i' sig.
  Proof.
    revert k S fm rho1 rho2 i i' sig. induction k as [k' IHk] using lt_wf_rec1; intros.
    intros. intro; intros. edestruct H; eauto. destructAll. split; eauto. split; eauto. split; eauto. 
    eapply preord_env_P_inj_monotonic; eassumption.
    split; eauto. split; eauto. split; eauto.
    destruct k'; eauto. rewrite <- fun_map_inv_eq in *. eapply IHk; eauto.
  Qed.

  Lemma fun_map_inv_antimon k S S' fm rho1 rho2 i sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    S' \subset S ->
    fun_map_inv k S' fm rho1 rho2 i sig.
  Proof.
    intros H1 H2. intro; intros; eauto.
  Qed.

  Lemma sub_map_set {A} rho x (v : A) :
    ~ x \in Dom_map rho ->
    sub_map rho (M.set x v rho).
  Proof.
    intros Hnin z1 v1 Hget1. rewrite M.gso; eauto.
    intros hc. subst. eapply Hnin. eexists; eauto.
  Qed.

  Lemma sub_map_trans {A} (rho1 rho2 rho3 : M.t A) :
    sub_map rho1 rho2 ->
    sub_map rho2 rho3 ->
    sub_map rho1 rho3.
  Proof.
    intros H1 H2 x v Hget. eauto.
  Qed.

  Lemma sub_map_refl {A} (rho : M.t A) :
    sub_map rho rho.
  Proof.
    intro; intros; eauto.
  Qed.

  Lemma occurs_free_in_env_set rho x v :
    occurs_free_in_env (M.set x v rho) \subset occurs_free_in_val v :|: occurs_free_in_env rho.
  Proof.
    intros z [y Hin]. destructAll. destruct (peq x y); subst.
    - rewrite M.gss in H. inv H. now left; eauto.
    - rewrite M.gso in H; eauto. right.
      do 4 eexists; split; eauto.
  Qed.

  Lemma occurs_free_in_env_get rho x v :
    M.get x rho = Some v ->
    occurs_free_in_val v \subset occurs_free_in_env rho.
  Proof.
    intros Hget z Hin.
    destruct v; try now inv Hin.
    do 4 eexists; split; eauto.
  Qed.
  
  Lemma occurs_free_in_env_get_list (rho : env) xs vs :
    get_list xs rho = Some vs ->
    \bigcup_(v in FromList vs) (occurs_free_in_val v) \subset occurs_free_in_env rho.
  Proof.
    revert vs. induction xs; intros vs Hget.
    - destruct vs; try now inv Hget. normalize_sets. rewrite big_cup_Empty_set. sets.
    - simpl in Hget. destruct (rho!a) eqn:Hgeta; try now inv Hget.
      destruct (get_list xs rho) eqn:Hgetl; try now inv Hget. inv Hget.
      normalize_sets. rewrite Union_big_cup. rewrite big_cup_Singleton.
      eapply Union_Included; eauto.
      eapply occurs_free_in_env_get. eassumption.
  Qed.

  
  Lemma occurs_free_in_env_def_funs B rho:
    occurs_free_in_env (def_funs B B rho rho) \subset occurs_free_fundefs B :|: name_in_fundefs B :|: occurs_free_in_env rho.
  Proof.
    intros x1 Hin1. inv Hin1. destructAll.
    destruct (Decidable_name_in_fundefs B). destruct (Dec x).
    + rewrite def_funs_eq in H; eauto. inv H. now left; eauto.
    + rewrite def_funs_neq in H; eauto. right. eapply occurs_free_in_env_get. eassumption.
      eassumption.
  Qed.
  
  Lemma occurs_free_in_env_def_funs' B rho:
    occurs_free_fundefs B :|: name_in_fundefs B \subset occurs_free_in_env (def_funs B B rho rho).
  Proof.
    intros x Hc. destruct B.
    - eapply occurs_free_in_env_get. simpl. rewrite M.gss. reflexivity. simpl. eassumption.
    - inv Hc. inv H. inv H.
  Qed.

  Lemma sub_map_occurs_free_in_env rho1 rho2 :
    sub_map rho1 rho2 ->
    occurs_free_in_env rho1 \subset occurs_free_in_env rho2.
  Proof.
    intros Hs z Hin. inv Hin. destructAll.
    eapply Hs in H. do 4 eexists. split. eassumption. eassumption.
  Qed.

  Lemma fun_map_inv_set_not_In_r k S fm rho1 rho2 i sig x x' v' : 
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in occurs_free_in_env rho1 ->
    ~ x' \in image (apply_r sig) (occurs_free_in_env rho1) ->
    fun_map_inv k S fm rho1 (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    revert S fm rho1 rho2 i sig x x' v'. induction k using lt_wf_rec1; intros. intro; intros.
    edestruct H0; eauto.
    destructAll. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
    - rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
      + intros Hc. eapply H1.   
        eapply occurs_free_in_env_get. eassumption. simpl. now inv Hc; eauto.
      + intros Hc. eapply H2. eapply image_monotonic; [| eassumption ]. 
        eapply Included_trans; [| eapply occurs_free_in_env_get; eauto ]. simpl. sets.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. omega. eassumption.
      + intros Hc. eapply H1.
        eapply sub_map_occurs_free_in_env. eassumption. eassumption.
      + intros Hc. eapply H2. eapply image_monotonic; [| eassumption ].
        eapply sub_map_occurs_free_in_env. eassumption.
  Qed.                
    
  Lemma fun_map_inv_set k S fm rho1 rho2 i sig x v x' v' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in Dom_map rho1 :|: Dom_map fm :|: occurs_free_in_env rho1 ->
    ~ x' \in image (apply_r sig) (occurs_free_in_env rho1) ->
    occurs_free_in_val v \subset occurs_free_in_env rho1 ->
    fun_map_inv k (x |: S) fm (M.set x v rho1) (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    intros Hinv Hnin Hnin' Hsub. intro; intros.
    rewrite M.gso in *.
    2:{ intros Heq; subst. eapply Hnin. left. right. eexists; eauto. }
    inv H.
    - inv H2. exfalso. eapply Hnin. left. left. eexists; eauto.
    - edestruct Hinv; eauto.
      destructAll. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
        intros Hc. eapply Hnin.  
        right. eapply occurs_free_in_env_get. eassumption. simpl. now inv Hc; eauto.
        intros Hc. eapply Hnin'. eapply image_monotonic; [| eassumption ]. 
        eapply Included_trans; [| eapply occurs_free_in_env_get; eauto ]. simpl. sets.
      + eapply sub_map_trans. eassumption. eapply sub_map_set.
        intros Hc. eapply Hnin. left. left. eassumption.
      + eapply Union_Disjoint_r; [| now sets ].
        eapply Union_Disjoint_r; [ now sets | ]. eapply Disjoint_Included_r. eapply occurs_free_in_env_set.
        rewrite Union_Same_set. sets. eassumption. 
      + eapply Union_Disjoint_r; [| now sets ]. eapply Union_Disjoint_r; [| now sets ].
        eapply Union_Disjoint_r; [ now sets | ]. eapply Disjoint_Included_r. eapply occurs_free_in_env_set.
        rewrite Union_Same_set. sets. eassumption.         
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
        eapply fun_map_inv_set_not_In_r. eapply fun_map_inv_antimon. eassumption.
        * eapply Included_trans. eapply occurs_free_in_env_set. sets.
        * intros Hc. eapply Hnin. right. eapply sub_map_occurs_free_in_env; eassumption.
        * intros Hc. eapply Hnin'. eapply image_monotonic; [| eassumption ].
          eapply sub_map_occurs_free_in_env; eassumption.
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

  Instance fm_map_Proper k : Proper (Same_set _ ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) (fun_map_inv k).
  Proof.
    repeat (intro; intros). subst. split; intros.
    intro; intros. rewrite <- H in H1. eauto.
    intro; intros. rewrite H in H1. eauto.
  Qed.

  Lemma Dom_map_set_lists {A} xs (vs : list A) rho rho' :
    set_lists xs vs rho = Some rho' ->
    Dom_map rho' <--> FromList xs :|: Dom_map rho.
  Proof.
    revert vs rho'. induction xs; intros vs rho' Hset.
    - destruct vs; inv Hset. repeat normalize_sets. reflexivity.
    - destruct vs; try now inv Hset.
      simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset1; inv Hset.
      repeat normalize_sets. rewrite Dom_map_set. rewrite IHxs. now sets.
      eassumption.
  Qed.

  Lemma sub_map_set_lists {A} rho rho' xs (vs : list A) :
    set_lists xs vs rho = Some rho' ->
    NoDup xs ->
    Disjoint _ (FromList xs) (Dom_map rho) ->
    sub_map rho rho'.
  Proof.
    revert rho rho' vs; induction xs; intros rho rho' vs Hset; destruct vs; try now inv Hset.
    simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset'; inv Hset.
    intros Hnd Hdis. inv Hnd. repeat normalize_sets. eapply sub_map_trans. eapply IHxs. eassumption. eassumption.
    now sets. eapply sub_map_set. intros Hc. eapply Hdis. constructor. now left.
    eapply Dom_map_set_lists in Hc; eauto. inv Hc; eauto. exfalso. contradiction.
  Qed.

  Lemma apply_r_set_list_f_eq xs ys sig : 
    f_eq (apply_r (set_list (combine xs ys) sig)) (apply_r sig <{ xs ~> ys }>). 
  Proof.
    revert ys sig. induction xs; intros; simpl. reflexivity.
    destruct ys. reflexivity.
    simpl. eapply Equivalence_Transitive.
    eapply apply_r_set_f_eq. eapply f_eq_extend. eauto.
  Qed.


  Lemma fun_map_inv_sig_extend_Disjoint k S fm rho1 rho2 i sig xs xs' :
    fun_map_inv k S fm rho1 rho2 i sig ->

    Disjoint _ (FromList xs) (S :|: occurs_free_in_env rho1) ->    
    
    fun_map_inv k S fm rho1 rho2 i (set_list (combine xs xs') sig).
  Proof.
    revert S fm rho1 rho2 i sig xs xs'.
    induction k using lt_wf_rec1; intros S fm rho1 rho2 i sig xs xs' Hfm Hdis1.
    intro; intros. edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split; [| split; [| split; [| split ]]].
    - rewrite apply_r_set_list_f_eq. 
      eapply preord_env_P_inj_extend_lst_not_In_P_r. eassumption.
      eapply Disjoint_Included_r; [| eapply Hdis1 ].
      eapply Included_Union_preserv_r. eapply Included_trans; [| eapply occurs_free_in_env_get; eauto ].
      simpl; now sets.
    - eassumption.
    - eassumption.
    - eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. omega.
      eassumption.
      eapply Disjoint_Included_r; [| eassumption ].
      eapply Included_Union_preserv_r. eapply Union_Included.
      + reflexivity.
      + eapply sub_map_occurs_free_in_env. eassumption.
  Qed.

  Lemma fun_map_inv_set_lists k S S' fm rho1 rho1' rho2 rho3 i sig xs xs' vs :
    fun_map_inv k S fm rho1 rho2 i sig ->

    fun_map_inv k S' fm rho3 rho2 i sig ->
    S \subset S' ->
    \bigcup_(v in FromList vs) occurs_free_in_val v \subset occurs_free_in_env rho3 ->
    sub_map rho1 rho3 ->
    
    NoDup xs ->
    Disjoint _ (FromList xs) (Dom_map rho1 :|: Dom_map fm :|: occurs_free_in_env rho3) ->    
    set_lists xs vs rho1 = Some rho1' ->
    
    fun_map_inv k (FromList xs :|: S) fm rho1' rho2 i (set_list (combine xs xs') sig).
  Proof.
    revert S S' fm rho1 rho1' rho2 rho3 i sig xs xs' vs.
    induction k using lt_wf_rec1;
      intros S S' fm rho1 rho1' rho3 rho2 i sig xs xs' vs Hfm Hfm' Hsub Hsub' Hsm Hnd Hdis1 Hset.
    intro; intros.
    destruct (Decidable_FromList xs). destruct (Dec f).
    - exfalso. eapply Hdis1. constructor. eassumption. left. right. eexists; eauto.
    - inv H0; try contradiction. erewrite <- set_lists_not_In in H2; [| eassumption | eassumption ].
      edestruct Hfm; eauto. destructAll. split; eauto. split; eauto. split; [| split; [| split; [| split ]]].
      + rewrite apply_r_set_list_f_eq. 
        eapply preord_env_P_inj_extend_lst_not_In_P_r. eassumption.
        eapply Disjoint_Included_r; [| eapply Hdis1 ].
        eapply Included_Union_preserv_r. eapply Included_trans; [| eapply occurs_free_in_env_get; eauto ].
        simpl; now sets.
      + eapply sub_map_trans. eassumption. eapply sub_map_set_lists. eassumption. eassumption.
        eapply Disjoint_Included_r; [| eapply Hdis1 ]. sets.
      + edestruct Hfm'. eapply Hsub. eassumption. eassumption. eapply Hsm. eassumption.
        destructAll.
        eapply Union_Disjoint_r; [| now sets ]. eapply Union_Disjoint_r; [ now sets | ].
        eapply Disjoint_Included_r. eapply occurs_free_in_env_set_lists_not_In. eassumption.
        eapply Union_Disjoint_r; [| eapply Disjoint_Included_r; [| eapply H7]; now sets ].
        eapply Disjoint_Included_r. eassumption. sets.
      + edestruct Hfm'. eapply Hsub. eassumption. eassumption. eapply Hsm. eassumption.
        destructAll.
        eapply Union_Disjoint_r; [| now sets ]. eapply Union_Disjoint_r; [| now sets ]. eapply Union_Disjoint_r; [ now sets | ].
        eapply Disjoint_Included_r. eapply occurs_free_in_env_set_lists_not_In. eassumption.
        eapply Union_Disjoint_r; sets. eapply Disjoint_Included_r; [| eapply H8 ]. sets.
      + destruct k; eauto.
        edestruct Hfm'. now eauto. eassumption. eapply Hsm. eassumption. destructAll. 
        rewrite <- fun_map_inv_eq in *. eapply fun_map_inv_sig_extend_Disjoint.
        eapply fun_map_inv_antimon. eapply H15.
        eapply Included_trans. eapply occurs_free_in_env_set_lists_not_In. eassumption.
        eapply Union_Included. eassumption. eapply sub_map_occurs_free_in_env. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_Union_preserv_r. eapply Union_Included.
        * eapply Included_trans. eapply occurs_free_in_env_set_lists_not_In. eassumption.
          eapply Union_Included. eassumption. eapply sub_map_occurs_free_in_env. eassumption.
        * eapply sub_map_occurs_free_in_env. eassumption.
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

  
  Lemma sub_map_def_funs rho B :
    Disjoint _ (name_in_fundefs B) (Dom_map rho) ->            
    sub_map rho (def_funs B B rho rho).
  Proof.
    intros Hdis x v Hget.
    rewrite def_funs_neq; eauto.
    intros Hc. eapply Hdis. constructor. eassumption. eexists. eassumption.
  Qed.    

  Lemma fun_map_inv_def_funs k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->
    
    preord_env_P_inj cenv PG (name_in_fundefs B1 :|: occurs_free_fundefs B1) i
                     (apply_r (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig))
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) ->

    unique_bindings_fundefs B1 ->
    occurs_free_fundefs B1 :|: occurs_free_in_env rho1 \subset S ->
    
    Disjoint _ (name_in_fundefs B1) (S :|: Dom_map rho1 :|: occurs_free_in_env rho1) ->

    fun_map_inv k (name_in_fundefs B1 :|: S) (add_fundefs B1 fm) (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2. induction k as [k IHk] using lt_wf_rec1.
    intros S fm rho1 rho2 i sig B1 B2 Hf Hrel Hun Hsub Hdis.
    intros f ft xs e rhoc B' f' HSin Heq1 Heq2.   
    destruct (Decidable_name_in_fundefs B1) as [Dec]. destruct (Dec f).
    - rewrite def_funs_eq in Heq2; eauto. inv Heq2.
      edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in Heq1; [| eassumption ]. inv Heq1. split; eauto.
      split; eauto. split; [| split; [| split; [| split ]]].
      + eassumption.
      + eapply sub_map_refl.
      + admit. (* seems OK *)
      + rewrite Dom_map_add_fundefs.
        admit. (* seems OK, add assump *)
      + destruct k; eauto. rewrite <- fun_map_inv_eq. eapply fun_map_inv_antimon. eapply IHk.
        omega. eapply fun_map_inv_mon. eassumption. omega. eassumption. eassumption.
        eassumption. now sets. 
        eapply Included_trans. eapply occurs_free_in_env_def_funs.
        rewrite (Union_commut (occurs_free_fundefs _)). rewrite <- Union_assoc.
        eapply Union_Included. now sets. eapply Included_trans. eassumption. sets.
    - rewrite def_funs_neq in Heq2; eauto.
      rewrite add_fundefs_not_in in Heq1; [| eassumption ]. inv HSin. contradiction. 
      edestruct Hf. eassumption. eassumption. eassumption. destructAll. split; eauto. split; eauto. 
      split; [| split; [| split; [| split ]]].
      + eapply preord_env_P_inj_def_funs_neq_r.

        rewrite apply_r_set_list_f_eq. eapply preord_env_P_inj_extend_lst_not_In_P_r.
        eassumption. admit. admit. (* I think OK *)
      + eapply sub_map_trans. eassumption. eapply sub_map_def_funs. sets.
      + admit. (* I think OK *)
      + admit.
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
 
        Set Nested Proofs Allowed.

 
  Lemma fun_map_inv_add_fundefs_Disjoint k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->
    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_in_env rho1) ->
    fun_map_inv k S (add_fundefs B1 fm) rho1 (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2; induction k using lt_wf_rec1; intros.
    intro; intros. rewrite add_fundefs_not_in in H3.
    edestruct H0; eauto. destructAll.
    repeat (split; [ now eauto |]). split; [| split; [| split; [| split ]]].
    - admit.
    - eassumption.
    - sets.
    - 
  (*   - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. *)
  (*     + omega. *)
  (*     + eassumption. *)
  (*     + eapply Disjoint_Included_r; [| eassumption ]. *)
  (*       eapply Included_Union_preserv_r. eapply Union_Included. reflexivity.  *)
  (*       eapply sub_map_occurs_free_in_env. eassumption. *)
  (*   - intros Hc. eapply H1. constructor. eassumption. now left. *)
  (* Qed. *)
        
        (* eassumption. *)
  (*       eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r. *)
  (*       eapply Union_Included. *)
  (*       eapply Included_trans; [| eapply occurs_free_in_env_get ]; eauto. simpl; now sets. *)
  (*       eapply sub_map_occurs_free_in_env. eassumption. *)
  (* Qed. *)
  Abort.
  Abort.
  
  Definition fun_map_vars (fm : fun_map) (F : Ensemble var) (sig : subst) :=
    forall f ft xs e,
      fm ! f = Some (ft, xs, e) ->
      unique_bindings e /\
      NoDup xs /\
      Disjoint _ (bound_var e) (occurs_free e :|: Dom_map fm) /\
      Disjoint _ F (bound_var e :|: image (apply_r sig) (occurs_free e)).

  Definition occurs_free_fun_map (fm : fun_map) : Ensemble var :=
    fun v => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ v \in (occurs_free e \\ FromList xs).

  Lemma fun_map_vars_set fm F sig x v :
    fun_map_vars fm F sig ->
    fun_map_vars fm (F \\ [set v]) (M.set x v sig).
  Proof.
    intros Hfm; intro; intros. eapply Hfm in H. destructAll.
    do 3 (split; eauto). eapply Union_Disjoint_r. now sets.
    eapply Disjoint_Included_r. eapply image_apply_r_set.
    eapply Union_Disjoint_r. now sets. now xsets.
  Qed.

  Lemma Dom_map_def_funs B rho B' rho' :
    Dom_map (def_funs B' B rho' rho) <--> name_in_fundefs B :|: Dom_map rho. 
  Proof.
    induction B; simpl; sets.
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.
    
  Opaque preord_exp'.
  
  Lemma inline_correct_mut d : 
    (forall e sig fm st S,
        unique_bindings e ->
        Disjoint _ (bound_var e) (occurs_free e :|: Dom_map fm) ->    
        Disjoint _ S (bound_var e :|: image (apply_r sig) (occurs_free e)) ->        
        fun_map_vars fm S sig ->        
        {{ fun _ s => fresh S (next_var (fst s)) }}
          beta_contract St IH d e sig fm st
        {{ fun _ _ e' s' =>
             fresh S (next_var (fst s')) /\
             unique_bindings e' /\
             occurs_free e' \subset image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm) /\
             bound_var e' \subset S /\
             (forall k rho1 rho2,
                 preord_env_P_inj cenv PG (occurs_free e) k (apply_r sig) rho1 rho2 ->
                 Disjoint _ (bound_var e) (occurs_free_in_env rho1 :|: Dom_map rho1) ->
                 Disjoint _ S (image (apply_r sig) (occurs_free_in_env rho1)) ->
                 fun_map_inv d (occurs_free e :|: occurs_free_in_env rho1) fm rho1 rho2 k sig ->
                 preord_exp cenv P1 PG k (e, rho1) (e', rho2)) }} ) /\ 

    (forall B sig sig0 fm st S,
        unique_bindings_fundefs B ->
        Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B :|: Dom_map fm) ->    
        Disjoint _ S (bound_var_fundefs B :|: image (apply_r sig) (occurs_free_fundefs B)) ->
        fun_map_vars fm S sig ->        
        {{ fun _ s => fresh S (next_var (fst s)) }}
          beta_contract_fundefs St IH d sig sig0 fm B st
        {{ fun _ _ B' s' =>
             fresh S (next_var (fst s')) /\
             unique_bindings_fundefs B' /\
             occurs_free_fundefs B' \subset image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm) /\
             bound_var_fundefs B' \subset S /\
             all_fun_name B' = apply_r_list sig (all_fun_name B) /\
             (forall f xs ft e1,
                 find_def f B = Some (xs, ft, e1) ->
                 exists xs' e2,
                   find_def (apply_r sig f) B = Some (xs', ft, e2) /\
                   (forall rho1 rho2 k,
                       preord_env_P_inj cenv PG (occurs_free_fundefs B) k (apply_r sig) rho1 rho2 ->
                       Disjoint _ (bound_var e1) (occurs_free_in_env rho1 :|: Dom_map rho1) ->
                       Disjoint _ S (image (apply_r sig) (occurs_free_in_env rho1)) ->
                       fun_map_inv d (occurs_free_fundefs B :|: occurs_free_in_env rho1) fm rho1 rho2 k sig ->
                       preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)))}}).

  Proof.
    revert e sig fm st S. induction d as [d IHd] using lt_wf_rec1.
    induction e using exp_ind'; intros sig fm st S Hun Hdis1 Hdis2 Hfm; inv Hun; rewrite beta_contract_eq.
    - (* constr *)
      eapply bind_triple. now eapply get_name_fresh. 
      intros x w1. eapply pre_curry_l. intros Hinx.
      eapply bind_triple. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1].
        rewrite Setminus_Union_distr. now sets. now sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply Included_Union_compat. reflexivity.
        eapply image_apply_r_set. 
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ].
        rewrite !image_Union. now xsets. now sets.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf [Hun [Hsub [Hsub' Hsem]]]].
        split; [| split; [| split; [| split ]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * constructor.
          intros Hc. eapply Hsub' in Hc. now inv Hc; eauto. eassumption. 
        * repeat normalize_occurs_free. rewrite !image_Union.
          rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity. 
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption. now sets.
          eapply Singleton_Included. eassumption.
        * intros r1 r2 k Henv Hdis Hdis' Hfm'. eapply preord_exp_const_compat.
          eassumption. eassumption.
          eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.          
          intros. eapply Hsem. 
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free. sets.
          -- rewrite preord_val_eq. split. reflexivity.
             eapply Forall2_Forall2_asym_included. eassumption.
          -- intros Hc. eapply Hdis2. constructor. eassumption.
             right. normalize_occurs_free. rewrite image_Union. right. eassumption.
          -- repeat normalize_bound_var_in_ctx. rewrite Dom_map_set.
             eapply Union_Disjoint_r.
             ++ eapply Disjoint_Included_r. eapply occurs_free_in_env_set. simpl. normalize_sets.
                eapply Disjoint_Included; [| | eapply Hdis]; sets.
             ++ eapply Union_Disjoint_r.
                ** eapply Disjoint_Singleton_r. eassumption.
                ** eapply Disjoint_Included; [| | eapply Hdis]; sets.
          -- eapply Disjoint_Included_r.
             eapply Included_trans. eapply image_monotonic. eapply occurs_free_in_env_set. simpl. repeat normalize_sets.
             now eapply image_apply_r_set.
             eapply Union_Disjoint_r. now sets. sets. 
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. omega.
             intros Hc. inv Hc. inv H2.
             ++ eapply Hdis. normalize_bound_var. constructor. now right. now right; eauto.
             ++ eapply Hdis1. constructor. normalize_bound_var. now right. now right; eauto.
             ++ eapply Hdis. normalize_bound_var. constructor. now right. now left; eauto.
             ++ intros Hc. eapply Hdis'. constructor; eassumption.
             ++ simpl. sets.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci.
                eapply Union_Included. now sets. eapply Included_trans. eapply occurs_free_in_env_set.
                simpl. sets.
    - (* Ecase [] *)
      admit.
    - (* Ecase (_ :: _) *)
      admit.
    - (* Eproj *)
      admit.
    - (* Eletapp *)
      admit.
    - (* Efun *)
      simpl. destruct (update_funDef St IH f2 sig st). 
      eapply bind_triple. now eapply get_names_lst_fresh. intros xs w.
      eapply pre_curry_l. intros Hinx.
      eapply pre_curry_l. intros Hnd. eapply bind_triple. admit.
      intros fds' w'. eapply bind_triple. eapply IHe.
      + eassumption.
      + rewrite Dom_map_add_fundefs.
        rewrite Union_Included_Union_Setminus with (s3 := name_in_fundefs f2); [| now tci | now sets ]. 
        rewrite (Union_commut (name_in_fundefs f2)). rewrite Union_assoc.
        eapply Union_Disjoint_r.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          eapply name_in_fundefs_bound_var_fundefs.
      + admit.
      + admit.
      + intros e' w''. eapply return_triple. intros _ w''' Hyp. destructAll.
        split; [| split; [| split; [| split ]]].
        * admit.
        * admit.
        * admit.
        * admit.
        * intros k rho1 rho2 Henv Hdis Hdis' Hfm'. eapply preord_exp_fun_compat.
          eassumption. eassumption.
          eapply H6.
          -- admit.
          -- admit.
          -- admit.
          -- admit. 
      admit.
    - (* Eapp *)
      simpl. destruct (update_App St IH (apply_r sig v) t (apply_r_list sig l) st) as [s b] eqn:Hup. 
      + destruct b.
        * destruct (fm ! v) as [[[ft xs] e] |] eqn:Heqf.
          destruct d.
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split ]]]; try eassumption.
             ++ constructor.
             ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ intros. eapply preord_exp_app_compat.
                assumption. assumption.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.              
          -- destruct (Datatypes.length xs =? Datatypes.length l)%nat eqn:Hbeq.
             { symmetry in Hbeq. eapply beq_nat_eq in Hbeq.
               edestruct Hfm. eassumption. destructAll. eapply post_weakening; [| eapply IHd ].
               ++ simpl. intros. destructAll. 
                  split; [| split; [| split; [| split ]]]; try eassumption.
                  ** eapply Included_trans. eassumption. 
                     eapply Included_trans. eapply image_apply_r_set_list.
                     unfold apply_r_list. rewrite list_length_map. eassumption.
                     normalize_occurs_free. rewrite !image_Union. rewrite FromList_apply_list.
                     eapply Union_Included. now sets.
                     rewrite !Setminus_Union_distr. rewrite !image_Union. eapply Included_Union_preserv_r.
                     eapply Union_Included; [| now sets ].
                     eapply image_monotonic. intros z Hin. do 4 eexists; split; eauto.
                  ** intros. eapply preord_exp_app_l.
                   --- admit. (* post *)
                   --- admit. (* post *)
                   --- intros. assert (Hf := H12). assert (Heqf' := Heqf). edestruct H12; eauto. destructAll.
                       do 2 subst_exp. eapply H8.
                       +++ edestruct preord_env_P_inj_get_list_l. now eapply H9. normalize_occurs_free. now sets.
                           eassumption. destructAll.                           
                           eapply preord_env_P_inj_set_lists_l'; try eassumption. eapply preord_env_P_inj_antimon. eassumption.
                           eapply Setminus_Included_Included_Union. eapply Included_trans. eapply occurs_free_in_fun.
                           eapply find_def_correct. eassumption. sets.
                       +++ erewrite Dom_map_set_lists; [| eassumption ]. rewrite Dom_map_def_funs.
                           eapply Union_Disjoint_r; [| now xsets ].
                           eapply Disjoint_Included_r. eapply occurs_free_in_env_set_lists_not_In. eassumption.
                           eapply Disjoint_Included_r. eapply Included_Union_compat. reflexivity.
                           eapply sub_map_occurs_free_in_env. eassumption.
                           rewrite Union_Same_set. now sets. eapply occurs_free_in_env_get_list. eassumption.
                       +++ eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                           unfold apply_r_list. rewrite list_length_map. eassumption.
                           eapply Union_Disjoint_r.
                           eapply Disjoint_Included_r; [|  eapply Hdis2 ]. normalize_occurs_free. rewrite image_Union.
                           rewrite FromList_apply_list. now sets.
                           eapply Disjoint_Included_r. eapply image_monotonic. eapply Setminus_Included.
                           eapply Disjoint_Included_r. eapply image_monotonic.
                           eapply occurs_free_in_env_set_lists_not_In. eassumption.
                           rewrite image_Union. eapply Union_Disjoint_r.
                           eapply Disjoint_Included_r; [|  eapply H11 ]. eapply image_monotonic.
                           eapply occurs_free_in_env_get_list. eassumption.
                           eapply Disjoint_Included_r; [| eapply H11 ]. eapply image_monotonic.
                           eapply sub_map_occurs_free_in_env. eassumption. 
                       +++ eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | | | | | eassumption ].
                           *** rewrite <- fun_map_inv_eq in *. eapply H23.
                           *** eapply fun_map_inv_mon. eapply Hf. omega.
                           *** sets.
                           *** eapply occurs_free_in_env_get_list. eassumption.
                           *** eassumption.
                           *** eassumption. 
                           *** rewrite Dom_map_def_funs. xsets.
                           *** eapply Included_trans. eapply Included_Union_compat. reflexivity.
                               eapply occurs_free_in_env_set_lists_not_In. eassumption.
                               eapply Union_Included; [| eapply Union_Included ]. 
                               ++++ eapply Included_trans.
                                    2:{ eapply Included_Union_compat. reflexivity. eapply occurs_free_in_env_get. eapply H14. }
                                    eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
                                    sets.
                               ++++ eapply Included_trans. eapply occurs_free_in_env_get_list. eassumption. sets.
                               ++++ eapply Included_trans. eapply sub_map_occurs_free_in_env. eassumption. sets.
               ++ omega.
               ++ eassumption.
               ++ eassumption.
               ++ eapply Union_Disjoint_r. now sets.
                  eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Union_Disjoint_r.
                  eapply Disjoint_Included_r; [| eapply Hdis2 ]. normalize_occurs_free.
                  rewrite image_Union. rewrite FromList_apply_list. now sets. now sets.
               ++ (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                  intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                  repeat (split; [ now eauto |]). eapply Union_Disjoint_r. now sets.
                  eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Union_Disjoint_r.
                  eapply Disjoint_Included_r; [| eapply Hdis2 ]. normalize_occurs_free.
                  rewrite image_Union. rewrite FromList_apply_list. now sets. now sets. }
             { eapply return_triple.
               intros. split; [| split; [| split; [| split ]]]; try eassumption.
               ++ constructor.
               ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                  rewrite FromList_apply_list. sets.
               ++ normalize_bound_var. sets.
               ++ intros. eapply preord_exp_app_compat.
                  assumption. assumption.
                  eapply H0. now constructor.
                  eapply Forall2_preord_var_env_map. eassumption.
                  now constructor. }
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split ]]]; try eassumption.
             ++ constructor.
             ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ intros. eapply preord_exp_app_compat.
                assumption. assumption.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.
        *  eapply return_triple.
           intros. split; [| split; [| split; [| split ]]]; try eassumption.
           ++ constructor.
           ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
              rewrite FromList_apply_list. sets.
           ++ normalize_bound_var. sets.
           ++ intros. eapply preord_exp_app_compat.
              assumption. assumption.
              eapply H0. now constructor.
              eapply Forall2_preord_var_env_map. eassumption.
              now constructor.
    - (* Eprim *)
      admit.
    - (* Ehalt *)
      admit.
  Qed.

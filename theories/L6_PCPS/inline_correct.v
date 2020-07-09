Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Classes.Morphisms.
Require Import compcert.lib.Maps compcert.lib.Coqlib.
Require Import L6.cps L6.state L6.freshen L6.cps_util L6.cps_show L6.ctx L6.hoare L6.inline L6.rename L6.identifiers
        L6.Ensembles_util L6.alpha_conv L6.functions L6.logical_relations L6.tactics L6.eval L6.map_util L6.inline_letapp.
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
       | (true, Some (ft, xs, e), S d') =>
         if (Nat.eqb (List.length xs) (List.length ys)) then 
           let sig' := set_list (combine xs ys') sig  in
           x' <- get_name x "" ;;         
           e' <- beta_contract _ IH d' e sig' fm s' ;;
           match inline_letapp e' x', Nat.eqb (List.length xs) (List.length ys) with
           | Some (C, x'), true =>
             ec' <- beta_contract _ IH d' ec (M.set x x' sig) fm s' ;;
             ret (C |[ ec' ]|)
           | _, _ =>
             x' <- get_name x "" ;;
             ec' <- beta_contract _ IH d ec (M.set x x' sig) fm s' ;;
             ret (Eletapp x' f' t ys' ec')
           end
         else              
           x' <- get_name x "" ;;
           ec' <- beta_contract _ IH d ec (M.set x x' sig) fm s' ;;
           ret (Eletapp x' f' t ys' ec')
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


Definition Range (x1 x2 : positive) : Ensemble var := fun z => x1 <= z < x2.

Lemma Disjoint_Range (x1 x2 x1' x2' : positive) :
  x2 <= x1' ->
  Disjoint _ (Range x1 x2) (Range x1' x2').
Proof.
  intros Hleq. constructor. intros x Hin. inv Hin.
  unfold Range, Ensembles.In in *. simpl in *. zify. omega.
Qed.    

Lemma Range_Subset (x1 x2 x1' x2' : positive) :
  x1 <= x1' ->
  x2' <= x2 ->
  Range x1' x2' \subset Range x1 x2.
Proof.
  intros H1 H2. intros z Hin. unfold Range, Ensembles.In in *.
  inv Hin. zify. omega.
Qed.
        
  
Lemma fresh_Range S (x1 x2 : positive) :
  fresh S x1 ->
  Range x1 x2 \subset S.
Proof.
  intros Hin z Hin'. inv Hin'. eapply Hin. eassumption.
Qed.

(** Spec for [get_name] *)
Lemma get_name_fresh A S y str :
  {{ fun _ (s : comp_data * A) => fresh S (next_var (fst s)) }}
    get_name y str
  {{ fun (r: unit) s x s' =>
       x \in S /\
       x \in Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) < next_var (fst s')) /\
       fresh (S \\ [set x]) (next_var (fst s'))      
  }}.  
Proof. 
  eapply pre_post_mp_l.
  eapply bind_triple. now eapply get_triple.  
  intros [[] w1] [[] w2].
  eapply pre_post_mp_l. simpl.
  eapply bind_triple. now eapply put_triple.
  intros x [r3 w3].
  eapply return_triple. 
  intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
  split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. omega.
  simpl. split. zify; omega.
  intros z Hin. constructor. eapply H; eauto. zify. omega.
  intros Hc. inv Hc. zify; omega.
Qed.

Lemma get_names_lst_fresh A S ns str :
  {{ fun _ (s : comp_data * A) => fresh S (next_var (fst s)) }}
    get_names_lst ns str
  {{ fun (r: unit) s xs s' =>
       NoDup xs /\ List.length xs = List.length ns /\
       FromList xs \subset S /\
       FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) <= next_var (fst s')) /\
       fresh (S \\ FromList xs) (next_var (fst s')) }}.  
Proof.
  unfold get_names_lst. revert S; induction ns; intros S.
  - simpl. eapply return_triple.
    intros. repeat normalize_sets. split; eauto. sets. now constructor. split; eauto.
    split. now sets. split. sets. split. reflexivity. eassumption.
  - simpl. eapply bind_triple. eapply get_name_fresh.
    intros x w.
    eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHns.
    intros xs w'. eapply return_triple. intros. destructAll.
    repeat normalize_sets. split; [| split; [| split; [| split; [| split ]]]].
    + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
    + simpl. congruence.
    + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
    + eapply Union_Included. eapply Singleton_Included.
      eapply Range_Subset; [| | eassumption ]. reflexivity. zify. omega.
      eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. reflexivity.
    + zify; omega.
    + rewrite <- Setminus_Union. eassumption.
Qed.

Fixpoint funname_in_exp (e : exp) : Ensemble var :=
  match e with
  | Econstr _ _ _ e
  | Eproj _ _ _ _ e
  | Eletapp _ _ _ _ e
  | Eprim _ _ _ e => funname_in_exp e
  | Ecase _ P =>
    (fix aux P :=
       match P with
       | [] => Empty_set _
       | (c, e) :: P => funname_in_exp e :|: aux P
       end) P      
  | Efun B e => funname_in_fundefs B :|: name_in_fundefs B :|: funname_in_exp e
  | Eapp _ _ _ 
  | Ehalt _ => Empty_set _
  end
with funname_in_fundefs (B : fundefs) : Ensemble var :=
       match B with
       | Fcons _ _ _ e B => funname_in_exp e :|: funname_in_fundefs B
       | Fnil => Empty_set var
       end.
  
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
           (Hpost_zero : forall e1 rho1 e2 rho2, post_zero e1 rho1 e2 rho2 P1)
           (HEapp_l : forall v t l rho1 x rho2, post_Eapp_l P1 P1 v t l rho1 x rho2)
           (HEletapp : remove_steps_letapp cenv P1 P1 P1)
           (Eletapp' : remove_steps_letapp' cenv P1 P1 P1)
           (Eletapp_OOT : remove_steps_letapp_OOT cenv P1 P1)
           (Eletapp_OOT' : remove_steps_letapp_OOT' cenv P1 P1).

  
  
  Definition occurs_free_fun_map (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in occurs_free e \\ FromList xs.

  Definition bound_var_fun_map (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in bound_var e \\ funname_in_exp e :|: FromList xs.

  Definition bound_var_fun_map' (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in bound_var e :|: FromList xs.


  Fixpoint fun_map_inv' (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (occurs_free e \\ FromList xs) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      (* sub_map (def_funs B B rhoc rhoc) rho1 /\ *)
      Disjoint _ (bound_var e) (name_in_fundefs B) /\
      Disjoint _ (FromList xs) (name_in_fundefs B) /\
      (* Disjoint _ S (occurs_free e \\ FromList xs) /\ *)
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free e \\ FromList xs) fm (def_funs B B rhoc rhoc) rho2 i sig
      end.

  Definition fun_map_inv (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (occurs_free e \\ FromList xs) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      (* sub_map (def_funs B B rhoc rhoc) rho1 /\ *)
      Disjoint _ (bound_var e) (name_in_fundefs B) /\
      Disjoint _ (FromList xs) (name_in_fundefs B) /\
      (* Disjoint _ S (occurs_free e \\ FromList xs) /\ *)
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free e \\ FromList xs) fm (def_funs B B rhoc rhoc) rho2 i sig
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
      split; eauto. split; eauto. split; eauto. split; eauto. split; eauto.
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
    split; eauto. split; eauto.
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


  Lemma occurs_free_fun_map_get f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    occurs_free e \\ (FromList xs) \subset occurs_free_fun_map fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.

  Lemma occurs_free_fun_map_add_fundefs B fm :
    occurs_free_fun_map (add_fundefs B fm) \subset occurs_free_fundefs B :|: name_in_fundefs B :|: occurs_free_fun_map fm.
  Proof.
    intros x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in H; eauto. inv H. left.
      eapply find_def_correct in H1. eapply occurs_free_in_fun in H1.
      inv H0. eapply H1 in H. inv H. contradiction. inv H0; eauto.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed.

  Lemma funname_in_exp_subset_mut :
    (forall e, funname_in_exp e \subset bound_var e) /\
    (forall B, funname_in_fundefs B \subset bound_var_fundefs B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros; normalize_bound_var; simpl; sets.

    eapply Union_Included. eapply Union_Included. now sets.
    eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
    sets.
  Qed.

  Lemma funname_in_exp_subset :
    forall e, funname_in_exp e \subset bound_var e.
  Proof. eapply funname_in_exp_subset_mut. Qed.

  Lemma funname_in_fundefs_subset :
    forall e, funname_in_fundefs e \subset bound_var_fundefs e.
  Proof. eapply funname_in_exp_subset_mut. Qed.


  Lemma fun_in_fundefs_bound_var_Setminus' e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    bound_var e \\ funname_in_exp e \subset bound_var_fundefs B \\ funname_in_fundefs B \\ name_in_fundefs B.
  Proof.
    intros Hin Hun. induction B; [| now inv Hin ].
    inv Hun. simpl in Hin. inv Hin.
    - inv H. simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r.
      eapply Included_Union_preserv_l. eapply Included_Setminus.
      + eapply Union_Disjoint_r. eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
      + rewrite <- Setminus_Union. eapply Included_Setminus; [| now sets ].
        eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
    - eapply Included_trans. eapply IHB; eauto.
      simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
      rewrite !Setminus_Union. rewrite <- !Union_assoc. rewrite (Union_commut (funname_in_exp _)). rewrite (Union_commut [set v]).
      rewrite <- !Union_assoc. rewrite Union_assoc. do 2 rewrite <- Setminus_Union. 
      eapply Included_Setminus; [| now sets ]. eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H0; eauto.
      eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
  Qed.

  Lemma fun_in_fundefs_bound_var_Setminus e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    bound_var e \\ funname_in_exp e \subset bound_var_fundefs B \\ funname_in_fundefs B.
  Proof.
    intros Hin Hun. eapply Included_trans. eapply fun_in_fundefs_bound_var_Setminus'. eassumption.
    eassumption. sets.
  Qed.


  Lemma fun_in_fundefs_FromList_subset e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    FromList xs \subset bound_var_fundefs B \\ funname_in_fundefs B \\ name_in_fundefs B.
  Proof.
    intros Hin Hun. induction B; [| now inv Hin ]. inv Hun. inv Hin.
    - inv H. simpl. normalize_bound_var. rewrite !Setminus_Union_distr. eapply Included_Union_preserv_r.
      eapply Included_Union_preserv_l. rewrite !Setminus_Union. eapply Included_Setminus; [| now sets ].
      eapply Union_Disjoint_r; eapply Union_Disjoint_r.
      + eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
      + eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
      + sets.
      + eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
    - eapply Included_trans. eapply IHB; eauto.
      simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
      rewrite !Setminus_Union. rewrite <- !Union_assoc. rewrite (Union_commut (funname_in_exp _)). rewrite (Union_commut [set v]).
      rewrite <- !Union_assoc. rewrite Union_assoc. do 2 rewrite <- Setminus_Union. 
      eapply Included_Setminus; [| now sets ]. eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H0; eauto.
      eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
  Qed.

  Lemma bound_var_fun_map_get f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    bound_var e \\ funname_in_exp e :|: (FromList xs) \subset bound_var_fun_map fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.


  Lemma bound_var_fun_map_add_fundefs_un B fm :
    unique_bindings_fundefs B ->
    bound_var_fun_map (add_fundefs B fm) \subset (bound_var_fundefs B \\ funname_in_fundefs B \\ name_in_fundefs B) :|: bound_var_fun_map fm.
  Proof.
    intros Hun x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll. erewrite add_fundefs_in in H; [| eassumption ]. inv H.
      edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
      left.     
      inv H0.
      + constructor. eapply fun_in_fundefs_bound_var_Setminus. eapply find_def_correct. eassumption. eassumption. eassumption.
        inv H8. intros hc. eapply H4; constructor; eauto.
      + eapply fun_in_fundefs_FromList_subset. eapply find_def_correct. eassumption. eassumption. eassumption.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed.

  Lemma bound_var_fun_map_get' f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    bound_var e :|: (FromList xs) \subset bound_var_fun_map' fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.


  Lemma bound_var_fun_map_add_fundefs_un' B fm :
    unique_bindings_fundefs B ->
    bound_var_fun_map' (add_fundefs B fm) \subset (bound_var_fundefs B \\ name_in_fundefs B) :|: bound_var_fun_map' fm.
  Proof.
    intros Hun x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll. erewrite add_fundefs_in in H; [| eassumption ]. inv H.
      edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
      left.     
      inv H0.
      + constructor. eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
        intros hc. eapply H4; constructor; eauto.
      + constructor.
        eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
        intros hc. eapply H5; constructor; eauto.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed. 


  (* TODO move *)
  Lemma preord_env_P_inj_set_extend_not_In_P_r_alt S k f rho1 rho2 x y v :
    preord_env_P_inj cenv PG S k f rho1 rho2 ->
    ~ x \in S ->
    ~ y \in (image f (Dom_map rho1)) ->
    preord_env_P_inj cenv PG S k (f {x ~> y}) rho1 (M.set y v rho2).
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto.
    rewrite extend_gso, M.gso. eassumption.
    intros Hc; subst. eapply Hnin'. eexists; eauto. split. eexists; eauto. reflexivity.
    intros Hc. subst. contradiction.
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

  Lemma Dom_map_def_funs B rho B' rho' :
    Dom_map (def_funs B' B rho' rho) <--> name_in_fundefs B :|: Dom_map rho. 
  Proof.
    induction B; simpl; sets.
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.

  Lemma Dom_map_sub_map {A : Type} (rho1 rho2 : M.t A) :
    sub_map rho1 rho2 ->
    Dom_map rho1 \subset Dom_map rho2.
  Proof.
    intros H1 x [y Hin]. eapply H1 in Hin.
    eexists; eauto.
  Qed.


  Lemma fun_map_inv_set_not_In_r k S fm rho1 rho2 i sig x x' v' : 
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in occurs_free_fun_map fm ->
    ~ x' \in image (apply_r sig) (occurs_free_fun_map fm) ->
    fun_map_inv k S fm rho1 (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    revert S fm rho1 rho2 i sig x x' v'. induction k using lt_wf_rec1; intros. intro; intros.
    edestruct H0; eauto. 
    destructAll. split; [| split; [| split; [| split; [| split ]]]]; eauto.
    - rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
      + intros Hc. eapply H1. eapply occurs_free_fun_map_get. eassumption. eassumption.
      + intros Hc. eapply H2. eapply image_monotonic; [| eassumption ].
        eapply occurs_free_fun_map_get. eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply H. omega. eassumption.
      intros hc. eapply H1. eassumption.
      intros hc. eapply H2. eapply image_monotonic; [| eassumption ]. reflexivity.
  Qed.
  
  Lemma fun_map_inv_set k S fm rho1 rho2 i sig x v x' v' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in occurs_free_fun_map fm :|: Dom_map fm ->
    ~ x' \in image (apply_r sig) (occurs_free_fun_map fm) ->
    fun_map_inv k (x |: S) fm (M.set x v rho1) (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    intros Hinv Hnin Hnin'. intro; intros.
    rewrite M.gso in *. 
    2:{ intros Heq; subst. eapply Hnin. right. eexists; eauto. }
    inv H.
    - inv H2. exfalso. eapply Hnin. right. eexists; eauto.
    - edestruct Hinv; eauto.
      destructAll. split; [| split; [| split; [| split; [| split ]]]]; eauto.
      + rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
        intros Hc. eapply Hnin. left. eapply occurs_free_fun_map_get; eauto.
        intros Hc. eapply Hnin'. eapply image_monotonic; [| eassumption ].
        eapply occurs_free_fun_map_get; eauto.
      (* + eapply sub_map_trans. eassumption. eapply sub_map_set. *)
      (*   intros Hc. eapply Hnin. left. eassumption. *)
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
        eapply fun_map_inv_set_not_In_r. eapply fun_map_inv_antimon. eassumption.
        * reflexivity.
        * sets.
        * sets.
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


  Lemma fun_map_inv_sig_extend_Disjoint k S fm rho1 rho2 i sig xs xs' :
    fun_map_inv k S fm rho1 rho2 i sig ->

    Disjoint _ (FromList xs) (occurs_free_fun_map fm) ->    
    
    fun_map_inv k S fm rho1 rho2 i (set_list (combine xs xs') sig).
  Proof.
    revert S fm rho1 rho2 i sig xs xs'.
    induction k using lt_wf_rec1; intros S fm rho1 rho2 i sig xs xs' Hfm Hdis1.
    intro; intros. edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split; [| split; [| split ]].
    - rewrite apply_r_set_list_f_eq. 
      eapply preord_env_P_inj_extend_lst_not_In_P_r. eassumption.
      eapply Disjoint_Included_r; [| eapply Hdis1 ]. 
      eapply occurs_free_fun_map_get. eassumption.
    - eassumption.
    - eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. omega.
      eassumption.
      sets.
  Qed.
  
  Lemma fun_map_inv_sig_extend_one_Disjoint k S fm rho1 rho1' rho2 i sig x x' :
    fun_map_inv k S fm rho1 rho2 i sig ->

    eq_env_P (Complement _ [set x]) rho1 rho1' ->
    ~ x \in (Dom_map fm) ->
    ~ x \in (occurs_free_fun_map fm) ->
    ~ x \in S ->
                    
    fun_map_inv k (x |: S) fm rho1' rho2 i (M.set x x' sig).
  Proof.
    intros Hfm HeqP Hdis1 Hdis2 Hdis3. 
    intro; intros. inv H. exfalso. inv H2. eapply Hdis1. eexists; eauto.
    rewrite <- HeqP in H1. 2:{ intros Hc; inv Hc; subst; eauto. }
    edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split; [| split; [| split ]].
    - rewrite apply_r_set_f_eq. 
      eapply preord_env_P_inj_extend_not_In_P_r. eassumption.
      intros Hc. eapply Hdis2. eapply occurs_free_fun_map_get. eassumption.
      eassumption.
    - eassumption.
    - eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply fun_map_inv_sig_extend_Disjoint with (xs := [x]) (xs' := [x']). eassumption.
      repeat normalize_sets. eapply Disjoint_Singleton_l.
      sets.
  Qed.
  
  Lemma fun_map_inv_env_eq_P S k fm rho1 rho2 i sig rho1' rho2' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    eq_env_P S rho1 rho1' ->
    eq_env_P (image (apply_r sig) (occurs_free_fun_map fm)) rho2 rho2' ->    
    fun_map_inv k S fm rho1' rho2' i sig.
  Proof.
    revert S fm rho1 rho2 i sig rho1' rho2'.
    induction k using lt_wf_rec1; intros S fm rho1 rho2 i sig rho1' rho2' Hfm Heq1 Hsub Heq2.
    intro; intros. rewrite <- Heq1 in H2; eauto. edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split; [| split; [| split ]].
    - eapply preord_env_P_inj_eq_env_P.
      eassumption.
      now eapply eq_env_P_refl.
      eapply eq_env_P_antimon. eassumption.
      eapply image_monotonic. eapply occurs_free_fun_map_get; eauto.
    (* - eapply sub_map_trans; eauto. *)
    - eassumption.
    - eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. omega.
      eassumption. eapply eq_env_P_refl. eassumption.
  Qed.


  Lemma eq_env_P_sub_map {A} (rho1 rho2 : M.t A) x:
    eq_env_P (Complement _ [set x]) rho1 rho2 ->
    ~ x \in Dom_map rho1 ->
    sub_map rho1 rho2.
  Proof.
    intros Henv Hnin z v Hget.
    rewrite <- Henv. eassumption. intros Hc. inv Hc.
    eapply Hnin. eexists; eauto.
  Qed.
  
  Lemma fun_map_inv_set_lists k S fm rho1 rho1' rho2 i sig xs vs :
    fun_map_inv k S fm rho1 rho2 i sig ->

    NoDup xs ->
    Disjoint _ (FromList xs) (occurs_free_fun_map fm :|: Dom_map fm) ->
    set_lists xs vs rho1 = Some rho1' ->
    
    fun_map_inv k (FromList xs :|: S) fm rho1' rho2 i sig.
  Proof.
    revert S fm rho1 rho1' rho2 i sig xs vs.
    induction k using lt_wf_rec1;
      intros S fm rho1 rho1' rho2 i sig xs vs Hfm Hnd Hdis1 Hset.
    intro f; intros.
    destruct (Decidable_FromList xs). destruct (Dec f).
    - exfalso. eapply Hdis1. constructor. eassumption. right. eexists; eauto.
    - inv H0; try contradiction. erewrite <- set_lists_not_In in H2; [| eassumption | eassumption ].
      edestruct Hfm; eauto.
  Qed.


  Lemma preord_env_P_inj_set_lists_not_In_P_r' S k f rho1 rho2 rho2' xs vs :
    preord_env_P_inj cenv PG S k f rho1 rho2 ->
    set_lists xs vs rho2 = Some rho2' ->
    Disjoint _(FromList xs) (image f S) ->
    preord_env_P_inj cenv PG S k f rho1 rho2'.
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto. erewrite <- set_lists_not_In. eassumption.
    eassumption. intros Hc. eapply Hnin'. constructor. eassumption.
    eapply In_image. eassumption.
  Qed.

  Lemma fun_map_inv_set_lists_r k S fm rho1 rho2' rho2 i sig xs vs :
    fun_map_inv k S fm rho1 rho2 i sig ->
    Disjoint _ (FromList xs) (image (apply_r sig) (occurs_free_fun_map fm)) ->

    set_lists xs vs rho2 = Some rho2' ->
    
    fun_map_inv k S fm rho1 rho2' i sig.
  Proof.
    revert S fm rho1 rho2' rho2 i sig xs vs.
    induction k using lt_wf_rec1;
      intros S fm rho1 rho1' rho2 i sig xs vs Hfm Hdis1 Hset.
    intro f; intros.
    edestruct Hfm; eauto. destructAll. split; eauto. split; eauto.
    split; [| split; [| split ]]; try eassumption.
    + eapply preord_env_P_inj_set_lists_not_In_P_r'. eassumption. eassumption.
      eapply Disjoint_Included_r; [| eassumption ]. eapply image_monotonic. eapply occurs_free_fun_map_get.
      eassumption.
    + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply H. omega. eassumption.
      eapply Disjoint_Included_r; [| eapply Hdis1 ]. reflexivity. eassumption.
  Qed.  


  Lemma fun_map_inv_add_fundefs_Disjoint k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->
    
    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_fun_map fm) ->
    Disjoint _ (name_in_fundefs B2) (image (apply_r sig) (occurs_free_fun_map fm)) ->

    fun_map_inv k S (add_fundefs B1 fm) rho1 (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2; induction k using lt_wf_rec1; intros.
    intro; intros. rewrite add_fundefs_not_in in H4.
    edestruct H0; eauto. destructAll.
    repeat (split; [ now eauto |]). split; [| split; [| split ]].
    - eapply preord_env_P_inj_def_funs_neq_r.
      rewrite apply_r_set_list_f_eq. eapply preord_env_P_inj_extend_lst_not_In_P_r.
      eassumption. rewrite <- Same_set_all_fun_name.
      eapply Disjoint_Included_r; [| eapply H1 ]. eapply Included_Union_preserv_r.
      eapply occurs_free_fun_map_get. eassumption.
      
      rewrite apply_r_set_list_f_eq. eapply Disjoint_Included_l.
      intros x Hc. destruct Hc. destructAll.
      rewrite extend_lst_gso. eapply In_image. eassumption.
      rewrite <- Same_set_all_fun_name. intros Hc. eapply H1. constructor. eassumption. right.
      eapply occurs_free_fun_map_get. eassumption. eassumption.
      eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ]. eapply image_monotonic.
      eapply occurs_free_fun_map_get. eassumption.
    - eassumption.
    - eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H.
      + omega.
      + eassumption.
      + eapply Union_Disjoint_r; [| sets ].
        eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
      eapply occurs_free_fun_map_get. eassumption.
      + sets.
    - intros Hc. eapply H1. constructor. eassumption. now left ; eauto.
  Qed.
  
  Lemma name_in_fundefs_funname_in_fundefs_Disjoint B1 : 
    unique_bindings_fundefs B1 ->
    Disjoint _ (name_in_fundefs B1) (funname_in_fundefs B1).
  Proof.
    induction B1; intros Hun.
    - inv Hun. simpl. eapply Union_Disjoint_r; eapply Union_Disjoint_l.
      + eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
      + eapply Disjoint_sym. eapply Disjoint_Included.
        eapply name_in_fundefs_bound_var_fundefs. eapply funname_in_exp_subset. eassumption. 
      + eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
      + eauto.
    - sets.
  Qed.
        
  Lemma fun_map_inv_def_funs k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->
    
    preord_env_P_inj cenv PG (name_in_fundefs B1 :|: occurs_free_fundefs B1) i
                     (apply_r (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig))
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) ->

    unique_bindings_fundefs B1 ->
    occurs_free_fundefs B1 \subset S ->
    
    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_fun_map fm) ->
    Disjoint _ (name_in_fundefs B2) (image (apply_r sig) (occurs_free_fun_map fm)) ->        
    
    fun_map_inv k (name_in_fundefs B1 :|: S) (add_fundefs B1 fm) (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2. induction k as [k IHk] using lt_wf_rec1.
    intros S fm rho1 rho2 i sig B1 B2 Hf Hrel Hun Hsub Hdis Hdis'.
    intros f ft xs e rhoc B' f' HSin Heq1 Heq2.
    destruct (Decidable_name_in_fundefs B1) as [Dec]. destruct (Dec f).
    - rewrite def_funs_eq in Heq2; eauto. inv Heq2.
      edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in Heq1; [| eassumption ]. inv Heq1. split; eauto.
      split; eauto. split; [| split; [| split ]].
      + eapply preord_env_P_inj_antimon. eassumption. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption. sets.
      + eapply find_def_correct in H. assert (H' := H). eapply unique_bindings_fun_in_fundefs in H; eauto. destructAll.
        eassumption.
      + eapply find_def_correct in H. assert (H' := H). eapply unique_bindings_fun_in_fundefs in H; eauto. destructAll.
        eassumption.
      + destruct k; eauto. rewrite <- fun_map_inv_eq. eapply fun_map_inv_antimon. eapply IHk.
        omega. eapply fun_map_inv_mon. eassumption. omega. eassumption. eassumption.
        eassumption. now sets. now sets. eapply Setminus_Included_Included_Union. 
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
        sets.
    - rewrite def_funs_neq in Heq2; eauto.
      rewrite add_fundefs_not_in in Heq1; [| eassumption ]. inv HSin. contradiction.
      edestruct Hf. eassumption. eassumption. eassumption. destructAll. split; eauto. split; eauto.
      split; [| split; [| split ]]; eauto.
      + eapply preord_env_P_inj_def_funs_neq_r.
        rewrite apply_r_set_list_f_eq. eapply preord_env_P_inj_extend_lst_not_In_P_r.
        eassumption.
        * rewrite <- Same_set_all_fun_name.
          eapply Disjoint_Included; [| | eapply Hdis ]. eapply Included_Union_preserv_r.
          eapply occurs_free_fun_map_get. eassumption. reflexivity. 
        * rewrite apply_r_set_list_f_eq. eapply Disjoint_Included_l. 
          intros x Hc. destruct Hc. destructAll.
          rewrite extend_lst_gso. eapply In_image. eassumption.
          rewrite <- Same_set_all_fun_name. intros Hc. eapply Hdis. constructor.
          eassumption. right.
          eapply occurs_free_fun_map_get. eassumption. eassumption.
          eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ]. apply image_monotonic.
          eapply occurs_free_fun_map_get. eassumption.
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
        eapply fun_map_inv_add_fundefs_Disjoint; try eassumption.
        * eapply Union_Disjoint_r; [| sets ].
          eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
          eapply occurs_free_fun_map_get. eassumption. 
  Qed.

  Lemma fun_in_fundefs_funname_in_exp f ft xs e B :
    (f, ft, xs, e) \infun_in_fundefs B ->
    funname_in_exp e \subset funname_in_fundefs B.
  Proof.
    induction B; intros Hin; inv Hin.
    + inv H. sets.
    + simpl. eapply Included_Union_preserv_r. eauto.
  Qed.
  
  Definition funname_fun_map (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in funname_in_exp e.

  Lemma funname_fun_map_fun_map_get f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    funname_in_exp e \subset funname_fun_map fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.
  

  Lemma funname_fun_map_add_fundefs B fm :
    funname_fun_map (add_fundefs B fm) \subset (funname_in_fundefs B) :|: funname_fun_map fm.
  Proof.
    intros x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in H; [| eassumption ]. inv H.
      left. eapply fun_in_fundefs_funname_in_exp. eapply find_def_correct. eassumption. eassumption.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed.
  

  Definition fun_map_vars (fm : fun_map) (F : Ensemble var) (sig : subst) :=
    forall f ft xs e,
      fm ! f = Some (ft, xs, e) ->
      unique_bindings e /\
      NoDup xs /\
      Disjoint _ (bound_var e) (FromList xs :|: occurs_free e) /\
      Disjoint _ (bound_var e \\ funname_in_exp e) (Dom_map fm :|: funname_fun_map fm) /\
      Disjoint _ (FromList xs) (Dom_map fm) /\
      Disjoint _ (funname_in_exp e) (bound_var_fun_map fm) /\
      
      Disjoint _ F (bound_var e :|: image (apply_r sig) (occurs_free e \\ FromList xs)).

  Lemma fun_map_vars_antimon fm F F' sig :
    fun_map_vars fm F sig ->
    F' \subset F ->
    fun_map_vars fm F' sig.
  Proof.
    intros Hfm Hsub; intro; intros. eapply Hfm in H. destructAll.
    do 6 (split; eauto). sets.
  Qed.

  Instance fm_map_vars_Proper fm : Proper (Same_set _ ==> eq ==> iff) (fun_map_vars fm).
  Proof.
    repeat (intro; intros). subst. split; intros.
    intro; intros. eapply H0 in H1. rewrite H in H1. eauto.
    intro; intros. eapply H0 in H1. rewrite <- H in H1. eauto.
  Qed.


  Lemma fun_map_vars_set fm F sig x v :
    fun_map_vars fm F sig ->
    fun_map_vars fm (F \\ [set v]) (M.set x v sig).
  Proof.
    intros Hfm; intro; intros. eapply Hfm in H. destructAll.
    do 6 (split; eauto). eapply Union_Disjoint_r. now sets.
    eapply Disjoint_Included_r. eapply image_apply_r_set.
    eapply Union_Disjoint_r. now sets. now xsets.
  Qed.

  Lemma fun_map_vars_set_list fm F sig xs vs :
    fun_map_vars fm F sig ->
    fun_map_vars fm (F \\ FromList vs) (set_list (combine xs vs) sig).
  Proof.
    revert F vs sig. induction xs; intros F vs sig.
    - simpl. intros Hin. eapply fun_map_vars_antimon. eassumption.
      now sets.
    - destruct vs; simpl.
      + intros Hf. eapply fun_map_vars_antimon. eassumption. sets.
      + intros Hfm. simpl. repeat normalize_sets. rewrite Union_commut.
        rewrite <- Setminus_Union. eapply fun_map_vars_set. 
        simpl. eapply IHxs; eauto.
  Qed.

  Lemma apply_r_list_eq xs ys sig :
    NoDup xs ->
    length xs = length ys ->
    apply_r_list (set_list (combine xs ys) sig) xs = ys.
  Proof.
    revert ys sig; induction xs; intros ys sig Hnd Hlen.
    - simpl. destruct ys; eauto. inv Hlen.
    - destruct ys; inv Hlen. inv Hnd.
      simpl. unfold apply_r. rewrite M.gss. f_equal.
      erewrite eq_P_apply_r_list. eapply IHxs. eassumption. eassumption.
      eapply eq_env_P_set_not_in_P_l. eapply eq_env_P_refl. eassumption.
  Qed.

  Lemma NoDup_all_fun_name B :
    unique_bindings_fundefs B ->
    NoDup (all_fun_name B).
  Proof.
    induction B; intros Hc; inv Hc.
    - simpl. constructor; eauto.
      intros Hc. eapply Same_set_all_fun_name in Hc. eapply H5.
      eapply name_in_fundefs_bound_var_fundefs. eassumption.
    - constructor.
  Qed.
  
  Lemma fun_map_vars_def_funs fm S sig B xs :
    fun_map_vars fm S sig ->
    unique_bindings_fundefs B ->

    Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B) ->
    Disjoint _ (bound_var_fundefs B \\ funname_in_fundefs B \\ name_in_fundefs B) (Dom_map fm :|: funname_fun_map fm) ->
    Disjoint _ (S \\ FromList xs) (bound_var_fundefs B :|: image (apply_r sig) (occurs_free_fundefs B)) ->    
    Disjoint _ (name_in_fundefs B) (bound_var_fun_map fm) ->
    Disjoint _ (funname_in_fundefs B) (bound_var_fun_map fm) ->
    
    Datatypes.length (all_fun_name B) = Datatypes.length xs ->
    
    fun_map_vars (add_fundefs B fm) (S \\ FromList xs) (set_list (combine (all_fun_name B) xs) sig).
  Proof.
    intros Hfm Hun Hdis1 Hdis2 Hdis3 Hdis4 Hdis5 Hlen x ft ys e Hget. destruct (Decidable_name_in_fundefs B). destruct (Dec x).
    - edestruct name_in_fundefs_find_def_is_Some; eauto. destructAll. erewrite add_fundefs_in in Hget; eauto.
      inv Hget. edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
      assert (Hin1 : bound_var e \subset bound_var_fundefs B).
      { eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets. }
      assert (Hin2 : FromList ys \subset bound_var_fundefs B).
      { eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets. }
      
      split. now eauto. split. now eauto. split; [| split; [| split; [| split ]]].
      + eapply Union_Disjoint_r. now sets.
        eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
        eassumption. now sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. eapply Union_Disjoint_r. now sets.
        * eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets.
          eapply Included_Setminus. now sets. 
          eapply fun_in_fundefs_bound_var_Setminus. eapply find_def_correct. eassumption. eassumption.
        * eapply Disjoint_Included_r. eapply funname_fun_map_add_fundefs. eapply Union_Disjoint_r.
          ++ eapply Disjoint_Included_l. eapply fun_in_fundefs_bound_var_Setminus. eapply find_def_correct. eassumption.
             eassumption. now sets.
          ++ eapply Disjoint_Included_l. eapply fun_in_fundefs_bound_var_Setminus'. eapply find_def_correct. eassumption.
             eassumption. now sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. eassumption.
        eapply Disjoint_Included_l.
        eapply Included_Setminus. eassumption. 
        eapply fun_in_fundefs_FromList_subset. eapply find_def_correct. eassumption. eassumption.
        now sets.
      + eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un. eassumption.
        eapply Disjoint_Included_l. eapply fun_in_fundefs_funname_in_exp. eapply find_def_correct. eassumption.
        eapply Union_Disjoint_r. now sets. eassumption.
      + eapply Union_Disjoint_r. now sets. eapply Disjoint_Included_r.
        eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r. now sets.
        rewrite <- Same_set_all_fun_name.
        eapply Disjoint_Included; [| | eapply Hdis3 ]; [| now sets ].
        eapply Included_Union_preserv_r. eapply image_monotonic. do 2 eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption. now sets.
    - rewrite add_fundefs_not_in in Hget; eauto. edestruct Hfm. eassumption. destructAll.
      split; eauto. split; eauto. split; [| split; [| split; [| split ]]].
      + now sets.        
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. eapply Union_Disjoint_r. 
        * eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. now sets.
        * sets.
        * eapply Disjoint_Included_r. eapply funname_fun_map_add_fundefs. eapply Union_Disjoint_r; [| now sets ].
          eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. now sets.         
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r; [| now sets ].
        eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. now sets.
      + eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un. eassumption.
        eapply Union_Disjoint_r; [| eassumption ].
        * eapply Disjoint_sym. eapply Disjoint_Included_r. eapply funname_fun_map_fun_map_get. eassumption.
          sets.
      + eapply Union_Disjoint_r. now sets. 
        eapply Disjoint_Included_r. eapply image_apply_r_set_list. eassumption.
        eapply Union_Disjoint_r. now sets. xsets.
  Qed.
  
  Opaque preord_exp'.


  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase (m1 : inlineM (list (ctor_tag * exp))) (x : var) y :
    st_eq
      (bind (ys <- m1 ;; ret (y :: ys)) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;; ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    repeat rewrite pbind_bind.
    eapply st_eq_transitive. eapply (assoc m1). simpl. 
    rewrite (assoc m1).
    apply bind_Proper_r; auto; intros x0.
    now do 2 rewrite left_id.
  Qed.

  Definition Ecase_shape sig (e e' : exp) : Prop :=
    match e with
    | Ecase x l => exists cl, e' = Ecase (apply_r sig x) cl /\ Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') l cl
    | _ => True
    end.
             

  Lemma inline_correct_mut d : 
    (forall e sig fm st S
            (Hun : unique_bindings e)
            (Hdis1 : Disjoint _ (bound_var e) (occurs_free e :|: occurs_free_fun_map fm))
            (Hdis1' : Disjoint _ (bound_var e :|: bound_var_fun_map' fm) (image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm)))
            (Hdis2 : Disjoint _ S ((bound_var e :|: bound_var_fun_map' fm) :|: image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm)))
            (Hdis3 : Disjoint _ (bound_var e \\ funname_in_exp e) (Dom_map fm :|: funname_fun_map fm))
            (Hdis4 : Disjoint _ (funname_in_exp e) (bound_var_fun_map fm))
            
            (Hfm : fun_map_vars fm S sig),
        {{ fun _ s => fresh S (next_var (fst s)) }}
          beta_contract St IH d e sig fm st
        {{ fun _ s e' s' =>
             fresh S (next_var (fst s')) /\ next_var (fst s) <= next_var (fst s') /\
             unique_bindings e' /\
             occurs_free e' \subset image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm) /\
             bound_var e' \subset (Range (next_var (fst s)) (next_var (fst s')))  /\ Ecase_shape sig e e' /\
             (forall k rho1 rho2,
                 preord_env_P_inj cenv PG (occurs_free e) k (apply_r sig) rho1 rho2 ->
                 fun_map_inv d (occurs_free e) fm rho1 rho2 k sig ->
                 preord_exp cenv P1 PG k (e, rho1) (e', rho2)) }} ) /\ 

    (forall B sig sig0 fm st S
            (Hun : unique_bindings_fundefs B)
            (Hdis1 : Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B :|: (occurs_free_fun_map fm \\ name_in_fundefs B)))
            (Hdis1' : Disjoint _ (bound_var_fundefs B :|: bound_var_fun_map' fm) (image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm)))

            (Hdis2 : Disjoint _ S ((bound_var_fundefs B :|: bound_var_fun_map' fm):|: image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm)))
            (Hdis3 : Disjoint _ (bound_var_fundefs B \\ name_in_fundefs B \\ funname_in_fundefs B) (Dom_map fm :|: funname_fun_map fm))
            (Hdis4 : Disjoint _ (funname_in_fundefs B) (bound_var_fun_map fm))            
            (Hfm : fun_map_vars fm S sig)
            (Hnames1 : NoDup (apply_r_list sig (all_fun_name B)))
            (Hnames2 : Disjoint _ (S :|: (bound_var_fundefs B :|: bound_var_fun_map' fm)) (FromList (apply_r_list sig (all_fun_name B)))), 
        {{ fun _ s => fresh S (next_var (fst s)) }}
          beta_contract_fundefs St IH d sig0 sig fm B st
        {{ fun _ s B' s' =>
             fresh S (next_var (fst s')) /\ next_var (fst s) <= next_var (fst s') /\
             unique_bindings_fundefs B' /\
             occurs_free_fundefs B' \subset image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm) /\
             bound_var_fundefs B' \\ name_in_fundefs B' \subset (Range (next_var (fst s)) (next_var (fst s'))) /\
             all_fun_name B' = apply_r_list sig (all_fun_name B) /\
             (forall f xs ft e1,
                 find_def f B = Some (ft, xs, e1) ->
                 exists xs' e2,
                   find_def (apply_r sig f) B' = Some (ft, xs', e2) /\
                   length xs = length xs' /\ NoDup xs' /\ FromList xs' \subset S /\
                   (forall rho1 rho2 k,
                       preord_env_P_inj cenv PG (occurs_free_fundefs B :|: name_in_fundefs B :|: FromList xs)
                                        k (apply_r sig <{ xs ~> xs' }>) rho1 rho2 ->
                       fun_map_inv d (occurs_free_fundefs B :|: name_in_fundefs B :|: FromList xs) fm rho1 rho2 k (set_list (combine xs xs') sig) ->
                       preord_exp cenv P1 PG k (e1, rho1) (e2, rho2))) }}).
  
  Proof.
    induction d as [d IHd] using lt_wf_rec1.
    exp_defs_induction IHe IHl IHB; intros; inv Hun; try rewrite beta_contract_eq.
    - (* constr *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_name_fresh. 
      intros x w1. simpl. eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros HinS. 
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        rewrite Setminus_Union_distr. now sets.
        eapply Disjoint_Singleton_r. eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply image_apply_r_set. eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
        rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.
      + eapply Disjoint_Included_r.
        eapply Included_Union_compat. reflexivity.
        eapply image_apply_r_set. 
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' Hsem]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; omega.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union.
          rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity. 
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; omega. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; omega.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_constr_compat.
          now eauto. now eauto.
          eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.          
          intros. eapply Hsem. 
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free. sets.
          -- rewrite preord_val_eq. split. reflexivity.
             eapply Forall2_Forall2_asym_included. eassumption.
          -- intros Hc. eapply Hdis2. constructor. eapply Hf. eapply Hf1. 
             right. normalize_occurs_free. rewrite !image_Union. left. right. eassumption.
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. omega.
             intros Hc. inv Hc.
             ++ eapply Hdis1. normalize_bound_var. normalize_occurs_free. constructor. now right. eauto.
             ++ eapply Hdis3. constructor. normalize_bound_var. simpl. constructor. now right.
                intros Hc. eapply H1. eapply funname_in_exp_subset. eassumption.
                now left; eauto.
             ++ intros Hc. eapply Hdis2. constructor; try eassumption. rewrite image_Union. do 2 right. eassumption.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci.
    - (* Ecase [] *)
      simpl. eapply bind_triple.
      eapply return_triple with (Q := fun r w l w' => fresh S (next_var (fst w)) /\ fresh S (next_var (fst w')) /\ l = [] /\ next_var (fst w) <= next_var (fst w')). now intros; eauto.
      intros xs w'. simpl. eapply return_triple. simpl; intros.  destructAll.
      split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + constructor.
      + simpl. normalize_occurs_free. sets.
      + normalize_bound_var. sets.
      + intros. eapply preord_exp_case_nil_compat. now eauto.
    - (* Ecase (_ :: _) *)
      simpl. setoid_rewrite assoc. eapply bind_triple.
      + eapply pre_transfer_r. eapply IHe.
        * eassumption.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1' ]; sets.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          xsets.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_l; [| eassumption ]. simpl. rewrite Setminus_Union_distr.
          eapply Included_Union_preserv_l. rewrite <- Setminus_Union. eapply Included_Setminus; [| sets ].          
          eapply Disjoint_Included; [| | eapply H5 ].
          eapply Included_trans; [| eapply funname_in_exp_subset ]. now sets. now sets.
        * sets.
        * eassumption.
      + intros e' w. simpl.
        eapply pre_curry_l. intros Hf. eapply pre_strenghtening.
        { intros. destructAll.
          eapply (conj H8 (conj H7 (conj H3 (conj H1 (conj H6 (conj H0 H)))))). }
        
        eapply pre_curry_l. intros Hrel. eapply pre_curry_l. intros Hcase. eapply pre_curry_l. intros Hfv. eapply pre_curry_l. intros Hun. 
        setoid_rewrite st_eq_Ecase. eapply bind_triple.
        * setoid_rewrite beta_contract_eq in IHl. unfold beta_contract' in IHl.
          do 2 eapply frame_rule. eapply pre_transfer_r.
          eapply IHl.
          -- eassumption.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             eapply Disjoint_Included; [| | eapply Hdis1' ]; sets.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             xsets.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             eapply Disjoint_Included_l; [| eassumption ]. simpl. rewrite Setminus_Union_distr.
             eapply Included_Union_preserv_r. rewrite Union_commut. rewrite <- Setminus_Union.
             eapply Included_Setminus; [| now sets ].             
             eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H5 ]. now sets.
             eapply funname_in_exp_subset.
          -- sets.
          -- eassumption.
        * intros ce w'. simpl. eapply pre_curry_l. intros Hbv. eapply pre_curry_l. intros Hleq.
          eapply pre_curry_l. intros Hf'.
          eapply pre_strenghtening.
          { intros. destruct H as (H1 & H2' & H3 & H4' & H5' & H6 & H7).
            eapply (conj H6 (conj H1 (conj H2' (conj H3 (conj H4' (conj H5' H7)))))). }
          eapply pre_curry_l. intros Hex. destructAll.
          eapply return_triple. intros. destructAll.
          split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
          ++ zify; omega.
          ++ constructor. eassumption. eassumption.
             eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_Range. reflexivity.
          ++ repeat normalize_occurs_free. eapply Union_Included; [| eapply Union_Included ].
             ** rewrite !image_Union, image_Singleton. sets.
             ** eapply Included_trans. eassumption. sets.
             ** eapply Included_trans. eassumption. sets.
          ++ normalize_bound_var. eapply Union_Included.
             ** eapply Included_trans. eassumption. eapply Range_Subset. reflexivity. eassumption.
             ** eapply Included_trans. eassumption. eapply Range_Subset. eassumption. reflexivity.
          ++ intros. eapply preord_exp_case_cons_compat.
             ** now eauto.
             ** now eauto.
             ** now eauto.
             ** now eauto.
             ** eapply H9. now constructor.
             ** intros. eapply Hrel.
                --- eapply preord_env_P_inj_monotonic; [| eapply preord_env_P_inj_antimon; [ eassumption | ]].
                    omega. normalize_occurs_free. sets.
                --- eapply fun_map_inv_antimon. eapply fun_map_inv_mon. eapply fun_map_inv_i_mon. eassumption.
                    omega. omega. normalize_occurs_free. sets.
             ** eapply H8.
                --- eapply preord_env_P_inj_monotonic; [| eapply preord_env_P_inj_antimon; [ eassumption | ]].
                    omega. normalize_occurs_free. sets.
                --- eapply fun_map_inv_antimon. eapply fun_map_inv_mon. eapply fun_map_inv_i_mon. eassumption.
                    omega. omega. normalize_occurs_free. sets.
    - (* Eproj *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_name_fresh. 
      intros x w1. simpl. eapply pre_curry_l. intros Hf.  eapply pre_curry_l. intros Hsin.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets. rewrite Setminus_Union_distr. sets.
        eapply Disjoint_Singleton_r. eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply image_apply_r_set. eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
        rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.  
      + eapply Disjoint_Included_r.
        eapply Included_Union_compat. reflexivity.
        eapply image_apply_r_set. 
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' Hsem]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; omega.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union, image_Singleton. eapply Union_Included. now sets.
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; omega. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; omega.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_proj_compat.
          now eauto. now eauto. eapply Henv. now constructor.
          intros. eapply Hsem. 
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free. sets.
          -- eassumption.
          -- intros Hc. eapply Hdis2. constructor. eapply Hf. eapply Hf1. 
             right. normalize_occurs_free. rewrite !image_Union. left. right. eassumption.
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. omega.
             intros Hc. inv Hc. 
             ++ eapply Hdis1. normalize_bound_var. constructor. now right. now right; eauto.
             ++ eapply Hdis3. constructor. normalize_bound_var. simpl. constructor. now right.
                intros Hc. eapply H1. eapply funname_in_exp_subset. eassumption.
                now left; eauto.
             ++ intros Hc. eapply Hdis2. constructor. eassumption. rewrite image_Union. do 2 right. eassumption.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci.
    - (* Eletapp *)
      simpl. Opaque beta_contract.  destruct (update_letApp St IH (apply_r sig f) ft (apply_r_list sig ys) st).
      match goal with
      | [ _ : _ |- {{ ?P }} (if _ then _ else ?E) {{ ?Q }} ] => set (Lemm := {{ P }} E {{ Q }})
      end.
      assert (Hsame : Lemm).
      { unfold Lemm. eapply bind_triple. eapply pre_transfer_r. eapply get_name_fresh. intros x' w1.
        simpl. eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros HSin.
        eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x']).
        - eassumption.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set x]). tci.
          eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
          rewrite Setminus_Union_distr. now sets. eapply Disjoint_Singleton_r. eassumption.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_r. eapply image_apply_r_set. eapply Union_Disjoint_r.
          eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
          rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_r.
          eapply Included_Union_compat. reflexivity.
          eapply image_apply_r_set. 
          eapply Union_Disjoint_r. now sets. eapply Union_Disjoint_r. now sets.
          eapply Disjoint_Included; [| | eapply Hdis2 ]; [| now sets ].
          eapply Included_Union_preserv_r. eapply image_monotonic. rewrite Setminus_Union_distr. sets. 
        - eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
        - eassumption.
        - eapply fun_map_vars_set. eassumption.
        - intros e' w2. eapply return_triple.
          intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' Hsem]]]]]]].
          split; [| split; [| split; [| split; [| split; [| split ]]]]].
          * eapply fresh_monotonic;[| eassumption ]. sets.
          * zify; omega.
          * constructor; [| eassumption ].
            intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
            reflexivity.
          * repeat normalize_occurs_free. rewrite !image_Union.
            rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat.
            rewrite image_Singleton. now sets. eapply Union_Included. now sets. 
            eapply Included_trans. eapply Included_Setminus_compat.
            eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
            rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
            rewrite image_Union. rewrite !Setminus_Union_distr. eapply  Union_Included; xsets.
          * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
            eapply Range_Subset. zify; omega. reflexivity.
            eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
            zify; omega.
          * simpl; eauto.
          * intros r1 r2 k Henv Hfm'. eapply preord_exp_letapp_compat.
            now eauto. now eauto. now eauto.
            eapply Henv. econstructor. now left.
            eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.          
            intros. eapply Hsem. 
            rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
            -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
               omega. normalize_occurs_free. sets.
            -- eassumption.
            -- intros Hc. eapply Hdis2. constructor. eapply Hf. eapply Hf1. 
               right. normalize_occurs_free. rewrite !image_Union. left. right. eassumption.
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. omega.
             intros Hc. inv Hc.
             ++ eapply Hdis1. constructor. normalize_bound_var. now right. right; eassumption.
             ++ eapply Hdis3. constructor. normalize_bound_var. simpl. constructor. now right.
                intros Hc. eapply H1. eapply funname_in_exp_subset. eassumption.
                now left; eauto.
             ++ intros Hc. eapply Hdis2. constructor. eassumption. rewrite image_Union.
                do 2 right. eassumption.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci. }
        
      destruct b. 
      + destruct (fm ! f) as [ [[? ?] ?] | ] eqn:Hf.
        * destruct d. eassumption.
          destruct (Datatypes.length l =? Datatypes.length ys)%nat eqn:Hlen; [| eassumption ]. 
          eapply beq_nat_true in Hlen.
          eapply bind_triple. eapply pre_transfer_r. now eapply get_name_fresh. 
          intros z w. simpl. eapply pre_curry_l. intros Hfx. eapply pre_curry_l. intros HSin. 
          { edestruct Hfm. eassumption. destructAll. eapply bind_triple.
            - do 2 eapply frame_rule. eapply pre_transfer_r. eapply IHd.
              + omega.
              + eassumption.
              + eapply Union_Disjoint_r. sets. admit.
              + eapply Disjoint_Included_r. eapply image_apply_r_set_list. unfold apply_r_list. rewrite map_length. eassumption.
                eapply Union_Disjoint_r.
                * eapply Disjoint_Included; [ | | eapply Hdis1' ].
                  rewrite FromList_apply_list. normalize_occurs_free. rewrite !image_Union. now sets.
                  eapply Union_Included; [| now sets ].
                  eapply Included_Union_preserv_r.
                  eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. sets.
                * eapply Disjoint_Included; [| | eapply Hdis1' ]. rewrite image_Union.
                  eapply Included_Union_preserv_r. eapply image_monotonic. rewrite Setminus_Union_distr. 
                  eapply Union_Included; [| now sets ]. eapply occurs_free_fun_map_get; eauto.
                  eapply Union_Included; [| now sets ]. eapply Included_Union_preserv_r.
                  eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
              + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. eapply Union_Disjoint_r.
                eapply Union_Disjoint_r. now sets. clear H7. now sets.
                eapply Disjoint_Included_r.
                eapply image_apply_r_set_list. unfold apply_r_list. rewrite map_length. eassumption. 
                eapply Union_Disjoint_r.
                rewrite FromList_apply_list.
                eapply Disjoint_Included; [| | eapply Hdis2 ]; [| now sets ]. rewrite !image_Union. now sets.
                
                rewrite !Setminus_Union_distr. rewrite image_Union. eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply H7 ]; now sets.
                eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.

              + sets.
              + sets.
              + (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                repeat (split; [ now eauto |]). eapply Union_Disjoint_r. now sets.
                eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                unfold apply_r_list. rewrite list_length_map. eassumption.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply Hdis2 ]. normalize_occurs_free.
                rewrite !image_Union. rewrite FromList_apply_list. now sets. now sets. now xsets.
            - intros ei w'. simpl. eapply pre_curry_l; intros Hfr. eapply pre_curry_l; intros Hleq. 
              eapply pre_curry_l; intros Hfz.
              destruct (inline_letapp ei z) as [ [C r] | ] eqn:Hinl.
              eapply pre_strenghtening.
              { intros. destructAll.
                assert (Hfr' : fresh (S \\ [set z] \\ bound_var ei) (next_var (fst s0))).
                { intros u Hleq'. constructor. eapply H8; eauto.
                  intros Hnin. eapply H12 in Hnin. unfold Ensembles.In, Range in Hnin. zify. omega. }
                assert (Hbv : bound_var ei \subset S \\ [set z]).
                { eapply Included_trans. eassumption. intros y Hin. unfold Ensembles.In, Range in *. inv Hin.
                  eapply Hfz. eassumption. }
                
                eapply (conj Hbv (conj H14 (conj H13 (conj H11 (conj H10 (conj H8 (conj H9 (conj H12 Hfr')))))))). }

              eapply pre_curry_l. intros Hbv. 
              eapply pre_curry_l. intros Hrel. eapply pre_curry_l. intros Hcase. eapply pre_curry_l. intros Hfv. eapply pre_curry_l. intros Hun.
              
              assert (Hdisr : Disjoint var (S \\ [set z] \\ bound_var ei :|: (bound_var e :|: bound_var_fun_map' fm)) [set r]).
              { edestruct inline_letapp_var_eq. eassumption.
                - subst. eapply Union_Disjoint_l. now sets. eapply Disjoint_sym.
                  eapply Disjoint_Included_l. eapply Singleton_Included. eapply HSin.
                  repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                  eapply Disjoint_Included_r; [ | eapply Hdis2 ]. now sets. 
                - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                  inv H8.
                  + eapply Disjoint_Included_r. eapply Singleton_Included. eassumption. eapply Union_Disjoint_l.
                    * sets.
                    * eapply Disjoint_Included_r. eassumption. eapply Disjoint_sym.
                      eapply Disjoint_Included; [ | | eapply Hdis2 ]. now sets. now sets.
                  + eapply Disjoint_Included_r. eapply Included_trans. eapply Singleton_Included. eassumption.
                    eassumption.
                    eapply Disjoint_Included_r. eapply image_apply_r_set_list. unfold apply_r_list. rewrite map_length. now eauto.
                    rewrite !Setminus_Union_distr, image_Union.
                    eapply Union_Disjoint_r; [| eapply Union_Disjoint_r ].
                    rewrite FromList_apply_list.
                    eapply Union_Disjoint_l. eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.
                    eapply Disjoint_Included; [| | eapply Hdis1' ]; now sets.
                    eapply Union_Disjoint_l. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis1' ]. rewrite image_Union. eapply Included_Union_preserv_r.
                    eapply image_monotonic. eapply occurs_free_fun_map_get; eauto. now sets. 
                    eapply Union_Disjoint_l.  eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.
                     eapply Disjoint_Included; [| | eapply Hdis1' ]; now sets. }
              
              eapply bind_triple.
              + do 3 eapply frame_rule.
                { eapply IHd.
                  + omega.
                  + eassumption.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set x]). tci.
                    eapply Union_Disjoint_r. rewrite Setminus_Union_distr. now eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
                    eapply Disjoint_Singleton_r. eassumption.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_r.
                    eapply image_apply_r_set. eapply Union_Disjoint_r. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis1' ]. rewrite Setminus_Union_distr. now sets. now sets.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.
                    eapply Disjoint_Included_r.
                    eapply image_apply_r_set. eapply Union_Disjoint_r. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis2 ]. rewrite Setminus_Union_distr. now sets. now sets.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_l; [| eapply Hdis3 ]. simpl. rewrite Setminus_Union_distr. xsets.
                  + sets.
                  + (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                    intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                    repeat (split; [ now eauto |]). eapply Union_Disjoint_r. now sets.
                    eapply Disjoint_Included_r. eapply image_apply_r_set.
                    eapply Union_Disjoint_r. now sets. now xsets. }
              + intros e' w''. eapply return_triple. intros _ w''' Hyp. destructAll.
                split; [| split; [| split; [| split; [| split; [| split ]]]]].
                * eapply fresh_monotonic; [| eassumption ]. sets.
                * zify; omega.
                * eapply (proj1 (ub_app_ctx_f e')). split; [| split ]; [| eassumption |].
                  eapply unique_bindings_inline_letapp; [ eassumption | | eassumption ].
                  intros Hc. eapply H10 in Hc.
                  unfold Ensembles.In, Range in Hc, Hfr. zify; omega.
                  eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
                  eapply Union_Disjoint_l.
                  -- eapply Disjoint_Included_r. eassumption. eapply Disjoint_Singleton_l.
                     intros Hc. unfold Ensembles.In, Range in Hc, Hfr. zify; omega.
                  -- eapply Disjoint_Included. eassumption. eassumption.
                     eapply Disjoint_Range. reflexivity.
                * eapply Included_trans. eapply occurs_fee_inline_letapp. eassumption.
                  assert (Hsub : occurs_free ei :|: (occurs_free e' \\ stemctx.bound_stem_ctx C) \subset
                                             occurs_free ei :|: (occurs_free e' \\ [set r])).
                  { edestruct inline_letapp_var_eq_alt. eassumption. inv H18; subst. now sets.
                    inv H18. now sets. rewrite Union_Setminus_Included with (s3 := [set r]); tci. sets.
                    sets. }
                  eapply Included_trans. eassumption. eapply Union_Included.
                  -- eapply Included_trans. eassumption. eapply Included_trans.
                     eapply image_apply_r_set_list. unfold apply_r_list. rewrite map_length. eassumption.
                     normalize_occurs_free. rewrite Setminus_Union_distr, !image_Union. eapply Union_Included.
                     rewrite FromList_apply_list. now sets.
                     eapply Union_Included; [| now sets ]. eapply Included_trans.
                     eapply image_monotonic. eapply occurs_free_fun_map_get. eassumption. sets.
                  -- eapply Included_trans. eapply Included_Setminus_compat.
                     eapply Included_trans. eassumption. eapply image_apply_r_set. reflexivity.
                     rewrite Setminus_Union_distr. eapply Union_Included. now sets.
                     normalize_occurs_free. rewrite !Setminus_Union_distr. now sets. 
                * rewrite bound_var_app_ctx. eapply Union_Included.
                  -- eapply Included_trans. eapply bound_var_inline_letapp. eassumption.
                     eapply Union_Included.
                     eapply Singleton_Included. unfold Ensembles.In, Range in *. zify; omega.
                     eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. zify; omega.
                  -- eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. zify; omega.
                * eauto.                     
                * intros. eapply inline_letapp_correct_alt with (C' := Hole_c);
                            [ | | | | | | | | | | now eauto | eassumption ]. 
                  -- eassumption.
                  -- eassumption.
                  -- eassumption.
                  -- eassumption.
                  -- eauto.
                  -- simpl. intros. edestruct H19 with (f0 := f). constructor. now left. eassumption. eassumption.
                     destructAll. do 2 subst_exp. eapply Hrel.
                     ++ edestruct preord_env_P_inj_get_list_l. now eapply H18. normalize_occurs_free. now sets.
                        eassumption. destructAll.                           
                        eapply preord_env_P_inj_set_lists_l'; try eassumption.
                        eapply preord_env_P_inj_monotonic; [| eassumption ]. omega.
                        eapply List_util.Forall2_monotonic; [| eassumption ].
                        intros. eapply preord_val_monotonic. eassumption. omega.
                     ++ eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | eassumption ].
                        ** eapply fun_map_inv_sig_extend_Disjoint. rewrite <- fun_map_inv_eq in *.
                           eapply fun_map_inv_i_mon. eassumption. omega. admit.
                           (* SearchAbout l. eapply Disjoint_Included; [| | eapply Hdis1 ]. sets.  *)
                           (* sets. rewrite Dom_map_def_funs. sets. *)
                        ** eassumption.
                        ** eapply Union_Disjoint_r. admit.
                           clear H29. xsets.
                        ** rewrite Union_Setminus_Included. sets. tci. sets.
                  -- intros. edestruct H19 with (f0 := f). constructor. now left. eassumption. eassumption.
                     destructAll. subst_exp. eapply H17.
                     ++ rewrite apply_r_set_f_eq. eassumption.
                     ++ eapply fun_map_inv_antimon.
                        2:{ eapply Included_trans. eapply Included_Union_Setminus with (s2 := [set x]); tci.
                            rewrite Union_commut. reflexivity. }
                        eapply fun_map_inv_sig_extend_one_Disjoint.
                        ** eapply fun_map_inv_env_eq_P.
                           eapply fun_map_inv_antimon. eapply fun_map_inv_mon.
                           eapply fun_map_inv_i_mon. eassumption. omega. omega. normalize_occurs_free. now sets.
                           
                           eapply eq_env_P_refl. 
                           eapply eq_env_P_antimon. eassumption.
                           normalize_bound_var_ctx. normalize_sets. intros y Hin Hin'.
                           eapply bound_var_inline_letapp in Hin'; [| eassumption ]. eapply Hdis2.
                           constructor. 2:{ right. rewrite image_Union. right. eassumption. }
                           inv Hin'. inv H28.
                           eapply Hfx. unfold Ensembles.In, Range in *. zify; omega.
                           eapply H10 in H28. eapply Hfx. unfold Ensembles.In, Range in *. zify; omega.
                        ** eassumption.
                        ** intros Hc. eapply Hdis3. constructor. 2:{ now left; eauto. }
                           normalize_bound_var. simpl. rewrite Setminus_Union_distr. right.
                           constructor. reflexivity. intros Hc1. eapply H1. eapply funname_in_exp_subset. eassumption.
                        ** intros Hc. eapply Hdis1. constructor. now constructor. now eauto.
                        ** intros Hc. inv Hc; eauto.
                  -- eassumption.
                  -- normalize_bound_var_ctx. normalize_sets.
                     eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
                     eapply Disjoint_Included; [| | eapply Hdis2 ]. normalize_occurs_free. rewrite image_Union. now sets.
                     eapply Union_Included. intros u Hc. inv Hc. eapply Hfx. unfold Ensembles.In, Range in *. zify; omega.
                     intros u Hc. eapply H10 in Hc. unfold Ensembles.In, Range in *. eapply Hfx. zify; omega.
                  -- intros Hc. eapply Hdis1'. normalize_occurs_free. normalize_bound_var.
                     constructor. now eauto. rewrite !image_Union. now eauto.
             + eapply post_weakening. 
                2:{ eapply pre_transfer_r. eapply pre_strenghtening. 2:{
                      eapply post_weakening; [| eassumption ]. simpl. intros.
                      eapply (conj H8 H9). }
                    simpl. intros.  destructAll. eapply fresh_monotonic; [| eassumption ]. sets. }
                simpl. intros. destructAll.
                split; [| split; [| split; [| split; [| split ]]]]; eauto.
                * zify; omega.
                * eapply Included_trans. eassumption. eapply Range_Subset; eauto.
                  zify; omega. zify; omega. }
        * eassumption.
      + eassumption.
    - (* Efun *) 
      simpl. destruct (update_funDef St IH f2 sig st). 
      eapply bind_triple. eapply pre_transfer_r. now eapply get_names_lst_fresh. intros xs w. simpl.
      eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros Hnd.  eapply pre_curry_l. intros Hlen.

      assert (Hsame1 : bound_var_fundefs f2 \\ funname_in_fundefs f2 \\ name_in_fundefs f2 \subset bound_var (Efun f2 e) \\ funname_in_exp (Efun f2 e)).
      { normalize_bound_var. simpl. rewrite !Setminus_Union_distr. eapply Included_Union_preserv_l.
        rewrite <- !Setminus_Union. eapply Included_Setminus; [| now sets ].
        eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets. } 

      assert (Hsame2 : bound_var e \\ funname_in_exp e \subset bound_var (Efun f2 e) \\ funname_in_exp (Efun f2 e)).
      { normalize_bound_var. simpl. rewrite !Setminus_Union_distr. eapply Included_Union_preserv_r.
        rewrite (Union_commut _ (funname_in_exp _)). rewrite <- Setminus_Union. eapply Included_Setminus; [| now sets ].
        eapply Disjoint_Included_r. eapply Union_Included. eapply funname_in_fundefs_subset.
        eapply name_in_fundefs_bound_var_fundefs. sets. } 

      
      assert (Hfm' : fun_map_vars (add_fundefs f2 fm) (S \\ FromList xs) (set_list (combine (all_fun_name f2) xs) sig)).
      { eapply fun_map_vars_def_funs; (try now eauto).
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        + eapply Disjoint_Included_l; [| eapply Hdis3 ]. eassumption.
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. xsets.
        + sets.
        + sets. }

      assert (Hnd' := NoDup_all_fun_name _ H2).
      assert (Hseq :  apply_r_list (set_list (combine (all_fun_name f2) xs) sig) (all_fun_name f2) = xs).
      { rewrite apply_r_list_eq. reflexivity. now eauto. now eauto. }
      eapply pre_curry_l. intros Hin. 
      eapply bind_triple. 
      { do 2 eapply frame_rule. eapply IHB with (S := S \\ FromList xs).
        - eassumption.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx. eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
          eapply Disjoint_Included_r. eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets. 
          eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
        - eapply Disjoint_Included.
          + eapply Included_trans. eapply image_apply_r_set_list. now eauto.
            rewrite <- Same_set_all_fun_name. rewrite !Setminus_Union_distr. eapply Included_Union_compat. reflexivity.
            eapply image_monotonic. eapply Included_Union_compat. reflexivity. eapply Included_Setminus_compat.
            eapply occurs_free_fun_map_add_fundefs. reflexivity.
          + eapply Included_Union_compat. reflexivity. eapply bound_var_fun_map_add_fundefs_un'. eassumption.
          + rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets. eapply Union_Disjoint_r.
            * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. normalize_bound_var. now sets. eassumption.
            * eapply Disjoint_Included; [| | eapply Hdis1' ]. normalize_occurs_free. eapply image_monotonic. now sets.
              normalize_bound_var. now sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx. eapply Union_Disjoint_r.
          + eapply Union_Disjoint_r. sets. eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un'. eassumption. xsets.
          + eapply Disjoint_Included_r. eapply image_apply_r_set_list. now eauto.
            rewrite <- Same_set_all_fun_name. rewrite !Setminus_Union_distr. rewrite !image_Union. 
            repeat (eapply Union_Disjoint_r; sets).
            now xsets.
            eapply Disjoint_Included_r. eapply image_monotonic. eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
            rewrite !Setminus_Union_distr.  rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets. now xsets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r.
          + eapply Union_Disjoint_r. now sets.
            eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets.
            rewrite Setminus_Union. rewrite Union_commut. rewrite <- Setminus_Union. eassumption.
          + eapply Disjoint_Included_r. eapply funname_fun_map_add_fundefs. eapply Union_Disjoint_r. now sets.
            eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets.
            rewrite Setminus_Union. rewrite Union_commut. rewrite <- Setminus_Union. eassumption.
        - eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un. eassumption. eapply Union_Disjoint_r.
          + now sets.
          + now sets.
        - eassumption.
        - rewrite Hseq. eassumption.
        - rewrite Hseq. eapply Union_Disjoint_l. now sets.
          eapply Disjoint_Included_r. eassumption. eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply Hdis2 ]. normalize_bound_var.
          eapply Union_Included. now sets. eapply Included_trans. eapply bound_var_fun_map_add_fundefs_un'. eassumption. sets. }

      intros fds' w'. simpl.
      eapply pre_curry_l. intros Hsub. eapply pre_curry_l. intros Hr. 
      eapply bind_triple.
      { eapply pre_strenghtening.
        2:{ eapply frame_rule. eapply IHe with (S := S \\ FromList xs).
            + eassumption.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              * eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). now tci.
                eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; try now sets.
                rewrite Setminus_Union_distr. eapply Union_Included. now sets.  eapply Included_trans.
                eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
                rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets. now sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_l. eapply Included_Union_compat. reflexivity. eapply bound_var_fun_map_add_fundefs_un'. eassumption. 
              eapply Disjoint_Included_r. 
              eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r.
              * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. eassumption.
              * rewrite <- Same_set_all_fun_name. rewrite Setminus_Union_distr.
                rewrite image_Union. eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.
                eapply Disjoint_Included_r. eapply image_monotonic. eapply Included_Setminus_compat.
                eapply occurs_free_fun_map_add_fundefs. reflexivity.
                rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets.
                eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. eapply Union_Disjoint_r. eapply Union_Disjoint_r. 
              now sets.
              eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un'. eassumption. now xsets.
              eapply Disjoint_Included_r. 
              eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r.
              * now sets.
              * rewrite <- Same_set_all_fun_name. rewrite Setminus_Union_distr.
                rewrite image_Union. eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
                eapply Disjoint_Included_r. eapply image_monotonic. eapply Included_Setminus_compat.
                eapply occurs_free_fun_map_add_fundefs. reflexivity.
                rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets.
                eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r.
              * eapply Union_Disjoint_r.
                -- eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
                -- eapply Disjoint_Included; [| | eapply Hdis3 ]; sets.
              * eapply Disjoint_Included_r. eapply funname_fun_map_add_fundefs. eapply Union_Disjoint_r.
                -- eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
                -- eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets. eassumption.
            + eapply Disjoint_Included_r. eapply bound_var_fun_map_add_fundefs_un. eassumption. eapply Union_Disjoint_r.
              * eapply Disjoint_Included_l. eapply funname_in_exp_subset. sets.
              * sets.
            + eassumption. }        
        simpl. intros u w1 [Hyp Hyp']. split. eapply Hyp'. eassumption. }


      intros e' w''. eapply return_triple. intros _ w''' Hyp. destructAll.
      split; [| split; [| split; [| split; [| split; [| split ]]]]].
      * eapply fresh_monotonic; [| eassumption ]. sets.
      * zify; omega. 
      * constructor. eassumption. eassumption.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs fds'). now tci.
        eapply Union_Disjoint_r.
        -- eapply Disjoint_Included. eassumption. eassumption.
           eapply Disjoint_sym. eapply Disjoint_Range. reflexivity.
        -- rewrite Same_set_all_fun_name. rewrite H13. rewrite Hseq.
           eapply Disjoint_Included. eassumption. eassumption.
           eapply Disjoint_sym. eapply Disjoint_Range. zify; omega.
      * repeat normalize_occurs_free. eapply Union_Included.
        -- eapply Included_trans. eapply Included_Setminus. eapply Disjoint_sym.
           eapply occurs_free_fundefs_name_in_fundefs_Disjoint. reflexivity.
           eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
           eapply Included_trans. eapply image_apply_r_set_list. now eauto.
           rewrite (Same_set_all_fun_name fds'). rewrite H13.
           rewrite apply_r_list_eq; eauto. eapply Union_Included. now sets. 
           eapply Included_Union_preserv_l. rewrite <- Same_set_all_fun_name.
           rewrite Setminus_Union_distr. rewrite !image_Union. eapply Union_Included. now sets.
           eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
           eapply occurs_free_fun_map_add_fundefs. reflexivity.
           rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set. repeat normalize_sets.
           rewrite image_Union. now xsets.
        -- eapply Included_trans. eapply Included_Setminus_compat. eassumption. reflexivity.
           eapply Setminus_Included_Included_Union. 
           eapply Included_trans. eapply image_apply_r_set_list. now eauto.
           rewrite (Same_set_all_fun_name fds'). rewrite H13.
           rewrite apply_r_list_eq; eauto. eapply Union_Included. now sets.
           eapply Included_Union_preserv_l. rewrite <- Same_set_all_fun_name.
           rewrite Setminus_Union_distr. rewrite !image_Union. eapply Union_Included. now sets.
           eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
           eapply occurs_free_fun_map_add_fundefs. reflexivity.
           rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set. repeat normalize_sets.
           rewrite image_Union. now xsets.
      * normalize_bound_var. eapply Union_Included.
        -- eapply Included_trans.
           eapply Included_Union_Setminus with (s2 := name_in_fundefs fds'). now tci. eapply Union_Included.
           ++ eapply Included_trans. eassumption. eapply Range_Subset; zify; omega. 
           ++ rewrite Same_set_all_fun_name. rewrite H13. rewrite Hseq.
              eapply Included_trans. eassumption. eapply Range_Subset; zify; omega. 
        -- eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. reflexivity.
      * eauto.
      * intros k rho1 rho2 Henv Hfm''. eapply preord_exp_fun_compat.
        now eauto. now eauto.
        assert (Hrel : preord_env_P_inj cenv PG
                                        (name_in_fundefs f2 :|: occurs_free (Efun f2 e)) 
                                        (k - 1) (apply_r (set_list (combine (all_fun_name f2) xs) sig))
                                        (def_funs f2 f2 rho1 rho1) (def_funs fds' fds' rho2 rho2)).
        { assert (Hi : (k - 1 <= k)%nat) by omega. 
          revert Hi. generalize (k - 1)%nat as i. intros i Hi. induction i as [i IHi] using lt_wf_rec1. 
          intros x HIn v Hgetx. destruct (Decidable_name_in_fundefs f2). destruct (Dec x).
          - rewrite def_funs_eq in Hgetx; [| now eauto ]. inv Hgetx. eexists. split.
            + rewrite def_funs_eq. reflexivity. eapply Same_set_all_fun_name. 
              rewrite H13. rewrite FromList_apply_list. eapply In_image.
              rewrite <- Same_set_all_fun_name. eassumption.
            + rewrite preord_val_eq. intros vs1 vs2 j t1 ys1 e2 rho1' Hlen' Hfind Hset.
              edestruct H14. eassumption. destructAll. 
              edestruct set_lists_length2 with (xs2 := x0) (vs2 := vs2) (rho' := def_funs fds' fds' rho2 rho2). 
              now eauto. eassumption. now eauto. do 3 eexists. split. eassumption. split. now eauto. 
              intros Hlt Hvs. eapply preord_exp_post_monotonic. eassumption. eapply H19. 
              * eapply preord_env_P_inj_set_lists_alt; [| eassumption | | | | | now eauto | now eauto ]. 
                -- eapply preord_env_P_inj_antimon. eapply IHi. eassumption. omega.
                   normalize_occurs_free. sets.
                -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
                   eassumption.
                -- eassumption.
                -- eassumption.
                -- eapply Disjoint_Included_r. eassumption.
                   eapply Disjoint_Included_l. eapply image_apply_r_set_list. now eauto.
                   eapply Union_Disjoint_l. now sets. rewrite <- Same_set_all_fun_name.
                   eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ].
                   normalize_occurs_free. now xsets. now sets.
              * assert (Hdisys : Disjoint positive (FromList ys1)
                                          (occurs_free_fundefs f2 :|: name_in_fundefs f2
                                                               :|: occurs_free_fun_map fm)).
                { rewrite Union_commut. rewrite Union_assoc. eapply Union_Disjoint_r.
                  - eapply Disjoint_Included_l.                          
                    eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eapply Hfind ]. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis1 ]. normalize_occurs_free. now sets. normalize_bound_var. now sets.
                  - eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. }
                eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | now eauto ].
                eapply fun_map_inv_set_lists_r; [| | now eauto ]. 
                -- rewrite <- Hseq. rewrite <- H13. eapply fun_map_inv_sig_extend_Disjoint.
                   eapply fun_map_inv_def_funs.
                   eapply fun_map_inv_i_mon. eassumption. omega. eapply preord_env_P_inj_antimon.
                   rewrite H13. rewrite Hseq. eapply IHi. eassumption. omega. normalize_occurs_free. now sets.
                   eassumption. normalize_occurs_free. now sets.
                   eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. normalize_bound_var.
                   eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets. 
                   
                   rewrite Same_set_all_fun_name, H13, Hseq. eapply Disjoint_Included ; [| | eapply Hdis2 ]. now sets. eassumption.
                   admit. 
                -- rewrite image_f_eq_subdomain.
                   2:{ rewrite apply_r_set_list_f_eq. eapply f_eq_subdomain_extend_lst_Disjoint.
                       eapply Disjoint_Included_r. eapply occurs_free_fun_map_add_fundefs. eassumption. }
                   eapply Disjoint_Included_r. 
                   eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r. 
                   eapply Disjoint_Included_l. eassumption. now sets.
                   rewrite <- Same_set_all_fun_name. eapply Disjoint_Included_l. eassumption. eapply Disjoint_Included_r.
                   eapply image_monotonic. eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
                   rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                   eapply Disjoint_Included; [| | eapply Hdis2 ]. normalize_occurs_free. now sets. now sets.
                -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                -- eapply Disjoint_Included_r. eapply Included_Union_compat. eapply occurs_free_fun_map_add_fundefs. 
                   eapply Dom_map_add_fundefs. rewrite !Union_assoc. eapply Union_Disjoint_r. now sets.
                   eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets.
                   eapply Included_trans. eapply fun_in_fundefs_FromList_subset. eapply find_def_correct. eassumption. eassumption.
                   normalize_bound_var. simpl. rewrite Setminus_Union_distr. eapply Included_Union_preserv_l.
                   rewrite <- !Setminus_Union. eapply Included_Setminus; [| now sets ]. eapply Disjoint_Included_r.
                   eapply funname_in_exp_subset. now sets.
                -- normalize_occurs_free. sets.
          - inv HIn. contradiction. rewrite def_funs_neq in Hgetx; [| eassumption ]. eapply Henv in Hgetx; [| eassumption ]. destructAll. 
            eexists. rewrite apply_r_set_list_f_eq. rewrite extend_lst_gso. rewrite def_funs_neq. 
            split; eauto. eapply preord_val_monotonic. eassumption. omega. 
            + intros Hc. eapply Same_set_all_fun_name in Hc. rewrite H13 in Hc. 
              rewrite apply_r_list_eq in Hc; [| | now eauto ]. eapply Hdis2. constructor. 
              2:{ right. eapply In_image. eauto. } 
              eapply fresh_Range. 2:{ eapply Hsub. eassumption. } eassumption. eassumption.
            + rewrite <- Same_set_all_fun_name. intros Hc. eapply Hdis1. constructor. normalize_bound_var. left.
              now eapply name_in_fundefs_bound_var_fundefs. now eauto. }
        eapply H9.
        -- eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free.
           rewrite !Union_assoc. rewrite Union_Setminus_Included; sets. tci.
        -- eapply fun_map_inv_antimon. rewrite <- Hseq. rewrite <- H13. eapply fun_map_inv_def_funs.
           eapply fun_map_inv_i_mon. eassumption. omega. rewrite H13, Hseq. eapply preord_env_P_inj_antimon.
           eassumption. normalize_occurs_free. now sets. eassumption. normalize_occurs_free. sets.
           eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. normalize_bound_var. now sets.

           rewrite Same_set_all_fun_name, H13, Hseq. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. eassumption.
           normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included. now sets. tci. now sets.
    - (* Eapp *)
      simpl. destruct (update_App St IH (apply_r sig v) t (apply_r_list sig l) st) as [s b] eqn:Hup. 
      + destruct b.
        * destruct (fm ! v) as [[[ft xs] e] |] eqn:Heqf.
          destruct d.
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
             ++ reflexivity.
             ++ constructor. 
             ++ repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ eauto.
             ++ intros. eapply preord_exp_app_compat.
                now eauto. now eauto.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.              
          -- destruct (Datatypes.length xs =? Datatypes.length l)%nat eqn:Hbeq.
             { symmetry in Hbeq. eapply beq_nat_eq in Hbeq.      
               edestruct Hfm. eassumption. destructAll. eapply post_weakening; [| eapply IHd ].
               ++ simpl. intros. destructAll.  
                  split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
                  ** eapply Included_trans. eassumption. 
                     eapply Included_trans. eapply image_apply_r_set_list.
                     unfold apply_r_list. rewrite list_length_map. eassumption.
                     normalize_occurs_free. rewrite !image_Union. rewrite FromList_apply_list.
                     eapply Union_Included. now sets.
                     rewrite !Setminus_Union_distr. rewrite !image_Union. eapply Included_Union_preserv_r.
                     eapply Union_Included; [| now sets ].
                     eapply image_monotonic. intros z Hin. do 4 eexists; split; eauto.
                  ** eauto.
                  ** intros. eapply preord_exp_app_l.
                     --- eauto.
                     --- eauto.
                     --- intros. assert (Hf := H15). assert (Heqf' := Heqf). edestruct H15; eauto. destructAll.
                         do 2 subst_exp. eapply H13.
                         +++ edestruct preord_env_P_inj_get_list_l. now eapply H14. normalize_occurs_free. now sets.
                             eassumption. destructAll.                           
                             eapply preord_env_P_inj_set_lists_l'; try eassumption.
                         +++ eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | eassumption ].
                             *** eapply fun_map_inv_sig_extend_Disjoint. rewrite <- fun_map_inv_eq in *. eassumption.
                                 eapply Disjoint_Included_l. eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
                                 admit.
                             *** eassumption.
                             *** eapply Union_Disjoint_r.
                                 eapply Disjoint_Included_l. eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
                                 admit. 
                                 clear H25. xsets.
                             *** rewrite Union_Setminus_Included. sets. tci. sets.
               ++ omega.
               ++ eassumption.
               ++ eapply Union_Disjoint_r. now sets. admit.
               ++ eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Union_Disjoint_r.
                  eapply Disjoint_Included; [ | | eapply Hdis1' ]. normalize_occurs_free.
                  rewrite !image_Union. rewrite FromList_apply_list. now sets.
                  eapply Union_Included; [| now sets ].
                  eapply Included_Union_preserv_r. eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
                  rewrite Setminus_Union_distr. rewrite !image_Union. eapply Union_Disjoint_r.
                  eapply Disjoint_Included; [| | eapply Hdis1' ]. eapply image_monotonic. eapply Included_Union_preserv_r.
                  eapply occurs_free_fun_map_get. eassumption.
                  eapply Included_Union_preserv_r. eapply Union_Included; [| now sets ].
                  eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
                  eapply Disjoint_Included; [| | eapply Hdis1' ]. eapply image_monotonic. eapply Included_Union_preserv_r. now sets.
                  eapply Included_Union_preserv_r. eapply Union_Included; [| now sets ].
                  eapply Included_trans; [| eapply bound_var_fun_map_get'; eauto ]. now sets.
               ++ eapply Union_Disjoint_r. eapply Union_Disjoint_r. now sets.
                  clear H5. now sets.
                  eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Disjoint_Included; [ | | eapply Hdis2 ]. normalize_occurs_free.
                  rewrite !image_Union. rewrite FromList_apply_list.
                  eapply Union_Included; [ now sets  | ]. rewrite Setminus_Union_distr, !Union_assoc. eapply Included_Union_preserv_r.
                  rewrite !image_Union. eapply Union_Included; [| now sets ].
                  eapply image_monotonic.
                  eapply occurs_free_fun_map_get. eassumption. now sets.
               ++ sets.
               ++ sets.
               ++ (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                  intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                  repeat (split; [ now eauto |]). eapply Union_Disjoint_r. now sets.
                  eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Union_Disjoint_r.
                  eapply Disjoint_Included_r; [| eapply Hdis2 ]. normalize_occurs_free.
                  rewrite image_Union. rewrite FromList_apply_list. now sets. now sets. }
             { eapply return_triple. 
               intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
               ++ reflexivity.
               ++ constructor.
               ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                  rewrite FromList_apply_list. sets.
               ++ normalize_bound_var. sets.
               ++ eauto.
               ++ intros. eapply preord_exp_app_compat.
                  now eauto. now eauto.
                  eapply H0. now constructor.
                  eapply Forall2_preord_var_env_map. eassumption.
                  now constructor. }
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
             ++ reflexivity.
             ++ constructor.
             ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ eauto.
             ++ intros. eapply preord_exp_app_compat.
                now eauto. now eauto.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.
        *  eapply return_triple.
           intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
           ++ reflexivity.
           ++ constructor.
           ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
              rewrite FromList_apply_list. sets.
           ++ normalize_bound_var. sets.
           ++ eauto.                              
           ++ intros. eapply preord_exp_app_compat.
              now eauto. now eauto.
              eapply H0. now constructor.
              eapply Forall2_preord_var_env_map. eassumption.
              now constructor.
    - (* Eprim *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_name_fresh. 
      intros x w1. simpl. eapply pre_curry_l. intros HSin. eapply pre_curry_l. intros Hf. 
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        eapply Disjoint_Singleton_r. eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply image_apply_r_set. eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets. now sets.
        rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1' ]. now sets. now sets.
      + eapply Disjoint_Included_r.
        eapply Included_Union_compat. reflexivity.
        eapply image_apply_r_set. 
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' Hsem]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; omega.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union.
          rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity. 
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; omega. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; omega.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_prim_compat.
          now eauto.
          eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.
    - (* Ehalt *)
      eapply return_triple.
      intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + reflexivity.
      + constructor.
      + repeat normalize_occurs_free. rewrite image_Union, image_Singleton. sets.
      + normalize_bound_var. sets.
      + simpl; eauto.
      + intros. eapply preord_exp_halt_compat. now eauto. now eauto.
        eapply H0. now constructor.
    - (* Fcons *)
      simpl. 
      eapply bind_triple. eapply pre_transfer_r. now eapply get_names_lst_fresh. intros xs w. simpl.
      eapply pre_curry_l. intros HSin. eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros Hnd.  eapply pre_curry_l. intros Hlen.
      eapply bind_triple. 
      { do 2 eapply frame_rule. eapply IHe with (S := S \\ FromList xs).
        - eassumption.
        - eapply Union_Disjoint_r. 
          + eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free with (B := (Fcons v t l e f5)).
            now left. constructor; eauto. eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. now sets.
          + eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs (Fcons v t l e f5)). now tci.
            eapply Union_Disjoint_r.
            eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. normalize_bound_var. now sets.
            eapply unique_bindings_fun_in_fundefs. now left. constructor; eauto.
        - repeat normalize_bound_var_in_ctx.
          (* eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets. *)
          eapply Disjoint_Included_r. eapply image_apply_r_set_list. now eauto.
          eapply Union_Disjoint_r.
          eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.
          rewrite FromList_apply_list in Hnames2. rewrite <- Same_set_all_fun_name in Hnames2.
          eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) (name_in_fundefs (Fcons v t l e f5))).
          now tci. eapply Union_Disjoint_r. eapply Disjoint_Included_r. eapply image_Setminus. now tci. rewrite Setminus_Union_distr. 
          eapply Disjoint_Included; [| | eapply Hdis1' ]. rewrite !Setminus_Union_distr. normalize_occurs_free.
          rewrite !Setminus_Union. eapply image_monotonic. eapply Union_Included. simpl. now sets. now sets. now sets. 
          now xsets.
        - eapply Union_Disjoint_r. repeat normalize_bound_var_in_ctx. now xsets.
          eapply Disjoint_Included_r. eapply image_apply_r_set_list. now eauto.
          eapply Union_Disjoint_r. now sets.
          eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) (name_in_fundefs (Fcons v t l e f5))).
          now tci. eapply Union_Disjoint_r. eapply Disjoint_Included_r. eapply image_Setminus. now tci. rewrite Setminus_Union_distr. 
          eapply Disjoint_Included; [| | eapply Hdis2 ]. rewrite !Setminus_Union_distr. normalize_occurs_free.
          rewrite !Setminus_Union. eapply Included_Union_preserv_r. eapply image_monotonic. eapply Union_Included. simpl.
          now sets. now sets. now sets. eapply Disjoint_Included; [| | eapply Hnames2 ]. rewrite FromList_apply_list. rewrite Same_set_all_fun_name.
          reflexivity. now sets.
        - eapply Disjoint_Included_l; [| eassumption ].
          normalize_bound_var. simpl. rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r.
          eapply Included_Union_preserv_l. rewrite !Setminus_Union. rewrite Union_commut.
          rewrite <- Union_assoc. rewrite <- Setminus_Union. eapply Included_Setminus; [| now sets ].
          eapply Union_Disjoint_r; [| eapply Union_Disjoint_r ]; sets.
          + eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
          + eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx. 
          sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply fun_map_vars_set_list. eassumption. }

      intros e' w'. simpl. eapply pre_curry_l. intros Hxs. eapply pre_curry_l; intros Hleq.     
      eapply bind_triple.

      { eapply pre_strenghtening.
        2:{ eapply frame_rule. eapply IHB with (S := S \\ FromList xs (* \\ bound_var e' *)).
            + eassumption.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). now tci.
              rewrite Setminus_Union_distr. eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ].
              simpl. rewrite Setminus_Union. now sets. now sets. now sets. 
            + eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) [set v]). now tci.
              eapply Union_Disjoint_r. eapply Disjoint_Included_r. eapply image_Setminus. now tci. rewrite !Setminus_Union_distr.
              eapply Disjoint_Included; [| | eapply Hdis1' ]. normalize_occurs_free. now sets. normalize_bound_var. now sets.
              eapply Disjoint_Included; [| | eapply Hnames2 ]. rewrite FromList_apply_list, <- Same_set_all_fun_name. simpl. now sets.
              normalize_bound_var. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. 
              eapply Union_Disjoint_r. 
              eapply Disjoint_Included; [| | eapply Hdis2 ]; now sets.
              eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) [set v]). now tci.
              eapply Union_Disjoint_r. 
              eapply Disjoint_Included_r. eapply image_Setminus. now tci.
              eapply Disjoint_Included; [| | eapply Hdis2 ]. eapply Included_Union_preserv_r.
              eapply image_monotonic. rewrite !Setminus_Union_distr. now sets. now sets.
              eapply Disjoint_Included; [| | eapply Hnames2 ]. rewrite FromList_apply_list, <- Same_set_all_fun_name. simpl. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_l; [| eapply Hdis3 ]. simpl. rewrite !Setminus_Union_distr.
              do 3 eapply Included_Union_preserv_r. rewrite !Setminus_Union.
              rewrite (Union_commut (funname_in_exp e)). rewrite <- !Union_assoc. rewrite (Union_commut [set v]). 
              rewrite Union_assoc. rewrite <- Union_assoc. rewrite <- Setminus_Union. rewrite <- Setminus_Union.
              eapply Included_Setminus; [| now sets ]. eapply Union_Disjoint_r.
              * eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
              * sets.
            + sets.
            + eapply fun_map_vars_antimon; eauto. sets.
            + simpl in Hnames1. inv Hnames1. eassumption.
            + eapply Disjoint_Included; [ | | eapply Hnames2 ]; simpl; sets. normalize_sets. sets. normalize_bound_var. now sets. } 

        simpl. intros u w1 [Hyp Hyp']. split. eapply Hyp'. eassumption. }


      intros B' w''. eapply return_triple. intros. destructAll. split; [| split ; [| split; [| split; [| split; [| split ]]]]].
      + eapply fresh_monotonic; [|  eassumption ]. sets.
      + zify; omega.
      + constructor; eauto.
        * intros Hc. eapply Hnames2. constructor. 2:{ left. reflexivity. }
          left. eapply H18 in Hc. unfold Ensembles.In, Range in Hc. eapply HSin. zify; omega.
        * intros Hc. eapply Included_Union_Setminus with (s2 := name_in_fundefs B') in Hc; [| tci ].
          inv Hc. 
          -- eapply Hnames2. constructor. 2:{ left. reflexivity. } left. 
             eapply HSin. eapply H13 in H21. unfold Ensembles.In, Range in H21. zify; omega.
          -- rewrite Same_set_all_fun_name in H21. rewrite H14 in H21. rewrite FromList_apply_list in H21.
             inv Hnames1. eapply H24; eauto. eapply FromList_apply_list. eassumption.
             
        * eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_sym. eapply Disjoint_Range. reflexivity.
        * eapply Disjoint_Included_l. eapply Included_Union_Setminus with (s2 := name_in_fundefs B'); tci. eapply Union_Disjoint_l.
          -- eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_sym. eapply Disjoint_Range. zify. omega.
          -- apply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hnames2 ].
             simpl. normalize_sets. rewrite Same_set_all_fun_name. rewrite H14. now sets.
             eapply Included_trans. eassumption. intros z Hc. left. eapply HSin. unfold Ensembles.In, Range in Hc. zify; omega.
        * eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs B'); tci. eapply Union_Disjoint_r.
          -- eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_Range. zify. omega.
          -- rewrite Same_set_all_fun_name.  rewrite H14. eapply Disjoint_Included; [ | | eapply Hnames2 ].
             simpl. normalize_sets. now sets.
             intros z Hin. eapply H18 in Hin. left. eapply HSin. unfold Ensembles.In, Range in Hin. zify; omega.
        * intros Hc. eapply Hnames2. constructor. 2:{ left. reflexivity. }
          left. eapply HSin. eapply Hxs in Hc. unfold Ensembles.In, Range in Hc. zify; omega.
      + normalize_occurs_free. eapply Included_trans. eapply Included_Union_compat.
        * eapply Included_Setminus_compat. eassumption. reflexivity.
        * eapply Included_Setminus_compat. eassumption. reflexivity.
        * eapply Union_Included.
          -- eapply Included_trans. eapply Included_Setminus_compat. eapply image_apply_r_set_list. now eauto. reflexivity.
             rewrite !Setminus_Union_distr. eapply Union_Included. now sets.
             rewrite Same_set_all_fun_name. rewrite H14. rewrite FromList_apply_list. rewrite <- Same_set_all_fun_name.
             rewrite (Union_commut (FromList xs)). rewrite Union_assoc. rewrite <- Setminus_Union.
             eapply Included_trans. eapply Setminus_Included. eapply Included_trans.
             rewrite <- image_Singleton, <- image_Union. eapply image_Setminus. now tci.
             rewrite !Setminus_Union_distr, !Setminus_Union. normalize_occurs_free.
             rewrite !image_Union. eapply Union_Included; xsets.
          -- rewrite <- image_Singleton. eapply Included_trans. eapply image_Setminus. now tci.
             rewrite Setminus_Union_distr. normalize_occurs_free. sets.             
      + normalize_bound_var. simpl. rewrite Setminus_Union_distr. eapply Union_Included. now sets.
        rewrite !Setminus_Union_distr. eapply Union_Included; [| eapply Union_Included ].
        * eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; omega.
        * eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; omega.
        * rewrite Union_commut. rewrite <- Setminus_Union.
          eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; omega.
      + simpl. rewrite H14. reflexivity.
      + intros. destruct (cps.M.elt_eq f v); subst.
        * inv H21. do 2 eexists. split; [| split; [| split; [| split ]]].
          -- simpl. rewrite peq_true. reflexivity.
          -- now eauto.
          -- eassumption.
          -- intros z HIn. eapply HSin. eapply Hxs in HIn. unfold Ensembles.In, Range in HIn. zify; omega.
          -- intros. eapply H20.
             ++ rewrite apply_r_set_list_f_eq.
                eapply preord_env_P_inj_antimon. eassumption. eapply Included_trans.
                eapply occurs_free_in_fun with (B := (Fcons v ft xs0 e1 f5)). now left.
                sets.
             ++ eapply fun_map_inv_antimon. eassumption.
                eapply Included_trans. eapply occurs_free_in_fun with (B := (Fcons v ft xs0 e1 f5)). now left.
                sets.
        * edestruct H15. eassumption. destructAll.
          do 2 eexists. split; [| split; [| split; [| split ]]].
          -- simpl. rewrite peq_false. eassumption. intros Hc. inv Hnames1. eapply H29. rewrite <- Hc.
             rewrite <- H14. eapply Same_set_all_fun_name. eapply find_def_name_in_fundefs. eassumption.
          -- now eauto.
          -- eassumption.
          -- eapply Included_trans. eassumption. sets.
          -- intros. eapply H26; eauto.
             ++ eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free.
                rewrite <- !Union_assoc.
                rewrite <- Union_Included_Union_Setminus with (s1 := occurs_free_fundefs _) (s3 := [set v]).
                now sets. tci. now sets.
             ++ eapply fun_map_inv_antimon. eassumption. normalize_occurs_free. 
                rewrite <- !Union_assoc.
                rewrite <- Union_Included_Union_Setminus with (s1 := occurs_free_fundefs _) (s3 := [set v]).
                now sets. tci. now sets.
    - (* Fnil *)
      eapply return_triple.
      intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + reflexivity.
      + constructor.
      + intros z Hin; inv Hin.
      + normalize_bound_var. sets.
      + intros. inv H0.
  Qed.

  Lemma apply_r_empty_f_eq : 
    f_eq (apply_r (M.empty var)) id.
  Proof.
    intros x. rewrite apply_r_empty. reflexivity.
  Qed.

  Lemma occurs_free_fun_map_empty :
    occurs_free_fun_map (M.empty _) <--> Empty_set _.
  Proof.
    split; sets.
    intros x Hin. inv Hin. destructAll. rewrite M.gempty in H. inv H.
  Qed.

  Lemma fun_name__fun_map_empty :
    funname_fun_map (M.empty _) <--> Empty_set _.
  Proof.
    split; sets.
    intros x Hin. inv Hin. destructAll. rewrite M.gempty in H. inv H.
  Qed.

  Lemma bound_var_fun_map_empty :
    bound_var_fun_map (M.empty _) <--> Empty_set _.
  Proof.
    split; sets.
    intros x Hin. inv Hin. destructAll. rewrite M.gempty in H. inv H.
  Qed.

  
  Lemma inline_correct_top d (e : exp) (st : St) (c:comp_data) rho1 rho2:
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    (max_var e 1%positive) < (next_var c) ->
    List_util.max_list (map fst (M.elements rho1)) 1%positive < next_var c ->
    exists e' c',
      beta_contract_top St IH e d st c  = (Ret e', c') /\
      unique_bindings e' /\
      occurs_free e' \subset occurs_free e /\
      (forall k,
          preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
          Disjoint _ (bound_var e) (Dom_map rho1) ->
          preord_exp cenv P1 PG k (e, rho1) (e', rho2)).
  Proof.
    intros. edestruct (inline_correct_mut d) as [He _].
    unfold beta_contract_top, triple in *.
    specialize (He e (M.empty _) (M.empty _) st
                   (fun x => Pos.max (max_var e 1%positive) (List_util.max_list (map fst (M.elements rho1)) 1%positive) < x) H H0).

    assert (Hdis1 : Disjoint var (fun x : var => Pos.max (max_var e 1) (List_util.max_list (map fst (M.elements rho1)) 1) < x)
                             (bound_var e :|: image (apply_r (M.empty var))
                                        (occurs_free e :|: occurs_free_fun_map
                                                     (M.empty (fun_tag * list var * exp))))).
    { rewrite apply_r_empty_f_eq. rewrite image_id. rewrite occurs_free_fun_map_empty. normalize_sets. 
      constructor. intros x Hnin. inv Hnin. inv H4. 
      eapply bound_var_leq_max_var with (y := 1%positive) in H5. unfold Ensembles.In in *. zify. omega.
      eapply occurs_free_leq_max_var with (y := 1%positive) in H5. unfold Ensembles.In in *. zify. omega. }
    
    assert (Hdis2 : Disjoint var (bound_var e \\ funname_in_exp e)
                             (Dom_map (M.empty (fun_tag * list var * exp)) :|: funname_fun_map (M.empty (fun_tag * list var * exp)))).
    { rewrite Dom_map_empty, fun_name__fun_map_empty. sets. }

    assert (Hdis3 : Disjoint var (funname_in_exp e) (bound_var_fun_map (M.empty (fun_tag * list var * exp)))).
    { rewrite bound_var_fun_map_empty. sets. }

    assert (Hfinv : fun_map_vars (M.empty (fun_tag * list var * exp))
                                 (fun x : var => Pos.max (max_var e 1) (List_util.max_list (map fst (M.elements rho1)) 1) < x)
                                 (M.empty var)).
    { unfold fun_map_vars. intros. rewrite M.gempty in H3. inv H3. }

    assert (Hf : fresh (fun x : var => Pos.max (max_var e 1) (List_util.max_list (map fst (M.elements rho1)) 1) < x) (next_var (fst (c, tt)))).
    { unfold fresh. intros. unfold Ensembles.In in *. simpl in *. zify; omega. }

    specialize (He Hdis1 Hdis2 Hdis3 Hfinv tt (c, tt) Hf).
    
    unfold runState, run_compM. simpl in *. 
    
    destruct (compM.runState
                (beta_contract St IH d e (cps.M.empty var) (cps.M.empty (fun_tag * list var * exp)) st) tt (c, tt)) eqn:Heq.   
    
    destruct e0. contradiction. destructAll.

    destruct p. do 2 eexists. split; [| split; [| split ]].
    - reflexivity.
    - eassumption.
    - eapply Included_trans. eassumption. rewrite apply_r_empty_f_eq. rewrite image_id, occurs_free_fun_map_empty.
      sets.
    - intros. eapply H9; eauto. rewrite apply_r_empty_f_eq.
      intros x Hin. unfold id. eauto.

      rewrite apply_r_empty_f_eq. rewrite image_id.
      constructor. intros x Hin. inv Hin. unfold Ensembles.In in *. destruct H13.
      eapply cps.M.elements_correct in H13.
      eapply in_map with (f := fst) in H13. eapply List_util.max_list_spec2 with (z := 1%positive) in H13.
      simpl in *.  zify; omega.

      intro; intros. rewrite M.gempty in H13; inv H13.
  Qed. 

End Inline_correct.

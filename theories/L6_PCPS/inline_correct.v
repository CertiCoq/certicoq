Require Import Common.compM Common.Pipeline_utils L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles .
Import ListNotations.
Require Import identifiers.
Require Import L6.state L6.freshen L6.cps_util L6.cps_show L6.ctx L6.hoare L6.inline L6.rename
        L6.Ensembles_util L6.alpha_conv L6.functions L6.logical_relations L6.tactics L6.eval.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Coq.Program.Wf.
Require Import Program.
(* Require Import Template.monad_utils. *)
Require Import Coq.Structures.OrdersEx.
Require Import Common.compM Libraries.CpdtTactics Libraries.maps_util.

Import MonadNotation.
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
      (match (inl, M.get f' fm, d) with
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
      (match (inl, M.get f' fm, d) with
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

  Definition fun_map_inv (fm : fun_map) (rho : env) :=
    forall f ft xs e,
      fm ! f = Some (ft, xs, e) ->
      exists rhoc B g, rho ! f = Some (Vfun rhoc B g) /\
                       find_def g B = Some (ft, xs, e).

  
  Lemma fun_map_inv_set fm rho x v :
    fun_map_inv fm rho ->
    ~ x \in Dom_map fm ->
    fun_map_inv fm (M.set x v rho).           

  Lemma fun_map_inv_set_lists fm rho xs vs :
    fun_map_inv fm rho ->
    Disjoint _ (FromList xs) (Dom_map fm) ->
    set_lists xs vs rho = Some rho' ->
    fun_map_inv fm rho'.

  Lemma fun_map_inv_def_funs fm rho B :
    fun_map_inv fm rho -
    fun_map_inv (add_fundefs B fm) (def_funs B B rho rho).
    
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
             preord_exp cenv P1 PG k (e, rho1) (e', rho2))

    }}.
  Proof.
    revert e sig fm st S. induction d as [d IHd] using lt_wf_rec1.
    induction e using exp_ind'; intros sig fm st S Hun Hdis1 Hdis2; inv Hun; rewrite beta_contract_eq.
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
        * intros r1 r2 k Henv. eapply preord_exp_const_compat.
          admit. admit. admit.
          intros. eapply Hsem. 
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free. sets.
          -- rewrite preord_val_eq. split. reflexivity.
             eapply Forall2_Forall2_asym_included. eassumption. 
          -- intros Hc. eapply Hdis2. constructor. eassumption.
             right. normalize_occurs_free. rewrite image_Union. right. eassumption.
    - 
          pre
          reflexivity. 
        rewrite Union_Setminus with (S1 := occurs_free e) (S2 := [set v]).
        2:{ 

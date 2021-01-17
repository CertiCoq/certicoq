From Coq Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import L4.expression L4.exp_eval.

(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Classes.Morphisms. *)
(* Require Import Coq.Classes.RelationClasses. *)

Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        tactics L4_to_L6 L4_to_L6_util L6.tactics identifiers
        bounds cps_util rename. 

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Bounds.

  Global Instance L4_resource_nat : @L4_resource nat.
  Proof.
    econstructor.
  Defined.   
  
  Global Instance L4_fuel_resource_nat : @L4_fuel_resource nat.
  Proof.
    econstructor; tci.
  Defined.

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.

  
  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.
  
  Global Instance trace_res : @trace_resource unit.
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.
    
  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition cps_bound (f_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.
  
  
  
  Global Instance eq_fuel_compat cenv :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel. 
  Proof.
    unfold eq_fuel. constructor; try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed. 

End Bounds.



Section Correct.

  Context (prim_map : M.t (kername * string (* C definition *) * nat (* arity *))). 
  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)                      
          (cenv : ctor_env).

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  
  Definition cps_cvt_rel := L4_to_L6.cps_cvt_rel func_tag kon_tag default_tag.
  Definition cps_cvt_rel_exps := L4_to_L6.cps_cvt_rel_exps func_tag kon_tag default_tag.
  Definition cps_cvt_rel_efnlst := L4_to_L6.cps_cvt_rel_efnlst func_tag kon_tag default_tag.
  Definition cps_cvt_rel_branches := L4_to_L6.cps_cvt_rel_branches func_tag kon_tag default_tag.
  Definition cps_env_rel := cps_env_rel cnstrs func_tag kon_tag default_tag.
  Definition cps_val_rel := cps_val_rel cnstrs func_tag kon_tag default_tag.
  
  (* Alpha-equiv corollaries *)
  
  Corollary cps_cvt_exp_alpha_equiv k :
    cps_cvt_exp_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_exps_alpha_equiv k :
    cps_cvt_exps_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_efnlst_alpha_equiv k :
    cps_cvt_efnlst_alpha_equiv eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.
  
  Corollary cps_cvt_branches_alpha_equiv k :
    cps_cvt_branches_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.
  
  (** ** Correctness statements *)
  
  Definition cps_cvt_correct_exp :=
    forall e v rho vs vnames k x vk e' v' S S' f i,
      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->

      eval_env_fuel vs e (Val v) f ->

      cps_env_rel vnames vs rho ->           
      cps_cvt_rel S e vnames k cnstrs S' e' ->
      cps_val_rel v v' ->
      
      preord_exp cenv (cps_bound f) eq_fuel i
                 ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                 (e', (M.set k vk rho)).

  
    Definition cps_cvt_correct_exps := forall (es: exps), True. (* FIX placeholder *)
      (* forall es es' vs rho vnames k x vk es'' vs' S S', *)
      (*   Forall2 (fun e v => eval_env vs e v) (exps_to_list es) es' -> *)
      (*   cps_env_rel vnames vs rho -> *)
      (*   Disjoint _ (k |: (FromList vnames)) S -> *)
      (*   Forall2 (fun e e' => cps_cvt_rel S e vnames k cnstrs S' e') *)
      (*           (exps_to_list es) es'' -> *)
      (*   Forall2 cps_val_rel es' vs' -> *)
      (*   Forall2 (fun e' v' => *)
      (*              preord_exp cenv (cps_bound f) eq_fuel  *)
      (*                  ((Eapp k kon_tag (x::nil)), *)
      (*                   (M.set x v' (M.set k vk (M.empty cps.val)))) *)
      (*                  (e', (M.set k vk rho))) *)
      (*           es'' vs'. *)

    Definition cps_cvt_correct_efnlst := forall (e : efnlst), True. (* FIXC placeholder *)
      (* forall efns efns' vs rho vnames k x vk efns'' vs' S S', *)
      (*   Forall2 (fun p v => let (na, e) := p : (name * expression.exp) in *)
      (*                        eval_env vs e v) (efnlst_as_list efns) efns' -> *)
      (*   cps_env_rel vnames vs rho -> *)
      (*   Disjoint _ (k |: (FromList vnames)) S -> *)
      (*   Forall2 (fun p e' => let (na, e) := p : (name * expression.exp) in *)
      (*              cps_cvt_rel S e vnames k cnstrs S' e') *)
      (*           (efnlst_as_list efns) efns'' -> *)
      (*   Forall2 cps_val_rel efns' vs' -> *)
      (*   Forall2 (fun e' v' => *)
      (*              equiv_exp cenv _ _ _ _  P1 PG *)
      (*                        ((Eapp k kon_tag (x::nil)), *)
      (*                         (M.set x v' (M.set k vk (M.empty cps.val)))) *)
      (*                        (e', (M.set k vk rho))) *)
      (*           efns'' vs'. *)

    Definition cps_cvt_correct_branches := forall (bs : branches_e), True.
      (* forall bs bs' vs rho vnames k x vk bs'' vs' S S', *)
      (*   Forall2 (fun p v => let '(dc, (n, l), e) := p in *)
      (*                       eval_env vs e v) (branches_as_list bs) bs' -> *)
      (*   cps_env_rel vnames vs rho -> *)
      (*   Disjoint _ (k |: (FromList vnames)) S -> *)
      (*   Forall2 (fun p e' => let '(dc, (n, l), e) := p in *)
      (*                       cps_cvt_rel S e vnames k cnstrs S' e') *)
      (*           (branches_as_list bs) bs'' -> *)
      (*   Forall2 cps_val_rel bs' vs' -> *)
      (*   Forall2 (fun e' v' => *)
      (*              equiv_exp cenv _ _ _ _  P1 PG *)
      (*                        ((Eapp k kon_tag (x::nil)), *)
      (*                         (M.set x v' (M.set k vk (M.empty cps.val)))) *)
      (*                        (e', (M.set k vk rho))) *)
      (*           bs'' vs'. *)


    Lemma cps_env_rel_nth_error vnames vs rho n y v : 
      cps_env_rel vnames vs rho -> 
      nth_error vnames n = Some y ->
      nth_error vs n = Some v -> 
      exists v', M.get y rho = Some v' /\ cps_val_rel v v'.
    Proof.
      intros Hrel. revert n y v; induction Hrel; intros n z v Hnth1 Hnth2.
      - destruct n; simpl in *; congruence.
      - destruct n; simpl in *.
        + inv Hnth1. inv Hnth2. destructAll. eauto.
        + eauto.
    Qed. 

    Lemma preord_var_env_extend_neq_l PostG (rho1 rho2 : env) (k : nat) (x1 y1 y2 : var)
          (v1 : cps.val) :
        preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
        y1 <> x1 ->
        preord_var_env cenv PostG k (M.set x1 v1 rho1) rho2 y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_extend_neq_r PostG (rho1 rho2 : env) (k : nat) (x1 y1 y2 : var)
          (v1 : cps.val) :
      preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
      y2 <> x1 ->
      preord_var_env cenv PostG k rho1 (M.set x1 v1 rho2) y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_get :
      forall PostG (rho1 rho2 : env) (k : nat) (x1 x2 : var) (v1 v2 : cps.val),
        preord_val cenv PostG k v1 v2 ->
        M.get x1 rho1 = Some v1 ->
        M.get x2 rho2 = Some v2 ->        
        preord_var_env cenv PostG k rho1 rho2 x1 x2.
    Proof.
      intros rho1 rho2 k x1 x2 v1 v2 Hval Hget1 Hget2 x' v' Hget.
      repeat subst_exp. eauto. 
    Qed.


    Definition one_step : @PostT nat unit :=
      fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + 1)%nat = f2.


    Lemma preord_exp_Efun_red k e B rho :          
      preord_exp cenv one_step eq_fuel k (e, def_funs B B rho rho) (Efun B e, rho).
    Proof.
      intros r cin cout Hleq Hbstep.
      do 3 eexists. split. econstructor 2. econstructor. eassumption.
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.

    Lemma preord_exp_Eapp_red k B rho f rho1 g xs ft ys e' vs rho2 :
      M.get f rho = Some (Vfun rho1 B g) ->
      find_def g B = Some (ft, ys, e') ->
      get_list xs rho = Some vs ->
      set_lists ys vs (def_funs B B rho1 rho1) = Some rho2 ->
      preord_exp cenv one_step eq_fuel k (e', rho2) (Eapp f ft xs , rho).
    Proof.
      intros r cin cout Hleq Hbstep Hget Hf Hgetl Hsetl.
      do 3 eexists. split. econstructor 2. econstructor; eauto. 
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.

    Lemma eq_fuel_idemp : 
      inclusion (exp * env * nat * unit) (comp eq_fuel eq_fuel) eq_fuel.
    Proof.
      clear. unfold comp, eq_fuel. intro; intros. 
      destruct x as [[[? ?] ?] ?].
      destruct y as [[[? ?] ?] ?]. destructAll. 
      destruct x as [[[? ?] ?] ?]. congruence.
    Qed.
           
    Opaque preord_exp'.
    
    Lemma cps_cvt_correct:
      cps_cvt_correct_exp /\
      cps_cvt_correct_exps /\
      cps_cvt_correct_efnlst /\
      cps_cvt_correct_branches.
    Proof.
      eapply exp_ind_alt.
      - (* Var_e *)
        intros n y rho vs vnames k x vk e' v' S S' f i Hdis Hnin1 Hnin2 Heval
               Hcenv Hcps Hval.  
        inv Heval. 2:{ inv H. } inv Hcps. 
        
        eapply preord_exp_app_compat.
        
        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.

        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.

        + eapply preord_var_env_extend_neq_l. 
          eapply preord_var_env_extend_eq. eapply preord_val_refl; tci.
          intros Hc; subst; eauto.
          
        + constructor; eauto.
          edestruct cps_env_rel_nth_error; eauto. destructAll.
          eapply preord_var_env_get.
          2:{ rewrite M.gss. reflexivity. }
          2:{ rewrite M.gso. eassumption. intros Hc; subst.
              eapply Hnin2. eapply nth_error_In. eassumption. } 
          eapply cps_cvt_val_alpha_equiv; eauto.
          eapply eq_fuel_compat. eapply eq_fuel_compat.
          clear; now firstorder. (* TODO find inclusion refl *)
        
      - (* Lam_e *)
        intros n e IHe y rho vs vnames k x vk e' v' S S' f i Hdis Hnin1 Hnin2 Heval
               Hcenv Hcps Hval.
        inv Heval. inv Hcps. 2:{ inv H. } (* inv Hval. *)

        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

            2:{ intros m. eapply preord_exp_Efun_red. }

            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat. 
            now eapply eq_fuel_compat. 

            eapply preord_var_env_extend_neq.
            eapply preord_var_env_extend_eq.
            eapply preord_val_refl. now tci. 

            - intros Hc; subst; eauto. 
            - intros Hc; subst. inv H2. eapply Hdis; eauto.
            - constructor; eauto. 
              eapply preord_var_env_extend_eq. inv Hval.
              (* Seems similar to other cases in alpha equiv, maybe lemma? *)
              eapply preord_val_fun.
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + intros rho1' j vs1 vs2 Heq Hset.
                destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
                destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
                eexists. split. reflexivity. intros. 
                eapply cps_cvt_exp_alpha_equiv; try eassumption.
                * reflexivity.
                * constructor; eauto.
                * normalize_sets. intros Hc. inv Hc. inv H3; eauto. eapply H9; eauto.
                * simpl. admit. (* easy len *)
                * normalize_sets. sets.
                * normalize_sets.
                  eapply Union_Disjoint_l. sets.
                  eapply Union_Disjoint_l; sets.
                * inv H0. inv H17. clear H18. normalize_sets. simpl.
                  rewrite extend_extend_lst_commut. rewrite extend_commut.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_not_In_P_l; eauto.
                  eapply preord_env_P_inj_set_not_In_P_r; eauto.
                  eapply preord_env_P_inj_set_not_In_P_r; eauto.
                  eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                  now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                  now xsets.
                  -- admit. (* easy disjointedness *)
                  -- admit.
                  -- admit.
                  -- admit.
                  -- admit.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; subst; eauto. inv H4; eauto.
                  -- intros Hc; eauto.
                  -- intros Hc; eauto. inv H4. eapply Hdis; eauto.
                  -- admit. (* easy len *) } 

        (* Post composition *) 
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct x0 as [[[? ?] ?] ?]. subst. simpl. lia. } 
      - (* App_e *) 
        intros e1 IHe1 e2 IHe2 v rho vs vnames k x vk e' v' S S' f i
               Hdis Hnin1 Hnin2 Heval Hcenv Hcps Hval.
        inv Hcps. inv Heval. inv H.
        
        (* App Lam  *) 
        + eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. } 

              assert (Hex : exists v', cps_val_rel (Clos_v rho' na e1'0) v') by admit. 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z) by admit. destructAll.
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IHe1; [ | | | eassumption | | eassumption | ].
                  - now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - (* weaken *) admit.
                  -  eassumption. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } simpl.
              
              assert (Hex : exists v', cps_val_rel v2 v') by admit. 
              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z) by admit. destructAll.
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IHe2; [ | | | eassumption | | eassumption | ].
                  - eapply Union_Disjoint_l; sets. admit. (* easy sets. *)
                  - eassumption.
                  - admit. (* easy sets. *)
                  - admit. (* weaken *)
                  - eassumption. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 


              
              (* weaken *) admit.
                  -  eassumption. }

              } 

              preord_exp_Eapp_red
                    econstructor.  
                  .  try eassumption. y. 4:{ eassumption . ; [ | | | eassumption | | | ]. ; try eassumption. 
                  
-- 
                  -- eappl y 
                     a
                  eassumption. 
                 
                  var_env_extend_eq. 
                  
                * 
                eassumption. eassumption. 
                ,.   with (k := j). eq_fuel eq_fuel cnstrs cenv ltac:(tci) ltac:(tci) j) as (Hexp & _). 
                inv Hset.
            tci.
            now  eapply 

        admit.

      - (* App_e *)
        
        intros e1 IHe1 e2 IHe2 v rho vs vnames k x vk e' v' S S' Heval Hcenv Hdis Hcps Hval.
        inv Heval.

        + (* Lam *)
          inv Hcps. inv Hval.
    Abort. 
(*

  equiv_exp cenv fuel Hfuel trace Htrace P1 PG
    (Eapp k kon_tag [x],
    M.set x (Vfun rho_m (Fcons f0 func_tag [x0; k0] e' Fnil) f0)
      (M.set k vk (M.empty val)))
    (Efun (Fcons f func_tag [k1; x1] e1' Fnil) (Eapp k kon_tag [f]), M.set k vk rho)


  equiv_exp cenv fuel Hfuel trace Htrace P1 PG
  (Eapp k kon_tag [x], M.set x (Vfun rho_m (Fcons f0 func_tag [x0; k0] e' Fnil) f0) (M.set k vk (M.empty val)))
  (Eapp k kon_tag [f]), M.set f (Vfun (M.set k vk rho) (Fcons f func_tag [k1; x1] e1' Fnil) f) (M.set k vk rho))



Efun (Fcons f func_tag [k1; x1] e1' Fnil) (

*) 

          
    (*            next1 next2 next3 H H0 H1 H2 H3 H4 H5 H6. *)
    (*     inv H. simpl in H5. *)
    (*     destruct (nth_error vars (N.to_nat n)) eqn:Heqn. 2:{ congruence. } *)
    (*     inv H5. *)
    (*     eapply preord_exp_app_compat. *)
    (*     + eapply HPost_app. eapply Hprops.  *)
    (*     + eapply HPost_OOT. eapply Hprops.  *)
    (*     + unfold preord_var_env. *)
    (*       intros v1 Hgetv1. rewrite M.gso in Hgetv1. *)
    (*       -- rewrite M.gss in Hgetv1. inv Hgetv1. *)
    (*          eexists. rewrite M.gss. split. *)
    (*          reflexivity. *)
    (*          eapply preord_val_refl. eapply HpropsG.  *)
    (*       -- unfold not in *. *)
    (*          intros Hfalse. symmetry in Hfalse. *)
    (*          apply H0 in Hfalse. destruct Hfalse.  *)
    (*     + econstructor. *)
    (*       -- unfold preord_var_env. *)
    (*          intros v1 Hgetv1. rewrite M.gss in Hgetv1. *)
    (*          inv Hgetv1. eexists. admit. *)
    (*       -- econstructor. *)


    (* Definition cps_cvt_correct_e c := *)
    (*   forall e e' rho rho' rho_m v v' x k vk vars *)
    (*          next1 next2 next3, *)
    (*     eval_env rho e v -> *)
    (*     ~(x = k) -> *)
    (*     (lt_symgen k next1) /\ (lt_symgen x next1) -> *)
    (*     (* (lt_symgen x next4) /\ (lt_symgen k next4) -> *) *)
    (*     cps_env_rel rho rho' ->  *)
    (*     gensym_n_nAnon next1 (List.length rho') = (vars, next2) -> *)
    (*     set_lists vars rho' (M.empty cps.val) = Some rho_m -> *)
    (*     cps_cvt e vars k next2 cnstrs = Some (e', next3) -> *)
    (*     (* cps_cvt_val v next4 cnstrs = Some (v', next5) -> *) *)
    (*     obs_rel' v v' -> *)
    (*     preord_exp cenv P1 PG c *)
    (*                ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val)))) *)
    (*                (e', (M.set k vk rho_m)). *)

    (* Definition cps_cvt_correct_es c := *)
    (*   forall es es' rho rho' rho_m vs vs' x k vk vars  *)
    (*          next1 next2 next3 next4 next5, *)
    (*     Forall2 (fun e v => eval_env rho e v) (exps_to_list es) vs -> *)
    (*     ~(x = k) -> *)
    (*     (lt_symgen x next1) /\ (lt_symgen x next1) /\ *)
    (*     (lt_symgen x next4) /\ (lt_symgen k next4) -> *)
    (*     cps_env_rel rho rho' -> *)
    (*     gensym_n_nAnon next1 (List.length rho') = (vars, next2) -> *)
    (*     set_lists vars rho' (M.empty cps.val) = Some rho_m -> *)
    (*     cps_cvt_exps' es vars k next2 cnstrs = Some (es', next3) -> *)
    (*     Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vs vs' -> *)
    (*     Forall2 *)
    (*       (fun e' v' => *)
    (*          preord_exp cenv P1 PG c *)
    (*                     ((Eapp k kon_tag (x::nil)), *)
    (*                      (M.set x v' (M.set k vk (M.empty cps.val)))) *)
    (*                     (e', (M.set k vk rho_m))) *)
    (*       es' vs'. *)

    (* Definition cps_cvt_correct_efnlst c := *)
    (*   forall efns efns' rho rho' rho_m vfns vfns' x k vk vars  *)
    (*          next1 next2 next3 next4 next5, *)
    (*     Forall2 (fun p v => let (na, e) := p : (name * expression.exp) in *)
    (*                         eval_env rho e v) (efnlst_as_list efns) vfns -> *)
    (*     ~(x = k) -> *)
    (*     (lt_symgen x next1) /\ (lt_symgen x next1) /\ *)
    (*     (lt_symgen x next4) /\ (lt_symgen k next4) -> *)
    (*     cps_env_rel rho rho' -> *)
    (*     gensym_n_nAnon next1 (List.length rho') = (vars, next2) -> *)
    (*     set_lists vars rho' (M.empty cps.val) = Some rho_m -> *)
    (*     cps_cvt_efnlst' efns vars k next2 cnstrs = Some (efns', next3) -> *)
    (*     Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vfns vfns' -> *)
    (*     Forall2 *)
    (*       (fun e' v' => *)
    (*          preord_exp cenv P1 PG c *)
    (*                     (e', (M.set k vk rho_m)) *)
    (*                     ((Eapp k kon_tag (x::nil)), *)
    (*                      (M.set x v' (M.set k vk (M.empty cps.val))))) *)
    (*       efns' vfns'. *)


    (* Definition cps_cvt_correct_branches c := *)
    (*   forall bs bs' rho rho' rho_m vs vs' x k vk vars  *)
    (*          next1 next2 next3 next4 next5, *)
    (*     Forall2 (fun p v => let '(dc, (n, l), e) := p in *)
    (*                         eval_env rho e v) (branches_as_list bs) vs -> *)
    (*     ~(x = k) -> *)
    (*     (lt_symgen x next1) /\ (lt_symgen x next1) /\ *)
    (*     (lt_symgen x next4) /\ (lt_symgen k next4) -> *)
    (*     cps_env_rel rho rho' -> *)
    (*     gensym_n_nAnon next1 (List.length rho') = (vars, next2) -> *)
    (*     set_lists vars rho' (M.empty cps.val) = Some rho_m -> *)
    (*     cps_cvt_branches' bs vars k next2 cnstrs = Some (bs', next3) -> *)
    (*     Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vs vs' -> *)
    (*     Forall2 *)
    (*       (fun e' v' => *)
    (*          preord_exp cenv P1 PG c *)
    (*                     (e', (M.set k vk rho_m)) *)
    (*                     ((Eapp k kon_tag (x::nil)), *)
    (*                      (M.set x v' (M.set k vk (M.empty cps.val))))) *)
    (*       bs' vs'. *)

    
    (* Lemma cps_cvt_correct: *)
    (*   forall k, *)
    (*     (cps_cvt_correct_e k) /\ *)
    (*     (cps_cvt_correct_es k) /\ *)
    (*     (cps_cvt_correct_efnlst k) /\ *)
    (*     (cps_cvt_correct_branches k). *)
    (* Proof. *)
    (*   intros k. induction k as [k IHk] using lt_wf_rec1. eapply my_exp_ind. *)
    (*   - intros n e' rho rho' rho_m v v' x k0 vk vars  *)
    (*            next1 next2 next3 H H0 H1 H2 H3 H4 H5 H6. *)
    (*     inv H. simpl in H5. *)
    (*     destruct (nth_error vars (N.to_nat n)) eqn:Heqn. 2:{ congruence. } *)
    (*     inv H5. *)
    (*     eapply preord_exp_app_compat. *)
    (*     + eapply HPost_app. eapply Hprops.  *)
    (*     + eapply HPost_OOT. eapply Hprops.  *)
    (*     + unfold preord_var_env. *)
    (*       intros v1 Hgetv1. rewrite M.gso in Hgetv1. *)
    (*       -- rewrite M.gss in Hgetv1. inv Hgetv1. *)
    (*          eexists. rewrite M.gss. split. *)
    (*          reflexivity. *)
    (*          eapply preord_val_refl. eapply HpropsG.  *)
    (*       -- unfold not in *. *)
    (*          intros Hfalse. symmetry in Hfalse. *)
    (*          apply H0 in Hfalse. destruct Hfalse.  *)
    (*     + econstructor. *)
    (*       -- unfold preord_var_env. *)
    (*          intros v1 Hgetv1. rewrite M.gss in Hgetv1. *)
    (*          inv Hgetv1. eexists. admit. *)
    (*       -- econstructor. *)
    (*   - intros na e IH e' rho rho' rho_m v v' x k0 vk vars *)
    (*            next1 next2 next3 Heval Hneq Hlt Hrel Hgen Hset Hcvt Hcvt_val. *)
    (*     inv Heval. simpl in Hcvt.  *)
    (*     destruct (gensym next2 (nNamed "k_lam")) eqn: Hgen_k. *)
    (*     destruct (gensym s (nNamed "x_lam")) eqn: Hgen_x. *)
    (*     destruct (gensym s0 na) eqn:Hgen_f. *)
    (*     destruct (cps_cvt e (v0 :: vars) v s1 cnstrs) eqn:Hcvt_e. *)
    (*     destruct p eqn:Hp. inv Hcvt. *)
    (*     2 : { inv Hcvt. } *)
        (* Zoe: commneting out because some stuff have changed *) 
        (* 
    rewrite cps_cvt_val_eq in Hcvt_val. simpl in Hcvt_val.
    destruct (cps_cvt_env rho next4 cnstrs) eqn:Hcps_env.
    2: { inv Hcvt_val. } 
    destruct p eqn:Hp.
    destruct (gensym_n s2 (rho_names rho)) eqn:Hgen_vars.
    destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset2.
    2: { inv Hcvt_val. }
    destruct (gensym s3 (nNamed "k_lam")) eqn:Hgen_k2.
    destruct (gensym s4 (nNamed "x_lam")) eqn:Hgen_x2.
    destruct (gensym s5 na) eqn:Hgen_f2.
    destruct (cps_cvt e (v3 :: l0) v2 s6 cnstrs) eqn:Hcvt_e_2.
    destruct p0 eqn:Hp0. inv Hcvt_val.
    2: { inv Hcvt_val. } *)
        (* 
       RHS:
       (Efun v1 [v0; v] e0 (Eapp k0 [v1]), [k0 -> vk]rho_m) ==>
       
       (Eapp k0 [v1], [v1 -> Vfun rho_m (Fun v1 [v0; v] e0) v1, k0 -> vk]rho_m

       Then apply preord_exp_app_compat

       Okay to use v1 in (Eapp k0 [v1], or should we use a different variable?

         *)
        
      (*   admit. *)
      (* - admit. *)
      (* - admit. *)
      (* - admit. *)
      (* - intros na e IH1 e0 IH2 e' rho rho' rho_m v v' x k0 vk vars *)
      (*          next1 next2 next3 Heval Hneq Hlt Hrel Hgen Hset Hcvt Hcvt_val. *)
      (*   simpl in Hcvt. *)
      (*   destruct (gensym next2 na) eqn: Hgen_x. *)
      (*   destruct (gensym s (nNamed "k")) eqn: Hgen_k. *)
      (*   destruct (cps_cvt e0 (v0 :: vars) k0 s0 cnstrs) eqn: Hcvt_e0. *)
      (*   2 : { congruence. }  *)
      (*   destruct p eqn: Hp. *)
      (*   destruct (cps_cvt e vars v1 s1 cnstrs) eqn: Hcvt_e. *)
      (*   2 : { congruence. }  *)
      (*   destruct p0 eqn: Hp0. *)
      (*   inv Hcvt. *)
      (*   inv Heval. *)
        (* Zoe: commneting out because some stuff have changed *) 
    (* 

    assert (Hex: exists v2' next6,
                 cps_cvt_val v2 next5 cnstrs = Some (v2', next6)) by admit.
    destruct Hex as (v2' & next6 & Hval). 
    eapply preord_exp_post_monotonic. eapply Hincl.
    eapply preord_exp_trans.
    eapply HpropsG.
    admit. admit. admit.
    { eapply IH2 with (rho' := (v2' :: rho')) (rho_m := map_util.M.set v0 v2' rho_m).
      7 : { eassumption. } 
      - eassumption.
      - eassumption.
      - eassumption.
      - admit.
      - admit. 
      - simpl. rewrite Hset. reflexivity. 
      - eassumption. }
    { intros m. clear IH2.
      
      assert (Hpre :
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (e2, (M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m))) ->
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (Efun (Fcons v1 kon_tag [v0] e1 Fnil) e2,
                             M.set k0 vk rho_m)) by admit. 
      eapply Hpre. clear Hpre. 

      specialize IH1 with (k0 := v1) (vk := (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1))
                        (v' := v2') (e' := e2).

      (* Adding mapping for v1 in the environment *)
      assert (Hpre:
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk (map_util.M.set v0 v2' rho_m)))
                            (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk rho_m)) ->
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk rho_m))) by admit.
      eapply Hpre. clear Hpre.

      (* Reduction required to apply IH1, x mapped to v2' in environment *)
      assert (Hpre:
                 preord_exp' cenv (preord_val cenv) P1 PG m
                             (Eapp v1 kon_tag [x],
                              M.set x v2'
                                    (M.set v1
                                           (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                           (M.empty cps.val)))
                             (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m)) ->
                 preord_exp' cenv (preord_val cenv) P1 PG m
                             (e1, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk (map_util.M.set v0 v2' rho_m)))
                             (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m))) by admit.
      eapply Hpre. clear Hpre. 
      eapply preord_exp_monotonic.
      eapply IH1.
      - eassumption.
      - (* x < next1 < next2 < s < v1 *) admit.
      - admit.
      - eassumption.
      - eassumption.
      - (* use some other rho? *) admit.
      - admit.
      - eassumption.
      - (* ? *) *)
    (* Abort.  *)

    
    (* Inductive bigStepResult {Term Value : Type} : Type := *)
    (*   Result : Value -> bigStepResult  *)
    (* | OutOfTime : Term -> bigStepResult  *)
    (* | Error : string -> option Term -> bigStepResult. *)

    (* Definition L6_evaln_fun n p : @bigStepResult (env * exp) cps.val := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, e)) := p *)
    (*   : ((prims * ctor_env * name_env * fun_env) * (env * cps.exp)) in *)
    (*   match bstep_f penv cenv rho e n with *)
    (*   | exceptionMonad.Exc s => Error s None *)
    (*   | Ret (inl t) => OutOfTime t *)
    (*   | Ret (inr v) => Result v *)
    (*   end. *)

    (* Definition print_BigStepResult_L6 p n := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, e)) := *)
    (*       p : ((M.t (list cps.val -> option cps.val) * ctor_env * name_env * fun_env) * *)
    (*            (M.t cps.val * cps.exp)) in *)
    (*   L7.L6_to_Clight.print ( *)
    (*       match (bstep_f penv cenv rho e n) with *)
    (*       | exceptionMonad.Exc s => s *)
    (*       | Ret (inl t) => *)
    (*         let (rho', e') := t : (env * cps.exp) in *)
    (*         "Out of time:" ++ (show_cenv cenv) ++ (show_env nenv cenv false rho') ++ *)
    (*                        (show_exp nenv cenv false e') *)
    (*       | Ret (inr v) => show_val nenv cenv false v *)
    (*       end). *)

    (* Definition print_BigStepResult_L6Val p := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, v)) := *)
    (*       p : ((M.t (list cps.val -> option cps.val) * ctor_env * name_env * fun_env) * *)
    (*            (M.t cps.val * cps.val)) in *)
    (*   L7.L6_to_Clight.print ((show_cenv cenv) ++ (show_env nenv cenv false rho) ++ *)
    (*                                           (show_val nenv cenv false v)). *)

    Abort.
    
End Post.
(*
Quote Recursively Definition test1_program :=
  ((fun x =>
      match x with
      | nil => 3%nat
      | cons h x' => h
      end) ((1%nat)::nil)).

Definition id_f (x : nat) := x.

Definition match_test (l : list nat) :=
  match l with
  | nil => false
  | cons el l' => true
  end.

Quote Recursively Definition test2_program := (match_test (1%nat::nil)).

Definition add_test := Nat.add 1%nat 0%nat.

Fixpoint id_nat (n : nat) :=
  match n with
  | O => O
  | S n' => S (id_nat n')
  end.

Definition plus_1 (l : list nat) :=
  let fix plus_1_aux l k :=
    match l with
    | nil => k nil
    | cons n l' => plus_1_aux l' (fun s => k ((Nat.add n 1%nat)::s))
    end
  in
  plus_1_aux l (fun s => s).

Definition hd_test := (@List.hd nat 0%nat (1%nat::nil)).

Definition let_simple :=
  let x := 3%nat in Nat.add x 0%nat.

Quote Recursively Definition test3_program := hd_test.

Quote Recursively Definition test4_program :=
  (List.hd 0%nat (plus_1 (0%nat::1%nat::nil))).

Quote Recursively Definition test5_program := (List.hd_error (false::nil)).


(* Quote Recursively Definition test3_program := *)


Definition test_eval :=
  Eval native_compute in (translateTo (cTerm certiL4) test5_program).

Print test_eval.

Definition test :=
  match test_eval with
  | exceptionMonad.Ret p => p
  | exceptionMonad.Exc s => (nil, expression.Prf_e)
  end.

Definition test_result :=
  match (convert_top test) with
  | Some (cenv, nenv, _, ctg, itg, e) =>
    let pr := cps.M.empty (list val -> option val) in
    let fenv := cps.M.empty fTyInfo in
    let env := cps.M.empty val in
    print_BigStepResult_L6 ((pr, cenv, nenv, fenv), (env, e)) 250%nat
  | None =>
    L7.L6_to_Clight.print ("Failed during comp_L6")
  end.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.

Extract Inductive Decimal.int =>
unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant L6_to_Clight.print =>
"(fun s-> print_string (String.concat """" (List.map (String.make 1) s)))".


Extract Constant   varImplDummyPair.varClassNVar =>
" (fun f (p:int*bool) -> varClass0 (f (fst p)))".

Extraction "test1.ml" test_result.
*)

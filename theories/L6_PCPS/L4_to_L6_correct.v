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
  
  Definition cps_cvt_correct_exp (vs : exp_eval.env) (e : expression.exp) (r : exp_eval.result) (f : nat) :=
    forall rho vnames k x vk e' S S' i,
      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->

      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->
      
      cps_cvt_rel S e vnames k cnstrs S' e' ->     

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
       preord_exp cenv (cps_bound f) eq_fuel i
                  ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                  (e', rho)) /\
      (* SOurce diverges *)
      (r = exp_eval.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel cenv rho e' c OOT tt).

  Definition cps_cvt_correct_exp_step (vs : exp_eval.env) (e : expression.exp) (r : exp_eval.result) (f : nat)  :=
    forall rho vnames k x vk e' S S' i,
      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->
                      
      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->

      cps_cvt_rel S e vnames k cnstrs S' e' ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
                    preord_exp cenv (cps_bound (f <+> exp_eval.one e)) eq_fuel i
                               ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                               (e', rho)) /\
      (* Source diverges *)
      (r = exp_eval.OOT ->
       exists c, ((f <+> exp_eval.one e) <= c)%nat /\ bstep_fuel cenv rho e' c OOT tt).

  
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

    (* TODO move *) 
    Ltac destruct_tuples :=
      try match goal with
          | [ X : ?A * ?B |- _ ] => destruct X; destruct_tuples
          end.


    (* Needs : well_formed exp (well-scoped, fix's are lambdas and index correct)
       + well_formed preserved by semantics

       ==>
       + Program terminates + is in the relation  
       + forall e, exists e', cps_cvt e e'    
     *) 

    Require Import set_util.


    Lemma MSet_non_member (s : PS.t) :
      exists x, ~ PS.In x s.
    Proof.
      destruct (PS.max_elt s) as [m | ] eqn:Hmax.
      - eexists (m + 1)%positive. 
        destruct (PS.mem (m + 1)%positive s) eqn:Hmem.
        + eapply PS.mem_spec in Hmem. eapply PS.max_elt_spec2 in Hmax; [ | eassumption ].
          exfalso. eapply Hmax. eapply Pos.compare_lt_iff. zify. lia.
        + intros Hc. eapply PS.mem_spec in Hc. congruence.
      - eapply PS.max_elt_spec3 in Hmax. eexists 1%positive.
        intros Hc. eapply Hmax. eassumption.
    Qed.

    Lemma ToMSet_non_member (S : Ensemble positive) {Hm: ToMSet S} :
      exists x, ~ x \in S.
    Proof.
      edestruct MSet_non_member. exists x. intros Hc.
      eapply H. eapply FromSet_sound. eapply Hm. eassumption.
    Qed.

    Lemma cps_env_rel_weaken vnames vs x v rho :
      cps_env_rel vnames vs rho ->
      ~ x \in FromList vnames ->
      cps_env_rel vnames vs (M.set x v rho).
    Proof.
      intros Henv Hnin. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      eapply Forall2_monotonic_strong; [ | eassumption ].
      simpl. intros x1 x2 Hin1 Hin2 Hr. rewrite M.gso; eauto.
      intros Hc; subst; auto.
    Qed.
    

    Lemma cps_env_rel_extend vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      M.get x rho = Some v' ->
      cps_val_rel v v' ->
      cps_env_rel (x :: vnames) (v :: vs) rho.
    Proof.
      intros Henv Hget Hval. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
    Qed.


    Lemma cps_env_rel_extend_weaken vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      cps_val_rel v v' ->
      ~ x \in FromList vnames ->
      cps_env_rel (x :: vnames) (v :: vs) (M.set x v' rho).
    Proof.
      intros Henv Hval Hnin. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
      - rewrite M.gss. eexists. split; eauto.
      - eapply cps_env_rel_weaken; eauto.
    Qed.

    Lemma nth_error_Forall2 (A B : Type) (P : A -> B -> Prop) (l : list A) (l' : list B) :
      (forall n t,
          nth_error l n = Some t ->
          exists t', nth_error l' n = Some t' /\ P t t') ->
      List.length l = List.length l' ->
      Forall2 P l l'.
    Proof.
      revert l'; induction l; intros l' Hyp Hlen.
      - destruct l'; simpl in *; try congruence. constructor.
      - destruct l'; simpl in *; try congruence. constructor.
        destruct (Hyp 0%nat a). reflexivity. destructAll. inv H. eassumption.

        eapply IHl; [ | congruence ].
        intros.
        
        destruct (Hyp (S n) t). eassumption. destructAll.
        eauto. 
    Qed.

    Lemma make_rec_env_rev_order_app fns vs :
      exists vs', make_rec_env_rev_order fns vs = vs' ++ vs /\
                  List.length vs' = efnlength fns /\
                  forall n, (n < efnlength fns)%nat ->
                            nth_error vs' n = Some (ClosFix_v vs fns (N.of_nat (efnlength fns - n - 1))).
    Proof.
      unfold make_rec_env_rev_order. generalize (efnlength fns) as m. 
      induction m.
      - simpl. eexists []. split. reflexivity. split.
        compute. reflexivity.
        intros. lia.
      - destructAll.
        eexists (ClosFix_v vs fns (N.of_nat (Datatypes.length x)) :: x). simpl.
        split; [ | split ].
        + rewrite H. reflexivity.
        + reflexivity.
        + intros. destruct n.
          * simpl. rewrite Nat.sub_0_r. reflexivity.
          * simpl. eapply H1. lia.
    Qed.

    Lemma cps_cvt_rel_efnlst_all_fun_name S efns vs fnames S' fdefs :
      cps_cvt_rel_efnlst S efns vs fnames cnstrs S' fdefs ->
      all_fun_name fdefs = fnames. 
    Proof.
      intros Hefn. induction Hefn.
      - reflexivity.
      - simpl. congruence.
    Qed.
      
    Lemma cps_env_rel_extend_fundefs fnames names S1 fns Bs S2 rho vs :
      cps_env_rel names vs rho ->
      cps_fix_rel cnstrs func_tag kon_tag default_tag fnames names S1 fnames fns Bs S2 ->
      NoDup fnames ->
      NoDup names ->
      Disjoint var (FromList names :|: FromList fnames) S1 ->
      Disjoint var (FromList names) (FromList fnames) ->
      cps_env_rel (rev (all_fun_name Bs) ++ names) (make_rec_env_rev_order fns vs) (def_funs Bs Bs rho rho).
    Proof.
      intros Hrel Hfix Hnd1 Hnd2 Hdis1 Hdis2.
      unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel'.
      destruct (make_rec_env_rev_order_app fns vs). destructAll. rewrite H.
      eapply Forall2_app.

      assert (Hlen : Datatypes.length x = Datatypes.length (all_fun_name Bs)).
      { erewrite cps_fix_rel_names; [ | eassumption ].
        rewrite H0. erewrite <- cps_fix_rel_length. reflexivity. eassumption. }

      - eapply nth_error_Forall2; [ | rewrite rev_length; eassumption ].
        intros.
        assert (exists f, nth_error (rev (all_fun_name Bs)) n = Some f).
        { eapply MCList.nth_error_Some_length in H2.
          rewrite Hlen, <- rev_length in H2. eapply nth_error_Some in H2.
          destruct (nth_error (rev (all_fun_name Bs)) n); eauto. congruence. }
        destructAll.
        eexists. split. eauto.
        eexists. split. rewrite def_funs_eq. reflexivity.
        eapply Same_set_all_fun_name. rewrite <- FromList_rev. eapply nth_error_In. eassumption.
        assert (Heq := H2). 
        rewrite H1 in Heq. 2:{ rewrite <- H0. eapply MCList.nth_error_Some_length. eassumption. }        
        inv Heq. econstructor; last eassumption; try eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        rewrite MCList.nth_error_rev.

        rewrite Nnat.Nat2N.id.
        replace (Datatypes.length (all_fun_name Bs) - S (efnlength fns - n - 1))%nat with n.
        2:{ rewrite <- H0, <- Hlen. eapply MCList.nth_error_Some_length in H2. lia. }
        eassumption.

        rewrite Nnat.Nat2N.id. rewrite <- H0, Hlen.
        destruct (all_fun_name Bs). now destruct n; inv H3.
        simpl. destruct n; lia.

      - eapply Forall2_monotonic_strong; [ | eassumption ].
        intros. rewrite def_funs_neq. eassumption.
        intros Hc. eapply Hdis2. constructor. eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        eapply Same_set_all_fun_name. eassumption.
    Qed.
    

    Ltac inv_setminus :=
      match goal with
      | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
      end.
    
    Lemma cps_cvt_correct : forall vs e r f, eval_env_fuel vs e r f -> cps_cvt_correct_exp vs e r f.
    Proof.
      eapply eval_env_fuel_ind' with (P0 := cps_cvt_correct_exp) (P := cps_cvt_correct_exp_step).

      - (* Con_e terminates *) 
        admit. (* TODO better induction principle *)

      - (* Con_e OOT *)
        admit.

      - (* App_e Clos_v *) 
        intros e1 e2 e1' v2 r' na vs vs' f1 f2 f3  Heval1 IH1 Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hcps.
        
        assert (Hex : exists v', cps_val_rel (Clos_v vs' na e1') v') by admit.
        assert (Hex' : exists v', cps_val_rel v2 v') by admit.  
        (* TODO needs correspondence proof *) destructAll. inv H0.
        
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> f2 <+> exp_eval.one (e1 $ e2))) eq_fuel m
                                            (e', M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1'0, rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | eassumption | reflexivity | ].
                  - now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - econstructor; eauto. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } simpl.
              
              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2.              
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IH2 ; [ | | | | | eassumption | reflexivity | eassumption ].                  
                  - eapply Union_Disjoint_l; sets.                   
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included_r. eassumption. sets. 
                  - eassumption.
                  - inv H4. eapply HS2 in H7. inv H7. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv H4. eapply HS2 in H7. inv H7. intros Hin. eapply Hdis. eauto.                    
                  - rewrite M.gss. reflexivity. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              (* inv H0. simpl. *)
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                intros Hc; subst. inv H4. eapply HS2 in H7. now inv H7.
                intros Hc; subst. eapply HS2 in H3. now inv H3.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.                    
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv H2. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv H4. eapply HS2 in H7. inv H7. now eapply Hdis; eauto.
                intros Hc; subst. eapply HS2 in H3. inv H3. now eapply Hdis; eauto.
              - simpl. reflexivity. } 

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        split.

        (* Termination *) 
        { intros v v' Heq1 Hvrel. subst. 

          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH3 with (x := x3); [ | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - repeat normalize_sets. sets.
                  - eassumption.
                  - repeat normalize_sets. intros Hc; inv Hc; eauto. inv H5; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    repeat normalize_sets. intros Hc. inv Hc; eauto. inv H5; eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
          
        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 

          edestruct IH3 with (x := x3) (rho :=  M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)));
            [ | | | | | eassumption | ].
          - repeat normalize_sets. sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H5; eauto. 
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            repeat normalize_sets. intros Hc; inv Hc. inv H5; eauto. eapply H14; eauto. 
          - rewrite M.gss. reflexivity.
          - destruct (H7 ltac:(reflexivity)). destructAll. eapply Heq in H15; [ | reflexivity ]. destructAll.
            destruct x6; try contradiction. destruct x8. eexists. split; [ | eassumption ].
            
            unfold exp_eval.one in *. simpl in *. lia. } 

      - (* App_e Clos_v, OOT 1 *)
        intros e1 e2 vs f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps.
        set (rho' := M.set k1 (Vfun rho
                                    (Fcons k1 kon_tag [x1]
                                           (Efun
                                              (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil)
                                              e2') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | eassumption | ].
        + sets.
        + eassumption.
        + intros Hc; inv H2; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H2. eapply Hdis; eauto. 
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H5. reflexivity. destructAll. eexists (x3 + 1)%nat. split.
          unfold exp_eval.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.
          
      - (* App_e Clos_v, OOT 2 *)
        intros e1 e2 v1 vs2 f1 f2 He1 IH1 Hoot IH2.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps.
        
        assert (Hex' : exists v', cps_val_rel v1 v') by admit. destructAll. 
        (* TODO needs correspondence proof *)

        set (rho' := M.set k2 (Vfun (M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) k1) rho)) (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) k2)
                           (M.set x1 x0
                                  (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1]
                                                             (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2])
                                                                          Fnil) e2') Fnil) k1) rho))).
        
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+>exp_eval.one (e1 $ e2))) eq_fuel m
                                            (e2', rho')
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | eassumption | reflexivity | ].
                  - now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }
          
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }  
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
               
              2:{ intros m. eapply preord_exp_Efun_red. } simpl. 

              eapply preord_exp_refl. tci.
              eapply preord_env_P_refl. tci. }
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        
        assert (Hex : exists x, ~ In var (k2 |: FromList (vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2. 
        
        edestruct IH2 with (rho := rho'); [ | | | | | eassumption | ].
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Setminus_Disjoint_preserv_r.
          eapply Disjoint_Included_r. eassumption. sets. 
        + eassumption.
        + inv H4. eapply HS2 in H5. inv H5. intros Hc; eauto. eapply Hdis; eauto.
        + inv_setminus. eapply HS2 in H5. inv_setminus.
          repeat eapply cps_env_rel_weaken; eauto; now intros Hc; eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct (H7 ltac:(reflexivity)). destructAll. eapply Heq in H9; [ | reflexivity ]. destructAll.
          destruct x5; try contradiction. destruct x7. eexists. split; [ | eassumption ].
          unfold exp_eval.one in *. simpl in *. lia.

      - (* Let_e *)
        intros e1 e2 v1 r vs na f1 f2 He1 IH1 He2 IH2.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. inv Hcps.
        
        assert (Hex' : exists v', cps_val_rel v1 v') by admit.  
        (* TODO needs correspondence proof *) destructAll.

        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> exp_eval.one (Let_e na e1 e2))) eq_fuel m
                                            (e2', map_util.M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho))
                                            (Efun (Fcons k1 kon_tag [x1] e2' Fnil) e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | eassumption | reflexivity | ].
                  - eapply Disjoint_Included_r. eapply cps_cvt_exp_subset. eassumption. now sets. 
                  - eassumption.
                  - intros Hc. inv H4. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H4. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }
              
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gss. reflexivity.
              - simpl. reflexivity. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } } 

        assert (Hex : exists x, ~ In var (k |: FromList (x1 :: vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.
        
        split. 
        (* Termination *) 
        { intros v v' Heq1 Hvrel. subst. 
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH2; [ | | | | | eassumption | reflexivity | eassumption ].                  
                  - repeat normalize_sets. eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - repeat normalize_sets. intros Hc; inv Hc; eauto. inv H1.
                    eapply Hdis. eauto.
                  - eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    intros Hc. inv H4. eapply Hdis; eauto.
                    intros Hc. eapply Hdis; eauto.
                  - rewrite !M.gso. eassumption.
                    intros Hc; subst; inv H4; eapply Hdis; eauto.
                    intros Hc; subst; inv H4; eapply Hdis; eauto. } 

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
        
        (* OOT *)
        { intros ?; subst.

          edestruct IH2 with (x := x2) (rho := M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho));
            [ | | | | | eassumption | ].
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H1. eapply Hdis; eauto. 
          - eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
          - rewrite !M.gso. eassumption.
            (* TODO tactic to do these + hint constructor *)
            intros Hc; subst; inv H4; eapply Hdis; eauto.
            intros Hc; subst; inv H4; eapply Hdis; eauto.
          - destruct (H3 ltac:(reflexivity)). destructAll. eapply Heq in H6; [ | reflexivity ]. destructAll.
            destruct x4; try contradiction. destruct x6. eexists. split; [ | eassumption ].
            
            unfold exp_eval.one in *. simpl in *. lia. } 
        
      - (* Let_e, OOT *)
        intros e1 e2 vs na f1 Hoot IH. 
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho).

        assert (HS2 := H10). eapply cps_cvt_rel_subset in HS2. 

        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 

        edestruct IH with (rho := rho'); [ | | | | | eassumption | ].
        + inv H4. eapply Disjoint_Included_r. eassumption. sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold exp_eval.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor; eauto.

      - (* App_e, ClosFix_v *)
        intros e1 e2 e1' vs1 vs2 vs3 n na fns v2 r f1 f2 f3  Heval1 IH1 Hnth Hrec Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps.  
        inv Hcps. 
        
        assert (Hex : exists v', cps_val_rel (ClosFix_v vs2 fns n) v') by admit.
        assert (Hex' : exists v', cps_val_rel v2 v') by admit.  
        (* TODO needs correspondence proof *) destructAll. inv H0. 
        edestruct cps_fix_rel_exists. eassumption. eassumption. eassumption. 
        destruct H0 as (y1 & na' & e3 & e3' & Hu). destructAll.  
        repeat subst_exp. 
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> f2 <+> exp_eval.one (e1 $ e2))) eq_fuel m
                                            (e3', (map_util.M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0))))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) e1'0,
                                             rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | eassumption | reflexivity | ].
                  - now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H2; eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - econstructor; eauto. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } simpl.
              
              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2.              
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IH2 ; [ | | | | | eassumption | reflexivity | eassumption ].                  
                  - eapply Union_Disjoint_l; sets.                   
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included_r. eassumption. sets. 
                  - eassumption.
                  - inv H4. eapply HS2 in H20. inv H20. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    intros Hc. inv H2. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv H4. eapply HS2 in H20. inv H20. intros Hin. eapply Hdis. eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              (* inv H0. simpl. *)
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                intros Hc; subst. inv H4. eapply HS2 in H20. now inv H20.
                intros Hc; subst. eapply HS2 in H3. now inv H3.
              - eassumption. 
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.                    
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv H2. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv H4. eapply HS2 in H20. inv H20. now eapply Hdis; eauto.
                intros Hc; subst. eapply HS2 in H3. inv H3. now eapply Hdis; eauto.
              - simpl. reflexivity. } 

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        split. 

        (* Termination *)  
        { intros v v' Heq1 Hvrel. subst. 

          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 

              repeat subst_exp.
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH3; [ | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - repeat normalize_sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Singleton_l. now eauto.
                    eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets. 
                  - repeat normalize_sets. rewrite FromList_rev. eassumption.
                  - repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto. inv H19; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
                    eapply cps_env_rel_extend_fundefs; try eassumption.
                    repeat normalize_sets. rewrite FromList_rev. now eauto.
                    repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
                    inv H19; eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
        
        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 

          edestruct IH3 with (rho := M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0)));
            [ | | | | |  eassumption | ].
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
            eapply Union_Disjoint_l; sets.
            eapply Disjoint_Singleton_l. now eauto.
            eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets.
          - repeat normalize_sets. rewrite FromList_rev. eassumption.
          - repeat normalize_sets. rewrite FromList_rev. sets.
            intros Hc; inv Hc; eauto. inv H19; eauto.
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
            eapply cps_env_rel_extend_fundefs; try eassumption.
            repeat normalize_sets. rewrite FromList_rev. now eauto.
            repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
            inv H19; eauto.
          - rewrite M.gss. reflexivity.
          - destruct (H20 ltac:(reflexivity)). destructAll. eapply Heq in H22; [ | reflexivity ]. destructAll.
            destruct x8; try contradiction. destruct x10. eexists. split; [ | eassumption ].
            
            unfold exp_eval.one in *. simpl in *. lia. } 
        

      - (* App_e, ClosFix_v, OOT 1 *)
        intros e1 e2 vs f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps.
        set (rho' := M.set k1 (Vfun rho
                                    (Fcons k1 kon_tag [x1]
                                           (Efun
                                              (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil)
                                              e2') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | eassumption | ].
        + sets.
        + eassumption.
        + intros Hc; inv H2; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          inv H2. intros Hc. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H5. reflexivity. destructAll. eexists (x3 + 1)%nat. split.
          unfold exp_eval.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.
          
      - (* App_e, ClosFix_v, OOT 2 *)
        intros e1 e2 v vs _ _ (* TODO remove from sem *) f1 f2 He1 IH1 Hoot IH2.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps.
        
        assert (Hex' : exists v', cps_val_rel v v') by admit. destructAll. 
        (* TODO needs correspondence proof *)

        set (rho' := M.set k2 (Vfun (M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) k1) rho)) (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) k2)
                           (M.set x1 x0
                                  (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1]
                                                             (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2])
                                                                          Fnil) e2') Fnil) k1) rho))).
        
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+>exp_eval.one (e1 $ e2))) eq_fuel m
                                            (e2', rho')
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | eassumption | reflexivity | ].
                  - now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }
          
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }  
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
               
              2:{ intros m. eapply preord_exp_Efun_red. } simpl. 

              eapply preord_exp_refl. tci.
              eapply preord_env_P_refl. tci. }
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, exp_eval.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        
        assert (Hex : exists x, ~ In var (k2 |: FromList (vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2. 
        
        edestruct IH2 with (rho := rho'); [ | | | | | eassumption | ].
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Setminus_Disjoint_preserv_r.
          eapply Disjoint_Included_r. eassumption. sets. 
        + eassumption.
        + inv H4. eapply HS2 in H5. inv H5. intros Hc; eauto. eapply Hdis; eauto.
        + inv_setminus. eapply HS2 in H5. inv_setminus.
          repeat eapply cps_env_rel_weaken; eauto; now intros Hc; eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct (H7 ltac:(reflexivity)). destructAll. eapply Heq in H9; [ | reflexivity ]. destructAll.
          destruct x5; try contradiction. destruct x7. eexists. split; [ | eassumption ].
          unfold exp_eval.one in *. simpl in *. lia.
          
      - (* Match_e *)
        admit.

      - (* Match_e OOT *)
        intros e1 vs n br f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split.
        congruence.
        intros _. inv Hcps.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | eassumption | ].
        + sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.          
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold exp_eval.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.

      - (* Var_e *)
        intros z vs v Hnth.  
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.
        
        eapply preord_exp_app_compat.
        
        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.
          
        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.
          
        + eapply preord_var_env_extend_neq_l. 
          eapply preord_var_env_get. eapply preord_val_refl; tci.
          rewrite M.gss. reflexivity. eassumption. intros Hc; subst; eauto.
          
        + constructor; eauto.
          edestruct cps_env_rel_nth_error; eauto. destructAll.
          eapply preord_var_env_get.
          2:{ rewrite M.gss. reflexivity. }
          2:{ eassumption. }
          eapply cps_cvt_val_alpha_equiv.
          eapply eq_fuel_compat. eapply eq_fuel_compat.
          clear; now firstorder. (* TODO find inclusion refl *)
          eassumption. eassumption. 
          
      - (* Lam_e *)
        intros e vs na.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.

        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

            2:{ intros m. eapply preord_exp_Efun_red. }

            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat. 
            now eapply eq_fuel_compat. 

            eapply preord_var_env_extend_neq.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. now rewrite M.gss; reflexivity. eassumption.
            
            - intros Hc; subst; eauto. 
            - intros Hc; subst. inv H2. eapply Hdis; eauto.
            - constructor; eauto. 
              eapply preord_var_env_extend_eq. inv Hval.
              (* Seems similar to other cases in alpha equiv, maybe lemma? *)
              eapply preord_val_fun.
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + assert (Hlen : Datatypes.length names = Datatypes.length vnames).
                { simpl. eapply Forall2_length in Hcenv. 
                  eapply Forall2_length in H5.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }
                
                intros rho1' j vs1 vs2 Heq Hset.
                destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
                destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
                eexists. split. reflexivity. intros. 
                eapply cps_cvt_exp_alpha_equiv; try eassumption.
                * reflexivity.
                * constructor; eauto.
                * normalize_sets. intros Hc. inv Hc. inv H3; eauto. eapply H9; eauto.
                * simpl. congruence. 
                * normalize_sets. sets.
                * normalize_sets.
                  eapply Union_Disjoint_l. sets.
                  eapply Union_Disjoint_l; sets.
                * assert (Hseq : k0 |: (x0 |: FromList names) \\ [set k0] \\ [set x0] \\ FromList names <--> Empty_set _) by xsets.
                  inv H0. inv H17. clear H18. normalize_sets. simpl.
                  rewrite extend_extend_lst_commut. rewrite extend_commut.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_not_In_P_l; eauto.
                  eapply preord_env_P_inj_set_not_In_P_r; eauto.
                  eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                  now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                  now xsets.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.                     
                     rewrite Hseq in Hc. 
                     inv Hc; eauto. now inv H0.
                     inv H2; eapply Hdis; eauto.
                  -- intros Hc. inv Hc. inv H0. inv H11; eauto. inv H0; eauto.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.                     
                     rewrite Hseq in Hc. 
                     inv Hc; eauto. inv H0.
                     inv H2. eapply Hdis. constructor. now right. eassumption.
                  -- intros Hc. eapply image_extend_Included' in Hc.
                     inv Hc; eauto. eapply image_extend_lst_Included in H0; eauto.
                     rewrite Hseq, image_id in H0. inv H0; eauto. inv H3.
                     inv H4. now eapply Hdis; eauto.
                     inv H0; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; subst; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; eauto. inv H4. eapply Hdis; eauto.
                  -- eassumption. }
        
        (* Invariant composition *) 
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia. } 

      - (* Fix_e *)  
        intros n vs efns.
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps. inv Hval.
        
        assert (Hfeq : all_fun_name fdefs = fnames).
        { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }
        
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

            2:{ intros m. eapply preord_exp_Efun_red. }
            
            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat. 
            now eapply eq_fuel_compat. 

            
            eapply preord_var_env_def_funs_not_In_r.
            rewrite Same_set_all_fun_name.
            erewrite Hfeq. intros Hc. now eapply Hdis; eauto.
            
            eapply preord_var_env_extend_neq_l.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. rewrite M.gss. reflexivity. eassumption.
            now intros Hc; subst.

            constructor; eauto.

            eapply preord_var_env_get.
            2:{ rewrite M.gss. reflexivity. } 
            2:{ rewrite def_funs_eq. reflexivity. eapply Same_set_all_fun_name.
                rewrite Hfeq. eapply nth_error_In. eassumption. } 
            
            revert f1 f0 H13 H11. generalize (N.to_nat n). induction f as [f IHf] using lt_wf_rec1. intros.

            edestruct cps_cvt_rel_efnlst_exists. eassumption. rewrite Hfeq. eassumption.
            rewrite Hfeq. eassumption. destructAll.

            edestruct cps_fix_rel_exists. eassumption. eassumption. eassumption. destructAll.

            eapply preord_val_fun.
            + eassumption.
            + eassumption.
            +
              assert (Hlen : Datatypes.length names = Datatypes.length vnames).
              { simpl. eapply Forall2_length in Hcenv.
                  eapply Forall2_length in H6.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }
              
              intros rho1' j vs1 vs2 Heq Hset.
              destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
              destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
              eexists. split. reflexivity. intros. repeat subst_exp.
              
              eapply cps_cvt_exp_alpha_equiv; try eassumption.
              * reflexivity.
              * constructor.
                -- intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.
                -- eapply NoDup_app; eauto.
                   eapply NoDup_rev. eassumption.
                   rewrite FromList_rev. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                intros Hc. inv Hc. inv H17; eauto. inv H17; eauto.
              * simpl. rewrite !app_length, !rev_length.
                rewrite H3. erewrite <- cps_fix_rel_length; [ | eassumption ]. congruence. 
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l. now sets.
                eapply Union_Disjoint_l.
                eapply Disjoint_Singleton_l. now eauto.
                eapply Disjoint_Included_r. eassumption. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included_r. eapply Included_trans. eapply Setminus_Included. eassumption.
                now sets.
                eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eassumption. sets. 

              * inv H24. inv H29. clear H30. simpl. repeat normalize_sets. 

                assert (Hseq : (x7 |: (x8 |: (name_in_fundefs Bs :|: FromList names)) \\ [set x7] \\ [set x8] \\
                                   name_in_fundefs Bs \\ FromList names) <--> Empty_set _) by xsets. 

                rewrite extend_extend_lst_commut. rewrite extend_commut.
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.
                
                rewrite extend_lst_app. rewrite extend_lst_rev; eauto. 

                erewrite <- cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ]. 
 
 
                eapply preord_env_P_inj_def_funs_Vfun.

                -- eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                   now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                   rewrite FromList_rev. rewrite Same_set_all_fun_name. now xsets.
                  
                -- rewrite H3. erewrite cps_fix_rel_names; [ | eassumption ].
                   eapply cps_fix_rel_length; eauto.

                -- erewrite cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ]. eassumption.
                   
                -- eapply Disjoint_Included_l.
                   eapply image_extend_lst_Included. eassumption.
                   rewrite FromList_rev, image_id, <- Same_set_all_fun_name, Hseq.
                   rewrite Same_set_all_fun_name.
                   eapply Disjoint_Included_r. eassumption. sets.
                   
                -- intros. eapply IHf. lia.
                   now erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0); eauto. 
                   eassumption.

                -- replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                   rewrite H3. eapply cps_fix_rel_length; eauto.
                   
                -- rewrite !rev_length.
                   rewrite H3. eapply cps_fix_rel_length; eauto.

                -- intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc.
                   repeat normalize_sets. rewrite !FromList_rev in Hc. rewrite <- Same_set_all_fun_name in Hc.
                   
                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in Hc; eauto.                   
                   rewrite Hseq in Hc. repeat normalize_sets. inv Hc; eauto. 
                   now eapply Same_set_all_fun_name in H17; inv H4; eauto.
                   now inv H4; eapply Hdis; eauto.
                   rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence. 

                -- intros Hc. eapply image_extend_Included' in Hc. inv Hc; eauto. 
                   eapply image_extend_lst_Included in H17; eauto. rewrite image_id in H17.
                   repeat normalize_sets. rewrite !FromList_rev in H17. rewrite <- Same_set_all_fun_name in H17.
                   
                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in H17; eauto.                   
                   rewrite Hseq in H17. repeat normalize_sets. inv H17; eauto. 
                   now eapply Same_set_all_fun_name in H24; inv H12; inv H17; eauto.
                   now inv H12; inv H17; eapply Hdis; eauto.
                   rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence.
                   inv H17; inv H12; eauto.
                   
                -- intros Hc; subst; eauto.

                -- intros Hc; subst; inv H12; eauto. 

                -- repeat normalize_sets.
                   intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.

                -- repeat normalize_sets. inv H12. inv H17.                    
                   intros Hc. eapply in_app_or in Hc. inv Hc.
                   eapply in_rev in H17; eauto. eapply Hdis; eauto.

                -- rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence. } 

        
        (* Invariant composition *) 
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia. } 

      - (* OOT *)
        intros vs e c Hlt. 
        intros rho vnames k x vk e' S S' f Hdis Hnin1 Hnin2 Hcenv Hcps. split.
        congruence.
        intros _.
        unfold exp_eval.one, lt in *. simpl in *. 
        eexists 0%nat. split. lia.
        constructor 1. unfold one. simpl. lia.

      - (* STEP *)
        now eauto. (* Immediate from IH for eval_step *)
        
    Abort. 
    
End Post.

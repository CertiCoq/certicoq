Require Import MetaCoq.Utils.bytestring.
From Coq Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.
Require Import set_util.

Import ListNotations.
Open Scope list_scope.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.
Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util LambdaBoxLocal_to_LambdaANF_corresp
        LambdaBoxLocal_to_LambdaANF_correct
        LambdaANF.tactics identifiers bounds cps_util rename.


Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


Section ANF_proof.

  Context (cenv : conId_map) (ctenv : ctor_env).
  Context (func_tag default_tag : positive).

  (** ** ANF value relation *)

  Definition convert_anf_rel := convert_anf_rel func_tag default_tag.
  Definition convert_anf_rel_exps := convert_anf_rel_exps func_tag default_tag.
  Definition convert_anf_rel_efnlst := convert_anf_rel_efnlst func_tag default_tag.
  Definition convert_anf_rel_branches := convert_anf_rel_branches func_tag default_tag.

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v',  M.get x rho = Some v' /\ P v v') vs vn.


  Inductive anf_fix_rel (fnames : list var) (env : list var) : Ensemble var -> list var -> efnlst -> fundefs -> Ensemble var -> Prop :=
  | fix_fnil :
    forall S, anf_fix_rel fnames env S [] eflnil Fnil S
  | fix_fcons :
    forall S1 S1' S2 S2' S3 fnames' e1 C1 r1 n n' efns B f x,
      x \in S1 ->
      S1' \subset S1 \\ [set x] ->
      S2' \subset S2 ->

      convert_anf_rel S1' e1 (x :: List.rev fnames ++ env) cenv S2 C1 r1 ->

      anf_fix_rel fnames env S2' fnames' efns B S3 ->

      anf_fix_rel fnames env S1 (f :: fnames') (eflcons n' (Lam_e n e1) efns) (Fcons f func_tag (x::nil) (C1 |[ Ehalt r1 ]|) B) S3.


  Inductive anf_val_rel : value -> val -> Prop :=
  | rel_Con :
    forall vs vs' dc c_tag,
      Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
      dcon_to_tag default_tag dc cenv = c_tag ->
      anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | rel_Clos :
    forall vs rho names na x f e C r S1 S2,
      anf_env_rel' anf_val_rel names vs rho ->

      NoDup names ->

      Disjoint var (x |: FromList names) S1 ->

      ~ x \in [set f] :|: FromList names ->
      ~ f \in FromList names ->

     convert_anf_rel S1 e (x::names) cenv S2 C r ->

     anf_val_rel (Clos_v vs na e)
                 (Vfun rho (Fcons f func_tag (x::nil) (C |[ Ehalt r ]|) Fnil) f)
  | rel_ClosFix :
    forall S1 S2 names fnames vs rho efns Bs n f,
      anf_env_rel' anf_val_rel names vs rho ->

      NoDup names ->
      NoDup fnames ->

      Disjoint _ (FromList names :|: FromList fnames) S1 ->
      Disjoint _ (FromList names) (FromList fnames) ->

      nth_error fnames (N.to_nat n) = Some f ->

      anf_fix_rel fnames names S1 fnames efns Bs S2 ->

      anf_val_rel (ClosFix_v vs efns n) (Vfun rho Bs f).


  Definition anf_env_rel := anf_env_rel' anf_val_rel.


  Definition convert_anf_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho env C x S S' i e',
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->

      occurs_free e' \subset x |: FromList env ->
         
      anf_env_rel env vs rho ->

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv (cps_bound f t) eq_fuel i
                               (e', (M.set x v' rho))
                               (C|[ e' ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).


  Definition convert_anf_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat)  :=
    forall rho env C x S S' i e',
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->

      occurs_free e' \subset x |: FromList env ->

      anf_env_rel env vs rho ->

      

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv
                               (cps_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                          (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                               eq_fuel i
                               (e', (M.set x v' rho))
                               (C|[ e' ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e) <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).



  Definition convert_anf_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat)  :=
    forall rho env C ys S S' vs2 e',
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length env)) es ->

      Disjoint _ (FromList env) S ->

      occurs_free e' \subset FromList ys :|: FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel_exps S es env cenv S' C ys ->

      Forall2 (anf_val_rel) vs1 vs2 ->

      exists rho',
        set_lists ys vs2 rho = Some rho' /\
        forall i,
          preord_exp ctenv (cps_bound f (t <+> (2 * Datatypes.length (exps_as_list es))%nat))
                     eq_fuel i (e', rho') (C |[ e' ]|, rho).

  Lemma convert_anf_result_not_fresh S e names cenv' S' C x :
    convert_anf_rel S e names cenv' S' C x ->
    ~ x \in S'.
  Proof.
  Admitted.

  Lemma convert_anf_fresh_subset S e names cenv' S' C x :
    convert_anf_rel S e names cenv' S' C x ->
    S' \subset S.
  Proof.
  Admitted.

  Lemma convert_anf_in_env S e names S' C x env v f t : 
    convert_anf_rel S e names cenv S' C x ->
    List.In x names -> 
    eval_env_fuel env e (Val v) f t ->
    Disjoint _ (FromList names) S ->
    exists n, nth_error env n = Some v /\ nth_error names n = Some x.
  Proof.
    intros Hrel. revert env v f t.
    eapply convert_anf_rel_ind with (P := fun S e names cenv S' C x =>
                                            forall env v f t
                                              (Hin : List.In x names)
                                              (Heval: eval_env_fuel env e (Val v) f t)
                                              (Hdis: Disjoint _ (FromList names) S),
                                            exists n, nth_error env n = Some v /\ nth_error names n = Some x); try eassumption; intros;
      try (now exfalso; eapply Hdis; split; [ eassumption | eassumption ]). 
    - inv Heval.
      + eexists; split; eauto.
      + inv H0.
    - exfalso; eapply Hdis; split; [ eassumption | ]. eapply H0.
    - inv Heval. inv H3. edestruct H2. now right. eassumption. 
      normalize_sets. eapply Union_Disjoint_l.
      eapply  Disjoint_Singleton_l. eapply convert_anf_result_not_fresh. eassumption.
      eapply Disjoint_Included_r; [ | eassumption ].
      eapply convert_anf_fresh_subset; eassumption.
      destructAll. destruct x0.
      + simpl in *. inv H3. inv H4.
        eapply H0. eassumption. eassumption.
        eassumption.
      + simpl in *. eauto.
    - exfalso; eapply Hdis; split; [ eassumption | ].
      eapply H. eapply nthN_In. eassumption.
    - exfalso; eapply Hdis; split; [ eassumption | ]. eapply H1.
  Qed.
  
  Require Import stemctx.
  
  Lemma occurs_free_ctx_comp (C1 C2 : exp_ctx) :
    occurs_free_ctx (comp_ctx_f C1 C2) \subset
    occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1).
  Proof.
    revert C2.
    eapply ctx_exp_mut with (P := fun C1 =>
                                    forall C2,
                                      occurs_free_ctx (comp_ctx_f C1 C2) \subset
                                                      occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1))
                            (P0 := fun F =>
                                     forall C,
                                       occurs_free_fundefs_ctx (comp_f_ctx_f F C) \subset
                                                               occurs_free_fundefs_ctx F :|: (occurs_free_ctx C \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      now sets.
    - simpl. repeat repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx. 
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      rewrite name_in_fundefs_ctx_comp. now sets.
    - simpl. repeat normalize_occurs_free_ctx. 
      eapply Union_Included; [ | now sets ].
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply H.
      eapply Union_Included.
      rewrite <- !Union_assoc. 
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
      now sets. now tci. now sets.
      normalize_bound_stem_ctx.
      rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
      rewrite !Union_assoc.
      rewrite (Union_commut _ (bound_stem_ctx e)).        
      rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
      rewrite <- ! Union_assoc.
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
      now sets. now tci. now sets. 
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      eapply Union_Included.
      + rewrite name_in_fundefs_ctx_comp. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets. 
  Qed.

  Lemma occurs_free_ctx_app (C : exp_ctx)  (e : exp) :
    occurs_free (C |[ e ]|) \subset
    occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C).
  Proof.
    revert e. 
    eapply ctx_exp_mut with (P := fun C =>
                                    forall e,
                                      occurs_free (C |[ e ]|) \subset
                                      occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C))
                            (P0 := fun F =>
                                     forall e,
                                       occurs_free_fundefs (F <[ e ]>) \subset
                                        occurs_free_fundefs_ctx F :|: (occurs_free e \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included. now sets.
      eapply Union_Included.
      + eapply Included_trans. eapply H.
        eapply Union_Included; now sets.
      + now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      + eapply Included_trans. eapply H. now sets.
      + rewrite <- name_in_fundefs_ctx_ctx at 1. now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included; [ | now sets ].

      eapply Setminus_Included_Included_Union.        
      eapply Included_trans. eapply H.
      eapply Union_Included.
      + rewrite <- !Union_assoc. 
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
        now sets. now tci. now sets.        
      + rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
        rewrite !Union_assoc.
        rewrite (Union_commut _ (bound_stem_ctx e)).        
        rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
        rewrite <- ! Union_assoc.
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
        now sets. now tci. now sets.
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      repeat normalize_occurs_free.
      eapply Union_Included.
      + rewrite <- name_in_fundefs_ctx_ctx. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets. 
  Qed.

    
  Corollary bound_stem_ctx_comp_f c c' :
    bound_stem_ctx (comp_ctx_f c c') <-->
    bound_stem_ctx c :|: bound_stem_ctx c'.
  Proof.
    symmetry. 
    eapply bound_stem_comp_ctx_mut.
  Qed.
    

  Lemma convert_anf_rel_efnlst_names S fns names fs S' fns' :
    convert_anf_rel_efnlst S fns names cenv fs S' fns' ->
    name_in_fundefs fns' <--> FromList fs.
  Proof.
    intros Hanf. induction Hanf; normalize_sets.
    - now sets.
    - simpl. rewrite IHHanf. reflexivity.
  Qed.
    
    
  Lemma convert_anf_res_included S e names S' C x :
    convert_anf_rel S e names cenv S' C x ->
    x \in FromList names :|: bound_stem_ctx C.
  Proof.
    revert S names S' C x.
    eapply expression.exp_ind' with (P := fun e =>
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names cenv S' C x),
                                              x \in FromList names :|: bound_stem_ctx C)
                                    (P0 := fun es =>
                                             forall S names S' C x
                                                    (Hanf : convert_anf_rel_exps S es names cenv S' C x),
                                               FromList x \subset FromList names :|: bound_stem_ctx C)
                                    (P1 := fun fns => True)
                                    (P2 := fun bs => True); intros; try inv Hanf; eauto;
      try (now try normalize_occurs_free_ctx; try normalize_sets; sets).
    - repeat normalize_occurs_free_ctx; repeat normalize_occurs_free.
      left. eapply nth_error_In. eassumption.
    - repeat normalize_bound_stem_ctx. simpl. now sets.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.      
      now sets. 
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx. now sets.
    - repeat normalize_bound_stem_ctx. rewrite !bound_stem_ctx_comp_f.
      repeat normalize_bound_stem_ctx. now sets.      
    - rewrite !bound_stem_ctx_comp_f.
      eapply H0 in H11. inv H11; [ | now eauto ].
      normalize_sets. inv H1; [ | now eauto ].
      inv H2.
      eapply H in H10. inv H10; eauto.
    - repeat normalize_bound_stem_ctx.
      right. left. eapply convert_anf_rel_efnlst_names. eassumption.
      eapply nthN_In. eassumption. 
    - normalize_sets. rewrite bound_stem_ctx_comp_f.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply H in H4. inv H4; eauto.
      + eapply H0 in H10. eapply Included_trans; eauto. now sets.
  Qed.      
      
      
  Lemma convert_anf_occurs_free_ctx S e names S' C x :
    convert_anf_rel S e names cenv S' C x ->
    occurs_free_ctx C \subset FromList names.
  Proof.
    revert S names S' C x.
    eapply expression.exp_ind' with (P := fun e =>
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names cenv S' C x),
                                              occurs_free_ctx C \subset FromList names)
                                    (P0 := fun es =>
                                             forall S names S' C x
                                                    (Hanf : convert_anf_rel_exps S es names cenv S' C x),
                                               occurs_free_ctx C \subset FromList names)
                                    (P1 := fun fns => forall S names fs S' fns' x
                                                             (Hanf : convert_anf_rel_efnlst S fns names cenv fs S' fns'),
                                               occurs_free_fundefs fns' \subset FromList names)
                                    (P2 := fun bs => forall S names S' x cl
                                                            (Hanf : convert_anf_rel_branches S bs x names cenv S' cl),
                                               Union_list (map (fun c => occurs_free (snd c)) cl) \subset FromList names); intros; inv Hanf;
      try (now normalize_occurs_free_ctx; sets).
    - repeat normalize_occurs_free_ctx; repeat normalize_occurs_free.
      simpl. assert (Hanf := H10).
      eapply H in H10. eapply convert_anf_res_included in Hanf. 
      eapply Union_Included; [ | now sets ]. 
      eapply Union_Included; [ | now sets ]. 
      eapply Setminus_Included_Included_Union. 
      eapply Included_trans. eapply occurs_free_ctx_app.
      normalize_occurs_free.
      eapply Union_Included.
      eapply Included_trans. eassumption. repeat normalize_sets. now sets.
      eapply Setminus_Included_Included_Union. eapply Singleton_Included. 
      repeat normalize_sets. inv Hanf; eauto. inv H0; eauto.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx. now sets.
      now sets. eauto.  eapply 
      
  
  Lemma convert_anf_correct :
      forall vs e r f t, eval_env_fuel vs e r f t -> convert_anf_correct_exp vs e r f t.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := convert_anf_correct_exp)
                                     (P0 := convert_anf_correct_exps)
                                     (P := convert_anf_correct_exp_step).

      6:{ (* Let_e *)
        intros e1 e2 v1 r env na f1 f2 t1 t2.
        intros Heval1 IH1 Heval2 IH2.
        intros rho names C x S1 S2 i e' Hwf Hwfexp Hdis Hfv Hanf Hcvt.
        split.
        - intros v v' Heq Hvrel. subst. inv Hcvt. inv Hwfexp.
          
          destruct (Decidable_FromList names). destruct (Dec x1); [ | ].
          + (* x1 \in names *)
            assert (Hin := f).
            rewrite <- app_ctx_f_fuse. 
            eapply preord_exp_post_monotonic.
            * admit. (* bounds *) 
            * eapply convert_anf_in_env in f; [ | eassumption | eassumption | eassumption ].
              destruct f as [n [Hnth' Hnth]].
              
              assert (Hrel := All_Forall.Forall2_nth_error _ _ _ Hanf Hnth' Hnth).
               
              destruct Hrel as [v1'' [Hget'' Hrel'']].
              
              eapply preord_exp_trans. now tci.
              now eapply eq_fuel_idemp.
              2:{ intros. eapply IH1; [ | | | | |  | reflexivity | ]; try eassumption.
                  eapply Included_trans. eapply occurs_free_ctx_app.
                  eapply Union_Included. admit. (* lemma fv ctx *)
                  eapply Included_trans. eapply Included_Setminus_compat.
                  eassumption. reflexivity.
                  rewrite Setminus_Union_distr.
                  eapply Union_Included; [ |  now sets ].
                  eapply Setminus_Included_Included_Union.
                  admit. (* lemma  x \ names U bound_stem C
                            (also bound_stem \subset S)                             
                          *) }
              
              eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
              2:{ intros. unfold convert_anf_correct_exp in IH2.
                  eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                  - constructor; eauto. eapply All_Forall.nth_error_forall; eassumption.
                  - simpl.
                    replace (N.pos (Pos.of_succ_nat (length names))) with
                      (1 + N.of_nat (length names)) by lia. eassumption.
                  - normalize_sets. eapply Union_Disjoint_l. 
                    admit. (* easy lemmas *)
                    admit. (* easy lemmas *) 
                  - eapply Included_trans. eassumption.
                    normalize_sets. now sets.
                  - constructor.
                    + eexists. split. rewrite M.gss. reflexivity. eassumption.
                    + eapply All_Forall.Forall2_impl. eassumption.
                      simpl. intros v2 z Hex. destructAll.
                      eexists. split; [ | eassumption ].
                      destruct (OrdersEx.Positive_as_OT.eq_dec x1 z).
                      * subst. rewrite M.gss. congruence.
                      * rewrite M.gso; eauto. } 

              eapply preord_exp_refl. now eapply eq_fuel_compat. (* TODO check bounds *)
              eapply preord_env_P_extend.
              2:{ eapply preord_val_refl. now eapply eq_fuel_compat. }
              intros z Hinz vz Hget. eexists vz. split.
              { destruct (OrdersEx.Positive_as_OT.eq_dec x1 z).
                * subst. rewrite M.gss. congruence.
                * rewrite M.gso; eauto. } (* TODO lemma *)
              eapply preord_val_refl. now eapply eq_fuel_compat.

          +  (* not (x1 \in names) *)
          assert (Hex : exists v1', anf_val_rel v1 v1') by admit. destructAll.           
          
          rewrite <- app_ctx_f_fuse. eapply preord_exp_post_monotonic.
          * admit. (* bounds *) 
          * eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
            2:{ intros. eapply IH1; [ | | | | |  | reflexivity | ]; try eassumption.
                eapply Included_trans. eapply occurs_free_ctx_app.
                eapply Union_Included. admit. (* lemma occurs_free_ctx C \subset x :|: names *)
                eapply Included_trans. eapply Included_Setminus_compat.
                eassumption. reflexivity.
                rewrite Setminus_Union_distr.
                eapply Union_Included; [ |  now sets ].
                eapply Setminus_Included_Included_Union.
                admit. (* lemma  x \ names U bound_stem C
                          (also bound_stem \subset S)                             
                        *) }
            
            eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
            2:{ intros. unfold convert_anf_correct_exp in IH2.
                eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                - constructor; eauto. admit. (* well_formed v1 *)
                - simpl.
                  replace (N.pos (Pos.of_succ_nat (length names))) with
                    (1 + N.of_nat (length names)) by lia. eassumption.
                - normalize_sets. eapply Union_Disjoint_l. 
                  admit. (* easy lemmas (subset free names) *)
                  admit. (* easy lemmas (subset free names) *) 
                - eapply Included_trans. eassumption.
                  normalize_sets. now sets.
                - constructor.
                  + eexists. split. rewrite M.gss. reflexivity. eassumption.
                  + eapply Forall2_monotonic_strong; [ | eassumption ].
                    intros z1 z2 Hin1 Hin2 Hex. simpl in *. destructAll.
                    eexists. split. rewrite M.gso. eassumption.
                    now intro; subst; eauto.
                    eassumption.  } 

            eapply preord_exp_refl. now eapply eq_fuel_compat. (* TODO check bounds *)
            eapply preord_env_P_extend.
            2:{ eapply preord_val_refl. now eapply eq_fuel_compat. }
            intros z Hinz vz Hget. eexists vz. split.
            rewrite M.gso. now eassumption. intros Heq. subst. eapply n.
            inv Hinz. eapply Hfv in H0. inv H0. congruence. eassumption. 
              eapply preord_val_refl. now eapply eq_fuel_compat.
          
          
      11:{ (* enil *)
        intros env. unfold convert_anf_correct_exps.
        intros rho names C rs S S' vs x ctag Hwfenv Hwf Hdis Henv Hanf Hall.
        inv Hall. inv Hanf.
        exists (M.empty val). exists [].  split; eauto.
        split. now constructor.
        intros i. eapply preord_exp_refl.
        admit. (* bounds *)
        now eauto. }

      11:{ (* econs *)
        intros env. intros e es v vs f fs t ts Heval IHe Hevalm IHes.
        intros rho names C rs S S' vs' x ctag Hwfenv Hwf Hdis Henv Hanf Hall.
        inv Hall. inv Hanf. inv Hwf.
        edestruct IHe; [ | | | | | eassumption | ]; try eassumption.
        admit. (* XXX not in *)
        
        clear H0. 
        specialize (H v y (ltac:(reflexivity)) H1).
 
        edestruct IHes; [ | | | | eassumption | | ]; try eassumption.
        admit. (* Disjoint names easy with lemma *)

        destructAll. Opaque preord_exp'.
        eexists. exists (((max_list x2 1) + 1)%positive::x2). split.
        simpl. rewrite H0. reflexivity.
        
        split. constructor; [ | assumption ].
        
        admit. (* easy max + 1 not in list *) 
        
        
        clear H0. 
        specialize (H v y (ltac:(reflexivity)) H1).

        
        edestrict 
        
        now tci. }
        intros 

        names C x S S' i Hwfenv Hwf Hdis Hnin1 Henv Hanf.

      - (* Con_e terminates *)
        intros es vs1 env dc f1 t1 Heval IH.
        intros rho names C x S S' i Hwfenv Hwf Hdis Hnin1 Henv Hanf.
        inv Hwf. inv Hanf. split; [ | congruence ]. 
        
        intros v1 v2 Heq Hrel. inv Heq. inv Hrel. 
        
        eapply preord_exp_post_monotonic. 
        
        2:{ edestruct IH with (x := x) (ctag := dcon_to_tag default_tag dc cenv)
              as [rho' [zs [Hset [Hnd Hrel]]]]; [ | | | | eassumption | | ]; try eassumption. 
            - now sets.
            - eapply preord_exp_trans.
              now tci.
              now eapply eq_fuel_idemp. 
              2:{ intros m.
                  rewrite <- app_ctx_f_fuse. eapply Hrel. }
              
                eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
                
                2:{ intros m. eapply preord_exp_Econstr_red.
                    eapply get_list_set_lists. eassumption. eassumption. }
                
                eapply preord_exp_halt_compat.
                now eapply eq_fuel_compat. 
                now eapply eq_fuel_compat. 
                
                eapply preord_var_env_extend_eq.
                eapply preord_val_refl. now tci. }
        
        { admit. (* bounds *) }
          
      - (* Con_e OOT *)  
        intros es es1 es2 e vs1 vs dc fs f1 t1 ts (* TODO fix order *) Heq Heval IH Hoot IHoot. 
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split. congruence.
        
        intros _.

        assert (Hwf := H1). eapply exps_wf_app with (es2 := econs e es2) in H1; [ | eassumption ].
        destruct H1 as [ H1 Hwf' ].
        
        edestruct cps_cvt_rel_exps_app with (es2 := econs e es2). eassumption. eassumption.
        destructAll.

        assert (Hex :  exists vs2, Forall2 (cps_val_rel) vs1 vs2).
        { eapply cps_val_rel_exists_list. eapply eval_fuel_many_wf in Heval.
          eassumption. eassumption.
          eapply Forall2_length in Hcenv. rewrite Hcenv. eassumption. } 
        destructAll.

        unfold cps_cvt_correct_exps in *.
        assert (Hexps := H9).
        
        eapply IH with (rho := rho) (ys := []) (vs' := []) in H9; clear IH; [ | | | | | | | | | | eassumption | reflexivity ]; eauto.
        + destructAll.

          inv H7.
          
          assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
          { eapply ToMSet_non_member. tci. } destructAll.
          
          set (rho'' := (M.set k1 (Vfun x8 (Fcons k1 kon_tag [x9] es' Fnil) k1) x8)).

          eapply IHoot with (rho := rho'') in H13.
          
          * destructAll.
            assert (Hoot' : bstep_fuel cenv x8 (Efun (Fcons k1 kon_tag [x9] es' Fnil) e'0) (x4 + 1)%nat OOT tt).
            { replace tt with (tt <+> tt) by reflexivity. econstructor 2. econstructor. simpl. eassumption. }
            
            edestruct H9. reflexivity. eassumption. destructAll.
            eexists. split.
            2:{ replace tt with (tt <+> tt).
                destruct x6; [ | contradiction ]. destruct x11. eassumption.
                reflexivity. } 
            
            simpl. unfold cps_bound, one, one_i in *; simpl; unfold_all.
            unfold fuel_exp. simpl. lia. 
            
          * eassumption.
          * eassumption.
          * inv Hwf'. eassumption.
          * eapply Disjoint_Included_r. eassumption.
            eapply Union_Disjoint_l.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
            xsets. 
          * eassumption.
          * intros Hc. eapply Hdis. constructor. now right.
            eapply H5.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.

        split; [ | congruence ]. 
        
        intros v1 v2 Heq Hrel. inv Heq. inv Hrel. 
                
        eapply preord_exp_post_monotonic. 
        
        2:{ edestruct IH with (ys := @nil var) (vs' := @nil val) (rho := rho);
            [ | | | | | | | | | eassumption | eassumption | | ]. 
            - eassumption.
            - eassumption.
            - repeat normalize_sets. eapply Union_Disjoint_l; xsets.
            - repeat normalize_sets.
              eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
              eapply Union_Included; eapply Included_trans; eauto; sets.
            - repeat normalize_sets.
              eapply Disjoint_Included_l; eauto; sets.
            - repeat normalize_sets; sets.
            - eassumption.              
            - eassumption.
            - repeat normalize_occurs_free. repeat normalize_sets. 
              eapply Union_Disjoint_l.
              now eapply Disjoint_Included_r; eauto; sets.
              rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
              now eapply Disjoint_Included_r; eauto; sets.
            - reflexivity.
            - destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply H0. } 
                             
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Econstr_red.
                  eapply get_list_set_lists. eassumption.
                  eassumption. }
              
              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
               
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_get.
              2:{ eapply M.gss. }
              2:{ erewrite <- set_lists_not_In; [ | eassumption | ].
                  eassumption.
                  simpl. intros Hc; subst. eapply H4 in Hc. inv Hc. now eapply Hdis; eauto. }
              
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              intros Hc; subst; eapply Hdis; now eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
        
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *.
            unfold fuel_exp, trace_exp. lia. }
          
      - (* Con_e OOT *)  
        intros es es1 es2 e vs1 vs dc fs f1 t1 ts (* TODO fix order *) Heq Heval IH Hoot IHoot. 
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split. congruence.
        
        intros _.

        assert (Hwf := H1). eapply exps_wf_app with (es2 := econs e es2) in H1; [ | eassumption ].
        destruct H1 as [ H1 Hwf' ].
        
        edestruct cps_cvt_rel_exps_app with (es2 := econs e es2). eassumption. eassumption.
        destructAll.

        assert (Hex :  exists vs2, Forall2 (cps_val_rel) vs1 vs2).
        { eapply cps_val_rel_exists_list. eapply eval_fuel_many_wf in Heval.
          eassumption. eassumption.
          eapply Forall2_length in Hcenv. rewrite Hcenv. eassumption. } 
        destructAll.

        unfold cps_cvt_correct_exps in *.
        assert (Hexps := H9).
        
        eapply IH with (rho := rho) (ys := []) (vs' := []) in H9; clear IH; [ | | | | | | | | | | eassumption | reflexivity ]; eauto.
        + destructAll.

          inv H7.
          
          assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
          { eapply ToMSet_non_member. tci. } destructAll.
          
          set (rho'' := (M.set k1 (Vfun x8 (Fcons k1 kon_tag [x9] es' Fnil) k1) x8)).

          eapply IHoot with (rho := rho'') in H13.
          
          * destructAll.
            assert (Hoot' : bstep_fuel cenv x8 (Efun (Fcons k1 kon_tag [x9] es' Fnil) e'0) (x4 + 1)%nat OOT tt).
            { replace tt with (tt <+> tt) by reflexivity. econstructor 2. econstructor. simpl. eassumption. }
            
            edestruct H9. reflexivity. eassumption. destructAll.
            eexists. split.
            2:{ replace tt with (tt <+> tt).
                destruct x6; [ | contradiction ]. destruct x11. eassumption.
                reflexivity. } 
            
            simpl. unfold cps_bound, one, one_i in *; simpl; unfold_all.
            unfold fuel_exp. simpl. lia. 
            
          * eassumption.
          * eassumption.
          * inv Hwf'. eassumption.
          * eapply Disjoint_Included_r. eassumption.
            eapply Union_Disjoint_l.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
            xsets. 
          * eassumption.
          * intros Hc. eapply Hdis. constructor. now right.
            eapply H5.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.

    Admitted.

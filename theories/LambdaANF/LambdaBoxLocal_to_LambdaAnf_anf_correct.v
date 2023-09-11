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
    forall rho env C r x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->
      ~ x \in FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv (cps_bound f t) eq_fuel i
                               (Ehalt x, (M.set x v' (M.empty cps.val)))
                               (C|[ Ehalt x ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).


  Definition convert_anf_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat)  :=
    forall rho env C x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->
      ~ x \in FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv
                               (cps_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                          (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                               eq_fuel i
                               (Ehalt x, (M.set x v' (M.empty cps.val)))
                               (C|[ Ehalt x ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e) <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).



  Definition convert_anf_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat)  :=
    forall rho env C rs S S' vs2 x ctag,
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length env)) es ->

      Disjoint _ (FromList env) S ->

      anf_env_rel env vs rho ->

      convert_anf_rel_exps S es env cenv S' C rs ->

      Forall2 (anf_val_rel) vs1 vs2 ->

      exists rho' ys,
        set_lists ys vs2 (M.empty _) = Some rho' /\ NoDup ys /\
        forall i,
          preord_exp ctenv (cps_bound f (t <+> (2 * Datatypes.length (exps_as_list es))%nat))
                     eq_fuel i (Econstr x ctag ys (Ehalt x), rho') (C |[ Econstr x ctag rs (Ehalt x) ]|, rho).



  Lemma convert_anf_correct :
      forall vs e r f t, eval_env_fuel vs e r f t -> convert_anf_correct_exp vs e r f t.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := convert_anf_correct_exp)
                                     (P0 := convert_anf_correct_exps)
                                     (P := convert_anf_correct_exp_step).
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

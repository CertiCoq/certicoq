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
        tactics L4_to_L6 L6.tactics identifiers cps_util rename. 

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section SUBSETS.

  (** ** Subset lemmas *)
  Context (func_tag kon_tag default_tag : positive) (cnstrs : conId_map).
  

  Definition cps_cvt_exp_subset_stmt :=
    forall e e' k1 vars1 S1 S2,
      cps_cvt_rel func_tag kon_tag default_tag S1 e vars1 k1 cnstrs S2 e' ->
      S2 \subset S1.

  Definition cps_cvt_exps_subset_stmt :=
    forall e e' k1 vars1 vs S1 S2,
      cps_cvt_rel_exps func_tag kon_tag default_tag S1 e vars1 k1 vs cnstrs S2 e' ->
      S2 \subset S1.

  Definition cps_cvt_efnlst_subset_stmt :=
    forall S1 efns vars1 nlst1 S2 fdefs1,
      cps_cvt_rel_efnlst func_tag kon_tag default_tag S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
      S2 \subset S1.

  Definition cps_cvt_branches_subset_stmt :=
    forall S1 bs vars1 k1 x1 S2 bs1,
      cps_cvt_rel_branches func_tag kon_tag default_tag S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      S2 \subset S1.

  
  Definition cps_cvt_rel_subset_stmt :=
    cps_cvt_exp_subset_stmt /\
    cps_cvt_exps_subset_stmt /\
    cps_cvt_efnlst_subset_stmt /\
    cps_cvt_branches_subset_stmt.


  Lemma cps_cvt_rel_subset : cps_cvt_rel_subset_stmt. 
  Admitted.

  
  Corollary cps_cvt_exp_subset : cps_cvt_exp_subset_stmt.
  Proof. eapply (proj1 cps_cvt_rel_subset). Qed.

  Corollary cps_cvt_exps_subset : cps_cvt_exps_subset_stmt.
  Proof. eapply (proj1 (proj2 cps_cvt_rel_subset)). Qed.

  Corollary cps_cvt_efnlst_subset : cps_cvt_efnlst_subset_stmt.
  Proof. eapply (proj1 (proj2 (proj2 cps_cvt_rel_subset))). Qed.

  Corollary cps_cvt_branches_subset : cps_cvt_branches_subset_stmt.
  Proof. eapply (proj2 (proj2 (proj2 cps_cvt_rel_subset))). Qed.
  
                                                          
End SUBSETS.


Section Post.
  
  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type}
          {Htrace : @trace_resource trace}.

    Context (P1 : PostT) (* Local *)
            (PG : PostGT) (* Global *)
            (cnstrs : conId_map)
            (cenv : ctor_env)
            (Hprops : Post_properties cenv P1 P1 PG)
            (HpropsG : Post_properties cenv PG PG PG)
            (Hincl : inclusion _ (comp P1 P1) P1)
            (HinclG : inclusion _ P1 PG)
            (pr_env : M.t (kername * string * nat)).

    Context (func_tag kon_tag default_tag default_itag : positive).

    Definition cps_cvt_rel := cps_cvt_rel func_tag kon_tag default_tag.
    Definition cps_cvt_rel_exps := cps_cvt_rel_exps func_tag kon_tag default_tag.
    Definition cps_cvt_rel_efnlst := cps_cvt_rel_efnlst func_tag kon_tag default_tag.
    Definition cps_cvt_rel_branches := cps_cvt_rel_branches func_tag kon_tag default_tag.


    (** ** CPS value relation *)


    Definition cps_env_rel' (P : value -> val -> Prop) (vn : list var)
               (vs : list value) (rho : M.t val) :=
      Forall2 (fun v x => exists v',  M.get x rho = Some v' /\ P v v') vs vn.   
    

    Inductive cps_val_rel : value -> val -> Prop :=
    | rel_Con :
        forall vs vs' dc c_tag cnstrs,
          Forall2 (fun v v' => cps_val_rel v v') vs vs' ->
          dcon_to_tag default_tag dc cnstrs = c_tag ->
          cps_val_rel (Con_v dc vs) (Vconstr c_tag vs')
    | rel_Prf :
        cps_val_rel Prf_v (Vint 0)
    | rel_Clos :
        forall rho rho_m names na k x f e e' cnstrs S1 S2,
          cps_env_rel' cps_val_rel names rho rho_m ->
          (* Forall2 (fun v v' => cps_val_rel v v') rho vs -> *)
          (* set_lists names vs (M.empty val) = Some rho_m -> *)
          (* (k > List.last names (1%positive))%positive /\ (x > k)%positive *)
          (* /\ (f > x)%positive /\ (n > f)%positive -> *)
          Disjoint _ (FromList (k::x::f::nil)) S1 ->
          ~ x \in k |: [set f]->
          f <> k ->
          (* cps_cvt e names k (SG (n, nenv)) cnstrs = Some (e', next) ->  *)
          cps_cvt_rel S1 e (x :: names) k cnstrs S2 e' ->
          cps_val_rel (Clos_v rho na e)
                      (Vfun rho_m (Fcons f func_tag (x::k::nil) e' Fnil) f).

    Definition cps_env_rel : list var -> list value -> M.t val -> Prop :=
      cps_env_rel' cps_val_rel.


    Opaque preord_exp'. 

    Lemma app_cons {A} (l1 l2 : list A) a :
      l1 ++ a :: l2 =  (l1 ++ [ a ]) ++ l2.
    Proof.
      simpl. rewrite <- app_assoc. reflexivity.
    Qed.
      
      
    Lemma ctx_bind_proj_alpha_equiv_gen k S f rho1 rho2 x1 x2 ctag proj_vars1 vars1 proj_vars2 vars2 e1 e2 n :
      preord_var_env cenv PG k rho1 rho2 x1 x2 ->
      
      preord_env_P_inj cenv PG (S :|: FromList vars1) k (f <{ vars1 ~> vars2 }>) rho1 rho2 ->

      List.length proj_vars1 = List.length proj_vars2 ->
      Datatypes.length vars1 = Datatypes.length vars2 ->
                                                
      NoDup proj_vars1 ->
      NoDup proj_vars2 ->
      
      Disjoint _ (FromList proj_vars1) (FromList vars1 :|: [set x1] :|: S) ->
      Disjoint _ (FromList proj_vars2) (FromList vars2 :|: [set x2] :|: image f S) ->
                                                     
      (forall rho1' rho2' m,
          (m <= k)%nat ->
          preord_env_P_inj cenv PG (S :|: FromList (vars1 ++ proj_vars1)) m (f <{ vars1 ++ proj_vars1 ~> vars2 ++ proj_vars2 }>) rho1' rho2' ->
          preord_exp cenv P1 PG m (e1, rho1') (e2, rho2')) ->
      
      preord_exp cenv P1 PG k
                 (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
                 (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
    Proof.
      revert k S f rho1 rho2 x1 x2 ctag proj_vars2 vars1 vars2 e1 e2 n. 
      induction proj_vars1;
        intros k S f rho1 rho2 x1 x2 ctag proj_vars2 vars1 vars2 e1 e2 n Hvar Henv Hlen Hlen' Hnd1 Hnd2 Hdis1 Hdis2 Hexp;
        destruct proj_vars2; simpl in *; try congruence. 
      - eapply Hexp. lia. repeat normalize_sets. rewrite !app_nil_r. eauto.
      - simpl. inv Hnd1; inv Hnd2. 
        eapply preord_exp_proj_compat. 
        + eapply Hprops.
        + eapply Hprops.
        + eassumption.
        + repeat normalize_sets. intros. eapply IHproj_vars1 with (vars1 := vars1 ++ [ a ]) (vars2 := vars2 ++ [ v ]) (S := S).
          * eapply preord_var_env_extend_neq.
            eapply preord_var_env_monotonic. eassumption. lia.
             
            intros Hc1; subst. eapply Hdis1. now constructor; eauto.
            
            intros Hc2; subst. eapply Hdis2. now constructor; eauto.
            
            
          * rewrite !extend_lst_app; eauto. simpl. rewrite extend_extend_lst_commut with (x := a) (y := v); eauto.
            eapply preord_env_P_inj_set_alt; eauto.
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [ | eassumption ].
            lia. repeat normalize_sets. now sets.
            
            -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
               inv Hc. repeat normalize_sets. eapply Hdis2. constructor. now left.
               right. eapply image_monotonic; eauto. sets.
               
               now eapply Hdis2; sets.
               

            -- intros Hc. eapply Hdis1; sets.

            -- intros Hc. eapply Hdis2; sets.

          * congruence.

          * rewrite !app_length. simpl. congruence. 

          * congruence.
          * eassumption.
          * repeat normalize_sets. clear Hdis2.
            rewrite (Union_commut _ [set a]). rewrite <- !Union_assoc. 
            eapply Union_Disjoint_r.

            eapply Disjoint_Singleton_r. eassumption.
            eapply Disjoint_Included; [ | | eapply Hdis1 ]; sets.

          * repeat normalize_sets. clear Hdis1.
            rewrite (Union_commut _ [set v]). rewrite <- !Union_assoc. 
            eapply Union_Disjoint_r.
            
            eapply Disjoint_Singleton_r. eassumption.
            eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
            
          * intros.
            eapply preord_exp_monotonic. eapply Hexp.
            2:{ rewrite !(app_cons vars1 proj_vars1).
                rewrite !(app_cons vars2 proj_vars2). eassumption. }
            
            lia.
            lia.                 
    Qed.             


    
    Corollary ctx_bind_proj_alpha_equiv k S f rho1 rho2 x1 x2 ctag proj_vars1 proj_vars2 e1 e2 n :
      preord_var_env cenv PG k rho1 rho2 x1 x2 ->
      
      preord_env_P_inj cenv PG S k f rho1 rho2 ->

      List.length proj_vars1 = List.length proj_vars2 ->

      NoDup proj_vars1 ->
      NoDup proj_vars2 ->
      
      Disjoint _ (FromList proj_vars1) (x1 |: S) ->
      Disjoint _ (FromList proj_vars2) (x2 |: image f S) ->
                                                     
      (forall rho1' rho2' m,
          (m <= k)%nat ->
          preord_env_P_inj cenv PG (S :|: FromList proj_vars1) m (f <{ proj_vars1 ~> proj_vars2 }>) rho1' rho2' ->
          preord_exp cenv P1 PG m (e1, rho1') (e2, rho2')) ->
      
      preord_exp cenv P1 PG k
                 (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
                 (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
    Proof.
      intros.
      eapply ctx_bind_proj_alpha_equiv_gen with (vars1 := []) (vars2 := []); try eassumption; simpl; repeat normalize_sets.
      eassumption.
      reflexivity.
      sets.
      sets.
    Qed.      


    Lemma cps_cvt_rel_branches_ctor_tag S1 S2 S3 S4 bs vars1 vars2 k1 k2 x1 x2 bs1 bs2 : 
      cps_cvt_rel_branches S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      cps_cvt_rel_branches S3 bs vars2 k2 x2 cnstrs S4 bs2 ->
      Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') bs1 bs2.
    Proof.
      revert S1 S2 S3 S4 vars1 vars2 k1 k2 x1 x2 bs1 bs2.
      induction bs; intros S1 S2 S3 S4 vars1 vars2 k1 k2 x1 x2 bs1 bs2 Hrel1 Hrel2.
      
      inv Hrel1; inv Hrel2; eauto.

      inv Hrel1; inv Hrel2; eauto.
    Qed.
    
    Lemma cps_cvt_rel_efnlst_exists S1 efns vars1 nlst1 S2 B1 f1 m :
      cps_cvt_rel_efnlst S1 efns vars1 nlst1 cnstrs S2 B1 ->      
      nth_error (all_fun_name B1) m = Some f1 ->
      NoDup (all_fun_name B1) ->
      exists k1 x1 na e1 e1' S1' S2',
        enthopt m efns = Some (Lam_e na e1) /\
        find_def f1 B1 = Some (func_tag, [k1; x1], e1') /\        
        x1 \in S1 /\
               k1 \in S1 \\ [set x1] /\
                      S1' \subset S1 /\
                      cps_cvt_rel (S1' \\ (k1 |: [set x1])) e1 (x1 :: vars1) k1 cnstrs S2' e1'.
    Proof.
      intros Hrel. revert f1 m. induction Hrel; intros.
      - inv H. destruct m; inv H2.
      - simpl in H3. destruct m.
        + inv H3. do 7 eexists. split; [ | split; [ | split; [ | split; [ | split ]]]].
          * reflexivity.
          * simpl. rewrite Coqlib.peq_true. reflexivity.
          * eassumption.
          * eassumption.
          * reflexivity.
          * eassumption.
        + edestruct IHHrel; eauto. inv H4. eassumption. destructAll.
          do 7 eexists. split; [ | split; [ | split; [ | split; [ | split ]]]]; [ | | | | |  eassumption ].
          * eassumption.
          * simpl. rewrite Coqlib.peq_false. eassumption.
            inv H4. simpl in H3. intros Hc; subst. eapply H13.
            eapply nth_error_In. eassumption. 
          * eapply cps_cvt_exp_subset in H2. eapply H2. eassumption.
          * inv H8. constructor; eauto.
            eapply cps_cvt_exp_subset in H2. eapply H2. eassumption.
          * eapply cps_cvt_exp_subset in H2.
            eapply Included_trans; eauto.
            eapply Included_trans; eauto. now sets.
    Qed.            
      
        
    
    (** ** Alpha-equivalence statements *)
    
     Definition cps_cvt_exp_alpha_equiv k :=
       forall e e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
         (m <= k)%nat -> 
        cps_cvt_rel S1 e vars1 k1 cnstrs S2 e1 ->
        cps_cvt_rel S3 e vars2 k2 cnstrs S4 e2 ->
        NoDup vars1 -> (* TODO is this needed? *)
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1) m
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG m (e1, rho1) (e2, rho2).

    Definition cps_cvt_exps_alpha_equiv k :=
      forall es es1 es2 m k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_exps S1 es vars1 k1 xs1 cnstrs S2 es1 ->
        cps_cvt_rel_exps S3 es vars2 k2 xs2 cnstrs S4 es2 ->

        NoDup vars1 ->
        NoDup xs1 ->

        ~(k1 \in (FromList vars1 :|: FromList xs1)) ->
        Disjoint _ (FromList vars1) (FromList xs1) -> (* TODO check if indeed needed *)

        List.length vars1 = List.length vars2 ->
        List.length xs1 = List.length xs2 ->
        
        Disjoint _ (k1 |: FromList vars1 :|: FromList xs1) S1 ->
        Disjoint _ (k2 |: FromList vars2 :|: FromList xs2) S3 ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1 :|: FromList xs1) m
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }> <{ rev xs1 ~> rev xs2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG m (es1, rho1) (es2, rho2). 

    Definition cps_cvt_efnlst_alpha_equiv k :=
      forall efns fdefs1 fdefs2 m k1 k2 vars1 vars2 vars1' vars2' nlst1 nlst2 rho1 rho2
             S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_efnlst S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
        cps_cvt_rel_efnlst S3 efns vars2 nlst2 cnstrs S4 fdefs2 ->

        vars1 = nlst1 ++ vars1' ->
        vars2 = nlst2 ++ vars2' ->
        
        NoDup vars1 ->
        NoDup (all_fun_name fdefs1) ->
        NoDup (all_fun_name fdefs2) ->

        List.length vars1' = List.length vars2' ->
        List.length (all_fun_name fdefs1) = List.length (all_fun_name fdefs2) ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->

        Disjoint var (k2 |: FromList vars2') (name_in_fundefs fdefs2) -> 
                
        preord_env_P_inj cenv PG (k1 |: FromList vars1') m
                         (id {k1 ~> k2 } <{ vars1' ~> vars2' }>) rho1 rho2 ->
        preord_env_P_inj cenv PG (k1 |: (FromList vars1 :|: FromList nlst1)) m
                         (id {k1 ~> k2 } <{ vars1' ~> vars2' }> <{ all_fun_name fdefs1 ~> all_fun_name fdefs2 }>)
                         (def_funs fdefs1 fdefs1 rho1 rho1)
                         (def_funs fdefs2 fdefs2 rho2 rho2).

        (* preord_val cenv PG k (Vfun rho1 fdefs1 f1) (Vfun rho2 fdefs2 f2). *)

    
    Definition cps_cvt_branches_alpha_equiv (k : nat) :=
      forall bs bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
             S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_branches S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
        cps_cvt_rel_branches S3 bs vars2 k2 x2 cnstrs S4 bs2 ->        
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->        
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: [set x1] :|: FromList vars1) S1 ->       
        Disjoint _ (k2 |: [set x2] :|: FromList vars2) S3 ->
        
        preord_env_P_inj cenv PG (k1 |: FromList vars1) m
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->        
        preord_var_env cenv PG m rho1 rho2 x1 x2 ->
        preord_exp cenv P1 PG m (Ecase x1 bs1, rho1)  (Ecase x2 bs2, rho2).

    
    Definition cps_cvt_alpha_equiv_statement k :=
      cps_cvt_exp_alpha_equiv k /\
      cps_cvt_exps_alpha_equiv k /\
      cps_cvt_efnlst_alpha_equiv k /\
      cps_cvt_branches_alpha_equiv k.

    
    Definition cps_cvt_val_alpha_equiv_statement k :=
      forall v v1 v2,
        cps_val_rel v v1 ->
        cps_val_rel v v2 ->
        preord_val cenv PG k v1 v2.     
    
    
    Lemma cps_cvt_rel_efnlst_name_in_fundes S1 na vars nlst S2 B : 
      cps_cvt_rel_efnlst S1 na vars nlst cnstrs S2 B ->
      name_in_fundefs B <--> FromList nlst.
    Proof.
      intros H. induction H.
      - normalize_sets. simpl. sets. 
      - simpl. normalize_sets. sets.
    Qed.


    Lemma cps_cvt_rel_efnlst_all_fun_name S1 na vars nlst S2 B : 
      cps_cvt_rel_efnlst S1 na vars nlst cnstrs S2 B ->
      all_fun_name B = nlst.
    Proof.
      intros H. induction H.
      - reflexivity.
      - simpl. congruence.
    Qed.

    Fixpoint in_efnlist (n : name) (e : expression.exp) (efns : efnlst) :=
      match efns with
      | eflnil => False
      | eflcons n' e' efns =>
        n = n' /\ e = e' \/ in_efnlist n e efns
      end.
    

    Lemma extend_lst_nth_error {A} f l (l' : list A) x n :
      NoDup l ->
      nth_error l n = Some x ->
      List.length l = List.length l' ->    
      exists x', f <{ l ~> l' }> x = x' /\ nth_error l' n = Some x'.
    Proof.
      revert n l'; induction l; intros n l' Hnd Hnin Hlen; simpl; eauto.
      - destruct n; inv Hnin.
      - destruct l'; try discriminate. inv Hlen.
        destruct n; simpl in Hnin.
        + inv Hnin. rewrite extend_gss.
          eexists; split; eauto.
        + inv Hnd. rewrite extend_gso; eauto. edestruct IHl as [x' [Heq HIn]]; eauto.
          intros Hc. subst. eapply H2. eapply nth_error_In. eassumption. 
    Qed.

    Lemma preord_env_P_inj_def_funs_Vfun S k f B1 B2 B1' B2' rho1 rho2 : 
      preord_env_P_inj cenv PG (S \\ name_in_fundefs B1) k f rho1 rho2 ->
      
      List.length (all_fun_name B1) = List.length (all_fun_name B2) ->
      NoDup (all_fun_name B1) ->
      Disjoint _ (image f (S \\ name_in_fundefs B1)) (name_in_fundefs B2) ->
      
      (forall n f1 f2,
          nth_error (all_fun_name B1) n = Some f1 ->
          nth_error (all_fun_name B2) n = Some f2 ->
          preord_val cenv PG k (Vfun rho1 B1' f1) (Vfun rho2 B2' f2)) ->
          
      preord_env_P_inj cenv PG S k (f <{ all_fun_name B1 ~> all_fun_name B2 }>) (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2).
    Proof.
      intros Henv Hlen Hnd Hdis Hrel x Hin v Hget.
      destruct (Decidable_name_in_fundefs B1). destruct (Dec x).
      
      - edestruct In_nth_error. eapply Same_set_all_fun_name. eassumption.
        edestruct (@extend_lst_nth_error var); try eassumption. destructAll.

        eexists. rewrite def_funs_eq in *; eauto. split. reflexivity.
        inv Hget. eapply Hrel.
        eassumption. eassumption.

        eapply Same_set_all_fun_name. eapply nth_error_In. eassumption.

      - rewrite extend_lst_gso. rewrite def_funs_neq in *; eauto. 
        
        eapply Henv. now constructor. eassumption.

        intros Hc. eapply Hdis. constructor; eauto.
        eapply In_image. now constructor; auto.
        
        rewrite <- Same_set_all_fun_name. eassumption.
    Qed.      
    
    (* TODO move *)

    Lemma exp_ind_alt : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop),
        (forall n : N, P (Var_e n)) ->
        (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) ->
        (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) ->
        (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) ->
        (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) ->
        (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) ->
        (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) ->
        P Prf_e ->
        (forall p : positive, P (Prim_e p)) ->
        P0 enil ->
        (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) ->
        P1 eflnil ->
        (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) ->              
        P2 brnil_e ->
        (forall (d : dcon) (p : N * list name) (e : expression.exp),
            P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) ->
        (forall e : expression.exp, P e) /\
        (forall e : exps, P0 e) /\
        (forall e : efnlst, P1 e) /\ (forall b : branches_e, P2 b).
    Proof.
      intros. eapply my_exp_ind; eauto.
      intros. eapply H11. now left. eassumption.
    Qed. 
      
    
    Lemma FromList_rev {A} (l : list A) :
      FromList (rev l) <--> FromList l.
    Proof.
      induction l.
      - reflexivity.
      - simpl. repeat normalize_sets. sets.
    Qed.
    
    
    Lemma cps_cvt_alpha_equiv :
      forall k, cps_cvt_alpha_equiv_statement k.
    Proof.
      induction k using lt_wf_rec. 
      eapply exp_ind_alt.
      - (* Var_e *)
        intros n e1 e2 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1. inv He2.
        eapply preord_exp_app_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
          { rewrite extend_lst_gso.
            rewrite extend_gss. reflexivity.
            eassumption. }
          rewrite Heq.
          eapply Henv. left. reflexivity.
        + econstructor; [ | now econstructor ].
          * assert (Heq: ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) v = v0). 
            { eapply extend_lst_get_nth_error; eauto. }
            rewrite <- Heq. eapply Henv. right.
            eapply nth_FromList. eassumption.

      - (* Lam_e *)
        intros na e IH e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        simpl in He1, He2. inv He1; inv He2.  
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic.
            simpl. eapply preord_exp_app_compat.
            - eapply Hprops. (* invariants *)
            - eapply Hprops. (* invariants *)
            - assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
              { rewrite extend_lst_gso. rewrite extend_gss. reflexivity.
                eassumption. }
              rewrite Heq.
              inv H3; inv H5. inv H6; inv H8. 
              
              eapply preord_env_P_inj_set_not_In_P_l.
              eapply preord_env_P_inj_set_not_In_P_r.
              eassumption.

              3:{ now left. }
              2:{ intros Hc. eapply Hdis1. constructor; [ | eapply H0 ]. eassumption. }
              
              intros Him. eapply image_extend_lst_Included in Him; eauto.
              rewrite image_extend_In_S in Him; eauto.
              
              assert (Hseq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set _) by sets.

              rewrite Hseq, image_Empty_set in Him. repeat normalize_sets.
              now eapply Hdis2; sets.

              rewrite Setminus_Union_distr. left. rewrite Setminus_Disjoint. reflexivity.
              sets.

            - econstructor. 2: { econstructor. }
              simpl. unfold preord_var_env.
              intros v5 Hset.
              rewrite M.gss in Hset. inv Hset.
              eexists. split.
              rewrite M.gss. reflexivity. eapply preord_val_fun.
              simpl. rewrite Coqlib.peq_true. reflexivity.
              simpl. rewrite Coqlib.peq_true. reflexivity.

              intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inv H1. eexists. split. reflexivity.

              intros Hlt' Hall. 
              
              eapply preord_exp_post_monotonic. now eapply HinclG.
              eapply preord_exp_monotonic.
              edestruct (H j) as [ Hexp _ _ _   ]. lia.
              eapply Hexp.
              + reflexivity.
              + eassumption.
              + eassumption.
              + constructor. intros Hc. eapply Hdis1. now sets. eassumption.
              + repeat normalize_sets. inv H5. intros Hc. inv Hc.
                * inv H5. eauto.
                * eapply Hdis1. now sets.
              + simpl. congruence.
              + repeat normalize_sets. xsets. (* ^^ yay sets *)
              + repeat normalize_sets. xsets. (* ^^ yay sets *)
              + repeat normalize_sets. simpl.
                assert (Hfeq : f_eq (((id {k3 ~> k4}) <{ vars1 ~> vars2 }>) {x1 ~> x0})
                                    (((id <{ vars1 ~> vars2 }>) {x1 ~> x0}) {k3 ~> k4})).
                { rewrite extend_extend_lst_commut; eauto.
                  rewrite extend_commut; eauto. reflexivity. 
                  - inv H5. intros Hc. subst. eauto.
                  - inv H8. intros Hc. subst. eauto.
                  - inv H5. intros Hc. eapply Hdis1. sets.
                  - inv H8. intros Hc. eapply Hdis2. sets. }
                
                rewrite Hfeq.

                inv Hall. inv H13. clear H16.

                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.

                eapply preord_env_P_inj_f_eq_subdomain.

                eapply preord_env_P_inj_antimon.
                eapply preord_env_P_inj_monotonic.
                2: { eassumption. } omega.
                now xsets.

                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. (* TODO add to normalize_sets *)
                repeat normalize_sets.
                rewrite Setminus_Union, (Union_commut [set k3]), <- Setminus_Union.
                rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                eapply f_eq_subdomain_extend_lst.
                eassumption.

                eapply f_eq_subdomain_extend_not_In_S_l; [ | reflexivity ].

                * intros Hc. inv Hc. inv H1. inv H9. eauto.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  rewrite image_id in Hc. inv Hc. inv H1. inv H7. inv H1.
                  inv H7; eauto.  inv H1; eauto.
                  inv H6. eapply Hdis2. now sets. eassumption.

                * intros Hc. inv Hc. inv H1. inv H9; eauto. inv H1; eauto.
                  inv H3. eapply Hdis1. now sets.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  rewrite image_id in Hc. inv Hc. inv H1. inv H7. inv H1.
                  inv H7; eauto.  inv H1; eauto.
                  inv H6. eapply Hdis2. now sets. eassumption.

                * intros Hc. inv Hc. inv H1. inv H7; eauto. inv H1; eauto.
                  inv H7; eauto.
                  
                  inv H1. rewrite extend_gss in H8. inv H8. now eauto. 

                  rewrite extend_gso in H8.
                  2:{ intros Hc; subst. rewrite extend_gss in H8. inv H8. now eauto. }
                  edestruct (@extend_lst_gss var). eassumption. eassumption. inv H7.
                  eapply Hdis2. constructor. right. eassumption. inv H8. eassumption.


              + lia.
                
            - lia. }
          
      - (* App_e *)
        intros e1 IHe1 e2 IHe2 e1' e2' m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1. inv He2.  
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IHe1; try eassumption.
            - inv H3. intros Hc. eapply Hdis1. sets.
            - sets.
            - sets.
            - simpl.
              assert (Hfeq : f_eq ((id {k3 ~> k5}) <{ vars1 ~> vars2 }>)
                                  ((id <{ vars1 ~> vars2 }>) {k3 ~> k5})). 
              { rewrite extend_extend_lst_commut; eauto. reflexivity. 
                - inv H3. intros Hc. eapply Hdis1. sets.
                - inv H8. intros Hc. eapply Hdis2. sets. }

              rewrite Hfeq.

              eapply preord_env_P_inj_set_alt; eauto.

              + eapply preord_env_P_inj_f_eq_subdomain.
                eapply preord_env_P_inj_antimon. eassumption.
                now sets.
                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                eapply f_eq_subdomain_extend_lst. eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l.
                
                intros Hc. inv Hc. now inv H0.
                reflexivity.

              + eapply preord_val_fun.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                
                intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                inv H1. eexists. split. reflexivity.
                
                intros Hlt' Hall. simpl.
                { eapply preord_exp_fun_compat.

                  + eapply HpropsG. (* invariants *)
                  + eapply HpropsG. (* invariants *)
                  + { destruct H with (m := (j - 1)%nat) as [ IHe _]. omega.
                      eapply preord_exp_post_monotonic. eapply HinclG.
                      eapply IHe; try eassumption.
                      - lia.
                      - inv H5. eapply cps_cvt_exp_subset in H1; [ | eassumption ].
                        inv H1. intros Hc. eapply Hdis1; eauto.
                      - eapply Union_Disjoint_l; sets.
                        eapply Disjoint_Included_r.
                        eapply Included_trans. eapply Setminus_Included.
                        eapply cps_cvt_exp_subset. eassumption.
                        sets.
                      - eapply Union_Disjoint_l; sets.
                        eapply Disjoint_Included_r.
                        eapply Included_trans. eapply Setminus_Included.
                        eapply cps_cvt_exp_subset. eassumption.
                        sets.
                      - simpl.
                        assert (Hfeq' : f_eq ((id {k4 ~> k6}) <{ vars1 ~> vars2 }>)
                                            ((id <{ vars1 ~> vars2 }>) {k4 ~> k6})). 
                        { rewrite extend_extend_lst_commut; eauto. reflexivity. 
                          - inv H5. eapply cps_cvt_exp_subset in H1; [ | eassumption ].
                            inv H1. intros Hc. eapply Hdis1; eauto.
                          - inv H10. eapply cps_cvt_exp_subset in H1; [ | eassumption ].
                            inv H1. intros Hc. eapply Hdis2; eauto. } 

                        rewrite Hfeq'. eapply preord_env_P_inj_set_alt; eauto.
                        
                        + rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                          normalize_sets.
                          eapply preord_env_P_inj_set_not_In_P_l.
                          eapply preord_env_P_inj_set_not_In_P_r.
                          eapply preord_env_P_inj_set_not_In_P_l.
                          eapply preord_env_P_inj_set_not_In_P_r.

                          eapply preord_env_P_inj_f_eq_subdomain.
                          eapply preord_env_P_inj_antimon.
                          eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                          now sets.
                          eapply f_eq_subdomain_extend_lst. eassumption.
                          eapply f_eq_subdomain_extend_not_In_S_l; [ | reflexivity ].

                          * intros Hc. inv Hc. now inv H1.
                          * inv H8. intros Hc.  eapply image_extend_lst_Included in Hc.
                            rewrite image_id in Hc. inv Hc.
                            inv H8. now inv H14.
                            eapply Hdis2. now sets. eassumption.
                          * inv H3. intros Hc. inv Hc. eapply Hdis1. sets.
                          * inv H5. intros Hc.
                            eapply image_extend_lst_Included in Hc. rewrite image_id in Hc. inv Hc.
                            inv H5. now inv H14; eauto.
                            eapply Hdis2. constructor. now right. eassumption. eassumption.
                          * intros Hc. inv Hc. eapply Hdis1. sets.
                            
                        + eapply preord_val_fun.
                          simpl. rewrite Coqlib.peq_true. reflexivity.
                          simpl. rewrite Coqlib.peq_true. reflexivity.
                          
                          intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          inv H1. eexists. split. reflexivity.
                          
                          intros Hlt'' Hall'. simpl.
                          { eapply preord_exp_app_compat.
                            - eapply HpropsG. (* invariants *)
                            - eapply HpropsG. (* invariants *)
                            - inv H11. eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_eq.
                              inv Hall. eapply preord_val_monotonic. eassumption. lia.

                              + intros Hc1; subst. inv H5. eapply cps_cvt_exp_subset in H1; [ | eassumption ].
                                inv H1. eauto.

                              + intros Hc1; subst. inv H10. eapply cps_cvt_exp_subset in H1; [ | eassumption ].
                                inv H1. eauto.

                              + intros Hc1; subst. eapply cps_cvt_exp_subset in H4; [ | eassumption ].
                                inv H4. eauto.
                                
                              + intros Hc1; subst. eapply cps_cvt_exp_subset in H9; [ | eassumption ].
                                inv H9. eauto.

                            - inv H11. constructor; [ | constructor; eauto ].
                              + eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_monotonic.
                                assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
                                { rewrite extend_lst_gso. rewrite extend_gss. reflexivity.
                                  eassumption. }
                                rewrite Heq. eapply Henv. now left. lia.

                                * intros Hc; subst. inv H3. eapply Hdis1; eauto.
                                * intros Hc; subst. inv H8. eapply Hdis2; eauto.
                                * intros Hc; subst. eapply Hdis1; eauto.
                                * intros Hc; subst. eapply Hdis2; eauto.
                                * intros Hc; subst. inv H5. eapply cps_cvt_exp_subset in H1; [ | eassumption ]. inv H1. 
                                  eapply Hdis1; eauto.
                                * intros Hc; subst. inv H10. eapply cps_cvt_exp_subset in H1; [ | eassumption ]. inv H1. 
                                  eapply Hdis2; eauto.
                                * intros Hc; subst. eapply cps_cvt_exp_subset in H4; [ | eassumption ]. inv H4. 
                                  eapply Hdis1; eauto.
                                * intros Hc; subst. eapply cps_cvt_exp_subset in H9; [ | eassumption ]. inv H9. 
                                  eapply Hdis2; eauto.
                                  
                              + eapply preord_var_env_extend_eq.
                                inv Hall'. eassumption. } 
                          
                        + intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc. inv Hc.
                          inv H1. inv H11; eauto. now inv H1.
                          inv H10. eapply cps_cvt_exp_subset in H11; [ | eassumption ]. inv H11.
                          eapply Hdis2; eauto.  } } 
              + intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc. inv Hc.
                inv H0. inv H1; eauto. now inv H0.
                inv H8. eapply Hdis2; eauto.
            - lia. }
          
      - (* Con_e *)
        intros dc es IH e1 e2 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hltm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2. 
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IH; try eassumption.
            - now constructor.              
            - repeat normalize_sets. inv H4. intros Hc. eapply Hdis1. xsets.
            - repeat normalize_sets. xsets .
            - reflexivity. 
            - repeat normalize_sets. xsets.
            - repeat normalize_sets. xsets.
              
            - simpl. 
              assert (Hfeq : f_eq ((id {k3 ~> k4}) <{ vars1 ~> vars2 }>)
                                  ((id <{ vars1 ~> vars2 }>) {k3 ~> k4})). 
              { rewrite extend_extend_lst_commut; eauto. reflexivity. 
                - inv H4. intros Hc. eapply Hdis1. sets.
                - inv H9. intros Hc. eapply Hdis2. sets. }
              
              rewrite Hfeq.
              
              eapply preord_env_P_inj_set_alt; eauto.
              
              + eapply preord_env_P_inj_f_eq_subdomain.                
                eapply preord_env_P_inj_antimon. eassumption.
                repeat normalize_sets. now sets.
                
                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                eapply f_eq_subdomain_extend_lst. eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l.
                
                intros Hc. inv Hc. repeat normalize_sets. now inv H0. reflexivity.

              + eapply preord_val_fun.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                
                intros. 

                edestruct set_lists_length2 with
                    (rho1 := rho1')
                    (rho' := def_funs
                               (Fcons k4 kon_tag vx0 (Econstr x0 (dcon_to_tag default_tag dc cnstrs) vx0 (Eapp k2 kon_tag [x0])) Fnil)
                               (Fcons k4 kon_tag vx0 (Econstr x0 (dcon_to_tag default_tag dc cnstrs) vx0 (Eapp k2 kon_tag [x0])) Fnil)
                               rho2 rho2); [ | | now eauto | ].
                rewrite H6. rewrite H11 . reflexivity. eassumption. 
                
                eexists. split. now eauto. 

                intros Hlt2 Hall.
                { eapply preord_exp_constr_compat.
                  - eapply HpropsG.
                  - eapply HpropsG.
                  - rewrite <- map_extend_lst_same with (xs := vx) (xs' := vx0)
                                                        (f := id).
                    eapply Forall2_preord_var_env_map.
                    2: { reflexivity. }
                    eapply preord_env_P_inj_set_lists_alt.
                    rewrite Setminus_Same_set_Empty_set.
                    intros x' Hin. now inv Hin.
                    eassumption.
                    eassumption. eassumption.
                    congruence.
                    rewrite Setminus_Same_set_Empty_set, image_id. now sets.
                    now eauto. now eauto.
                    eassumption.
                    replace (@Datatypes.length positive vx) with (@Datatypes.length var vx) by reflexivity.
                    congruence.

                  - intros i vs vs' Hlt Hall1.
                    eapply preord_exp_app_compat.
                    + eapply HpropsG.
                    + eapply HpropsG.
                    + assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
                      { rewrite extend_lst_gso.
                        rewrite extend_gss. reflexivity.
                        eassumption. }
                      rewrite Heq.
                      eapply preord_env_P_inj_set_not_In_P_l.
                      eapply preord_env_P_inj_set_not_In_P_r.
                      eapply preord_env_P_inj_set_lists_l_Disjoint.
                      2: { now eauto. }
                      eapply preord_env_P_inj_set_lists_r_Disjoint.
                      2: { eassumption. }
                      eapply preord_env_P_inj_set_not_In_P_l.
                      eapply preord_env_P_inj_set_not_In_P_r.
                      eapply preord_env_P_inj_monotonic.
                      2 : { eassumption. }
                      lia.

                      * intros Hc. eapply image_extend_lst_Included in Hc.
                        inv Hc.
                        
                        eapply image_extend_Included' in H12. 
                        rewrite image_id in H12.

                        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set in H12.
                        repeat normalize_sets.
                        rewrite Setminus_Union, (Union_commut (FromList vars1)), <- Setminus_Union, Setminus_Same_set_Empty_set in H12.
                        repeat normalize_sets. 
                        inv H12. inv H9. eapply Hdis2. now sets.
                        inv H9. eapply Hdis2. now sets.
                        eassumption.

                      * intros Hc. inv Hc. inv H11.
                        inv H4. eapply Hdis1. now sets.
                        inv H4. eapply Hdis1. now sets.

                      * eapply Disjoint_Included_r.
                        eapply image_extend_lst_Included. eassumption.
                        eapply Union_Disjoint_r; sets.
                        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
                        repeat normalize_sets.
                        eapply Disjoint_Included_r.
                        eapply image_monotonic. eapply Setminus_Included.
                        eapply Disjoint_Included_r.
                        eapply image_extend_Included'.
                        eapply Union_Disjoint_r.
                        rewrite image_id.
                        rewrite Setminus_Same_set_Empty_set. now sets.

                        eapply Disjoint_Singleton_r. intros Hc. eapply H10 in Hc.
                        inv Hc. now eapply Hdis2; eauto.
                        
                        eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis2 ].
                        eapply Included_trans; sets. sets.

                      * eapply Union_Disjoint_r.
                        eapply Disjoint_Singleton_r. intros Hc. eapply H5 in Hc.
                        inv Hc. now eapply Hdis1; eauto.
                        
                        eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis1 ].
                        eapply Included_trans; sets. sets.

                      * intros Hc.
                        eapply image_extend_lst_Included in Hc. inv Hc.
                        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set in H12.
                        repeat normalize_sets.
                        eapply image_extend_Included' in H12. rewrite  image_id in H12.
                        inv H12. inv H15. inv H12. now eauto.
                        inv H15. eapply Hdis2. now sets.
                        eapply Hdis2. now sets.
                        eassumption.

                      * intros Hc. inv Hc. inv H12. 
                        eapply Hdis1; now sets.
                        eapply Hdis1; now sets.

                      * now left.

                    + constructor; [ | now eauto ].
                      eapply preord_var_env_extend_eq.
                      rewrite preord_val_eq. simpl.
                      split. reflexivity. eassumption. }

              + repeat normalize_sets. rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set. normalize_sets. 
                intros Hc. eapply image_extend_lst_Included in Hc.
                inv Hc.

                rewrite image_id in H0. inv H0. now inv H1.

                inv H9. eapply Hdis2. constructor; now eauto. eassumption.

            - omega. }
          
      - (* Match_e *)
        intros e IHe pars bs IHbs e1 e3 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hltm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eapply preord_exp_monotonic.
          eapply IHe; try eassumption.
          * inv H5. intros Hc. eapply Hdis1. sets.
          * sets.
          * sets.
          * simpl. rewrite extend_extend_lst_commut.
            eapply preord_env_P_inj_set_alt.
            rewrite Setminus_Union_distr.
            rewrite Setminus_Same_set_Empty_set. normalize_sets.
            rewrite Setminus_Disjoint.
            eapply preord_env_P_inj_f_eq_subdomain.
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic.
            reflexivity.
            eassumption.
            sets.

            eapply f_eq_subdomain_extend_lst. eassumption.
            rewrite Setminus_Same_set_Empty_set.
            intros x Hx. now inv Hx.
            inv H5. eapply Disjoint_Included_r.
            eapply Singleton_Included. eassumption. sets.

            { eapply preord_val_fun.
              simpl.
              simpl. rewrite Coqlib.peq_true. reflexivity.
              simpl. rewrite Coqlib.peq_true. reflexivity.

              intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inv H1. eexists. split. reflexivity.
              
              intros Hlt Hall. 
              
              eapply preord_exp_monotonic.
              eapply preord_exp_post_monotonic. eapply HinclG. 
              edestruct (H j) as (_ & _ & _ & Hexp ). lia.
              eapply Hexp; try eassumption.
              + reflexivity.
              + eapply Disjoint_Included_r.
                eapply cps_cvt_exp_subset. eassumption. xsets. 
              + eapply Disjoint_Included_r.
                eapply cps_cvt_exp_subset. eassumption. xsets. 
              + eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_monotonic.
                2: { eassumption. } lia.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.
                  
                  eapply image_extend_Included' in H1. 
                  rewrite image_id in H1.

                  assert (Heq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set  _) by now sets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  inv H7. eapply Hdis2. now sets.
                  inv H7. eapply Hdis2. now sets.
                  eassumption.

                * intros Hc.
                  inv H5. eapply Hdis1. now sets.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.
                  
                  eapply image_extend_Included' in H1. 
                  rewrite image_id in H1.

                  assert (Heq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set  _) by now sets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  inv H7. eapply Hdis2. now sets.
                  inv H7. eapply Hdis2. now sets.
                  eassumption.

                * intros Hc.
                  inv H5. eapply Hdis1. now sets.

              + eapply preord_var_env_extend_eq. inv Hall. eassumption.

              + omega. }

            rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
            repeat normalize_sets.
            intros Hc. eapply image_extend_lst_Included in Hc.
            inv Hc.
            
            assert (Heq : (FromList vars1 \\ [set k3] \\ FromList vars1) <--> Empty_set  _) by now sets.
            rewrite Heq, image_id in H0. now inv H0.
            inv H7. eapply Hdis2. now sets. eassumption.

            intros Hin. inv H5. eapply Hdis1. now sets.

            intros Hin. inv H7. eapply Hdis2. now sets.
            eassumption.

          * lia.
            
      - (* Let_e *)
        intros na e1 IHe1 e2 IHe2 m e1' e2' k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IHe1; try eassumption.
            - inv H5. intros Hc. eapply Hdis1. sets.
            - eapply Disjoint_Included_r.
              eapply cps_cvt_exp_subset. eassumption.
              sets. 
            - eapply Disjoint_Included_r.
              eapply cps_cvt_exp_subset. eassumption.
              sets. 
            - simpl.
              assert (Hfeq : f_eq ((id {k3 ~> k4}) <{ vars1 ~> vars2 }>)
                                  ((id <{ vars1 ~> vars2 }>) {k3 ~> k4})). 
              { rewrite extend_extend_lst_commut; eauto. reflexivity. 
                - inv H5. intros Hc. eapply Hdis1. sets.
                - inv H7. intros Hc. eapply Hdis2. sets. }
              
              rewrite Hfeq.

              eapply preord_env_P_inj_set_alt; eauto.
              
              + eapply preord_env_P_inj_f_eq_subdomain.                
                eapply preord_env_P_inj_antimon. eassumption.
                now sets.
                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                eapply f_eq_subdomain_extend_lst. eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l.
                
                intros Hc. inv Hc. now inv H0.
                reflexivity.
                
              + eapply preord_val_fun.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                simpl. rewrite Coqlib.peq_true. reflexivity.

                intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                inv H1. eexists. split. reflexivity.

                intros Hlt Hall.
                edestruct (H j) as [Hexp _]. lia.
                eapply preord_exp_post_monotonic. eapply HinclG. 
                eapply Hexp; try eassumption.
                lia.
                constructor; try eassumption.
                intros Hc. eapply Hdis1; now sets.

                repeat normalize_sets. intros Hc.
                inv Hc. inv H1. eapply Hdis1. now sets.
                eapply Hdis1. now sets.
                simpl. congruence.

                repeat normalize_sets. now xsets.
                repeat normalize_sets. now xsets.
                
                simpl. repeat normalize_sets.
                
                
                eapply preord_env_P_inj_set_alt; eauto.
                
                * rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                  repeat normalize_sets.
                  eapply preord_env_P_inj_set_not_In_P_l.
                  eapply preord_env_P_inj_set_not_In_P_r.
                  
                  eapply preord_env_P_inj_antimon.
                  eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                  now sets.

                  ** intros Hc. eapply image_extend_lst_Included in Hc.
                     inv Hc.
                     eapply image_extend_Included' in H1.
                     rewrite image_id in H1.
                     assert (Heq: [set k1] \\ [set x1] :|: (FromList vars1 \\ [set x1]) \\ FromList vars1 \\ [set k1] <--> Empty_set _) by sets.

                     rewrite Heq in H1. repeat normalize_sets. inv H1.
                     inv H7. eapply Hdis2. now sets.
                     inv H7. eapply Hdis2. now sets.
                     eassumption.

                  ** rewrite <- Setminus_Union_distr. intros Hc. inv Hc.
                     inv H5. eapply Hdis1; eauto.

                * inv Hall. eassumption.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.
                  eapply image_extend_Included' in H1.
                  rewrite image_id in H1.
                  assert (Heq: k1 |: (x1 |: FromList vars1) \\ [set x1] \\ FromList vars1 \\ [set k1] <--> Empty_set _) by xsets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  eapply Hdis2. now sets.
                  eapply Hdis2. now sets.
                  eassumption.

              + rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                intros Hc. eapply image_extend_lst_Included in Hc.
                inv Hc.
                rewrite image_id in H0. inv H0. inv H1. now eauto.

                inv H7. eapply Hdis2. now sets. eassumption.

            - lia. }
          
          
      - (* Fix_e *)
        intros e IH na e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        simpl in He1, He2. inv He1; inv He2.  
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { simpl. eapply preord_exp_app_compat. 
            - eapply Hprops. (* invariants *)
            - eapply Hprops. (* invariants *)
            - eapply preord_var_env_monotonic.

              eapply preord_var_env_def_funs_not_In_l.

              rewrite cps_cvt_rel_efnlst_name_in_fundes; [ | eassumption ].
              intros Hin. eapply Hdis1. now constructor; eauto.

              eapply preord_var_env_def_funs_not_In_r.

              rewrite cps_cvt_rel_efnlst_name_in_fundes; [ | eassumption ].
              intros Hin. eapply Hdis2. now constructor; eauto.

              assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
              { rewrite extend_lst_gso. rewrite extend_gss. reflexivity. eassumption. }
              rewrite Heq.
              eapply Henv. now left. lia.

            - set (Heq1 := cps_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ H6).
              set (Heq2 := cps_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ H10). 
              constructor; eauto.

              eapply preord_env_P_inj_def_funs.
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.
              congruence.
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.

              2:{ eapply preord_env_P_inj_monotonic with (k0 := m). lia. 
                  eapply IH; try eassumption. reflexivity. reflexivity.
                  
                  - eapply NoDup_app; eauto.
                    eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis1 ]; now sets.

                  - rewrite Heq1. eassumption.
                  - rewrite Heq2. eassumption.

                  - congruence.
                    
                  - normalize_sets. now xsets.
                    
                  - normalize_sets. now xsets.
                    
                  - rewrite Same_set_all_fun_name. rewrite Heq2. now xsets.

              } 
              
              + normalize_sets.
                rewrite cps_cvt_rel_efnlst_name_in_fundes; eauto. now sets. }
          
      - (* Prf_e *)
        intros e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.

      - (* Prim_e *)
        intros p e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2. 
        (* TODO add Prim_e to relation ? *)
        
      - (* enil *)
        intros es1 es2 m k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Hdup Hdup' Hnot Hdis Hlen Hlen' Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_app_compat; simpl.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }> <{ rev xs1 ~> rev xs2 }>) k1).
          { rewrite extend_lst_gso. rewrite extend_lst_gso.
            rewrite extend_gss. reflexivity. now eauto. rewrite FromList_rev. eauto. } 
          rewrite Heq. eapply Henv. now left.
        + assert
            (Heq : rev xs2  = map (((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) <{ rev xs1 ~> rev xs2 }>) (rev xs1)).
          { rewrite map_extend_lst_same. reflexivity.
            eapply NoDup_rev. eassumption.
            rewrite !rev_length. eassumption. }
          
          rewrite Heq.
          eapply Forall2_preord_var_env_map. eassumption.
          rewrite FromList_rev. sets.

      - (* econs *)
        intros e IHe es IHes e1 e2 m k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Hdup Hdup' Hnot Hdis Hlen Hlen' Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { simpl. eapply preord_exp_monotonic.
            eapply IHe; try eassumption.
            - inv H3. intros Hc. eapply Hdis1. sets.
            - xsets. 
            - xsets.
            - simpl. rewrite extend_extend_lst_commut; eauto.
              + eapply preord_env_P_inj_set_alt.
                * rewrite Setminus_Union_distr.
                  rewrite Setminus_Same_set_Empty_set. normalize_sets.
                  eapply preord_env_P_inj_f_eq_subdomain.
                  eapply preord_env_P_inj_antimon.
                  eapply preord_env_P_inj_monotonic.
                  reflexivity. eassumption. now sets.
                  
                  rewrite f_eq_subdomain_extend_lst_Disjoint. 
                  eapply f_eq_subdomain_extend_lst. eassumption.

                  assert (Heq: FromList vars1 \\ [set k3] \\ FromList vars1 <--> Empty_set _) by sets.
                  rewrite Heq. intros x Hin. now inv Hin.
                  rewrite FromList_rev. sets.

                * { eapply preord_val_fun.
                    simpl. rewrite Coqlib.peq_true. reflexivity.
                    simpl. rewrite Coqlib.peq_true. reflexivity.
                    
                    intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                    destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                    inv H1. eexists. split. reflexivity.              
                    intros Hlt Hall. 
                    
                    eapply preord_exp_monotonic.
                    eapply preord_exp_post_monotonic. eapply HinclG. 
                    edestruct (H j) as (_ & Hexps & _ & _ ). lia.
                    eapply Hexps; try eassumption. reflexivity.
                    - constructor; eauto. 
                      intros Hin. eapply Hdis1. constructor; eauto.
                      
                    - normalize_sets. intros Hc. inv Hc; eauto.
                      inv H1; eauto.
                      inv H7. inv H3. eapply Hdis1. constructor; eauto.

                    - normalize_sets. eapply Union_Disjoint_r; [ | now sets ].
                      eapply Disjoint_Singleton_r. intros Hc. eapply Hdis1; sets.
                      
                    - simpl. congruence.

                    - eapply Disjoint_Included_r.
                      eapply cps_cvt_exp_subset. eassumption. repeat normalize_sets. xsets.
                      
                    - eapply Disjoint_Included_r.
                      eapply cps_cvt_exp_subset. eassumption. repeat normalize_sets. xsets.
                      
                    - simpl. rewrite !extend_lst_app. 2:{ rewrite !rev_length. eassumption. }
                      simpl. rewrite extend_extend_lst_commut.


                      + inv Hall. eapply preord_env_P_inj_set_alt; [ | eassumption | ].
                        
                        eapply preord_env_P_inj_set_not_In_P_r.
                        eapply preord_env_P_inj_set_not_In_P_l.

                        eapply preord_env_P_inj_antimon.
                        eapply preord_env_P_inj_monotonic.
                        2: { eassumption. } lia.
                        normalize_sets. now sets.
                        
                        * repeat normalize_sets. intros Hc. inv Hc; eauto.
                          inv H1; eauto. inv H9. inv H1. inv H3. now eapply Hdis1; eauto.
                          inv H3. now eapply Hdis1; eauto.
                          inv H9; eauto. inv H3. now eapply Hdis1; eauto.

                        * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                          inv Hc; eauto.

                          eapply image_extend_lst_Included in H1; eauto.

                          inv H1.
                          eapply image_extend_Included' in H7. 
                          rewrite image_id in H7.
                          repeat normalize_sets. 

                          rewrite FromList_rev in H7. inv H7. 

                          
                          assert (Heq : (k1 |: FromList vars1 :|: (x1 |: FromList xs1) \\ [set x1] \\ FromList  xs1 \\ FromList vars1 \\ [set k1] ) <--> Empty_set _) by xsets.

                          eapply  Heq in H1. now inv H1.

                          inv H1. inv H6. now eapply Hdis2; eauto.
                          inv H6. now eapply Hdis2; eauto.

                          rewrite FromList_rev in H1.
                          inv H6. now eapply Hdis2; eauto.

                          rewrite !rev_length. eassumption.

                        * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                          inv Hc; eauto.

                          eapply image_extend_lst_Included in H1; eauto.

                          inv H1.
                          eapply image_extend_Included' in H7. 
                          rewrite image_id in H7.
                          repeat normalize_sets. 

                          rewrite FromList_rev in H7. inv H7. 

                          
                          assert (Heq : (k1 |: FromList vars1 :|: (x1 |: FromList xs1) \\ [set x1] \\ FromList  xs1 \\ FromList vars1 \\ [set k1] ) <--> Empty_set _) by xsets.

                          eapply  Heq in H1. now inv H1.

                          inv H1. inv H6. now eapply Hdis2; eauto.
                          inv H6. now eapply Hdis2; eauto.

                          rewrite FromList_rev in H1.
                          inv H6. now eapply Hdis2; eauto.

                          rewrite !rev_length. eassumption.

                      + intros H1c. eapply in_rev in H1c.
                        eapply Hdis1; eauto. 
                        
                      + intros H1c. eapply in_rev in H1c.
                        eapply Hdis2; eauto.
                        
                      + rewrite !rev_length. eassumption.
                        
                    - lia. }
                  
                * rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                  intros Hc.
                  eapply image_extend_lst_Included in Hc; eauto.
                  rewrite image_id in Hc. inv Hc.

                  inv H0. inv H1; now eauto.

                  inv H6. now eapply Hdis2; eauto.

              + intros Hc. inv H3. eapply Hdis1; eauto.

              + intros Hc. inv H6. eapply Hdis2; eauto.

            - lia. } 
          
      - (* eflnil *)
        intros B1 B2 m k1 k2 vars1 vars2 vars1' vars2' nl1 nl2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Heq1 Heq2 Hnd Hnd1 Hnd2 Hlen1 Hlen2 Hdis1 Hdis2 Hdis3 Henv.
        inv He1. inv He2. simpl. repeat normalize_sets.
        simpl in *. repeat normalize_sets. eassumption. 
         
      - (* eflcons *)
        intros n e efns Hin IHe B1 B2 m k1 k2 vars1 vars2 vars1' vars2' nl1 nl2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Heql1 Heql2 Hnd Hnd1 Hnd2 Hlen1 Hlen2 Hdis1 Hdis2 Hdis3 Henv.

        revert m Hm Henv.
        induction k using lt_wf_rec. intros m Hm Henv.
 
        assert (Heq1 : all_fun_name B1 = nl1). { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }

        assert (Heq2 : all_fun_name B2 = nl2). { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }

        eapply preord_env_P_inj_def_funs_Vfun. 

        + rewrite Same_set_all_fun_name. rewrite Heq1.
          eapply preord_env_P_inj_antimon. eassumption.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
          subst. repeat normalize_sets. xsets.
          
        + eassumption.

        + eassumption.

        + subst. rewrite Same_set_all_fun_name.
          eapply Disjoint_Included_l.
          eapply image_extend_lst_Included. eassumption.
          eapply Union_Disjoint_l.
          
          eapply Disjoint_Included_l.
          eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite image_id.
          assert (Heq : k1 |: (FromList (all_fun_name B1 ++ vars1') :|: FromList (all_fun_name B1)) \\
                           FromList (all_fun_name B1) \\ FromList vars1' \\ [set k1] <--> Empty_set _).
          { repeat normalize_sets. now xsets. }
          
          rewrite Heq. now sets.
          
          rewrite Same_set_all_fun_name. repeat normalize_sets.

          rewrite <- Same_set_all_fun_name. now xsets. 
          now sets.
                    
        + { intros. 
            edestruct cps_cvt_rel_efnlst_exists with (S1 := S1); try eassumption. destructAll.
            edestruct cps_cvt_rel_efnlst_exists with (S1 := S3); try eassumption. destructAll.
            
            eapply preord_val_fun.          
            - eassumption.
            - eassumption.
            - intros rho1' j vs1 vs2 Hlen' Hset.
              destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inversion Hset. eexists. split. reflexivity.              
              intros Hlt Hall. inv Hall. inv H21. clear H22.
              
              edestruct (H j) as [ Hexp _ _ _   ]. lia. repeat subst_exp. 
              eapply preord_exp_post_monotonic. eapply HinclG.
              eapply Hexp.
              + omega.
              + eassumption.
              + eassumption.
              + constructor; [ | eassumption ]. repeat normalize_sets.
                intros Hc. eapply Hdis1.
                eapply in_app_or in Hc. inv Hc; eauto. 
              + repeat normalize_sets. inv H6. intros Hc. inv Hc.
                * inv H6. eauto.
                * eapply Hdis1. now sets.
              + simpl. rewrite !app_length. congruence.
              + repeat normalize_sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included; [ | | eapply Hdis1 ]; sets.
              + repeat normalize_sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
              + repeat normalize_sets. simpl.
                assert (Hfeq : f_eq (((id {x ~> x6}) <{ all_fun_name B1 ++ vars1' ~> all_fun_name B2 ++ vars2' }>) {x0 ~> x7})
                                    (((id <{ all_fun_name B1 ++ vars1' ~> all_fun_name B2 ++ vars2' }>) {x0 ~> x7}) {x ~> x6})).
                { rewrite extend_extend_lst_commut; eauto.
                  rewrite extend_commut; eauto. reflexivity. 
                  - inv H6. intros Hc. subst. eauto.
                  - inv H12. intros Hc. subst. eauto.
                  - inv H6. intros Hc. eapply Hdis1.
                    eapply in_app_or in Hc. inv Hc; eauto.
                  - inv H12. intros Hc. eapply Hdis2.
                    eapply in_app_or in Hc. inv Hc; eauto.
                  - rewrite !app_length. congruence. }
                
                rewrite Hfeq. 
                
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.
                
                * eapply preord_env_P_inj_f_eq_subdomain.
                  eapply preord_env_P_inj_antimon.
                  { eapply H0 with (m := j).
                    - lia.
                    - intros. eapply H. lia.
                    - eauto.
                    - reflexivity.
                    - eapply preord_env_P_inj_antimon.
                      eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                      repeat normalize_sets. sets. }
                  
                  repeat normalize_sets. now xsets.

                  rewrite extend_lst_app.

                  eapply f_eq_subdomain_extend_lst. eassumption.
                  eapply f_eq_subdomain_extend_lst. eassumption.
                  
                  
                  assert (Hfeq' : (x |: (x0 |: (FromList (all_fun_name B1) :|: FromList vars1')) \\ [set x] \\ [set x0] \\
                                     FromList (all_fun_name B1) \\ FromList vars1') <--> Empty_set _) by xsets.
                  rewrite Hfeq'. intros z Hinz. now inv Hinz. eassumption. 
                  
                * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                  rewrite image_id in Hc. inv Hc; eauto. inv H9; eauto. inv H15; eauto. 
                  inv H9; eauto. inv H15; eauto. repeat normalize_sets. now inv H9; eauto.

                  repeat normalize_sets. eapply Hdis2. now sets.
                  rewrite !app_length. congruence.                  
                  
                * intros Hc. eapply image_extend_Included' in Hc.
                  inv H12. inv Hc; eauto.
                  
                  eapply image_extend_lst_Included in H12; eauto.
                  rewrite image_id in H12.

                  repeat normalize_sets.
                  assert (Heq :x |: (x0 |: (FromList (all_fun_name B1) :|: FromList vars1')) \\ [set x] \\ [set x0] \\
                                 (FromList (all_fun_name B1) :|: FromList vars1') <--> Empty_set _) by xsets.
                  
                  rewrite Heq in H12. repeat normalize_sets.
                  now eapply Hdis2; eauto.
                  rewrite !app_length. congruence. } 
          
      - (* brnil_e *)
        intros bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv Hvar.
        inv He1; inv He2.
        eapply preord_exp_case_nil_compat.
        eapply Hprops.


      - (* brcons_e *)
        intros d p e IHe bs IHbs bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv Hvar.
        inv He1; inv He2.
        eapply preord_exp_case_cons_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eapply Hprops.
        + eapply cps_cvt_rel_branches_ctor_tag; eauto.
        + eassumption.
        + intros.
          assert (Hv1 :  FromList vars \subset S1).
          { eapply cps_cvt_rel_subset in H16. eapply Included_trans; sets. }
          assert (Hv2 :  FromList vars0 \subset S3).
          { eapply cps_cvt_rel_subset in H22. eapply Included_trans; sets. }

          eapply preord_exp_monotonic.
          * eapply ctx_bind_proj_alpha_equiv.
            -- eassumption.
            -- eassumption.
            -- congruence.
            -- eassumption.
            -- eassumption. 
            -- eapply Disjoint_Included_l. eassumption. sets.
            -- eapply Disjoint_Included_l. eassumption.
               eapply Union_Disjoint_r. now sets.
               eapply Disjoint_Included_r.
               eapply image_extend_lst_Included. eassumption.
               eapply Union_Disjoint_r; sets.
               rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
               repeat normalize_sets.
               eapply Disjoint_Included_r.
               eapply image_extend_Included'.
               eapply Union_Disjoint_r.
               rewrite image_id. now sets. now sets.

            -- intros. eapply IHe; try eassumption. lia.
               
               ++ eapply NoDup_app; eauto.
                  eapply Disjoint_Included_l. eassumption. sets.
                  
               ++ repeat normalize_sets.
                  intros Hc. inv Hc; eauto. eapply Hdis1. now eauto.
               ++ rewrite !app_length. congruence.
               ++ eapply cps_cvt_rel_subset in H16.
                  repeat normalize_sets.
                  eapply Union_Disjoint_l; sets.
                  
                  eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc; eauto. eapply Hdis1. constructor. left. now left.
                  now eauto.
                  eapply Union_Disjoint_l; sets.
                  eapply Disjoint_Included; [ | | eapply Hdis1 ].
                  eapply Included_trans; [ | eapply H16 ]. now sets.
                  now sets. 
               ++ eapply cps_cvt_rel_subset in H22.
                  repeat normalize_sets. 
                  eapply Union_Disjoint_l; sets.
                  
                  eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc; eauto. eapply Hdis2. constructor. left. now left.
                  now eauto.
                  eapply Union_Disjoint_l; sets.
                  eapply Disjoint_Included; [ | | eapply Hdis2 ].
                  eapply Included_trans; [ | eapply H22 ]. now sets.
                  now sets.
               ++ rewrite extend_lst_app.
                  eapply preord_env_P_inj_antimon. eassumption.
                  repeat normalize_sets. now sets.
                  replace (@Datatypes.length positive) with (@Datatypes.length var); eauto. congruence.

          * lia.
        + eapply IHbs; try eassumption. 
    Qed.
    
    Lemma cps_cvt_val_alpha_equiv :
      forall k, cps_cvt_val_alpha_equiv_statement k.
    Proof.
    Admitted.
      
    
    (* Inductive StrictlyIncreasing' : list positive -> Prop := *)
    (* | SInc_nil : StrictlyIncreasing' [] *)
    (* | SInc_cons1 a : StrictlyIncreasing' [a] *)
    (* | SInc_consn a b l : *)
    (*     StrictlyIncreasing' (b :: l) -> *)
    (*     (a < b)%positive  -> *)
    (*     StrictlyIncreasing' (a :: b :: l). *)

    (* Definition StrictlyIncreasing l := *)
    (*   Sorted (fun p1 p2 => (p1 < p2)%positive) l. *)

    Definition cps_env_rel'' (R : value -> cps.val -> Prop) rho vs :=
      forall v n,
        nth_error rho n = Some v ->
        exists v',
          nth_error vs n = Some v' ->
          forall v'' k,
            R v v'' ->
            preord_val cenv PG k v'' v'.

    (* Lemma Forall2_aux_is_Forall2 : *)
    (*   forall vs l,  *)
    (*     (fix Forall2_aux (vs1 : list value) (vs2 : list cps.val) {struct vs1} : *)
    (*        Prop := *)
    (*        match vs1 with *)
    (*        | [] => match vs2 with *)
    (*                | [] => True *)
    (*                | _ :: _ => False *)
    (*                end *)
    (*        | v1 :: vs3 => *)
    (*          match vs2 with *)
    (*          | [] => False *)
    (*          | v2 :: vs4 => cps_val_rel' v1 v2 /\ Forall2_aux vs3 vs4 *)
    (*          end *)
    (*        end) vs l -> *)
    (*     Forall2 cps_val_rel' vs l. *)
    (* Proof. *)
    (*   induction vs; intros l Haux. *)
    (*   - destruct l. constructor. destruct Haux. *)
    (*   - destruct l. destruct Haux. *)
    (*     destruct Haux. econstructor. *)
    (*     eassumption. eapply IHvs. eassumption. *)
    (* Qed. *)


(*     Lemma cps_val_alpha_equiv : *)
(*       forall k, *)
(*         (forall m, (m < k)%nat -> cps_cvt_alpha_equiv_statement m) -> *)
(*         cps_cvt_val_alpha_equiv_statement k. *)
(*     Proof. *)
(*       induction k using lt_wf_rec. intros IH. *)
(*       intros v. induction v using value_ind'; *)
(*                   intros v1 v2 next1 next2 next3 next4 Hv1 Hv2; *)
(*                   rewrite cps_cvt_val_eq in *. *)
(*       - simpl in Hv1, Hv2. *)
(*         destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1. *)
(*         2: { inv Hv1. } destruct p. inv Hv1. *)
(*         destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2. *)
(*         2: { inv Hv2. } destruct p. inv Hv2. *)
(*         rewrite preord_val_eq. simpl. split. reflexivity. *)
(*         eapply Forall2_Forall2_asym_included. *)
(*         generalize dependent l0. generalize dependent l. *)
(*         generalize dependent next1. generalize dependent next3. *)
(*         induction H0; intros next3 next1 l1 Henv1 l2 Henv2. *)
(*         + simpl in Henv1, Henv2. inv Henv1. inv Henv2. econstructor.  *)
(*         + simpl in Henv1, Henv2. *)
(*           destruct (cps_cvt_val x next1 cnstrs) eqn:Hval1. *)
(*           2: { inv Henv1. } destruct p. *)
(*           destruct (cps_cvt_env l s cnstrs) eqn:Hcvt1. *)
(*           2: { inv Henv1. } destruct p. inv Henv1. *)
(*           destruct (cps_cvt_val x next3 cnstrs) eqn:Hval2. *)
(*           2: { inv Henv2. } destruct p. *)
(*           destruct (cps_cvt_env l s0 cnstrs) eqn:Hcvt2. *)
(*           2: { inv Henv2. } destruct p. inv Henv2. *)
(*           econstructor. *)
(*           eapply H0. eassumption. eassumption. *)
(*           eapply IHForall. eassumption. eassumption.  *)
(*       - simpl in Hv1, Hv2. inv Hv1. inv Hv2. *)
(*         eapply preord_val_refl. eassumption. *)
(*       - simpl in Hv1, Hv2. *)
(*         destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1; inv Hv1. *)
(*         destruct p eqn:Hp. *)
(*         destruct (gensym_n s (rho_names vs)) eqn:Hgen_n1. *)
(*         destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset. 2: { inv H2. } *)
(*         destruct (gensym s0 (nNamed "k_lam")) eqn:Hgen_k1. *)
(*         destruct (gensym s1 (nNamed "x_lam")) eqn:Hgen_x1. *)
(*         destruct (gensym s2 na) eqn:Hen_f1. *)
(*         destruct (cps_cvt e (v0 :: l0) v s3 cnstrs) eqn:Hcvt1. 2: { inv H2. } *)
(*         destruct p0. inv H2. *)
(*         destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2; inv Hv2. *)
(*         destruct p eqn:Hp. *)
(*         destruct (gensym_n s4 (rho_names vs)) eqn:Hgen_n2. *)
(*         destruct (set_lists l2 l1 (M.empty cps.val)) eqn:Hset2. 2: { inv H2. } *)
(*         destruct (gensym s5 (nNamed "k_lam")) eqn:Hgen_k2. *)
(*         destruct (gensym s6 (nNamed "x_lam")) eqn:Hgen_x2. *)
(*         destruct (gensym s7 na) eqn:Hen_f2. *)
(*         destruct (cps_cvt e (v4 :: l2) v1 s8 cnstrs) eqn:Hcvt2. 2: { inv H2. }  *)
(*         destruct p0. inv H2. *)
(*         rewrite preord_val_eq. unfold preord_val'. *)
(*         { intros vs1 vs2 j tg xs1 e2 rho1' Hlen_eq Hfind Hsetl. *)
(*           simpl in Hfind. simpl. *)
(*           rewrite peq_true in *. *)
(*           inv Hfind. *)
(*           pose proof (set_lists_length2) as Hsetl2. *)
(*           edestruct Hsetl2 with (rho := (def_funs (Fcons v3 func_tag [v; v0] e2 Fnil) *)
(*                                                        (Fcons v3 func_tag [v; v0] e2 Fnil) t t)) *)
(*                                      (xs1 := [v; v0]) (vs1 := vs1) *)
(*                                      (xs2 := [v5; v5]) (vs2 := vs2); clear Hsetl2. *)
(*           econstructor. *)
(*           eassumption. *)
(*           symmetry. rewrite H2. eassumption.  *)
(*           simpl in Hsetl. *)
(*           destruct vs1. inv Hsetl. *)
(*           destruct vs1. inv Hsetl. *)
(*           destruct vs1; inv Hsetl. *)
(*           simpl in H1. *)
(*           destruct vs2. inv H1. *)
(*           destruct vs2. inv H1. *)
(*           destruct vs2. 2: { inv H1. } rewrite <- H2. inv H1.  *)
(*           eexists. eexists. eexists. split. *)
(*           reflexivity. split. *)
(*           reflexivity. *)
(*           intros Hlt2 Hall. *)
(*           eapply preord_exp_post_monotonic. *)
(*           eapply HinclG. *)
(*           eapply preord_exp_monotonic. *)
(*           unfold cps_cvt_alpha_equiv_statement in IH. *)
(*           edestruct IH with (m := j) as (IHstep & _). eassumption. *)
(*           eapply IHstep.  *)
(*           eassumption. *)
(*           eassumption. *)
(*           admit. admit. *)
(*           simpl. f_equal. eapply gensym_n_length_eq. *)
(*           eassumption. eassumption.  *)
(*           admit. *)
(*           simpl. *)
(*           (* Zoe: Something broke here from flipping the args *) *)
(*           (* eapply preord_env_P_inj_set_alt. *) *)
(*           (* rewrite Setminus_Union_distr. *) *)
(*           (* rewrite FromList_cons. (* normalize_sets *) *) *)
(*           (* assert (Hsets: ([set v] \\ [set v0] :|: (v0 |: FromList l0 \\ [set v0])) *) *)
(*           (*                  <--> ([set v] :|: (FromList l0))). *) *)
(*           (* { rewrite Setminus_Union_distr. *) *)
(*           (*   rewrite Setminus_Same_set_Empty_set. normalize_sets. *) *)
(*           (*   rewrite Setminus_Disjoint. rewrite Setminus_Disjoint. *) *)
(*           (*   reflexivity. admit. admit. } *) *)
(*           (* rewrite Hsets. clear Hsets. *) *)
(*           (* rewrite extend_extend_lst_commut. *) *)
(*           (* eapply preord_env_P_inj_set_alt. *) *)
(*           (* rewrite Setminus_Union_distr at 1. *) *)
(*           (* rewrite Setminus_Same_set_Empty_set. *) *)
(*           (* rewrite Setminus_Disjoint. normalize_sets. *) *)
(*           (* eapply preord_env_P_inj_set_not_In_P_l. *) *)
(*           (* eapply preord_env_P_inj_set_not_In_P_r. *) *)
(*           (* eapply preord_env_P_inj_set_lists_alt. *) *)
(*           (* 7: { eassumption. } 7: { eassumption. } *) *)
(*           (* econstructor. rewrite M.gempty in H3. inv H3. *) *)
(*           (* eapply cps_cvt_env_alpha_equiv. *) *)
(*           (* eapply H. eassumption. intros m Hlt3. *) *)
(*           (* eapply IH. omega. eassumption. eassumption.  *) *)
(*           (* admit. admit. admit. *) *)
(*           (* rewrite Setminus_Same_set_Empty_set. rewrite image_Empty_set. *) *)
(*           (* eapply Disjoint_Empty_set_l. *) *)
(*           (* admit. *) *)
(*           (* admit. admit.  *) *)
(*           (* inversion Hall. inversion H7. eassumption. *) *)
(*           (* admit. *) *)
(*           (* admit. admit. admit. *) *)
(*           (* inversion Hall. eassumption. *) *)
(*           admit. *)
(*           omega. *)
(*         } *)

(*       - simpl in Hv1, Hv2. *)
(*         destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1. 2: { inv Hv1. } *)
(*         destruct p. destruct (gensym_n s (rho_names vs)) eqn:Hgen_n1. *)
(*         destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset1. 2: { inv Hv1. } *)
(*         destruct (efnlst_names fnl) eqn:Hefns1. *)
(*         destruct (gensym_n s0 l1) eqn:Hgen_lst1. *)
(*         destruct (cps_cvt_efnlst fnl (l2 ++ l0) l2 s1 cnstrs) eqn:Hcvt_efns1. *)
(*         2: { inv Hv1. } destruct p. inv Hv1. *)
(*         destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2. 2: { inv Hv2. } *)
(*         destruct p. destruct (nth_error l2 (N.to_nat n)) eqn:Herr1; inv H2. *)
(*         destruct (gensym_n s3 (rho_names vs)) eqn:Hgen_n2. *)
(*         destruct (set_lists l4 l3 (M.empty cps.val)) eqn:Hset2. 2: { inv Hv2. }  *)
(*         destruct (gensym_n s2 l1) eqn:Hgen_lst2. *)
(*         destruct (cps_cvt_efnlst fnl (l5 ++ l4) l5 s4 cnstrs) eqn:Hcvt_efns2. *)
(*         2: { inv Hv2. } destruct p. *)
(*         destruct (nth_error l5 (N.to_nat n)) eqn:Herr2; inv Hv2. *)
(*         rewrite preord_val_eq. unfold preord_val'. *)
(*         { intros vs1 vs2 j tg xs1 e2 rho1' Hlen_eq Hfind Hsetl. *)
(*           edestruct (cps_cvt_efnlst_nth_error). *)
(*           admit. eapply Hcvt_efns1. eassumption. *)
(*           edestruct H1.   *)
(*           pose proof (cps_cvt_efnlst_find_def) as Hexists. *)
(*           edestruct Hexists; clear Hexists. *)
(*           4: { eapply Hcvt_efns1. } 4: { eapply Hcvt_efns2. }  *)
(*           eapply gensym_n_NoDup. eassumption. *)
(*           eapply gensym_n_NoDup. eassumption. *)
(*           eapply gensym_n_length_eq. eassumption. eassumption.  *)
(*           2: { eassumption. }  *)
(*           eassumption. *)
(*           eassumption.  *)
(*           destructAll.  *)
(*           pose proof (set_lists_length2) as Hsetl2. *)
(*           edestruct Hsetl2 with (xs1 := [x4; x3]) (vs1 := vs1) *)
(*                                 (vs2 := vs2); clear Hsetl2. admit. eassumption. *)
(*           symmetry. eassumption. *)
(*           eexists. eexists. eexists. split. *)
(*           rewrite Herr2 in H9. inv H9. eassumption. split.  *)
(*           symmetry. eassumption. *)
(*           intros Hlt Hall. *)
(*           unfold cps_cvt_alpha_equiv_statement in IH. *)
(*           edestruct IH with (m := j) as (IHstep & _). eassumption. *)
(*           unfold cps_cvt_exp_alpha_equiv in IHstep. *)
(*           eapply preord_exp_post_monotonic. eapply HinclG. eapply IHstep. *)
(*           eassumption. *)
(*           eassumption. *)
(*     Admitted. *)

(* Lemma cps_cvt_alpha_equiv : *)
(*       forall k, cps_cvt_alpha_equiv_statement k. *)
(*     Proof. *)




    Fixpoint fundefs_to_list (fdefs : fundefs) :=
      match fdefs with
      | Fnil => []
      | Fcons v tg vars e fdefs' => (v, tg, vars, e) :: (fundefs_to_list fdefs')
      end.

    Require Import exp_equiv. 

    (** ** Correctness statements *)
    
    Definition cps_cvt_correct_exp :=
      forall e v rho vs vnames k x vk e' v' S S',
        eval_env vs e v ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: FromList vnames) S ->
        cps_cvt_rel S e vnames k cnstrs S' e' ->
        cps_val_rel v v' ->
        equiv_exp cenv _ _ _ _ P1 PG
                  ((Eapp k kon_tag (x::nil)),
                   (M.set x v' (M.set k vk (M.empty cps.val))))
                  (e', (M.set k vk rho)).

    Definition cps_cvt_correct_exps :=
      forall es es' vs rho vnames k x vk es'' vs' S S',
        Forall2 (fun e v => eval_env vs e v) (exps_to_list es) es' ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: (FromList vnames)) S ->
        Forall2 (fun e e' => cps_cvt_rel S e vnames k cnstrs S' e')
                (exps_to_list es) es'' ->
        Forall2 cps_val_rel es' vs' ->
        Forall2 (fun e' v' =>
                   equiv_exp cenv _ _ _ _  P1 PG
                       ((Eapp k kon_tag (x::nil)),
                        (M.set x v' (M.set k vk (M.empty cps.val))))
                       (e', (M.set k vk rho)))
                es'' vs'.

    Definition cps_cvt_correct_efnlst :=
      forall efns efns' vs rho vnames k x vk efns'' vs' S S',
        Forall2 (fun p v => let (na, e) := p : (name * expression.exp) in
                             eval_env vs e v) (efnlst_as_list efns) efns' ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: (FromList vnames)) S ->
        Forall2 (fun p e' => let (na, e) := p : (name * expression.exp) in
                   cps_cvt_rel S e vnames k cnstrs S' e')
                (efnlst_as_list efns) efns'' ->
        Forall2 cps_val_rel efns' vs' ->
        Forall2 (fun e' v' =>
                   equiv_exp cenv _ _ _ _  P1 PG
                             ((Eapp k kon_tag (x::nil)),
                              (M.set x v' (M.set k vk (M.empty cps.val))))
                             (e', (M.set k vk rho)))
                efns'' vs'.

    Definition cps_cvt_correct_branches :=
      forall bs bs' vs rho vnames k x vk bs'' vs' S S',
        Forall2 (fun p v => let '(dc, (n, l), e) := p in
                            eval_env vs e v) (branches_as_list bs) bs' ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: (FromList vnames)) S ->
        Forall2 (fun p e' => let '(dc, (n, l), e) := p in
                            cps_cvt_rel S e vnames k cnstrs S' e')
                (branches_as_list bs) bs'' ->
        Forall2 cps_val_rel bs' vs' ->
        Forall2 (fun e' v' =>
                   equiv_exp cenv _ _ _ _  P1 PG
                             ((Eapp k kon_tag (x::nil)),
                              (M.set x v' (M.set k vk (M.empty cps.val))))
                             (e', (M.set k vk rho)))
                bs'' vs'.

    Lemma cps_cvt_correct:
      cps_cvt_correct_exp /\
      cps_cvt_correct_exps /\
      cps_cvt_correct_efnlst /\
      cps_cvt_correct_branches.
    Proof.
      eapply exp_ind_alt.
      - intros n y rho vs vnames k x vk e' v' S S' Heval Hcenv Hdis Hcps Hval.
        inv Heval. inv Hcps. 

        admit. 
        
        (* cps_val_rel (List.nth (N.to_nat n) vs Prf_v) v' from Hval *) 

        (* From Henv, there exist v''
           cps_val_rel (List.nth (N.to_nat n) vs Prf_v) v'' from Hval
           and
           M.get v rho = Some v''
         *)

        (* From alpha_equiv_cps_val: v' ~ v'' *) 
        
      - (* Lam_e *)
        intros n e IHe y rho vs vnames k x vk e' v' S S' Heval Hcenv Hdis Hcps Hval. 
        inv Heval. inv Hcps. inv Hval.

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

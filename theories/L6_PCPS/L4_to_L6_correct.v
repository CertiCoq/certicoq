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
          cps_cvt_rel S1 e names k cnstrs S2 e' ->
          cps_val_rel (Clos_v rho na e)
                      (Vfun rho_m (Fcons f func_tag (x::k::nil) e' Fnil) f).

    Definition cps_env_rel : list var -> list value -> M.t val -> Prop :=
      cps_env_rel' cps_val_rel.


    


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
     forall e e1 e2 k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
        cps_cvt_rel S1 e vars1 k1 cnstrs S2 e1 ->
        cps_cvt_rel S3 e vars2 k2 cnstrs S4 e2 ->
        NoDup vars1 -> (* TODO is this needed? *)
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG k (e1, rho1) (e2, rho2).

    Definition cps_cvt_exps_alpha_equiv k :=
      forall es es1 es2 k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4,
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

        preord_env_P_inj cenv PG (k1 |: FromList vars1 :|: FromList xs1) k
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }> <{ rev xs1 ~> rev xs2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG k (es1, rho1) (es2, rho2). 

    Definition cps_cvt_efnlst_alpha_equiv k :=
      forall efns fdefs1 fdefs2 k1 k2 vars1 vars2 nlst1 nlst2 rho1 rho2
             S1 S2 S3 S4 f1 f2 n,
        cps_cvt_rel_efnlst S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
        cps_cvt_rel_efnlst S3 efns vars2 nlst2 cnstrs S4 fdefs2 ->

        NoDup vars1 ->
        NoDup (all_fun_name fdefs1) ->
        NoDup (all_fun_name fdefs2) ->

        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->
        
        (* Disjoint _ (FromList vars1) (name_in_fundefs fdefs1) -> *)
        (* Disjoint _ (FromList vars2) (name_in_fundefs fdefs2) -> *)

        
        nth_error (all_fun_name fdefs1) n = Some f1 ->
        nth_error (all_fun_name fdefs2) n = Some f2 ->
        
        preord_env_P_inj cenv PG (k1 |: (FromList vars1) \\ name_in_fundefs fdefs1) k
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_val cenv PG k (Vfun rho1 fdefs1 f1) (Vfun rho2 fdefs2 f2).

    
    Definition cps_cvt_branches_alpha_equiv (k : nat) :=
      forall bs bs1 bs2 k1 k2 vars1 vars2 x1 x2 rho1 rho2
             S1 S2 S3 S4,
        cps_cvt_rel_branches S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
        cps_cvt_rel_branches S3 bs vars2 k2 x2 cnstrs S4 bs2 ->        
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->        
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: FromList vars1) S1 ->       
        Disjoint _ (k2 |: FromList vars2) S3 ->
        
        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->        
        preord_var_env cenv PG k rho1 rho2 x1 x2 ->
        preord_exp cenv P1 PG k (Ecase x1 bs1, rho1)  (Ecase x2 bs2, rho2).

    
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
      
    
    (* Lemma exp_ind_alt_exp : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop), *)
    (*     (forall n : N, P (Var_e n)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) -> *)
    (*     (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) -> *)
    (*     (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) -> *)
    (*     (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) -> *)
    (*     P Prf_e -> *)
    (*     (forall p : positive, P (Prim_e p)) -> *)
    (*     P0 enil -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) -> *)
    (*     P1 eflnil -> *)
    (*     (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) -> *)
    (*     P2 brnil_e -> *)
    (*     (forall (d : dcon) (p : N * list name) (e : expression.exp), *)
    (*         P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) -> *)
    (*     (forall e : expression.exp, P e) *)
    (* with exp_ind_alt_exps : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop), *)
    (*     (forall n : N, P (Var_e n)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) -> *)
    (*     (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) -> *)
    (*     (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) -> *)
    (*     (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) -> *)
    (*     P Prf_e -> *)
    (*     (forall p : positive, P (Prim_e p)) -> *)
    (*     P0 enil -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) -> *)
    (*     P1 eflnil -> *)
    (*     (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) -> *)
    (*     P2 brnil_e -> *)
    (*     (forall (d : dcon) (p : N * list name) (e : expression.exp), *)
    (*         P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) -> *)
    (*     (forall e : exps, P0 e) *)
    (* with exp_ind_alt_efnlst : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop), *)
    (*     (forall n : N, P (Var_e n)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) -> *)
    (*     (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) -> *)
    (*     (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) -> *)
    (*     (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) -> *)
    (*     P Prf_e -> *)
    (*     (forall p : positive, P (Prim_e p)) -> *)
    (*     P0 enil -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) -> *)
    (*     P1 eflnil -> *)
    (*     (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) -> *)
    (*     P2 brnil_e -> *)
    (*     (forall (d : dcon) (p : N * list name) (e : expression.exp), *)
    (*         P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) -> *)
    (*     (forall e : efnlst, P1 e) *)
    (* with exp_ind_alt_branches : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop), *)
    (*               (forall n : N, P (Var_e n)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) -> *)
    (*     (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) -> *)
    (*     (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) -> *)
    (*     (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) -> *)
    (*     (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) -> *)
    (*     P Prf_e -> *)
    (*     (forall p : positive, P (Prim_e p)) -> *)
    (*     P0 enil -> *)
    (*     (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) -> *)
    (*     P1 eflnil -> *)
    (*     (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) -> *)
    (*     P2 brnil_e -> *)
    (*     (forall (d : dcon) (p : N * list name) (e : expression.exp), *)
    (*         P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) -> *)
    (*     (forall b : branches_e, P2 b). *)
    (* Proof. *)

    (* TODO move *)

    Lemma FromList_rev {A} (l : list A) :
      FromList (rev l) <--> FromList l.
    Proof.
      induction l.
      - reflexivity.
      - simpl. repeat normalize_sets. sets.
    Qed.
    
    Opaque preord_exp'. 
    
    Lemma cps_cvt_alpha_equiv :
      forall k, cps_cvt_alpha_equiv_statement k.
    Proof.
      induction k using lt_wf_rec.
      eapply exp_ind_alt.
      - (* Var_e *)
        intros n e1 e2 k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
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
        intros na e IH e1 e2 k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
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

              intros Hlt Hall. 
              
              eapply preord_exp_post_monotonic. now eapply HinclG.
              eapply preord_exp_monotonic.
              edestruct (H j) as [ Hexp _ _ _   ]. lia.
              eapply Hexp.
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
        intros e1 IHe1 e2 IHe2 e1' e2' k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
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

                intros Hlt Hall. simpl.
                { eapply preord_exp_fun_compat.

                  + admit. (* invariants *)
                  + admit. (* invariants *)
                  + { destruct H with (m := (j - 1)%nat) as [ IHe _]. omega. 
                      eapply IHe; try eassumption.
                      - admit. (* subset lemma for cvt_rel. *)
                      - admit. (* subset lemma for cvt_rel. *)
                      - admit. (* subset lemma for cvt_rel. *)
                      - simpl.
                        assert (Hfeq' : f_eq ((id {k4 ~> k6}) <{ vars1 ~> vars2 }>)
                                            ((id <{ vars1 ~> vars2 }>) {k4 ~> k6})). 
                        { rewrite extend_extend_lst_commut; eauto. reflexivity. 
                          - admit. (* subset lemma for cvt_rel. *)
                          - admit. (* subset lemma for cvt_rel. *) }

                        rewrite Hfeq'.
                        

                        eapply preord_env_P_inj_set_alt; eauto.
                        
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
                          * inv H5. intros Hc. inv Hc. eapply Hdis1. admit. (* lemma *)
                          * intros Hc. inv Hc. eapply Hdis1. sets.

                        + eapply preord_val_fun.
                          simpl. rewrite Coqlib.peq_true. reflexivity.
                          simpl. rewrite Coqlib.peq_true. reflexivity.
                          
                          intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          inv H1. eexists. split. reflexivity.
                          
                          intros Hlt' Hall'. simpl.
                          { eapply preord_exp_app_compat.
                            - admit. (* invariants *)
                            - admit. (* invariants *)
                            - inv H11. eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_eq.
                              inv Hall. eapply preord_val_monotonic. eassumption. lia.
                              
                              admit. (* lemma *)
                              admit. (* lemma *)
                              admit. (* lemma *)
                              admit. (* lemma *)

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
                                admit.
                                admit.
                                admit.
                                admit.
                                admit.
                                admit.
                                admit.
                                admit. (* var neq *)

                              + eapply preord_var_env_extend_eq.
                                inv Hall'. eassumption. } 

                        + admit. } }
              + admit.

            - lia. }       
      - (* Con_e *)
        intros dc es IH e1 e2 k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
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
                - inv H8. intros Hc. eapply Hdis2. sets. }
              
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
                rewrite H7. rewrite H11. reflexivity. eassumption. 

                eexists. split. now eauto. 

                intros Hlt2 Hall.
                { eapply preord_exp_constr_compat.
                  - admit. (* invariants *)
                  - admit. (* invariants *)
                  - rewrite <- map_extend_lst_same with (xs := vx) (xs' := vx0)
                                                        (f := id).
                    eapply Forall2_preord_var_env_map.
                    2: { reflexivity. }
                    eapply preord_env_P_inj_set_lists_alt.
                    rewrite Setminus_Same_set_Empty_set.
                    intros x' Hin. now inv Hin.
                    eassumption.

                    admit. (* TODO add NoDUp vx to rel *)
                    admit. (* TODO add NoDUp vx to rel *)
                    congruence.
                    rewrite Setminus_Same_set_Empty_set, image_id. now sets.
                    now eauto. now eauto.
                    admit. (* TODO add NoDUp vx to rel *)
                    replace (@Datatypes.length positive vx) with (@Datatypes.length var vx) by reflexivity.
                    congruence.

                  - intros m vs vs' Hlt Hall1.
                    eapply preord_exp_app_compat.
                    + eapply Hprops.
                    + eapply Hprops.
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
                        
                        eapply image_extend_Included' in H10. 
                        rewrite image_id in H10.

                        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set in H10.
                        repeat normalize_sets.
                        rewrite Setminus_Union, (Union_commut (FromList vars1)), <- Setminus_Union, Setminus_Same_set_Empty_set in H10.
                        repeat normalize_sets. 
                        inv H10. inv H8. eapply Hdis2. now sets.
                        inv H8. eapply Hdis2. now sets.
                        eassumption.

                      * intros Hc. inv Hc. inv H10.
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

                        admit. admit. (* TODO change rel *)

                      * admit. (* TODO change rel *)

                      * intros Hc.
                        eapply image_extend_lst_Included in Hc. inv Hc.
                        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set in H10.
                        repeat normalize_sets.
                        eapply image_extend_Included' in H10. rewrite  image_id in H10.
                        inv H10. inv H12. inv H10. now eauto.
                        inv H12. eapply Hdis2. now sets.
                        eapply Hdis2. now sets.
                        eassumption.

                      * intros Hc. inv Hc. inv H10. 
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

                inv H8. eapply Hdis2. constructor; now eauto. eassumption.

            - omega. }
          
      - (* Match_e *)
        intros e IHe pars bs IHbs e1 e3 k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
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
              + admit. (* lemma. *)
              + admit. (* lemma *)
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
        intros na e1 IHe1 e2 IHe2 e1' e2' k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IHe1; try eassumption.
            - inv H5. intros Hc. eapply Hdis1. sets.
            - admit. (* lemma *)
            - admit. (* lemma *)
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

            - omega. }
          
          
      - (* Fix_e *)
        intros na e IH e1 e2 k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.  
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
              
              eapply preord_env_P_inj_def_funs with (S := k1 |: FromList vars1 :|: name_in_fundefs fdefs).
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.
              congruence.
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.
              now sets.

              eapply preord_env_P_inj_def_funs_Vfun.
                  
              + eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic;  [ |  eassumption ]. lia.
                sets.

              + congruence.
              + rewrite Heq1. eassumption.

              + rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
                repeat normalize_sets.
                eapply Disjoint_Included_l.
                eapply image_extend_lst_Included. eassumption.
                eapply Union_Disjoint_l.
                
                eapply Disjoint_Included_l.
                eapply image_extend_Included'.
                eapply Union_Disjoint_l.
                rewrite image_id.
                assert (Heq : (k1 |: FromList vars1 \\ name_in_fundefs fdefs \\ FromList vars1 \\ [set k1]) <--> Empty_set _). now xsets.
                rewrite Heq. now sets.

                rewrite Same_set_all_fun_name. rewrite Heq2.
                eapply Disjoint_Singleton_l. intros Hc. now eapply Hdis2; sets.

                rewrite Same_set_all_fun_name. rewrite Heq2.
                eapply Disjoint_Included; [ | | eapply Hdis2 ]. eassumption. now sets.
                
              + { intros. eapply preord_val_monotonic. eapply e; try eassumption.
                  8:{ rewrite extend_lst_app.
                       2:{ replace (@Datatypes.length positive) with (@Datatypes.length var) by reflexivity.
                           congruence. }
                       
                       repeat normalize_sets.
                       
                       rewrite !Setminus_Union_distr. rewrite <- Heq1, <- Same_set_all_fun_name at 1.
                       rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                       
                       eapply preord_env_P_inj_f_eq_subdomain.
                       
                       eapply preord_env_P_inj_antimon. eassumption.
                       eapply Included_Union_compat. now eapply Setminus_Included. now sets.
                                                                     
                       rewrite f_eq_subdomain_extend_lst_Disjoint with (xs := nlst).
                       reflexivity.

                       rewrite <- Heq1. rewrite <- Same_set_all_fun_name. now sets. }
                  
                  - eapply NoDup_app; eauto.
                    eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis1 ]; now sets.

                  - rewrite Heq1. eassumption.
                  - rewrite Heq2. eassumption.

                  - normalize_sets.
                    intros Hc. destruct Hc.
                    eapply Hdis1. now constructor; eauto.
                    now eauto.

                  - rewrite !app_length. congruence.
                    
                  - normalize_sets. now xsets.

                  - normalize_sets. now xsets.

                  (* - normalize_sets. admit. (* wrong *) *)

                  (* - normalize_sets. admit. (* wrong *) *)

                  - omega. } }

      - (* Prf_e *)
        intros e1 e2 k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.

      - (* Prim_e *)
        intros p e1 e2 k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2. 
        (* TODO add Prim_e to relation ? *)
        
      - (* enil *)
        intros es1 es2 k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hdup' Hnot Hdis Hlen Hlen' Hdis1 Hdis2 Henv.
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
        intros e IHe es IHes e1 e2 k1 k2 vars1 vars2 xs1 xs2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hdup' Hnot Hdis Hlen Hlen' Hdis1 Hdis2 Henv.
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
                    eapply Hexps; try eassumption.
                    - constructor; eauto. 
                      intros Hin. eapply Hdis1. constructor; eauto.
                      
                    - normalize_sets. intros Hc. inv Hc; eauto.
                      inv H1; eauto.
                      inv H7. inv H3. eapply Hdis1. constructor; eauto.

                    - normalize_sets. eapply Union_Disjoint_r; [ | now sets ].
                      eapply Disjoint_Singleton_r. intros Hc. eapply Hdis1; sets.
                      
                    - simpl. congruence.

                    - admit. (* lemma *)

                    - admit. (* lemma *)
                      
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
        intros B1 B2 k1 k2 vars1 vars2 nl1 nl2 rho1 rho2 S1 S2 S3 S4
               f1 f2 n He1 He2 Hnd Hnd1 Hnd2 Hnin1 Hlen Hdis1 Hdis2 (* Hdis3 Hdis4 *)  Hnth1 Hnth2 Henv.
        inv He1. inv He2. simpl. repeat normalize_sets.
        rewrite preord_val_eq. intro; intros. inv H1. 
        
      - (* eflcons *)
        intros n e efns Hin IHe B1 B2 k1 k2 vars1 vars2 nl1 nl2 rho1 rho2 S1 S2 S3 S4
               f1 f2 m He1 He2 Hnd Hnd1 Hnd2 Hnin1 Hlen Hdis1 Hdis2 (* Hdis3 Hdis4 *) Hnth1 Hnth2 Henv.

        edestruct cps_cvt_rel_efnlst_exists with (S1 := S1); try eassumption.  destructAll.
        edestruct cps_cvt_rel_efnlst_exists with (S1 := S3); try eassumption.  destructAll.
        
        eapply preord_val_fun.          
        + eassumption.
        + eassumption.
        + intros rho1' j vs1 vs2 Hlen' Hset.
          destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
          destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
          inv Hset. eexists. split. reflexivity.              
          intros Hlt Hall. inv Hall. inv H17.
          
          { edestruct (H j) as [ Hexp _ _ _   ]. lia. repeat subst_exp. 
            eapply preord_exp_post_monotonic. eapply HinclG.
            eapply Hexp.
            + eassumption.
            + eassumption.
            + constructor; [ | eassumption ]. intros Hc. eapply Hdis1. now sets.
            + repeat normalize_sets. inv H3. intros Hc. inv Hc.
              * inv H3. eauto.
              * eapply Hdis1. now sets.
            + simpl. congruence.
            + repeat normalize_sets.
              eapply Union_Disjoint_l; sets.
              eapply Union_Disjoint_l; sets.
              eapply Disjoint_Included; [ | | eapply Hdis1 ]; sets.
            + repeat normalize_sets.
              eapply Union_Disjoint_l; sets.
              eapply Union_Disjoint_l; sets.
              eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
            + repeat normalize_sets. simpl.
              assert (Hfeq : f_eq (((id {x ~> x6}) <{ vars1 ~> vars2 }>) {x0 ~> x7})
                                  (((id <{ vars1 ~> vars2 }>) {x0 ~> x7}) {x ~> x6})).
              { rewrite extend_extend_lst_commut; eauto.
                rewrite extend_commut; eauto. reflexivity. 
                - inv H3. intros Hc. subst. eauto.
                - inv H9. intros Hc. subst. eauto.
                - inv H3. intros Hc. eapply Hdis1. sets.
                - inv H9. intros Hc. eapply Hdis2. sets. }
              
              rewrite Hfeq.
              
              eapply preord_env_P_inj_set_alt; eauto.
              eapply preord_env_P_inj_set_alt; eauto.
              eapply preord_env_P_inj_def_funs_neq_l.
              eapply preord_env_P_inj_def_funs_neq_r.

              eapply preord_env_P_inj_f_eq_subdomain.
              
              eapply preord_env_P_inj_antimon.
              eapply preord_env_P_inj_monotonic.
              2: { eassumption. } omega.
              now xsets.

              * eapply f_eq_subdomain_extend_lst. eassumption.
                
                eapply f_eq_subdomain_extend_not_In_S_l; [ | reflexivity ].
                
                intros Hc. inv Hc. inv H6. inv H13. inv H6; eauto. inv H13; eauto.

              * eapply Disjoint_Included_l. 
                eapply image_extend_lst_Included. eassumption. rewrite image_id.
                xsets. 
              * xsets.
              * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                rewrite image_id in Hc. inv Hc; eauto. inv H6; eauto. inv H12; eauto. 
                inv H6; eauto. inv H12; eauto. now inv H6; eauto. 
                eapply Hdis2. now sets.
                
              * intros Hc. eapply image_extend_Included' in Hc.
                inv H9. inv Hc; eauto.
                
                eapply image_extend_lst_Included in H9; eauto.
                rewrite image_id in H9.
                
                assert (Heq : x |: (x0 |: FromList vars1) \\ [set x] \\ [set x0] \\ FromList vars1 <--> Empty_set _) by xsets.

                rewrite Heq in H9. repeat normalize_sets.
                now eapply Hdis2; eauto. }
          
      - (* brnil_e *)
        admit.
        
      - (* brcons_e *)
        admit.
        (* intros dc p e IHe bs IHbs bs1 bs2 k1 k2 r1 r2 vars1 vars2 x1 x2 *)
        (*        rho1 rho2 next1 next2 next3 next4 *)
        (*        Hbs1 Hbs2 Hdup Hnot Hlen Hlt Henv Hvar. *)
        (* simpl in Hbs1, Hbs2. *)
        (* destruct p. *)
        (* destruct (cps_cvt_branches bs vars1 k1 r1 next1 cnstrs) eqn:Hcvt_bs1. *)
        (* 2: { inv Hbs1. } destruct p. destruct (gensym_n s (rev l)) eqn:Hgen_l. *)
        (* destruct (ctx_bind_proj (dcon_to_tag dc cnstrs) r1 (Datatypes.length l) *)
        (*                         (hd 1%positive l1) 0) eqn:Hctx1. *)
        (* destruct (cps_cvt e (rev l1 ++ vars1) k1 s0 cnstrs) eqn:Hcvt_e1. *)
        (* 2: { inv Hbs1. } destruct p. inv Hbs1. *)
        (* destruct (cps_cvt_branches bs vars2 k2 r2 next3 cnstrs) eqn:Hcvt_bs2. *)
        (* 2: { inv Hbs2. } destruct p. destruct (gensym_n s1 (rev l)) eqn:Hgen_l2. *)
        (* destruct (ctx_bind_proj (dcon_to_tag dc cnstrs) r2 (Datatypes.length l) *)
        (*                         (hd 1%positive l3) 0) eqn:Hctx2. *)
        (* destruct (cps_cvt e (rev l3 ++ vars2) k2 s2 cnstrs) eqn:Hcvt_e2. *)
        (* 2: { inv Hbs2. } destruct p. inv Hbs2. *)
        (* eapply preord_exp_case_cons_compat. *)
        (* + admit. *)
        (* + admit. *)
        (* + admit. *)
        (* + admit. *)
        (* + eassumption. *)
        (* + admit. *)
        (* + eapply IHbs; eassumption. *)
    Admitted.

    Lemma cps_cvt_val_alpha_equiv :
      forall k, cps_cvt_val_alpha_equiv_statement k.
    Proof.
    Admitted.
      
    
    Inductive StrictlyIncreasing' : list positive -> Prop :=
    | SInc_nil : StrictlyIncreasing' []
    | SInc_cons1 a : StrictlyIncreasing' [a]
    | SInc_consn a b l :
        StrictlyIncreasing' (b :: l) ->
        (a < b)%positive  ->
        StrictlyIncreasing' (a :: b :: l).

    Definition StrictlyIncreasing l :=
      Sorted (fun p1 p2 => (p1 < p2)%positive) l.

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

   (*  Definition cps_cvt_exp_alpha_equiv k := *)
(*       forall e e1 e2 k1 k2 vars1 vars2 rho1 rho2 next1 next2 next3 next4, *)
(*         cps_cvt e vars1 k1 next1 cnstrs = Some (e1, next2) -> *)
(*         cps_cvt e vars2 k2 next3 cnstrs = Some (e2, next4) -> *)
(*         NoDup vars1 -> *)
(*         ~(k1 \in (FromList vars1)) -> *)
(*         List.length vars1 = List.length vars2 -> *)
(*         Forall (fun v => lt_symgen v next1) vars1 -> *)
(*         preord_env_P_inj cenv PG (k1 |: FromList vars1) k *)
(*                          (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 -> *)
(*         preord_exp cenv P1 PG k (e1, rho1) (e2, rho2). *)

(*     Definition cps_cvt_exps_alpha_equiv k := *)
(*       forall es es1 es2 k1 k2 vars1 vars2 rho1 rho2 next1 next2 next3 next4, *)
(*         cps_cvt_exps es vars1 k1 nil next1 cnstrs = Some (es1, next2) -> *)
(*         cps_cvt_exps es vars2 k2 nil next3 cnstrs = Some (es2, next4) -> *)
(*         NoDup vars1 -> *)
(*         ~(k1 \in (FromList vars1)) -> *)
(*         List.length vars1 = List.length vars2 -> *)
(*         Forall (fun v => lt_symgen v next1) vars1 -> *)
(*         preord_env_P_inj cenv PG (k1 |: FromList vars1) k *)
(*                          (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 -> *)
(*         preord_exp cenv P1 PG k (es1, rho1) (es2, rho2).  *)

(*     Definition cps_cvt_efnlst_alpha_equiv k := *)
(*       forall efns fdefs1 fdefs2 k1 k2 vars1 vars2 nlst1 nlst2 rho1 rho2 *)
(*              next1 next2 next3 next4, *)
(*         cps_cvt_efnlst efns vars1 nlst1 next1 cnstrs = Some (fdefs1, next2) -> *)
(*         cps_cvt_efnlst efns vars2 nlst2 next3 cnstrs = Some (fdefs2, next4) -> *)
(*         NoDup vars1 -> *)
(*         ~(k1 \in (FromList vars1)) -> *)
(*         List.length vars1 = List.length vars2 -> *)
(*         Forall (fun v => lt_symgen v next1) vars1 -> *)
(*         preord_env_P_inj cenv PG (k1 |: FromList vars1) k *)
(*                          (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 -> *)
(*         preord_env_P_inj cenv PG (k1 |: (FromList vars1 :|: FromList nlst1)) k *)
(*                          (id {k1 ~> k2 } <{ vars1 ~> vars2 }> <{ nlst1 ~> nlst2}>) *)
(*                          (def_funs fdefs1 fdefs1 rho1 rho1) *)
(*                          (def_funs fdefs2 fdefs2 rho2 rho2). *)

(*     (* Definition cps_cvt_branches_alpha_equiv k := *) *)
(*     (*   forall bs bs1 bs2 k1 k2 r1 r2 vars1 vars2 rho1 rho2 next1 next2 next3 next4, *) *)
(*     (*     cps_cvt_branches bs vars1 k1 r1 next1 cnstrs = Some (bs1, next2) -> *) *)
(*     (*     cps_cvt_branches bs vars1 k2 r2 next3 cnstrs = Some (bs2, next4) -> *) *)
(*     (*     NoDup vars1 -> *) *)
(*     (*     ~(k1 \in (FromList vars1)) -> *) *)
(*     (*     List.length vars1 = List.length vars2 -> *) *)
(*     (*     Forall (fun v => lt_symgen v next1) vars1 -> *) *)
(*     (*     preord_env_P_inj cenv PG (k1 |: FromList vars1) k *) *)
(*     (*                      (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 -> *) *)
(*     (*     Forall2 (fun '(c1, e1) '(c2, e2) => *) *)
(*     (*                c1 = c2 /\ preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) *) *)
(*     (*             bs1 bs2. *) *)

(*     Definition cps_cvt_branches_alpha_equiv k := *)
(*       forall bs bs1 bs2 k1 k2 r1 r2 vars1 vars2 x1 x2 rho1 rho2 *)
(*              next1 next2 next3 next4, *)
(*         cps_cvt_branches bs vars1 k1 r1 next1 cnstrs = Some (bs1, next2) -> *)
(*         cps_cvt_branches bs vars2 k2 r2 next3 cnstrs = Some (bs2, next4) -> *)
(*         NoDup vars1 -> *)
(*         ~(k1 \in (FromList vars1)) -> *)
(*         List.length vars1 = List.length vars2 -> *)
(*         Forall (fun v => lt_symgen v next1) vars1 -> *)
(*         preord_env_P_inj cenv PG (k1 |: FromList vars1) k *)
(*                          (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 -> *)
(*         preord_var_env cenv PG k rho1 rho2 x1 x2 -> *)
(*         preord_exp cenv P1 PG k (Ecase x1 bs1, rho1)  (Ecase x2 bs2, rho2). *)

(*     Definition cps_cvt_alpha_equiv_statement k := *)
(*       cps_cvt_exp_alpha_equiv k /\ *)
(*       cps_cvt_exps_alpha_equiv k /\ *)
(*       cps_cvt_efnlst_alpha_equiv k /\ *)
(*       cps_cvt_branches_alpha_equiv k. *)

(*     Definition cps_cvt_val_alpha_equiv_statement k := *)
(*       forall v v1 v2 next1 next2 next3 next4, *)
(*         cps_cvt_val v next1 cnstrs = Some (v1, next2) -> *)
(*         cps_cvt_val v next3 cnstrs = Some (v2, next4) -> *)
(*         preord_val cenv PG k v1 v2. *)

(*     Opaque preord_exp'. *)

(*     Lemma cps_cvt_env_alpha_equiv : *)
(*       forall vs k vs1 vs2 next1 next2 next3 next4, *)
(*         cps_cvt_val_alpha_equiv_statement k -> *)
(*         cps_cvt_env vs next1 cnstrs = Some (vs1, next2) -> *)
(*         cps_cvt_env vs next3 cnstrs = Some (vs2, next4) -> *)
(*         Forall2 (preord_val cenv PG k) vs1 vs2. *)
(*     Proof. *)
(*       induction vs; intros k vs1 vs2 next1 next2 next3 next4 IH Hcvt1 Hcvt2. *)
(*       - simpl in Hcvt1, Hcvt2. inv Hcvt1. inv Hcvt2. econstructor. *)
(*       - simpl in Hcvt1. *)
(*         destruct (cps_cvt_val a next1 cnstrs) eqn:Hval1. 2: { inv Hcvt1. }  *)
(*         destruct p. destruct (cps_cvt_env vs s cnstrs) eqn:Henv1. 2: { inv Hcvt1. }  *)
(*         destruct p. inv Hcvt1. *)
(*         simpl in Hcvt2. *)
(*         destruct (cps_cvt_val a next3 cnstrs) eqn:Hval2. 2: { inv Hcvt2. } *)
(*         destruct p. destruct (cps_cvt_env vs s0 cnstrs) eqn:Henv2. 2: { inv Hcvt2. } *)
(*         destruct p. inv Hcvt2. *)
(*         econstructor. *)
(*         + eapply IH. eassumption. eassumption. *)
(*         + eapply IHvs. eassumption. eassumption. eassumption. *)
(*     Qed. *)

(*     Definition leq_symgen :=  *)
(*     fun (v1 : var) (next : symgen) => *)
(*       match next with *)
(*       | SG (v2, _) => (v1 <= v2)%positive *)
(*       end. *)

(*     Definition lt_symgen_compare := *)
(*       fun (next1 : symgen) (next2 : symgen) => *)
(*       match next1, next2 with *)
(*       | SG (v1, _), SG (v2, _) => (v1 <= v2)%positive *)
(*       end. *)

(*     Lemma nth_error_Some_eq_nth : *)
(*       forall l n v, *)
(*         nth_error l n = Some v -> *)
(*         nth l n = v. *)
(*     Proof. *)
(*       induction l; intros n v H. *)
(*       - destruct n. *)
(*         simpl in *. inv H. *)
(*         simpl in *. inv H. *)
(*       - unfold nth. unfold nth_default. destruct n. *)
(*         simpl in *. inv H. reflexivity. *)
(*         simpl in *. rewrite H. reflexivity. *)
(*     Qed.  *)

(*     Lemma cps_cvt_efnlst_find_def : *)
(*       forall fn l1 l2 l3 l4 l1' l3' next1 next2 next3 next4 n f1 f2 tg xs1 e1 *)
(*              na1 efn v1, *)
(*         NoDup l1 -> *)
(*         NoDup l3 -> *)
(*         Datatypes.length l1 = Datatypes.length l3 -> *)
(*         cps_cvt_efnlst fn (l1' ++ l2) l1 next1 cnstrs = Some (f1, next2) -> *)
(*         cps_cvt_efnlst fn (l3' ++ l4) l3 next3 cnstrs = Some (f2, next4) -> *)
(*         (nth_error (efnlst_as_list fn) n) = Some (na1, efn) -> *)
(*         nth_error l1 n = Some v1 -> *)
(*         find_def v1 f1 = Some (tg, xs1, e1) -> *)
(*         exists e2 v2 x1 k1 x2 k2 next5 next6 next7 next8 *)
(*                na1' na2 esrc1, *)
(*           geq_symgen x1 next1 /\ geq_symgen x2 next3 /\ *)
(*           (k1 > x1)%positive /\ (k2 > x2)%positive /\ *)
(*           lt_symgen k1 next5 /\ lt_symgen k2 next7 /\ *)
(*           nth_error l3 n = Some v2 /\ *)
(*           find_def v2 f2 = Some (tg, [k2; x2], e2) /\ *)
(*           xs1 = [k1; x1] /\ *)
(*           efn = Lam_e na1' esrc1 /\ *)
(*           (nth_error (efnlst_as_list fn) n) = Some (na2, (Lam_e na1' esrc1)) /\  *)
(*           cps_cvt esrc1 (x1 :: (l1' ++ l2)) k1 next5 cnstrs = Some (e1, next6) *)
(*           /\ *)
(*           cps_cvt esrc1 (x2 :: (l3' ++ l4)) k2 next7 cnstrs = Some (e2, next8). *)
(*     Proof. *)
(*       induction fn; intros l1 l2 l3 l4 l1' l3' next1 next2 next3 next4 n' *)
(*                            f1 f2 tg xs1 e1 na1 efn v1 *)
(*                            Hdup1 Hdup2 Hlen Hcvt_fn1 Hcvt_fn2 Herror Hnth Hfind. *)
(*       - simpl in Hcvt_fn1. inv Hcvt_fn1. simpl in Hfind. inv Hfind. *)
(*       - simpl in *. *)
(*         destruct (gensym next1 (nNamed "fix_x")) eqn:Hgen_x1. *)
(*         destruct (gensym s (nNamed "fix_k")) eqn:Hgen_k1. *)
(*         destruct e eqn:He1; inv Hcvt_fn1. *)
(*         destruct (cps_cvt e0 (v :: l1' ++ l2) v0 s0 cnstrs) eqn: Hcvt1. *)
(*         2: { inv H0. } destruct p. *)
(*         destruct (cps_cvt_efnlst fn (l1' ++ l2) (tl l1) s1 cnstrs) eqn:Hrec1. *)
(*         2: { inv H0. } destruct p. inv H0. *)
(*         destruct (gensym next3 (nNamed "fix_x")) eqn:Hgen_x2. *)
(*         destruct (gensym s2 (nNamed "fix_k")) eqn:Hgen_k2.  *)
(*         destruct (cps_cvt e0 (v2 :: l3' ++ l4) v3 s3 cnstrs) eqn:Hcvt2. *)
(*         2: { inv Hcvt_fn2. } destruct p. *)
(*         destruct (cps_cvt_efnlst fn (l3' ++ l4) (tl l3) s4 cnstrs) eqn:Hrec2. *)
(*         2: { inv Hcvt_fn2. } destruct p. inv Hcvt_fn2. *)
(*         destruct n' eqn:Hn'. *)
(*         + simpl in *. inv Herror. unfold nth in *. *)
(*           unfold nth_default in *. simpl in *. destruct l1 eqn:Hl1. *)
(*           * destruct l3 eqn:Hl3. *)
(*             -- simpl in *. inv Hnth.  *)
(*             -- simpl in *. inv Hnth. *)
(*           * destruct l3 eqn:Hl3. *)
(*             -- inv Hlen.  *)
(*             -- simpl in *. inv Hnth. *)
(*                rewrite peq_true in *. inversion Hfind. *)
(*                repeat eexists. *)
(*                eapply geq_gensym. eassumption. *)
(*                eapply geq_gensym. eassumption. *)
(*                eapply geq_gensym in Hgen_k1. *)
(*                destruct next1. destruct p. eapply lt_symgen_gensym_2 in Hgen_x1. *)
(*                unfold lt_symgen in Hgen_x1. unfold geq_symgen in Hgen_k1. *)
(*                destruct s. destruct p. zify. omega. *)
(*                5: { rewrite <- H2. eassumption. } *)
(*                5: { eassumption. } *)
(*                admit. *)
(*                eapply lt_symgen_gensym_2. eassumption. *)
(*                eapply lt_symgen_gensym_2. eassumption. *)
(*                rewrite peq_true. reflexivity.  *)
(*         + simpl in *. destruct l1 eqn:Hl1. *)
(*           simpl in Hfind. inv Hnth. *)
(*           destruct l3 eqn:Hl3. inv Hlen. *)
(*           simpl in *. rewrite peq_false in *. *)
(*           inv Hdup1. inv Hdup2. edestruct IHfn. *)
(*           eapply H2. eapply H4. *)
(*           inv Hlen. reflexivity. *)
(*           eassumption.  *)
(*           eassumption. *)
(*           eassumption. *)
(*           eassumption. *)
(*           eassumption. *)
(*           destructAll. *)
(*           repeat eexists; try eauto. admit. admit. *)
(*           rewrite peq_false. eassumption. *)
(*           admit. admit.  *)
(*     Admitted. *)


(*     Lemma cps_cvt_efnlst_nth_error : *)
(*       forall fnl l1 l2 n v f next1 next2, *)
(*         N.to_nat (efnlst_length fnl) = Datatypes.length l1 -> *)
(*         cps_cvt_efnlst fnl l2 l1 next1 cnstrs = Some (f, next2) -> *)
(*         nth_error l1 n = Some v -> *)
(*         exists na e, *)
(* Proof. *)
(*       induction fnl; intros l1 l2 n' v f next1 next2 Hlen Hcvt Hnth. *)
(*       - simpl in *. inv Hcvt. *)
(*         destruct n'. *)
(*         simpl in *. destruct l1. inv Hnth. inv Hlen. *)
(*         simpl in *. destruct l1. inv Hnth. inv Hlen. *)
(*       - destruct l1. destruct n'. *)
(*         inv Hnth. inv Hnth.  *)
(*         simpl in Hcvt. *)
(*         destruct (gensym next1 (nNamed "fix_x")) eqn:Hgen_x. *)
(*         destruct (gensym s (nNamed "fix_k")) eqn:Hgen_k. *)
(*         destruct e eqn:He; inv Hcvt. *)
(*         destruct (cps_cvt e0 (v1 :: l2) v2 s0 cnstrs) eqn:Hcvt. 2: { inv H0. }  *)
(*         destruct p. *)
(*         destruct (cps_cvt_efnlst fnl l2 l1 s1 cnstrs) eqn:Hcvt2. 2: { inv H0. } *)
(*         destruct p. inv H0. *)
(*         simpl. destruct n'. *)
(*         + simpl in *. repeat eexists. *)
(*         + simpl in *. eapply IHfnl. *)
(*           destruct (efnlst_length fnl). simpl in Hlen. *)
(*           rewrite Pos2Nat.inj_1 in Hlen. *)
(*           inv Hlen. simpl. eassumption.  *)
(*           simpl in *. destruct p; try (zify; omega).  *)
(*           eassumption. eassumption. *)
(*     Qed.  *)

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

    Lemma gensym_n_nAnon'_strictlyInc :
      forall n v nenv vars nenv' v',
        gensym_n_nAnon' v nenv n = (vars, nenv', v') ->
        StrictlyIncreasing vars.
    Proof.
      induction n; intros v nenv vars nenv' v' Hgen; unfold StrictlyIncreasing in *.
      - simpl in Hgen. inv Hgen. econstructor.
      - simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon nenv) n) eqn: Hgen2.
        destruct p eqn: Hp.
        inv Hgen. econstructor.
        + eapply IHn. eapply Hgen2.
        + destruct l eqn: Hl.
          econstructor.
          econstructor.
          assert (Heq: v0 = Pos.succ v).
          { unfold gensym_n_nAnon' in Hgen2.
            destruct n eqn: Hn.
            inv Hgen2.
            destruct (
                (fix gensym_n_nAnon' (i : var) (env : name_env) (n : nat)
                     {struct n} :
                   list var * name_env * var :=
                   match n with
                   | 0%nat => ([], env, i)
                   | S n' =>
                     let
                       '(vlst, env'', next_var) :=
                       gensym_n_nAnon' (Pos.succ i) (M.set i nAnon env) n' in
                     (i :: vlst, env'', next_var)
                   end) (Pos.succ (Pos.succ v))
                        (M.set (Pos.succ v) nAnon (M.set v nAnon nenv)) n0
              ) eqn:Hgen.
            destruct p eqn: Hp.
            inv Hgen2. reflexivity. }
          rewrite Heq. zify. lia. 
    Qed.

    Lemma gensym_n_nAnon'_cons :
      forall n vars p p' nenv nenv' v,
        gensym_n_nAnon' p nenv n = (p' :: vars, nenv', v) ->
        exists nenv1, gensym_n_nAnon' (Pos.succ p) nenv (n - 1) = (vars, nenv1, v).
    Proof.
      induction n; intros vars p p' nenv nenv' v Hgen.
      - unfold gensym_n_nAnon' in Hgen. inv Hgen.
      - simpl. rewrite Nat.sub_0_r. unfold gensym_n_nAnon'. 
        destruct n eqn: Hn.
        + unfold gensym_n_nAnon' in Hgen. inversion Hgen.
          eexists. reflexivity. 
        + unfold gensym_n_nAnon' in Hgen.
          destruct (
              (fix gensym_n_nAnon' (i : var) (env : name_env) (n1 : nat) {struct n1} :
                 list var * name_env * var :=
                 match n1 with
                 | 0%nat => ([], env, i)
                 | S n' =>
                   let
                     '(vlst, env'', next_var) :=
                     gensym_n_nAnon' (Pos.succ i) (M.set i nAnon env) n' in
                   (i :: vlst, env'', next_var)
                 end) (Pos.succ (Pos.succ p)) (M.set (Pos.succ p) nAnon nenv) n0
            ) eqn: Hgen2.
          destruct p0 eqn: Hp0.      
    Abort.

    Lemma gensym_n_nAnon_cons :
      forall n v nenv vars a next,
        gensym_n_nAnon (SG (v, nenv)) n = (a :: vars, next) ->
        exists next1, gensym_n_nAnon (SG (Pos.succ v, nenv)) (n - 1) = (vars, next1).
    Proof.
      induction n; unfold gensym_n_nAnon; intros v nenv vars a next Hgen.
      - destruct (gensym_n_nAnon' v nenv 0) eqn: Hgen2.
        destruct p eqn: Hp.
    Abort. 
      
    Lemma gensym_n_nAnon_strictlyInc :
      forall vars next next1 n,
        gensym_n_nAnon next n = (vars, next1) ->
        StrictlyIncreasing vars.
    Proof.
      intros vars. 
      induction vars; intros next next1 n Hgen.
      - unfold StrictlyIncreasing. econstructor.
      - unfold StrictlyIncreasing in *. econstructor.
        + unfold gensym_n_nAnon in Hgen.
          destruct next eqn: Hnext.
          destruct p eqn: Hp.
          destruct (gensym_n_nAnon' v n0 n) eqn: Hgen2.
          destruct p0 eqn: Hp0.
          inv Hgen.
          eapply IHvars. 
          admit.
        + unfold gensym_n_nAnon in Hgen. destruct vars eqn: Hvars.
          econstructor.
          econstructor.
          destruct next eqn: Hnext.
          destruct p eqn: Hp.
          destruct (gensym_n_nAnon' v0 n0 n) eqn: Hgen2.
          destruct p0 eqn: Hp0.
          inv Hgen.
          eapply gensym_n_nAnon'_strictlyInc in Hgen2.
          unfold StrictlyIncreasing in Hgen2.
          inv Hgen2. inv H2. eassumption. 
    Admitted. 


    Lemma geq_gensym :
      forall next1 next2 na v,
        gensym next1 na = (v, next2) ->
        geq_symgen v next1.
    Proof.
      intros next1 next2 na v Hgen.
      destruct next1. simpl in Hgen.
      destruct p. inv Hgen.
      simpl. zify. lia.
    Qed. 

    Lemma lt_symgen_In_lst :
      forall vars next1 next2 na v',
        Forall (fun v => lt_symgen v next1) vars ->
        gensym next1 na = (v', next2) ->
        ~ In var (FromList vars) v'.
    Proof.
      induction vars; intros next1 next2 na v' Hall Hgen.
      - intros Hin. inv Hin.
      - intros Hin.
        inv Hall. 
        unfold lt_symgen in H1.
        destruct next1. destruct p eqn:Hp.
        inv Hin.
        + assert (Hgt: (v' >= v)%positive).
          { eapply geq_gensym in Hgen. simpl in Hgen. eassumption. } 
          zify. lia.
        + eapply IHvars in H. destruct H.
          eassumption. eassumption.
    Qed.

    Lemma lt_symgen_gensym :
      forall n nenv na v next,
        gensym (SG (n, nenv)) na = (v, next) ->
        lt_symgen n next.
    Proof.
      intros n nenv na v next H.
      simpl in H.
      unfold lt_symgen. destruct next. destruct p.
      inv H. zify. lia.
    Qed.

    Lemma lt_symgen_gensym_2 :
      forall next1 next2 v na,
        gensym next1 na = (v, next2) ->
        lt_symgen v next2.
    Proof.
      intros next1 next2 v na H.
      destruct next1. destruct p. simpl in H.
      destruct next2. destruct p. inv H.
      unfold lt_symgen. zify. lia.
    Qed. 

    Lemma lt_lst_symgen_gensym_n' :
      forall n v1 v2 nenv nenv' vars,
        gensym_n_nAnon' v1 nenv n = (vars, nenv', v2) ->
        (v1 <= v2)%positive.
    Proof.
      induction n; intros v1 v2 nenv nenv' vars Hgen.
      - simpl in Hgen. inv Hgen. zify. lia.
      - simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon nenv) n) eqn:Hgen2.
        destruct p eqn:Hp. inv Hgen.
        eapply IHn in Hgen2. zify. lia. 
    Qed. 

    Lemma lt_lst_symgen_gensym_n :
      forall n vars next1 next2,
        gensym_n_nAnon next1 n = (vars, next2) ->
        Forall (fun v => lt_symgen v next2) vars.
    Proof.
      induction n; intros vars next1 next2 Hgen; unfold gensym_n_nAnon in Hgen.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:Hgen2.
        destruct p. simpl in Hgen2. inv Hgen2. inv Hgen.
        econstructor.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:Hgen2.
        destruct p. simpl in Hgen2.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:Hgen3.
        destruct p. inv Hgen2. inv Hgen.
        econstructor.
        + unfold lt_symgen. eapply lt_lst_symgen_gensym_n' in Hgen3.
          zify. lia. 
        + specialize IHn with (next1 := (SG (Pos.succ v, (M.set v nAnon n0)))).
          eapply IHn. unfold gensym_n_nAnon.
          destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n).
          destruct p. inv Hgen3. reflexivity.
    Qed.

    Lemma Forall_lt_symgen_gensym :
      forall vars next1 next2 na v,
        Forall (fun v => lt_symgen v next1) vars ->
        gensym next1 na = (v, next2) ->
        Forall (fun v => lt_symgen v next2) vars.
    Proof.
      induction vars; intros next1 next2 na v Hall Hgen.
      - econstructor.
      - inv Hall. econstructor.
        pose proof lt_symgen_gensym as Hgen2.
        destruct next1. destruct p. eapply Hgen2 in Hgen.  
        unfold lt_symgen in *. destruct next2. destruct p.
        zify. lia.
        eapply IHvars. eassumption. eassumption.
    Qed.

    Lemma Forall_lt_symgen_gensym_n :
      forall vars1 n vars2 next1 next2,
        Forall (fun v => lt_symgen v next1) vars1 ->
        gensym_n_nAnon next1 n = (vars2, next2) ->
        Forall (fun v => lt_symgen v next2) vars1.
    Proof.
      induction vars1; intros n vars2 next1 next2 Hall Hgen.
      - econstructor.
      - econstructor.
        + pose proof lt_lst_symgen_gensym_n as Hgen2.
          inv Hall.
          destruct next1. destruct p. simpl in Hgen.
          destruct (gensym_n_nAnon' v n0 n) eqn:Hgen'. destruct p.
          eapply lt_lst_symgen_gensym_n' in Hgen'.
          inv Hgen. unfold lt_symgen in *. zify. lia. 
        + inv Hall.
          eapply IHvars1. eassumption. eassumption.
    Qed. 

    Lemma gensym_n_nAnon_length_eq :
      forall n next1 next2 next3 next4 l1 l2,
        gensym_n_nAnon next1 n = (l1, next2) ->
        gensym_n_nAnon next3 n = (l2, next4) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      induction n; intros next1 next2 next3 next4 l1 l2 Hgen1 Hgen2;
        unfold gensym_n_nAnon in *.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:H1. destruct p.
        destruct next3. destruct p.
        destruct (gensym_n_nAnon' v1 n1 0) eqn:H2. destruct p.
        simpl in H1, H2. inv H1. inv Hgen1. inv H2. inv Hgen2.
        reflexivity.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:H1. destruct p.
        destruct next3. destruct p.
        destruct (gensym_n_nAnon' v1 n2 (S n)) eqn:H2. destruct p.
        simpl in H1, H2.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:H1'.
        destruct p.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon n2) n) eqn:H2'.
        destruct p.
        inv H1. inv Hgen1.
        inv H2. inv Hgen2.
        simpl. f_equal.
        specialize IHn with (next1 := SG (Pos.succ v, (M.set v nAnon n0)))
                            (next3 := SG (Pos.succ v1, (M.set v1 nAnon n2))).
        eapply IHn.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:H1. destruct p.
        inv H1'. reflexivity.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon n2) n) eqn:H2. destruct p.
        inv H2'. reflexivity.
    Qed.

    Lemma gensym_n'_length_eq :
      forall names v1 v2 v3 v4 nenv1 nenv2 nenv3 nenv4 l1 l2,
        gensym_n' v1 nenv1 names = (l1, nenv2, v2) ->
        gensym_n' v3 nenv3 names = (l2, nenv4, v4) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      induction names; intros v1 v2 v3 v4 nenv1 nenv2 nenv3 nenv4 l1 l2 Hgen1 Hgen2.
      - simpl in Hgen1, Hgen2. inv Hgen1. inv Hgen2. econstructor.
      - simpl in Hgen1, Hgen2.
        destruct (gensym_n' (Pos.succ v1) (M.set v1 a nenv1) names) eqn:H1.
        destruct p.
        destruct (gensym_n' (Pos.succ v3) (M.set v3 a nenv3) names) eqn:H2.
        destruct p.
        inv H1. inv Hgen1. inv H2. inv Hgen2.
        simpl. f_equal.
        eapply IHnames. eassumption. eassumption.
    Qed. 

    Lemma gensym_n_length_eq :
      forall names next1 next2 next3 next4 vars1 vars2,
        gensym_n next1 names = (vars1, next2) ->
        gensym_n next3 names = (vars2, next4) ->
        Datatypes.length vars1 = Datatypes.length vars2.
    Proof.
      destruct names; intros next1 next2 next3 next4 vars1 vars2 Hgen1 Hgen2.
      - destruct next1. destruct p.
        destruct next3. destruct p.
        simpl in Hgen1, Hgen2. inv Hgen1. inv Hgen2.
        econstructor.
      - destruct next1. destruct p. simpl in Hgen1.
        destruct (gensym_n' (Pos.succ v) (M.set v n n0) names) eqn:H1. destruct p.
        destruct next3. destruct p. simpl in Hgen2.
        destruct (gensym_n' (Pos.succ v1) (M.set v1 n n2) names) eqn:H2. destruct p.
        inv H1. inv Hgen1.
        inv H2. inv Hgen2.
        simpl. f_equal.
        eapply gensym_n'_length_eq. eassumption. eassumption.
    Qed. 

    Lemma StrictlyInc_impl_NoDup :
      forall l,
        StrictlyIncreasing l -> NoDup l.
    Proof.
      induction l; intros H.
      - econstructor.
      - inv H. econstructor.
    Abort.

    Lemma Forall_lt_not_In :
      forall l x,
        Forall (fun v => (x < v)%positive) l ->
        ~ List.In x l.
    Proof.
      induction l; intros x Hall.
      - intros Hnot. inv Hnot.
      - intros Hnot. inv Hall. inv Hnot.
        zify. lia.
        unfold not in IHl. eapply IHl. eassumption. eassumption.
    Qed.

    Lemma Forall_lt_gensym_n_nAnon_Pos_succ :
      forall n v v' nenv nenv' vars,
        gensym_n_nAnon' (Pos.succ v) nenv n = (vars, nenv', v') ->
        Forall (fun v' => (v < v')%positive) vars.
    Proof.
      induction n; intros v v' nenv nenv' vars H.
      - simpl in H. inv H. econstructor.
      - simpl in H.
        destruct (gensym_n_nAnon' (Pos.succ (Pos.succ v))
                                  (M.set (Pos.succ v) nAnon nenv) n) eqn:Hgen.
        destruct p eqn:Hp. inv H. econstructor.
        zify. lia.
        eapply IHn in Hgen. eapply All_Forall.Forall_impl.
        eassumption.
        intros x H. simpl in H. zify. lia.
    Qed.

    Lemma Forall_lt_gensym_n_Pos_succ :
      forall nlst v v' nenv nenv' vars,
        gensym_n' (Pos.succ v) nenv nlst = (vars, nenv', v') ->
        Forall (fun v'=> (v < v')%positive) vars.
    Proof.
      induction nlst; intros v v' nenv nenv' vars H.
      - simpl in H. inv H. econstructor.
      - simpl in H.
        destruct (gensym_n' (Pos.succ (Pos.succ v))
                            (M.set (Pos.succ v) a nenv) nlst) eqn:Hgen.
        destruct p. inv H. econstructor.
        zify. lia.
        eapply IHnlst in Hgen. eapply All_Forall.Forall_impl.
        eassumption.
        intros x H. simpl in H. zify. lia.
    Qed. 

    Lemma gensym_n_nAnon_NoDup :
      forall n vars next1 next2,
        gensym_n_nAnon next1 n = (vars, next2) ->
        NoDup vars.
    Proof.
      induction n; intros vars next1 next2 H; unfold gensym_n_nAnon in *.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:Hgen. destruct p.
        simpl in Hgen. inv Hgen. inv H. econstructor.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:Hgen. destruct p.
        simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:Hgen2.
        destruct p. inv Hgen. inv H.
        econstructor. eapply Forall_lt_not_In.
        eapply Forall_lt_gensym_n_nAnon_Pos_succ. eassumption.
        specialize IHn with (next1 := SG (Pos.succ v, (M.set v nAnon n0))).
        eapply IHn. destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n).
        destruct p. inv Hgen2. reflexivity.
    Qed.

    Lemma gensym_n_NoDup :
      forall l next1 next2 vars,
        gensym_n next1 l = (vars, next2) ->
        NoDup vars.
    Proof.
      induction l; intros next1 next2 vars H.
      - destruct next1. destruct p. simpl in H. inv H. econstructor.
      - destruct next1. destruct p. simpl in H.
        destruct (gensym_n' (Pos.succ v) (M.set v a n) l) eqn:Hgen.
        destruct p. inv Hgen. inv H. econstructor.
        eapply Forall_lt_not_In.
        eapply Forall_lt_gensym_n_Pos_succ. eassumption.
        specialize IHl with (next1 := SG ((Pos.succ v), (M.set v a n))).
        eapply IHl. simpl. destruct (gensym_n' (Pos.succ v) (M.set v a n) l).
        destruct p. inv H1. reflexivity.
    Qed. 

    Fixpoint fundefs_to_list (fdefs : fundefs) :=
      match fdefs with
      | Fnil => []
      | Fcons v tg vars e fdefs' => (v, tg, vars, e) :: (fundefs_to_list fdefs')
      end.

    Lemma preord_env_P_inj_set_lists_l_Disjoint S k f rho1 rho2 rho1' xs vs :
      preord_env_P_inj cenv PG S k f rho1 rho2 ->
      set_lists xs vs rho1 = Some rho1' ->
      Disjoint _(FromList xs) S ->
      preord_env_P_inj cenv PG S k f rho1' rho2.
    Proof.
      intros Henv Hnin Hnin' z Hy v' Hget.
      edestruct Henv as [v'' [Hget' Hv]]; eauto.
      erewrite <- set_lists_not_In in Hget. eassumption.
      eassumption. intros Hc. eapply Hnin'. constructor; eauto.
    Qed.

    Lemma preord_env_P_inj_set_lists_r_Disjoint S k f rho1 rho2 rho2' xs vs :
      preord_env_P_inj cenv PG S k f rho1 rho2 ->
      set_lists xs vs rho2 = Some rho2' ->
      Disjoint _ (FromList xs) (image f S) ->
      preord_env_P_inj cenv PG S k f rho1 rho2'.
    Proof.
      intros Henv Hnin Hnin' z Hy v' Hget.
      edestruct Henv as [v'' [Hget' Hv]]; eauto. eexists.
      split. 
      erewrite <- set_lists_not_In. eassumption.
      eassumption. intros Hc. eapply Hnin'. constructor; eauto.
      eapply In_image. eassumption. eassumption.
    Qed.

    
    Lemma f_eq_subdomain_extend_lst
          (A : Type) (S : Ensemble positive) (f f' : positive -> A)
          (xs : list positive) (ys : list A) :
      length xs = length ys -> 
      f_eq_subdomain S f f' ->
      f_eq_subdomain (FromList xs :|: S) (f <{xs ~> ys}>) (f' <{xs ~> ys}>).
    Proof.
      revert A S f f' ys.
      induction xs; intros.
      - simpl. normalize_sets. rewrite Union_Empty_set_neut_l. eassumption.
      - destruct ys; simpl. inv H. inv H. simpl.
        normalize_sets. rewrite <- Union_assoc. eapply f_eq_subdomain_extend. 
        eapply IHxs; eauto.
    Qed.


    (** ** Correctness statements *)
    
    Definition cps_cvt_correct_exp i :=
      forall e v rho vs vnames k x vk e' v' S S',
        eval_env vs e v ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: FromList vnames) S ->
        cps_cvt_rel S e vnames k cnstrs S' e' ->
        cps_val_rel v v' ->
        preord_exp cenv P1 PG i
                   ((Eapp k kon_tag (x::nil)),
                    (M.set x v' (M.set k vk (M.empty cps.val))))
                   (e', (M.set k vk rho)).

    Definition cps_cvt_correct_exps i :=
      forall es es' vs rho vnames k x vk es'' vs' S S',
        Forall2 (fun e v => eval_env vs e v) (exps_to_list es) es' ->
        cps_env_rel vnames vs rho ->
        Disjoint _ (k |: (FromList vnames)) S ->
        Forall2 (fun e e' => cps_cvt_rel S e vnames k cnstrs S' e')
                (exps_to_list es) es'' ->
        Forall2 cps_val_rel es' vs' ->
        Forall2 (fun e' v' =>
                   preord_exp cenv P1 PG i
                       ((Eapp k kon_tag (x::nil)),
                        (M.set x v' (M.set k vk (M.empty cps.val))))
                       (e', (M.set k vk rho)))
                es'' vs'.

    Definition cps_cvt_correct_efnlst i :=
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
                   preord_exp cenv P1 PG i
                       ((Eapp k kon_tag (x::nil)),
                        (M.set x v' (M.set k vk (M.empty cps.val))))
                       (e', (M.set k vk rho)))
                efns'' vs'.

    Definition cps_cvt_correct_branches i :=
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
                   preord_exp cenv P1 PG i
                       ((Eapp k kon_tag (x::nil)),
                        (M.set x v' (M.set k vk (M.empty cps.val))))
                       (e', (M.set k vk rho)))
                bs'' vs'.

    Lemma cps_cvt_correct:
      forall k,
        (cps_cvt_correct_exp k) /\
        (cps_cvt_correct_exps k) /\
        (cps_cvt_correct_efnlst k) /\
        (cps_cvt_correct_branches k).
    Proof.
      intros k. induction k as [k IHk] using lt_wf_rec1. eapply my_exp_ind.
      - 

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

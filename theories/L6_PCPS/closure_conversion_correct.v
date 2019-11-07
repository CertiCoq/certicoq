(* Correctness proof for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.tactics L6.closure_conversion_invariants L6.closure_conversion L6.closure_conversion_util.
From CertiCoq.L6 Require Import cps size_cps cps_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions eval logical_relations_cc.
Require Import compcert.lib.Coqlib.
From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega
                        Sorting.Permutation ArithRing.
Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Section Closure_conversion_correct.

  Variable pr : prims.
  Variable cenv : ctor_env.
  Variable clo_tag : ctor_tag.

  (* Parameterize over the postconditions *)
  (* Currently assume that the bounds are independent from the size of exp and environment for simplicity *)
  (* For the current cost model and L6 transformations that should suffice *)
  Context (boundL : nat (* local steps *) -> relation nat)
          (boundG : nat -> relation (exp * env * nat))
          (bound_refl : forall c n, n <= 7 * c -> boundL n c c)

          (Hbounds_eq : forall i e1 rho1 c1 e2 rho2 c2, boundL 0 c1 c2 <-> boundG i (e1, rho1, c1) (e2, rho2, c2))

          (bound_add_compat : forall A B c c1 c2, B <= 7*A -> (* maximum overhead per step *)
                                             boundL c c1 c2 -> boundL (c + B) (c1 + A) (c2 + A))
          (bound_add_compt_alt : forall c1 c2 m a b, b <= 7 * a -> boundL m c1 c2 -> boundL (m + b) (c1 + a) c2)
          (bound_locals_l : forall c1 c2 n a, boundL n c1 (c2 + a) -> boundL (n + a) c1 c2)
          (bound_locals_r : forall c1 c2 n a, boundL (n + a) c1 c2 ->  boundL n c1 (c2 + a))
          
          (bound_letapp_compat :
             forall c k f1 rho1 rho' rho'' B f' t xs vs e1 e2 rho2 c1 c2 c1' c2' A A',
               A' + 3 <= 7 * A -> (* maximum overhead per step *)
               M.get f1 rho1 = Some (Vfun rho' B f') ->
               find_def f' B = Some (t, xs, e1) ->
               set_lists xs vs (def_funs B B rho' rho') = Some rho'' ->
               boundG (k - 1) (e1, rho'', c1) (e2, rho2, c2) ->
               boundL c c1' c2' ->
               boundL (c + A') (c1 + c1' + A) (c2 + c2' + A + 3))
          (bound_app_compat :
             forall c f1 rho1 rho' rho'' B f' t xs vs e1 c1 c2 A A',
               A' + 3 <= 7 * A -> (* maximum overhead per step *)
               M.get f1 rho1 = Some (Vfun rho' B f') ->
               find_def f' B = Some (t, xs, e1) ->
               set_lists xs vs (def_funs B B rho' rho') = Some rho'' ->
               boundL (c + A') (c1 + A) (c2 + A + 3)).

  
  (** ** Semantics preservation proof *)

  (** We show observational approximation of the final results as well as an
    * upper bound on the concrete execution cost of the translated program *)
  
  (* Short-hands so that we don't have to apply the parameters every time *)
  Definition FV_inv := FV_inv pr cenv clo_tag boundG. 
  Definition Fun_inv := Fun_inv pr cenv clo_tag boundG. 
  Definition GFun_inv := GFun_inv pr cenv clo_tag boundG. 
  Definition closure_env := closure_env pr cenv clo_tag boundG. 
  
  
  (** * Lemmas about the existance of the interpretation of an evaluation context *)
  
  Lemma project_var_ctx_to_rho Scope Funs GFuns σ c Γ FVs x x' C S S' v1 k rho1 rho2 :
    Disjoint _ S (image σ (GFuns \\ Scope)) ->
    project_var clo_tag Scope Funs GFuns σ c Γ FVs S x x' C S' ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    M.get x rho1 = Some v1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hg Hproj HFV HFun HGfun Hget. inv Hproj.
    - eexists; econstructor; eauto.
    - edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      eexists; econstructor; eauto.
      simpl. rewrite Hget2. rewrite Hget1. reflexivity.
      constructor.
    - edestruct HGfun with (c := c) as
          [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]; eauto.
      eexists; econstructor; eauto. reflexivity. 
      subst. econstructor.
      simpl. rewrite M.gso, Hget2.
      rewrite M.gss. reflexivity.
      intros Hc; subst. eapply Hg. constructor.
      now eapply H3. eapply In_image. now constructor; eauto.
      constructor.
    - edestruct HFV as [c' [g [Hgetg [Hleq Hin]]]].
      eapply Forall2_nthN in Hin; eauto.
      destruct Hin as [v2 [Hnth' Hyp]]. destruct FVs; try now inv H2.
      rewrite Hleq in *; try congruence. 
      eexists. econstructor; eauto. constructor. 
  Qed.

  Lemma make_closures_ctx_to_rho B S Γ C σ S' k rho1 rho2 :
    make_closures clo_tag B S Γ C σ S' ->
    unique_functions B ->
    Disjoint _ S (name_in_fundefs B) ->
    ~ In _ (name_in_fundefs B) Γ ->
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ Γ ->
    (forall f, In _ (name_in_fundefs B) f -> exists v, M.get f rho1 = Some v) ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hclo. revert rho1 rho2. induction Hclo; intros rho1 rho2 Hun Hd Hnin HFun Hyp. 
    - eexists; constructor. 
    - destruct (Hyp f) as [v' Hget'].
      now left; eauto.
      edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      now apply not_In_Empty_set.
      now left; eauto. inv Hun.
      edestruct IHHclo as [rho2' Hctx]; [ eassumption | | | | | ]. 
      + eauto with Ensembles_DB.
      + intros Hc; eapply Hnin; right; eauto.
      + eapply Fun_inv_set_not_In_Funs_r_not_Γ with (x := f).
        rewrite Setminus_Empty_set_neut_r.
        intros Hin. eapply make_closures_image_Included in Hclo.
        eapply Hd.  constructor; [| now left; eauto ].
        eapply Hclo. eassumption.
        intros Hc; subst. eapply Hnin. now left; eauto.
        intros x v Hninx Hinx Hget.
        edestruct HFun  with (f0 := x) as
            [vs'' [rho3' [B3' [f3' [rho4' [B4' [f4' [Hget1' [Heq2' [Ηnin2' [Hget2' Happrox']]]]]]]]]]]; eauto.
        now right.
        repeat eexists; eauto.
      + intros. eapply Hyp. right; eauto.
      + eexists. econstructor; eauto.
        simpl. rewrite Hget1, Hget2. reflexivity.
  Qed.
  
  Lemma project_vars_ctx_to_rho Scope Funs GFuns σ c Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
    project_vars clo_tag Scope Funs GFuns σ c Γ FVs S xs xs' C S' ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ -> 
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    get_list xs rho1 = Some vs1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof. 
    revert Scope Funs Γ FVs xs' C S S' vs1 k
           rho1 rho2.
    induction xs;
      intros Scope Funs Γ FVs xs' C S S' vs1 k
             rho1 rho2 HD Hvars HFun HGfun HFV Hget_list.
    - inv Hvars. eexists; econstructor; eauto.
    - inv Hvars. simpl in Hget_list.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate. 
      destruct (get_list xs rho1) eqn:Hget_list1; try discriminate. 
      edestruct project_var_ctx_to_rho with (rho1 := rho1) as [rho2' Hctx1]; eauto.
      eapply Disjoint_Included_r; [| eassumption ].
      now eauto 10 with Ensembles_DB functions_BD. 
      edestruct IHxs with (rho2 := rho2') as [rho2'' Hctx2].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + eassumption.
      + inv Hget_list. intros f v' Hnin Hin Hget.
        edestruct HFun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        repeat eexists; eauto.
        erewrite <- project_var_get; eauto.  intros Hc. eapply HD. now eauto.
        erewrite <- project_var_get; eauto. 
        intros Hin'. eapply HD. constructor. now eauto.
        right. left. eapply In_image. do 2 constructor; eauto.
      + intros x v1 c' Hin Hget. inv Hget_list.
        edestruct HGfun as [rho0 [B1 [f1 [rho3 [B2 [f2 [Heq1 [Hnin [Hget' Hcc]]]]]]]]]; eauto.
        subst.
        repeat eexists; eauto. 
        erewrite <- project_var_get; eauto.
        intros Hin'. eapply HD. constructor; eauto.
        right. left. eapply In_image. right. eauto.
      + edestruct HFV as [c' [g [Hgetg [Hleq Hinv]]]].
        exists c'.  eexists; split; eauto.
        erewrite <- project_var_get; eauto.
        intros Hin. eapply HD. now eauto.
      + eassumption.
      + exists rho2''. eapply ctx_to_rho_comp_ctx_f_r; eassumption.
  Qed.

  (** * Correctness lemmas *)
  
  (** Correctness of [closure_conversion_fundefs]. Basically un-nesting the nested
      induction that is required by the correctness of [Closure_conversion] *) 
  Lemma Closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
        Scope c Γ FVs Funs' GFuns GFuns' GFuns'' σ FVs' :
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e : exp) (rho rho' : env) (e' : exp)
         (Scope Funs GFuns : Ensemble var) σ c (Γ : var) (FVs : list var)
         (C : exp_ctx),
         cc_approx_env_P pr cenv clo_tag Scope m boundG rho rho' ->
         ~ In var (bound_var e) Γ ->
         binding_in_map (occurs_free e) rho ->
         fundefs_names_unique e ->
         injective_subdomain (Funs \\ Scope :|: GFuns) σ ->
         Disjoint var (image σ (Funs \\ Scope :|: GFuns)) (bound_var e) ->
         Fun_inv m rho rho' Scope Funs σ Γ ->
         GFun_inv m rho rho' Scope GFuns σ ->
         FV_inv m rho rho' Scope Funs GFuns c Γ FVs ->
         Closure_conversion clo_tag Scope Funs GFuns σ c Γ FVs e e' C ->
         cc_approx_exp pr cenv clo_tag m (boundL 0) boundG (e, rho) (C |[ e' ]|, rho')) ->
    (* FVs *)
    (occurs_free_fundefs B1 \\ GFuns) <--> (FromList FVs) ->
    (* unique functions *)
    fundefs_names_unique_fundefs B1 ->
    fundefs_names_unique_fundefs B1' ->
    binding_in_map (occurs_free_fundefs B1) rho ->
    GFun_inv k rho rho' Scope GFuns σ ->
    is_gfuns GFuns (name_in_fundefs B1') FVs GFuns'' ->
    add_global_funs GFuns (name_in_fundefs B1) (FromList FVs) GFuns' ->
    (* Closure Conversion *)
    Closure_conversion_fundefs clo_tag (name_in_fundefs B1) GFuns' σ c FVs B1 B2 ->
    Closure_conversion_fundefs clo_tag Funs' GFuns' σ c FVs' B1' B2' ->
    Disjoint _ (image σ (name_in_fundefs B1 :|: GFuns')) (bound_var_fundefs B1) ->
    Disjoint _ (image σ (name_in_fundefs B1')) Scope ->
    Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2) ->
    injective_subdomain (name_in_fundefs B1 :|: GFuns) σ ->
    injective_subdomain (name_in_fundefs B1' :|: GFuns) σ ->
    ~ In _ (image σ GFuns :|: name_in_fundefs B1) Γ ->
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2) Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    FV_inv k rho rho' (Empty_set _) (Empty_set _) GFuns c Γ FVs ->
    Fun_inv k (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho') Scope (name_in_fundefs B1') σ Γ /\
    GFun_inv k (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho') Scope GFuns'' σ.
  Proof.
    revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' GFuns GFuns' GFuns'' FVs' c. 
    induction k as [k IHk] using lt_wf_rec1.
    induction B1'; 
      intros rho rho' B2 B1 B2' Scope Γ FVs Funs' GFuns GFuns' GFuns'' FVs' c
             IHe Hs Hun Hun' Hfv Hgfun Hadd1 Hadd2 Hcc Hcc' Hd Hd'' Hseq Hinj Hinj' Hnin1 Hnin1' Hnin2 Hnin2' Henv.
    - inv Hcc'. 
      (* show the IH for B first *)
      assert (HB1 : Fun_inv k (def_funs B1 B1' rho rho) (def_funs B2 defs' rho' rho') Scope (name_in_fundefs B1') σ Γ /\
                    GFun_inv k (def_funs B1 B1' rho rho) (def_funs B2 defs' rho' rho') Scope (GFuns'' \\ [set v]) σ).
      { eapply IHB1'; eauto. 
        * intros B H. inv H; eauto. specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
          inv Hun'; eauto.
        * eapply is_gfuns_setminus. eassumption. 
        * eapply Disjoint_Included_l; [| eassumption ].
          eapply image_monotonic.  now apply Included_Union_r.
        * eapply injective_subdomain_antimon. eassumption. now sets.
        * intros Hc. apply Hnin1'. simpl; eauto.
        * intros Hc. apply Hnin2'. simpl; eauto. }
      destruct HB1 as [IHF IHG].
      (* Now show each goal separately *)
      split.
      + edestruct Henv as [c' [vs [Hgetg [Hleq Hallg]]]].
        simpl. eapply Fun_inv_set. 
        * eassumption.
        * intros Hc. eapply Hnin2'. subst. left. eauto.          
        * intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
          left. eauto.
        * simpl in Hinj'.
          assert (Hinj'' : injective_subdomain (v |: name_in_fundefs B1') σ). 
          { eapply injective_subdomain_antimon. eauto. sets. }
          eapply injective_subdomain_Union_not_In_image in Hinj''.
          intros Hc. eapply Hinj''. constructor; eauto. eexists; eauto.
          eapply image_monotonic; [| eassumption ]. now sets.
          eapply Disjoint_sym. eapply Disjoint_Singleton_r.
          specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
          inv Hun'; eauto.
        * rewrite def_funs_neq. eassumption.
          intros Hc. eapply Hnin2'. right. eauto.
        * (* Finally show that the added funs ares related *)     
          simpl. rewrite cc_approx_val_eq. 
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.  
          edestruct (@set_lists_length val)
            with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset'].
          eassumption. now eauto.
          edestruct closure_conversion_fundefs_find_def
            as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]; [  |  | eassumption |].
          eapply injective_subdomain_antimon. now eapply Hinj. now sets. eassumption. 
          exists Γ'', xs1. do 2 eexists.
          split. reflexivity. split. eassumption. split.
          simpl. rewrite Hset'. reflexivity.        
          intros Hlt Hall.
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) σ Γ /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) GFuns' σ).
          { eapply IHk with (Funs' := name_in_fundefs B1); try eassumption. 
            - intros. eapply IHe; eauto. omega.
            - eapply GFun_inv_Scope.
              eapply Disjoint_sym.
              eapply Disjoint_Included; [ | | now eapply Hd ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.  
              eapply image_monotonic. eapply Included_trans.
              eapply add_global_funs_included; [| eassumption ]; tci. now sets.
              eapply GFun_inv_monotonic; eauto. omega. 
            - eapply add_global_funs_is_gfuns. eassumption.
            - eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [ | now eapply Hd ] ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]...
              now sets. now sets.
            - sets.
            - eapply FV_inv_monotonic. eassumption. omega. }
          destruct HK as [Hkf Hkg].
          eapply cc_approx_exp_rel_mon with (P1 := boundL 0).
          2:{ intros c1 c2. rewrite Hbounds_eq. eauto. }
          (* Apply IHe *)
          eapply IHe with (Scope := FromList xs1) (GFuns := GFuns' \\ FromList xs1). 
          -- eassumption.
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin''. right; left. eassumption.
          -- intros Hc. apply Hnin''. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- intros B Hin. eapply Hun. left. 
             eapply fun_in_fundefs_funs_in_fundef; eauto.
             eapply find_def_correct. eassumption.
          -- eapply injective_subdomain_antimon. now eapply Hinj.
             eapply Union_Included. eapply Included_Union_preserv_l. now eapply Setminus_Included.
             eapply Included_trans. eapply Setminus_Included.             
             rewrite Union_commut. eapply add_global_funs_included_r. eassumption.
          -- eapply Disjoint_Included;[ | | eapply Hd ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             rewrite !Union_assoc. now apply Included_Union_r.
          -- (* Fun_inv *)
             eapply Fun_inv_rename with (Γ := Γ). intros Hin. 
             eapply Hnin2. rewrite <- Hseq. eapply image_monotonic; [| eassumption ].
             now apply Setminus_Included.
             intros Hin. eapply Hnin''. left. rewrite image_Union. left; eassumption. 
             eapply Fun_inv_set_lists_In_Scope_l; [ now apply Included_refl | | now eauto ].
             eapply Fun_inv_set_lists_In_Scope_r; [ now apply Included_refl | | | eassumption ].
             eapply Disjoint_Included_r; 
               [| eapply Disjoint_Included_l;
                  [ apply image_monotonic; now apply Setminus_Included | eapply Disjoint_Included_l; [| now apply Hd ]]].
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             right; eauto. now sets. eapply Fun_inv_reset; eauto.
          -- eapply GFun_inv_set_not_In_GFuns_r.
             intros Hc. eapply Hnin''.
             left. eapply image_monotonic; [| eassumption ]. sets.
             eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ].
             now sets.
             eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ].
             eapply Disjoint_sym.
             eapply Disjoint_Included; [ | | now eapply Hd ].
             eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.
              eapply image_monotonic. sets.
              eapply GFun_inv_antimon. eassumption. sets.
          -- do 2 eexists. split. rewrite M.gss. reflexivity.
             split. intros. reflexivity.
             eapply Forall2_monotonic; [| eassumption ].
             intros x v1 Hyp v2 Hnin3 Hnin4 Hnin5 Hget'.  
             erewrite <- set_lists_not_In in Hget'; [| now eauto | eassumption ].
             erewrite def_funs_neq in Hget'.
             eapply cc_approx_val_monotonic. eapply Hyp; eauto.
             now eapply not_In_Empty_set. now eapply not_In_Empty_set.
             intros Hnin. eapply Hnin5. constructor; eauto.
             eapply add_global_funs_included in Hnin; [| | eassumption ]; tci. inv Hnin; eauto.
             contradiction. omega. eassumption.
          -- destruct FVs.
             eapply Closure_conversion_tag_inv. eassumption.
             rewrite Hleq. eassumption. congruence.
      + edestruct Henv as [c' [vs [Hgetg [Hleq Hallg]]]].
        simpl. eapply GFun_inv_set. 
        * eassumption.
        * intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
          left. eauto.
        * assert (Hda: Disjoint _ (image σ (GFuns'' \\ [set v])) [set (σ v)]).
          { rewrite <- image_Singleton. eapply injective_subdomain_Union_not_In_image; sets.
            eapply injective_subdomain_antimon; [ eassumption |  ].
            rewrite <- Union_Setminus; tci. eapply Union_Included; sets.
            eapply Included_trans. eapply is_gfuns_included_r; eauto; tci.
            sets. }
          intros Hc. eapply Hda. constructor; eauto.
        * (* Finally show that the added funs ares related *)     
          simpl. intros c'' Hin. rewrite cc_approx_val_eq.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.  
          edestruct (@set_lists_length val)
            with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset'].
          eassumption. now eauto.
          edestruct closure_conversion_fundefs_find_def
            as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]; [  |  | eassumption |]. 
          eapply injective_subdomain_antimon. now eapply Hinj. now sets. eassumption. 
          exists Γ'', xs1. do 2 eexists.
          split. reflexivity. split. eassumption. split.
          simpl. rewrite Hset'. reflexivity.        
          intros Hlt Hall.
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) σ Γ /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) GFuns' σ).
          { eapply IHk with (Funs' := name_in_fundefs B1); try eassumption. 
            - intros. eapply IHe; eauto. omega.
            - eapply GFun_inv_Scope.
              eapply Disjoint_sym.
              eapply Disjoint_Included; [ | | now eapply Hd ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.  
              eapply image_monotonic. eapply Included_trans.
              eapply add_global_funs_included; [| eassumption ]; tci. now sets.
              eapply GFun_inv_monotonic; eauto. omega. 
            - eapply add_global_funs_is_gfuns. eassumption.
            - eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [ | now eapply Hd ] ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]...
              now sets. now sets.
            - sets.
            - eapply FV_inv_monotonic. eassumption. omega. }
          destruct HK as [Hkf Hkg].
          assert (Hgfun' : GFun_inv j rho1' (M.set Γ'' (Vconstr c'' []) rho2') (FromList xs1) 
                                    (GFuns' \\ FromList xs1) σ). 
          { eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply Hnin''.
            left. eapply image_monotonic; [| eassumption ]. sets.
            eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ].
            now sets.
            eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ].
            eapply Disjoint_sym.
            eapply Disjoint_Included; [ | | now eapply Hd ].
            eapply Included_trans;
              [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
            now sets.
            eapply image_monotonic. sets.
            eapply GFun_inv_antimon. eassumption. sets. }
          eapply cc_approx_exp_rel_mon with (P1 := boundL 0).
          2:{ intros c1 c2. rewrite Hbounds_eq. eauto. }          
          (* Apply IHe *) 
          eapply IHe with (Scope := FromList xs1) (GFuns := GFuns' \\ FromList xs1). 
          -- eassumption.
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin''. right; left. eassumption.
          -- intros Hc. apply Hnin''. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- intros B Hin'. eapply Hun. left. 
             eapply fun_in_fundefs_funs_in_fundef; eauto.
             eapply find_def_correct. eassumption.
          -- eapply injective_subdomain_antimon. now eapply Hinj.
             eapply Union_Included. eapply Included_trans. eapply Setminus_Included.
             eapply Included_Union_l. 
             eapply Included_trans. eapply Setminus_Included.
             rewrite Union_commut. eapply add_global_funs_included_r. eassumption.
          -- eapply Disjoint_Included;[ | | eapply Hd ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             rewrite !Union_assoc. now apply Included_Union_r.
          -- (* Fun_inv *)              
            eapply Fun_inv_from_GFun_inv; [ | eassumption | rewrite M.gss; reflexivity ].
            destruct Hadd1 as [[Ha1 Ha2] | [Ha1 Ha2]]; subst.
            ** inv Hadd2. sets. exfalso. eapply H. normalize_sets. reflexivity.
            ** exfalso. eapply Ha2. eassumption. now left.
          -- eassumption.
          -- do 2 eexists. split; [| split; [| constructor ]]. rewrite M.gss. reflexivity.
             eauto.
          -- destruct Hadd1 as [ [Heq He2] | [Heq1 He2] ]; subst.
             eapply Closure_conversion_tag_inv. eassumption.
             exfalso. eapply He2. eassumption. now left.
    - split. intros f v Hnin Hin Hget. now inv Hin.
      inv Hcc'. simpl. eapply GFun_inv_antimon.
      eassumption. 
      eapply Included_trans. eapply is_gfuns_included_r; eauto; tci.
      sets.
  Qed.

  
  (** Correctness of [project_var] *)
  Lemma project_var_correct k rho1 rho2 rho2' Scope GFuns Funs σ c Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs GFuns σ c Γ FVs S x x' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ])))  ->
    ~ In _ S' x' /\
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x'.
  Proof.
    intros Hproj Hcc Hfun Hgfun Henv Hctx Hd.
    inv Hproj.
    - inv Hctx. repeat split; eauto. intros Hc. eapply Hd; eauto.
    - inv Hctx. inv H9.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. eauto.
      + (* TODO : make lemma *) 
        intros f v Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | now intros Heq; subst; eapply Hd; eauto ].
        rewrite M.gso. eassumption. 
        intros Hc. subst; eapply Hd; constructor; eauto. right; left.
        eexists. split; eauto. left. constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto. right; left.
        eapply image_monotonic; eauto. sets. 
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        simpl in H8. rewrite Hget2 in H8; inv H8.
        rewrite Hget1 in H3; inv H3. eassumption.
    - inv Hctx. inv H11. inv H10. inv H13. repeat split. 
      + intros Hc. inv Hc. eapply H4; eauto.
      + eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. constructor. eapply H3. now sets. 
        intros Hc. eapply Hd. constructor. eapply H2. now sets.
      + eapply Fun_inv_set_not_In_Funs_r_not_Γ.
        intros Hc. eapply Hd. constructor; eauto. right. left. eapply image_monotonic; eauto. now sets.
        intros Hc. subst. eapply Hd; eauto.
        eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ].
        intros Hc. subst. eapply Hd; eauto. constructor.
        now eapply H3. right. left. eapply image_monotonic; eauto.  sets.
        intros Hc1. subst. eapply Hd; eauto. constructor. eapply H3. sets.
      + intros f v c1 Hin Hget.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Heq2 [Hget2 Happrox]]]]]]]]]; eauto.
        simpl in H12.
        subst. repeat eexists; eauto.
        rewrite M.gso. 2:{ intros Heq; subst. eapply Hd. constructor; eauto. right. left. 
                           eapply In_image. sets. }
        rewrite M.gso. eassumption.  
        intros Hc. subst; eapply Hd; constructor. eapply H3. right; left.
        eexists. split; [| now eauto ]. now sets. 
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eapply FV_inv_set_r. intros Heq; subst; eapply Hd; eauto. constructor. 
        eapply H3. now sets. eassumption. 
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Heq2 [Hget2 Happrox]]]]]]]]]; eauto.
        subst. simpl in H12.
        rewrite !M.gss, !M.gso in H12. rewrite Hget2 in H12. inv H12.
        eassumption. intros Hc. subst. eapply Hd. constructor.
        eapply H3; eauto. right. left. eapply In_image. now sets.
    - inv Hctx. inv H13.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.        
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. eauto.
      + intros f' v' Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | now intros Heq; subst; eapply Hd; eauto ].
        rewrite M.gso. eassumption. 
        intros Hc. subst; eapply Hd; constructor; eauto. right; left.
        eexists. split; [| now eauto ]. left; constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto. right; left.
        eapply image_monotonic; eauto. sets.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Henv as [g [ce [Hgetg [Hc Hinv]]]].
        repeat subst_exp. eapply Forall2_nthN' in Hinv; eauto. 
  Qed.
  
  (** Correctness of [project_vars] *)
  Lemma project_vars_correct k rho1 rho2 rho2'
        Scope Funs GFuns σ c Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs GFuns σ c Γ FVs S xs xs' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->        
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->   
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    (forall vs,
       get_list xs rho1 = Some vs ->
       exists vs', get_list xs' rho2' = Some vs' /\
              Forall2 (cc_approx_val pr cenv clo_tag k boundG) vs vs').
  Proof.
    revert k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S.
    induction xs;
      intros k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S Hproj Hcc Hfun Hgfuns Henv Hctx Hd.
    - inv Hproj. inv Hctx. repeat split; eauto. 
      eexists. split. reflexivity. 
      inv H. now constructor. 
    - inv Hproj.
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_correct in Hctx1; eauto.
      destruct Hctx1 as [Hnin [Hcc1 [Hfun1 [Hgfun1 [Henv1 Hcc_var]]]]].
      edestruct IHxs as [Hcc2 [Hfun2 [Hgfun2 [Henv2 Hyp]]]]; eauto. 
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included; eassumption.
      repeat split; eauto. intros vs Hget. 
      simpl in Hget. destruct (M.get a rho1) eqn:Hget'; try discriminate. 
      destruct (get_list xs rho1) eqn:Hget_list; try discriminate.
      inv Hget. edestruct Hyp as [vs' [Hget_list' Hall]]; [ reflexivity |].
      edestruct Hcc_var as [v' [Hget''' Hcc''']]; eauto.
      eexists. split; eauto. simpl. rewrite Hget_list'. 
      erewrite <- project_vars_get; eauto. rewrite Hget'''. reflexivity.
  Qed.
  


  (** Correctness of [make_closures] *)
  Lemma make_closures_correct k rho1 rho2 rho2' B S Γ' C σ S' Scope Funs GFuns FVs c Γ :
    make_closures clo_tag B S Γ' C σ S' ->

    unique_functions B ->   
    ~ In _ (name_in_fundefs B) Γ ->
    ~ In _ (name_in_fundefs B) Γ' ->
    Included _ (name_in_fundefs B) Scope ->
    Disjoint _ S (name_in_fundefs B) ->
    Disjoint _ (image σ GFuns) (name_in_fundefs B) ->

    cc_approx_env_P pr cenv clo_tag (Setminus _ Scope (name_in_fundefs B)) k boundG rho1 rho2 ->
    
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->  
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ Γ' ->
    GFun_inv k rho1 rho2 (Empty_set _) GFuns σ ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    
    ctx_to_rho C rho2 rho2' ->
    
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hmake. revert k rho1 rho2 rho2' Scope Funs GFuns FVs Γ.
    induction Hmake;
      intros k rho1 rho2 rho2' Scope Funs GFuns FVs Γ1 Hun Hnin1 Hnin2
             Hsub Hd Hd' Hcc Hfun HGfun Hfun' HGfun' Henv Hctx.
    - inv Hctx. repeat split; eauto. simpl in Hcc.
      eapply cc_approx_env_P_antimon; eauto. sets.
    - eapply ctx_to_rho_comp_ctx_l in Hctx; [| apply Constr_cc; constructor ].
      destruct Hctx as [rho2'' [Hctx1 Hctx2]].
      inv Hctx1. inv H7. inv Hun.
      edestruct IHHmake with (Scope := Scope) (GFuns := GFuns)
        as [Hcc1 [Hfun1 [Hgfun1 Henv1]]];
        [ eassumption | | | | | | | | | | | | eassumption | ]. 
      + intros Hc. eapply Hnin1. right. now apply Hc. 
      + intros Hc. eapply Hnin2. right. now apply Hc.
      + eapply Included_trans; [| eassumption ]. sets.
      + sets. 
      + eapply Disjoint_Included; [| | eapply Hd' ]. sets. sets.
      + eapply cc_approx_env_P_antimon;
          [| now apply (@Included_Union_Setminus _ _ (Singleton var f) _) ]. 
        eapply cc_approx_env_P_union.
        eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_antimon. eassumption.
        simpl. now sets. intros Hc. inv Hc; eauto.
        intros x Hin v Hget. inv Hin.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
          [| | eassumption |]. now apply not_In_Empty_set. now left.
        eexists. split. now rewrite M.gss. subst.
        simpl in H6. rewrite Hget1, Hget2 in H6. inv H6.
        eassumption.
      + eapply Fun_inv_set_In_Scope_r_not_Γ ; [| | eassumption ].
        * eapply Hsub. now left.
        * intros Hc; subst. eapply Hnin1. left; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eapply GFun_inv_antimon; try eassumption ]; simpl; sets.
        intros Hc; subst. eapply Hd'. constructor; eauto.
        now left.
      + intros f'' v Hnin Hin Hget.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
          [| | eassumption |]. now apply not_In_Empty_set. now right.
        subst. repeat eexists; eauto. 
        rewrite M.gso. eassumption. 
        intros Hc; subst. eapply Hnin2. now left; eauto.
        rewrite M.gso. eassumption.
        intros Hc; subst.
        eapply make_closures_image_Included in Hmake.
        eapply Hd. constructor; [| now left; eauto ].
        eapply Hmake. eexists; eauto.
      + intros f'' v Hnin Hin Hget. 
        edestruct HGfun' as
            [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]];
          [| eassumption |]; eauto.
        repeat eexists; eauto.
        rewrite M.gso. eassumption. 
        intros Hc; subst. eapply Hd'. constructor.
        eapply In_image. eassumption. now left.
      + eapply FV_inv_set_r.
        intros Hc; subst. eapply Hnin1. left; eauto. eassumption.
      + repeat split; eauto.
  Qed. 
  

  (* TODO move *)

  Lemma mult_le_n n m :
    1 <= m ->
    n <= n * m.
  Proof.
    rewrite Nat.mul_comm.
    edestruct mult_O_le; eauto. omega.
  Qed.

  Lemma plus_le_mult  (a1 a2 b1 b2 b3 : nat) :
    b3 <= a1 ->
    1 <= b2 ->
    a2 <= b1 * b3 ->
    a1 + a2 <= (1 + b1) * a1 * b2.
  Proof.
    intros.
    rewrite <- mult_assoc, NPeano.Nat.mul_add_distr_r.
    eapply plus_le_compat.
    - simpl. rewrite <- plus_n_O.
      now eapply mult_le_n.
    - eapply le_trans. eapply le_trans. eassumption.
      eapply mult_le_compat. eauto. eassumption.
      rewrite mult_assoc. eapply mult_le_n. eassumption.
  Qed.
  
  Context
    (bound_locals_add : forall n c1 c2 c c0 , c <= 4 (* the max overhead of cc per step *) ->
                                       1 <= c0 ->
                                       boundL n c1 c2 -> boundL (n + c) (c1 + c0) (c2 + c0)).
  

  Lemma Ecase_correct k rho1 rho2 rho2' C x x' c e e' l l' :
    ctx_to_rho C rho2 rho2' ->
    sizeOf_exp_ctx C <= 4 ->
    Forall2 (fun p1 p2 : ctor_tag * exp => fst p1 = fst p2) l l' ->
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x' ->
    cc_approx_exp pr cenv clo_tag k (boundL 0)
                  boundG (e, rho1) (e', rho2') ->
    cc_approx_exp pr cenv clo_tag k (boundL 0)
                  boundG (Ecase x l, rho1) (C |[ Ecase x' l' ]|, rho2) ->
    cc_approx_exp pr cenv clo_tag k (boundL 0)
                  boundG (Ecase x ((c, e) :: l), rho1)
                  (C |[ Ecase x' ((c, e') :: l') ]|, rho2).
  Proof.
    intros Hctx Hleq Hall Henv Hcc1 Hcc2.
    eapply ctx_to_rho_cc_approx_exp.
    - intros. eapply bound_locals_r. eassumption.
    - eassumption.
    - eapply cc_approx_exp_case_cons_compat; try eassumption;
        [ | | eapply cc_approx_exp_ctx_to_rho; try eassumption ].
      + intros. eapply bound_locals_add; eauto.
      + intros. rewrite plus_comm. eapply bound_add_compat; eauto. omega.
      + intros. eapply bound_locals_l; eauto.
  Qed.


  (* Axiom about prims. Currently assuming that they do not return functions *)
  Parameter primAxiom :
    forall f f' vs v k,
      M.get f pr = Some f' ->
      f' vs = Some v ->
      sizeOf_val k v = 0.

  (* TODO move *)
  Lemma Disjoint_In_l {A} (s1 s2 : Ensemble A) x :
    Disjoint _ s1 s2 ->
    x \in s1 ->
          ~ x \in s2.
  Proof.
    intros Hd Hin Hc. eapply Hd. constructor; eauto.
  Qed.


  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct k rho rho' e e' Scope Funs GFuns σ c Γ FVs C :
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain (Funs \\ Scope :|: GFuns) σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Funs \\ Scope :|: GFuns)) (bound_var e) ->
    (* [Fun] invariant *)
    Fun_inv k rho rho' Scope Funs σ Γ ->
    (* Free variables invariant *)
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    (* Global functions invariant *)
    GFun_inv k rho rho' Scope GFuns σ ->
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs GFuns σ c Γ FVs e e' C ->
    cc_approx_exp pr cenv clo_tag k (boundL 0) boundG (e, rho) (C |[ e' ]|, rho').
  Proof with now eauto with Ensembles_DB.
    revert k e rho rho' e' Scope Funs GFuns σ c Γ FVs C.
    induction k as [k IHk] using lt_wf_rec1. intros e.
    revert k IHk; induction e using exp_ind';
      intros k IHk rho1 rho2 e' Scope Funs GFuns σ c' Γ FVs C Happrox Hnin HFVs Hun Hinj Hd Hfun Hgfun Henv Hcc.
    - (* Case Econstr *)      
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4*length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_constr_compat with (S0 := boundL 0).
        * eapply Forall2_cc_approx_var_env; eauto.
        * intros. eapply bound_add_compat. omega. eassumption.
        * intros vs1 vs2 Hget Hall.
          { eapply IHe; [ | | | | | | | | | | eassumption ].
            * eauto.
            * eapply cc_approx_env_P_extend with (v2 := Vconstr t vs2).
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              rewrite cc_approx_val_eq. constructor; eauto.
              eapply logical_relations.Forall2_Forall2_asym_included; eauto. (* TODO fix dependency *)
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Econstr_Included. 
            * intros f Hfin. eauto.
            * eapply injective_subdomain_antimon; eauto. sets. 
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              intros Heq; subst. now eauto.
              eapply Fun_inv_mon; [ | now eauto ]. 
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              now intros Hc; inv Hc; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor.
              rewrite image_Union. right. eapply image_monotonic; eauto...
              normalize_bound_var... sets.
              eapply GFun_inv_Scope_extend; sets.
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
              eapply GFun_inv_antimon; sets. } 
    - (* Case [Ecase x []] *)
      inv Hcc. inv H12.
      intros v1 c1 Hleq Hstep. inv Hstep. inv H5. 
    - (* Case [Ecase x ((c, p) :: pats] *)
      inv Hcc.
      inversion H12 as [ | [c1 p1] [c2 p2] l1 l2 [Heq [C' [e' [Heq' Hcc]]]] Hall ];
        simpl in Heq, Heq'; subst.
      repeat normalize_bound_var_in_ctx.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Disjoint_Included_r; [| eassumption ]. sets.
      now eauto 10 with Ensembles_DB functions_BD.   
      edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [Hget' Happ']; eauto. 
      eapply Ecase_correct; try eassumption.
      + inv H12. eapply Forall2_monotonic; try eassumption.
        firstorder.
      + eapply IHe; try eassumption.
        * now intros Hc; eapply Hnin; eauto.
        * eapply binding_in_map_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor.
        * eauto with Ensembles_DB.
      + eapply IHe0; try eassumption.
        * now eauto.
        * eapply binding_in_map_antimon; [| eassumption ].
          intros x Hin. inv Hin; eauto.
        * intros f Hfin. eapply Hun. inv Hfin. 
          econstructor; eauto. constructor 2. eassumption.
        * eauto with Ensembles_DB.
        * econstructor; eauto.
    - (* Case Eproj *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      now eauto 10 with Ensembles_DB functions_BD.   
      edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [Hget' Happ']; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_proj_compat with (S0 := boundL 0).
        * eassumption.
        * intros. eapply bound_add_compat. omega. eassumption.
        * intros v1' v2' c1 vs1 Hget Hin Hv.
          { eapply IHe; [ now eauto | | | | | | | | | | eassumption ].
            * eapply cc_approx_env_P_extend.
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              eassumption.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Eproj_Included. 
            * intros f Hfin. eauto.
            * eapply injective_subdomain_antimon; eauto; sets.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              intros Heq; subst. now eauto.
              eapply Fun_inv_mon; [ | now eauto ].
              eapply Disjoint_Included; [ | | now apply Hd ].
              normalize_bound_var... sets.
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              now intros Hc; inv Hc; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor.
              rewrite image_Union. right. eapply image_monotonic; eauto...
              normalize_bound_var... sets.
              eapply GFun_inv_Scope_extend; sets.
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
              eapply GFun_inv_antimon; sets. } 
    - (* Case letapp *)
      inv Hcc. intros v1 c2 Hleq Hstep.
      assert (Hstep' := Hstep). inv Hstep'.
      
      assert (Hadm : sizeOf_exp_ctx C <= 4 + 4 * length ys).
      { eapply le_trans. eapply project_vars_sizeOf_ctx_exp; eauto. simpl; omega. }
      
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      simpl. rewrite H5, H7. reflexivity. 
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. 
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H5, H7. reflexivity.
      simpl in Hget'.
      destruct (M.get f' rho2') eqn:Hgetf';
        destruct (get_list ys' rho2') eqn:Hgetvs; try congruence. inv Hget'. 
      inv Happ'.
      assert (Hv := H2). rewrite cc_approx_val_eq in H2.
      destruct v0 as [ | | ]; try contradiction.
      simpl in H2. destruct l0 as [ | ? [|]] ; try contradiction; destruct v0;  try contradiction.      
      destruct v2; try contradiction.
      edestruct H2 with (j := 0) as [Gamma [xs2 [e2' [rho2'' [Heqc [Hfdef [Hset Hlt]]]]]]]; [ | now eauto | now eauto | ].
      eapply Forall2_length. eassumption. subst.

      assert (Hnin' :  ~ In var (f' |: FromList ys') f'').
      { eapply Disjoint_In_l; [| eassumption ]. 
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eassumption. }
        
      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_letapp_compat with (P' := boundL 0) (rho1 := rho1) (f1 := f).
      + simpl. intros. rewrite <-  (Nat.add_0_l (sizeOf_exp_ctx _)).
        eapply bound_letapp_compat. omega. eassumption. eassumption. eassumption.
        eassumption. eassumption. 
      + rewrite (Union_commut [set f']), <- Union_assoc. intros Hc. inv Hc; eauto. inv H. contradiction.
        revert H. eapply Disjoint_In_l; [| eassumption ]. 
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eassumption. 
      + eassumption.
      + intros v3 v4. repeat subst_exp. eexists; split; eauto.
      + eapply Forall2_cc_approx_var_env; eauto.
      + econstructor. eassumption. reflexivity. econstructor. 
        rewrite M.gso. eassumption. now intros Heq; subst; eauto.
        reflexivity. constructor.
      + intros m v4 v5 Hleq' Hvs.
        eapply cc_approx_exp_monotonic.
        eapply IHe with (k := m); [ | | | | | | | | | | eassumption ].
        * intros. eapply IHk; eauto. omega. 
        * eapply cc_approx_env_P_extend; [| eassumption ].
          eapply cc_approx_env_P_set_not_in_P_r.
          eapply cc_approx_env_P_set_not_in_P_r. 
          eapply cc_approx_env_P_antimon.
          eapply cc_approx_env_P_monotonic; [| eassumption ]. omega. now sets.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [ | | eapply H4 ]; sets.
          eapply project_vars_free_set_Included. eassumption.
          
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [ | | eapply H4 ]; sets.
          eapply project_vars_free_set_Included. eassumption.
        * now eauto.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply occurs_free_Eletapp_Included.
        * intros g Hfin. eauto.
        * eapply injective_subdomain_antimon; eauto; sets.
        * eapply Disjoint_Included_r;
            [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
          normalize_bound_var... now eauto with Ensembles_DB.
        * eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
          intros Hc. subst. now eauto.          
          
          eapply Fun_inv_set_not_In_Funs_r_not_Γ.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ].
          eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eassumption. sets.

          eapply Fun_inv_set_not_In_Funs_r_not_Γ.
          eapply Disjoint_In_l; [| eapply H15 ]. 
          eapply Disjoint_Included; [| | eapply H4 ].
          now eauto 10 with Ensembles_DB functions_BD. 
          eapply project_vars_free_set_Included. eassumption.  
          
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eapply H15. now sets.
          
          apply Fun_inv_set_In_Scope_l. now eauto.
          eapply Fun_inv_monotonic. eapply Fun_inv_mon; [| eassumption ]. 
          eapply Disjoint_Included; [ | | now apply Hd ].
          normalize_bound_var... sets. omega.
        * eapply FV_inv_set_In_Scope_l. now constructor.
          eapply FV_inv_set_r. intros Hc. eapply Hnin.
          subst. now eauto.
          eapply FV_inv_set_r; [| eapply  FV_inv_set_r; eauto ].
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eassumption. now sets.
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eapply H15. now sets.
          eapply FV_inv_extend_Scope_GFuns. eapply FV_inv_monotonic. eassumption. omega.
        * eapply GFun_inv_set_not_In_GFuns_l.
          now intros Hc; inv Hc; eauto.
          eapply GFun_inv_set_not_In_GFuns_r.
          intros Hc. eapply Hd. constructor.
          rewrite image_Union. right. eapply image_monotonic; eauto...
          normalize_bound_var... sets.
          eapply GFun_inv_set_not_In_GFuns_r.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ].
          eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.
          eapply GFun_inv_set_not_In_GFuns_r.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ].
          eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.
           
          eapply GFun_inv_Scope_extend; sets. 
          eapply Disjoint_Included; [| | now eapply Hd ].
          normalize_bound_var... sets.          
          eapply GFun_inv_antimon. eapply GFun_inv_monotonic; eauto. sets.
        * omega.
    - (* Case Efun -- the hardest one! *)
      inv Hcc.
      assert (Hsub : FromList FVs' \subset occurs_free_fundefs f2).
      { rewrite <- H1... } 
      specialize (occurs_free_fundefs_cardinality _ _ Hsub H2); intros Hlen.
      assert (Ha : exists vs, get_list FVs' rho1 = Some vs).
      { eapply In_get_list. intros x Hin. eapply HFVs.
        rewrite occurs_free_Efun. left. eauto. }
      destruct Ha as [vs Hget_list].
      (* sizes of evaluation contexts *)
      assert (HC1 : sizeOf_exp_ctx C' <= 4 * (length FVs')) by
          (eapply le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | omega ]).
      assert (HC2 : sizeOf_exp_ctx C0 <= 3 * numOf_fundefs f2) by
          (eapply make_closures_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; [ | eassumption | | | | | ]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' [Hgfun' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto. rewrite <- app_ctx_f_fuse. simpl.
      eapply ctx_to_rho_cc_approx_exp;  try (now intros; eauto).

      assert (Hfuns : Fun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
                                (Empty_set var) (name_in_fundefs f2) σ Γ' /\
                        GFun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2')) (Empty_set _) GFuns' σ
               ).
        { eapply Closure_conversion_fundefs_correct with (c := c'0) ; eauto.
          * intros f Hfin. inv Hfin; eauto.
          * intros f Hfin. inv Hfin; eauto.
          * eapply binding_in_map_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption.
          * eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply H5. constructor; eauto. rewrite image_Union. sets.
            eapply GFun_inv_Scope. sets. eassumption.
          * eapply add_global_funs_is_gfuns. eassumption.
          * eapply Disjoint_Included_l.
            eapply image_monotonic. eapply Included_Union_compat. reflexivity.
            eapply add_global_funs_included_r. eassumption.
            rewrite Union_Same_set; sets. rewrite image_Union.
            eapply Union_Disjoint_l. repeat normalize_bound_var_in_ctx.
            eapply Disjoint_Included; [ | | eapply Hd ]; sets.
            eapply Disjoint_Included; [ | | eapply H7 ]; sets. normalize_bound_var...
            eapply Included_trans;  [ eapply make_closures_image_Included; eassumption |]...                
          * now apply Disjoint_Empty_set_r.
          * eapply closure_conversion_fundefs_Same_set_image. eassumption.
          * eapply make_closures_injective; [| | |  eassumption].
            eapply Disjoint_Included_r; [| eassumption ]. normalize_bound_var.
            eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
            eapply Disjoint_Included_r; [| eassumption ]. rewrite image_Union. sets.
            eapply injective_subdomain_antimon. eassumption. sets. 
          * eapply make_closures_injective; [| | |  eassumption].
            eapply Disjoint_Included_r; [| eassumption ]. normalize_bound_var.
            eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
            eapply Disjoint_Included_r; [| eassumption ]. rewrite image_Union. sets.
            eapply injective_subdomain_antimon. eassumption. sets. 
          * intros Hc. eapply H5. constructor; eauto. rewrite image_Union.
            inv Hc; now eauto.
          * intros Hc. eapply H5. now eauto.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H7. constructor.
            eapply make_closures_image_Included. eassumption.
            eassumption. now eauto.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H7. constructor.
            eapply make_closures_image_Included. eassumption.
            eassumption. now eauto.
          * edestruct Hvar as [vs' [Hget_list' Hall]]; eauto.
            eapply FV_inv_Forall2. eassumption. rewrite M.gss. reflexivity.
            eassumption. }
        destruct Hfuns as [Hf Hg].
        
        eapply ctx_to_rho_cc_approx_exp with (C := Econstr_c Γ' c'0 FVs'' Hole_c);
          try (now intros; eauto).
        econstructor. eassumption. now constructor. 
        simpl sizeOf_exp_ctx. simpl plus. rewrite Nat_as_OT.add_0_r.

        eapply ctx_to_rho_cc_approx_exp with (C := Efun1_c B' Hole_c); try (now intros; eauto).
        simpl. econstructor. now constructor.
        edestruct make_closures_ctx_to_rho
          with (rho2 := def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
          as [rho2'' Htp_rho']; eauto.
        + eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_preserv_l. normalize_bound_var.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
        + intros Hc. eapply H5. now eauto.
        + intros. eapply binding_in_map_def_funs. eassumption. now left.
        + eapply ctx_to_rho_cc_approx_exp; try (now intros; eauto).
          rewrite plus_comm. rewrite <- (Nat_as_OT.add_0_l (_ + _)). rewrite <- !plus_assoc. 
          eapply ctx_to_rho_cc_approx_exp_left_weak with (C := (Efun1_c f2 Hole_c)) (m := 0);
            try (now intros; eauto).
          * constructor; eauto; constructor.
          * { assert (Hcc := H16). eapply Closure_conversion_fundefs_numOf_fundefs in H16. 
              assert (Hlen' : Datatypes.length FVs'' = Datatypes.length FVs') by (symmetry; eapply project_vars_length; eauto).
              simpl sizeOf_exp_ctx. rewrite !Nat_as_OT.add_0_r. rewrite Hlen'. rewrite <- !H16.
              assert (Hlen1 : List.length FVs' <= PS.cardinal (fundefs_fv f2)).
              { rewrite PS.cardinal_spec. eapply Same_set_FromList_length.
                eassumption. rewrite <- FromSet_elements, <- fundefs_fv_correct, <- H1. sets. }
              assert (Hlen2 : PS.cardinal (fundefs_fv B') <= PS.cardinal (fundefs_fv f2)).
              { eapply le_trans with (m := PS.cardinal (@mset (FromList (map σ (PS.elements (fundefs_fv f2)))) _)).
                rewrite !PS.cardinal_spec at 1.  eapply Same_set_FromList_length.
                eapply NoDupA_NoDup. eapply PS.elements_spec2w. 
                rewrite <- !(FromSet_elements (fundefs_fv B')) at 1. rewrite <- FromSet_elements, <- mset_eq.                
                rewrite <- fundefs_fv_correct at 1. eapply Included_trans. 
                eapply Closure_conversion_occurs_free_Included_alt_mut. eassumption.
                intros f1 Hfun1. eapply Hun. inv Hfun1; now eauto.
                rewrite FromList_map_image_FromList. rewrite <- FromSet_elements.
                rewrite <- fundefs_fv_correct at 1. eapply image_monotonic. eapply Included_Intersection_l.
                unfold mset. eapply le_trans. eapply PS_cardinal_map. 
                rewrite !PS.cardinal_spec.
                assert (Heq' : PS.elements (@mset (@FromList positive (PS.elements (fundefs_fv f2))) _) =
                               PS.elements (fundefs_fv f2)).
                { eapply elements_eq. eapply Same_set_From_set. rewrite <- mset_eq, <- FromSet_elements.
                  reflexivity. }
                rewrite Heq'. reflexivity. }
              eapply le_trans with (m := 4 * numOf_fundefs f2 + 6 * PS.cardinal (fundefs_fv f2) + 2).
              omega.
              simpl; omega. }
          * { edestruct make_closures_correct with
                  (Scope := Union var (name_in_fundefs f2) Scope)
                  (Γ := Γ)
                  (rho1 := def_funs f2 f2 rho1 rho1)
                  (rho2 := def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2')
                                    (M.set Γ' (Vconstr c'0 v') rho2'))
                  (GFuns := GFuns') (Funs := Funs)
                as [Hcc'' [Hfun'' [Hgfun''  Henv'']]]. 
              + eauto.
              + eauto.
              + intros Hc. eapply Hnin. constructor.
                now eapply name_in_fundefs_bound_var_fundefs.
              + intros Hc. eapply H5. now eauto.
              + eapply Included_Union_l.
              + eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
                normalize_bound_var...
              + eapply Disjoint_Included_l. eapply image_monotonic. eapply add_global_funs_included_r. eassumption.
                rewrite image_Union. rewrite make_closures_image_eq; eauto.
                eapply Union_Disjoint_l. 
                eapply Disjoint_Included; [| | eapply Hd ].
                eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                normalize_bound_var... sets.
                eapply Disjoint_Included; [| | eapply H7 ].
                eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                normalize_bound_var... sets. 
              + eapply cc_approx_env_P_def_funs_not_In_P_l.
                now eauto with Ensembles_DB.
                eapply cc_approx_env_P_def_funs_not_In_P_r.
                erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); [| eassumption ].
                eapply Disjoint_Included_r.
                now eapply make_closures_image_Included; eauto.
                rewrite Setminus_Union_distr. now eauto 7 with Ensembles_DB.
                eapply cc_approx_env_P_set_not_in_P_r.
                eapply cc_approx_env_P_antimon; [ eassumption |].
                now sets.
                intros Hin. inv Hin. inv H. eauto. eapply H5. eauto.
              + repeat normalize_bound_var_in_ctx. eapply Fun_inv_def_funs.
                * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
                  eapply H7. constructor.
                  eapply make_closures_image_Included. eassumption. eassumption.
                  rewrite !Union_assoc...
                * intros Hc. eapply Hnin. eapply Included_Union_l.
                  now apply name_in_fundefs_bound_var_fundefs.
                * eapply Disjoint_Included; [| | now eapply Hd ]; sets.              
                  apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
                * erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].
                  eapply Disjoint_Included_r;
                    [ eapply make_closures_image_Included; eassumption |].
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | now eapply H7 ]; sets.
                  rewrite image_Union...
                * eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | ].
                  intros Hc. eapply H5. constructor; eauto.
                  right. right. left. rewrite image_Union. left. eassumption.
                  intros Hc. subst. eapply H5. constructor. now eauto.
                  now eauto. now eauto.
              + eapply GFun_inv_fuse with (names := name_in_fundefs f2); tci. 
                * eapply GFun_inv_Scope_extend.
                  eapply Disjoint_Included; [| | now eapply Hd ]; sets.              
                  normalize_bound_var. apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
                  eapply GFun_inv_def_funs_not_In_GFuns_r.
                  erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); eauto.
                  rewrite make_closures_image_eq; eauto.
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | now eapply H7 ]; sets.
                  rewrite image_Union. now eauto 20 with Ensembles_DB.
                  eapply GFun_inv_def_funs_not_In_GFuns_l. sets.
                  eapply GFun_inv_set_not_In_GFuns_r.
                  intros Hc. eapply H5. constructor; eauto. rewrite image_Union.
                  do 2 right. left. right. eapply image_monotonic; [| eassumption ]; sets.
                  eapply GFun_inv_antimon. eassumption. sets.
                * sets.
                * rewrite make_closures_image_eq; eauto.
                  eapply Disjoint_sym.
                  eapply Disjoint_Included; [| | now eapply H7 ]; sets.
                  normalize_bound_var. eapply Union_Included; sets.
                  do 2 apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
              + eassumption.
              + eassumption. 
              + eapply FV_inv_antimonotonic_add_global_funs; [ | | eassumption | ]; tci.
                eapply FV_inv_def_funs.
              * intros Hc. eapply Hnin. constructor. 
                now eapply name_in_fundefs_bound_var_fundefs.
              * intros Hc.
                erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
                eapply H7. constructor.
                eapply make_closures_image_Included. eassumption. eassumption.
                rewrite !Union_assoc. now apply Included_Union_r.
              * eapply FV_inv_set_r.
                intros Hc. subst. eapply H5. constructor; eauto.
                eassumption.
              * sets.
            + eauto.
            + eapply IHe with (GFuns := GFuns'); eauto.
              * eapply binding_in_map_antimon.
                eapply Included_trans. now eapply occurs_free_Efun_Included.
                rewrite Union_commut. now apply Included_refl.
                apply binding_in_map_def_funs. eassumption.
              * intros f Hfin; eauto.
              * eapply injective_subdomain_antimon.
                eapply make_closures_injective; try eassumption. 
                eapply Disjoint_Included_r; [| eassumption ]. 
                eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                normalize_bound_var...
                eapply Disjoint_Included_r; [| eassumption ].
                now eauto 20 with Ensembles_DB functions_BD.
                eapply Union_Included; sets. eapply Included_trans.
                eapply add_global_funs_included_r. eassumption. sets.
              * rewrite image_Union. eapply Union_Disjoint_l.
                eapply Disjoint_Included; [| | eapply Hd ]. normalize_bound_var...
                sets.  
                eapply Disjoint_Included_l. eapply image_monotonic. eapply add_global_funs_included_r.
                eassumption. rewrite image_Union. rewrite make_closures_image_eq; eauto.
                eapply Union_Disjoint_l.
                eapply Disjoint_Included; [| | eapply Hd ]; sets. normalize_bound_var...
                eapply Disjoint_Included; [| | eapply H7 ]; sets. normalize_bound_var... }
    - (* Case Eapp *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4 * length l + 4)
        by (eapply le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | simpl; omega ]).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep); inv Hstep'.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      simpl. rewrite H4, H5. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H4, H5. reflexivity. 
      eapply ctx_to_rho_cc_approx_exp; [ now eauto | eassumption | | omega | eassumption ]. 
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try congruence.
      destruct (get_list ys' rho2') eqn:Hgetys'; try congruence. inv Hget'. inv Happ'.
      assert (Hnin' :  ~ In var (f' |: FromList ys') f'').
      { eapply Disjoint_In_l; [| eassumption ]. 
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eassumption. }             
      eapply cc_approx_exp_app_compat. 
      (* TODO remove redntant arg *) eassumption. eassumption. eassumption. eassumption.
      + intros. eapply bound_app_compat. omega. eassumption. eassumption. eassumption. 
      + rewrite (Union_commut [set f']), <- Union_assoc. intros Hc. inv Hc; eauto. inv H. contradiction.
        revert H. eapply Disjoint_In_l; [| eassumption ]. 
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eassumption.
      + eassumption.
      + intros x Hget. repeat subst_exp. eexists; split; eauto.
      + eapply Forall2_cc_approx_var_env; eauto.
    (* Case Eprim *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4 * length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_prim_compat with (S0 := boundL 0).
        * intros. eapply bound_add_compat. omega.
          eassumption.
        * eapply Forall2_cc_approx_var_env; eauto. 
      * intros vs1 vs2 l1 f Hgetl Hgetf Happf Hall.
        { eapply IHe with (c := c'); [ now eauto | | | | | | | | | | eassumption ].
          * eapply cc_approx_env_P_extend with (v2 := vs2).
            eapply cc_approx_env_P_antimon; [ eassumption |]...
            eassumption.
          * now eauto.
          * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
            eapply occurs_free_Eprim_Included. 
          * intros f1 Hfin. eauto.
          * eapply injective_subdomain_antimon. eassumption. sets. 
          * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
            normalize_bound_var... now eauto with Ensembles_DB.
          * eapply Fun_inv_set_In_Scope_l. now eauto.
            eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
            intros Heq; subst. now eauto.
            eapply Fun_inv_mon; [ | now eauto ].
            eapply Disjoint_Included; [| | eapply Hd ]; sets.
          * eapply FV_inv_set_In_Scope_l. now constructor.
            eapply FV_inv_set_r. intros Hc. eapply Hnin.
            subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
          * eapply GFun_inv_set_not_In_GFuns_l. intros Hc. inv Hc. eapply H0. reflexivity.
            eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply Hd. constructor. rewrite image_Union.
            right. eapply image_monotonic; [| eassumption ]; sets. sets.
            eapply GFun_inv_Scope_extend; sets.
            eapply Disjoint_Included; [| | now eapply Hd ].
            normalize_bound_var... sets. 
            eapply GFun_inv_antimon; sets. }
    (* Case Ehalt *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Disjoint_Included_r; [| eassumption ]. rewrite image_Union.
      eauto 10 with Ensembles_DB.
      edestruct project_var_correct as [Hnin' [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_halt_compat. eapply bound_refl. omega.
      eassumption. 
  Qed.
  
  
End Closure_conversion_correct. 

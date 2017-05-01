(* Correspondence of the computational definition and the declarative spec for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.ctx L6.hoare L6.Ensembles_util
        L6.List_util L6.lambda_lifting L6.functions
        L6.logical_relations L6.eval L6.lambda_lifting_correct.
Require Import compcert.lib.Coqlib.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.


(** * Correspondence of the relational and the computational definitions of  lambda lifting *)
 
Section Lambda_lifting_corresp.

  (** Construct a function map similar to the one that is used in the relational spec from as [FunInfoMap]  *)
  Definition fun_map (m : FunInfoMap) : var -> option (var * fTag * list var) :=
    fun f =>
      match M.get f m with
        | Some inf =>
          match inf with
            | Fun f' ft fvs => Some (f', ft, fvs)
              end
        | None => None
      end.

  (** Useful equality to use the IH for [Ecase]  *)
  Lemma st_eq_Ecase {S} (m1 : state S (list (cTag * exp))) (x : var) y :
    st_eq
      (bind (bind m1 (fun ys => ret (y :: ys))) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;;
             ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s). reflexivity.
  Qed.

  Global Opaque bind ret.


  (** * Lemmas about [rename] *)

  Lemma rename_set_FreeVar_f_eq m x y :
    f_eq (rename (M.set x (FreeVar y) m))
         ((rename m) {x ~> y}).
  Proof.
    intros z. unfold rename.
    destruct (peq z x); subst; simpl.
    - now rewrite M.gss, extend_gss.
    - now rewrite M.gso, extend_gso.
  Qed.
  
  Lemma rename_not_in_domain_f_eq m x :
    binding_not_in_map (Singleton _ x) m ->
    f_eq (rename m) ((rename m) {x ~> x}).
  Proof with now eauto with Ensembles_DB.
    intros H y. unfold rename.
    destruct (peq y x); subst; simpl.
    - rewrite extend_gss. destruct (M.get x m) eqn:Heq; eauto.
      rewrite H in Heq; try congruence. eauto.
    - rewrite extend_gso; eauto.
  Qed.

  Lemma rename_not_in_domain_lst_f_eq m xs :
    binding_not_in_map (FromList xs) m ->
    f_eq (rename m) ((rename m) <{xs ~> xs}>).
  Proof with now eauto with Ensembles_DB.
    induction xs; intros Hnin; simpl; eauto.
    - reflexivity.
    - rewrite <- IHxs. rewrite <- rename_not_in_domain_f_eq. reflexivity.
      eapply binding_not_in_map_antimon; [| eassumption ]; rewrite FromList_cons...
      eapply binding_not_in_map_antimon; [| eassumption ]; rewrite FromList_cons...
  Qed.
  
  (** * Lemmas about [fun_map] *)
  
  Lemma fun_map_set_Fun_f_eq m f f' ft fvs :
    f_eq (fun_map (M.set f (Fun f' ft fvs) m))
         ((fun_map m) {f ~> Some (f', ft, fvs)}).
  Proof.
    intros z. unfold fun_map.
    destruct (peq z f); subst; simpl.
    - now rewrite M.gss, extend_gss.
    - now rewrite M.gso, extend_gso.
  Qed.
  
  (** Spec for [get_name] *)
  Lemma get_name_fresh S :
    {{ fun s => fresh S (next_var s) }}
      get_name
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (next_var s') }}.  
  Proof.   
    eapply pre_post_mp_l.
    eapply bind_triple. eapply get_triple.
    intros [x1 ft1] [x2 ft2].
    eapply pre_post_mp_l. eapply bind_triple.
    eapply put_triple. intros u [x3 ft3]. eapply return_triple. 
    intros [x4 ft4] Heq1 [Heq2 Heq3] H; subst. inv Heq1. inv Heq2. inv Heq3. 
    split; eauto. intros y Hleq.
    constructor.
    - eapply H. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. eapply Pos.le_nlt in Hleq.
      eapply Hleq. zify. omega.
  Qed.

  Lemma Forall_monotonic {A} (P P' : A -> Prop) l :
    (forall x, P x -> P' x) ->
    Forall P l ->
    Forall P' l.
  Proof.
    intros H Hall. induction Hall; eauto.
  Qed.    

  (** Spec for [get_names] *)
  Lemma get_names_fresh n S :
    {{ fun s => fresh S (next_var s) }}
      get_names n
    {{ fun _ xs s' => Forall (fresh S) xs /\
                   length xs = n /\
                   NoDup xs /\
                   fresh (Setminus var S (FromList xs)) (next_var s') }}.  
  Proof with now eauto with Ensembles_DB. 
    revert S. induction n; intros S.
    - eapply return_triple. intros.
      split; eauto. split; eauto.
      split. now constructor.
      now rewrite FromList_nil, Setminus_Empty_set_neut_r.
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. eapply pre_curry_l. intros Hf.
      eapply bind_triple. now eapply IHn.
      intros xs s2. apply return_triple.
      intros s3 [Hall [Hlen [Hnd Hf']]].
      simpl. split; [| split; [| split ]].
      + constructor; eauto.
        eapply Forall_monotonic; [| eassumption ].
        intros y Hd. eapply fresh_monotonic; [| eassumption ]...
      + congruence.
      + constructor; [| assumption ].
        intros Hc. eapply Forall_forall in Hall; eauto.
        specialize (Hall x (Pos.le_refl x)). inv Hall.
        eauto.
      + rewrite FromList_cons.
        eapply fresh_monotonic; [| eassumption ]...
  Qed.
  
  (** Spec for [get_tag] *)
  Lemma get_tag_preserv P :
    {{ fun s => P (next_var s)}}
      get_tag
    {{ fun _ x s' => P (next_var s') }}.  
  Proof.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [x1 t1] [x2 t2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [x3 t3]. apply return_triple.
    intros [s4 x4] H1 [H2 H3] Hp.
    inv H1; inv H2; inv H3. eauto.
  Qed.

  (** [add_functions] is sound w.r.t. its relational spec *)
  Lemma add_functions_sound B fvs fvm fm S :
    binding_not_in_map (Union _ S (bound_var_fundefs B)) fvm ->
    {{ fun s => fresh S (next_var s) }}
      add_functions B fvs fm
    {{ fun s m' s' => 
         exists σ ζ S',
           Add_functions B fvs (rename fvm) (fun_map fm) S σ ζ S' /\
           f_eq σ (rename fvm) /\
           f_eq ζ (fun_map m') /\
           fresh S' (next_var s') }}.
  Proof with now eauto with Ensembles_DB.
    revert fm S. induction B; intros m S Hnin.
    - eapply bind_triple.
      + eapply IHB. eapply binding_not_in_map_antimon; [| eassumption ].
        normalize_bound_var...
      + intros m' s1. eapply pre_existential; intros g1.
        eapply pre_existential; intros g2.
        eapply pre_existential; intros S'.
        eapply pre_curry_l. intros Hadd.
        eapply pre_curry_l. intros Hfeq1.
        eapply pre_curry_l. intros Hfeq2.
        eapply bind_triple. now apply get_name_fresh.
        intros x s2. eapply pre_curry_l. intros Hf'.       
        eapply bind_triple. now apply get_tag_preserv.
        intros ft s3. apply return_triple. intros s4 Hf.
        do 3 eexists. split ; [| split; [| split ]].
        * econstructor. eassumption. eapply Hf' with (y := x).
          zify; omega.
        * symmetry. rewrite Hfeq1, <- !rename_not_in_domain_f_eq. reflexivity.
          eapply binding_not_in_map_antimon; [| eassumption ].
          eapply Singleton_Included. left.
          eapply Add_functions_free_set_Included; eauto.
          eapply Hf'. zify; omega.
          eapply binding_not_in_map_antimon; [| eassumption ].
          normalize_bound_var...
        * symmetry. rewrite Hfeq2. apply fun_map_set_Fun_f_eq.
        * eassumption.
    - apply return_triple. intros s Hf.
      repeat eexists; eauto. constructor; reflexivity.
  Qed.

  (** [add_free_var] spec *)
  Lemma add_free_vars_f_eq xs fvm S P :
    binding_not_in_map P fvm ->    
    (* Disjoint _ (domain (fun_map m)) (FromList xs) -> *)
    (* binding_not_in_map S m -> *)
    {{ fun s => fresh S (next_var s) }}
      add_free_vars xs fvm
    {{ fun s p s' =>
         let (ys, fvm') := p in  
         f_eq ((rename fvm) <{xs ~> ys}>) (rename fvm') /\
         binding_not_in_map (Setminus _ P (FromList xs)) fvm' /\
         NoDup ys /\
         Forall (fresh S) ys /\
         length xs = length ys /\
         fresh (Setminus var S (FromList ys)) (next_var s') }}.
  Proof with now eauto with Ensembles_DB.
    revert fvm S. induction xs as [| x xs IHxs ]; intros fvm S Hnin.
    - apply return_triple. simpl.
      intros s Hf. repeat split; eauto.
      eapply binding_not_in_map_antimon; eauto.
      rewrite FromList_nil... now constructor.
    - eapply bind_triple.
      + eapply IHxs; eauto.
      + intros [ys m'] _.
        apply pre_curry_l. intros Hfeq1. 
        apply pre_curry_l. intros Hnin'.
        apply pre_curry_l. intros Hnd.
        apply pre_curry_l. intros Hall.
        apply pre_curry_l. intros Hlen.
        eapply bind_triple. now apply get_name_fresh.
        intros y s1. apply return_triple. 
        intros s2 [Hf1 Hf2]. split; [| split; [| split; [| split; [| split ]]]].
        * simpl. rewrite rename_set_FreeVar_f_eq, Hfeq1.
          reflexivity.
        * eapply binding_not_in_map_set_not_In_S.
          eapply binding_not_in_map_antimon; [| eassumption ].
          rewrite FromList_cons...
          intros Hc; inv Hc. eapply H0. rewrite FromList_cons...
        * constructor; eauto. intros Hc.
          specialize (Hf1 y (Pos.le_refl y)). inv Hf1.
          eauto.
        * constructor; eauto.
          eapply fresh_monotonic; [| eassumption ]...
        * simpl; congruence.
        * rewrite FromList_cons, Union_commut, <- Setminus_Union. eassumption.
  Qed.

  (** [Add_functions] up to functional extensionality *)
  Lemma Add_functions_f_eq B fvs σ1 ζ1 σ2 ζ2 S1 S2 σ1' ζ1' S1'  :
    Add_functions B fvs σ1 ζ1 S1 σ2 ζ2 S2 ->
    f_eq σ1 σ1' -> f_eq ζ1 ζ1' -> Same_set _ S1 S1' ->
    exists σ2' ζ2' S2',
      Add_functions B fvs σ1' ζ1' S1' σ2' ζ2' S2' /\
      f_eq σ2 σ2' /\ f_eq ζ2 ζ2' /\ Same_set _ S2 S2'.
  Proof.
    intros Hadd.
    induction Hadd; intros Heq1 Heq2 Heq3.
    - edestruct IHHadd as [σ2' [ζ2' [S2' [Hadd' [Heq1' [Heq2' Heq3']]]]]]; eauto.
      do 3 eexists. split; [| split; [| split ]].
      constructor. eassumption. rewrite <- Heq3'. eassumption.
      rewrite Heq1'. reflexivity. rewrite Heq2'. reflexivity.
      rewrite Heq3'. reflexivity. 
    - do 3 eexists. split; [| split; [| split ]]; try eassumption.
      constructor.
  Qed.


  Lemma Add_functions_f_eq' B fvs σ1 ζ1 σ2 ζ2 S1 S2 σ1' ζ1' :
    Add_functions B fvs σ1 ζ1 S1 σ2 ζ2 S2 ->
    f_eq σ1 σ1' -> f_eq ζ1 ζ1' ->
    exists σ2' ζ2',
      Add_functions B fvs σ1' ζ1' S1 σ2' ζ2' S2 /\
      f_eq σ2 σ2' /\ f_eq ζ2 ζ2'.
  Proof.
    intros Hadd.
    induction Hadd; intros Heq1 Heq2.
    - edestruct IHHadd as [σ2' [ζ2' [Hadd' [Heq1' Heq2']]]]; eauto.
      do 2 eexists. split; [| split ].
      constructor. eassumption. eassumption.
      rewrite Heq1'. reflexivity. rewrite Heq2'. reflexivity.
    - do 2 eexists. split; [| split ]; try eassumption.
      constructor.
  Qed.

  (** * Some Proper instances *)
  
  Instance FunsFVs_Proper : Proper (f_eq ==> Same_set _) FunsFVs.
  Proof.
    constructor; intros z [f [f' [ft [fvs [Heq Hin]]]]].
    rewrite H in Heq. now repeat eexists; eauto.
    rewrite <- H in Heq. now repeat eexists; eauto.
  Qed.

  Instance lifted_name_Proper : Proper (f_eq ==> f_eq) lifted_name.
  Proof.
    intros f1 f2 Heq x. unfold lifted_name. rewrite Heq; reflexivity.
  Qed.
    
  Instance Funs_Proper : Proper (f_eq ==> Same_set _) Funs.
  Proof.
    constructor; intros z [f H']; eexists; unfold lifted_name in *.
    rewrite <- H; eassumption.
    rewrite H; eassumption.
  Qed.

  Instance LiftedFuns_Proper : Proper (f_eq ==> Same_set _) LiftedFuns.
  Proof.
    intros f1 f2 Heq. unfold LiftedFuns.
    rewrite !Heq. reflexivity.
  Qed.
  
  Lemma Exp_lambda_lift_proper_mut :
    (forall e ζ σ ζ' σ' S1 e' S2
       (Hll : Exp_lambda_lift ζ σ e S1 e' S2)
       (Heq1 : f_eq σ σ') (Heq2 : f_eq ζ ζ'),
       Exp_lambda_lift ζ' σ' e S1 e' S2) /\
    (forall B ζ σ ζ' σ' S1 B' S2
       (Hll : Fundefs_lambda_lift ζ σ B S1 B' S2) (Heq1 : f_eq σ σ') (Heq2 : f_eq ζ ζ'),
       Fundefs_lambda_lift ζ' σ' B S1 B' S2).
  Proof.
    eapply exp_def_mutual_ind; simpl; intros; inv Hll.
    - rewrite Heq1. econstructor; eauto. eapply H; eauto.
      rewrite Heq1; reflexivity.
    - rewrite Heq1. econstructor; eauto.
    - rewrite Heq1. econstructor; eauto.
    - rewrite Heq1. econstructor; eauto.
      eapply H; eauto. rewrite Heq1; reflexivity.
    - edestruct Add_functions_f_eq' as [σ'' [ζ'' [Hadd1 [Heq1' Heq2']]]]; eauto.
      econstructor. eapply Included_trans. eassumption.
      eapply Included_Union_compat. reflexivity.
      eapply Included_Union_compat; rewrite <- Heq2; reflexivity.
      eassumption. eassumption. now eapply H; eauto.
      now eapply H0; eauto.
    - rewrite !Heq1. econstructor; eauto. rewrite <- Heq2. eauto.
    - rewrite !Heq1. econstructor; eauto. rewrite <- Heq2. eauto.
    - rewrite Heq1. econstructor; eauto. eapply H; eauto.
      rewrite Heq1. reflexivity.
    - rewrite Heq1. econstructor; eauto.
    - rewrite Heq1. econstructor; eauto. rewrite <- Heq2; eauto.
      eapply H; eauto. rewrite Heq1. reflexivity.
    - constructor.
  Qed.

  Instance Exp_lambda_lift_Proper_ζ :
    Proper (f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Exp_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Exp_lambda_lift_Proper_σ :
    Proper (eq ==> f_eq ==> eq ==> eq ==> eq ==> eq ==> iff) Exp_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda_lift_Proper_ζ :
    Proper (f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda_lift_Proper_σ :
    Proper (eq ==> f_eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  (** Alternative definition for [Funs] *)
  Lemma Funs_Same_set ζ : 
    Same_set _ (Funs ζ) (domain ζ).
  Proof.
    split; intros x [y H]. unfold lifted_name in H.
    edestruct (ζ x) eqn:Heq; simpl in H; eauto.
    repeat eexists; eauto. 
    inv H.
    destruct y as [[? ?] ?]. eapply lifted_name_eq in H.
    repeat eexists; eauto.
  Qed.
  
  Lemma Add_functions_name_in_fundefs_Included (B : fundefs) (fvs : list var) (σ : var -> var)
        (ζ : var -> option (var * fTag * list var)) (S : Ensemble var)
        (σ' : var -> var) (ζ' : var -> option (var * fTag * list var))
        (S' : Ensemble var) :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included var (name_in_fundefs B) (domain ζ').
  Proof with now eauto with Ensembles_DB.
    intros Hadd; induction Hadd.
    - simpl. rewrite <- domain_extend_Some...
    - now eauto with Ensembles_DB.
  Qed.

  (** Soundness of [exp_true_fv] *)
  Section TrueFV_correct.
    
    Variable (funmap : FunInfoMap).

    Lemma exp_true_fv_fundefs_true_fv_correct :
      (forall e Scope FVset x,
         PS.In x (exp_true_fv_aux funmap e Scope FVset) ->
         ((In _ (occurs_free e) x /\ ~ PS.In x Scope) \/
          (In _ (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap))) x) \/
          PS.In x FVset)) /\
      (forall B Scope FVset,
         let '(Scope', FVset') := fundefs_true_fv_aux funmap B Scope FVset in
         (forall x, PS.In x Scope' <-> (PS.In x Scope \/ In _ (name_in_fundefs B) x)) /\
         (forall x, PS.In x FVset' ->
               ((In _ (occurs_free_fundefs B) x /\ ~ PS.In x Scope) \/
                (In _ (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap))) x) \/
                PS.In x FVset))).
    Proof.
      exp_defs_induction IHe IHl IHdefs; simpl; intros.
      - eapply IHe in H. inv H.
        + inv H0. left. split. constructor 2; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto.
          eapply add_list_spec in H. inv H; eauto.
          inv H0; left; eauto.
      - destruct (PS.mem v Scope) eqn:Heq; eauto.
        repeat apply_set_specs_ctx; eauto. left; split; eauto.
        intros Hc. eapply PS.mem_spec in Hc. congruence.
      - eapply IHl in H. inv H.
        + inv H0. left; eauto.
        + inv H0; eauto. eapply IHe in H. inv H; eauto. inv H0; eauto.
      - eapply IHe in H. inv H.
        + inv H0. left. split. constructor; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + destruct (PS.mem v0 Scope) eqn:Heq; eauto. inv H0; eauto.
          apply_set_specs_ctx; eauto. left; split; eauto.
          intros Hc.  apply PS.mem_spec in Hc. congruence.
      - destruct (fundefs_true_fv_aux funmap f2 Scope FVset) as [Scope' FVset'] eqn:Heq.
        specialize (IHdefs Scope FVset). rewrite Heq in IHdefs.
        destruct IHdefs as [H1 H2].
        eapply IHe in H. inv H.
        + inv H0. left; split. constructor; eauto.
          intros Hc. eapply H3. eapply H1; eauto.
          intros Hc. eapply H3. eapply H1; eauto.
        + inv H0; eauto. eapply H2 in H. inv H; eauto. inv H0; eauto.
      - destruct (Maps.PTree.get v funmap) eqn:Heqf.
        + destruct f. eapply add_list_spec in H. inv H; eauto.
          repeat apply_set_specs_ctx; eauto.
          right; left; right. repeat eexists. erewrite lifted_name_eq; eauto.
          unfold fun_map. rewrite Heqf; reflexivity.
          erewrite lifted_name_eq; eauto.
          unfold fun_map. rewrite Heqf; reflexivity.
          right; left; left. repeat eexists.
          unfold fun_map. rewrite Heqf; reflexivity.
          eassumption.
          now inv H0; left; split; eauto.
        + destruct (PS.mem v Scope) eqn:Heq; eauto.
          * eapply add_list_spec in H. inv H; eauto.
            inv H0. left. split; eauto.
          * eapply add_list_spec in H. inv H; eauto.
            repeat apply_set_specs_ctx; eauto.
            left; split; eauto. intros Hc.
            eapply PS.mem_spec in Hc. congruence.
            inv H0; eauto.
      - eapply IHe in H. inv H.
        + inv H0. left. split. eapply Free_Eprim2 ; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto. eapply add_list_spec in H. inv H; eauto.
          inv H0; left; eauto.
      - destruct (PS.mem v Scope) eqn:Heq; eauto.
        repeat apply_set_specs_ctx; eauto. left; split; eauto.
        intros Hc. eapply PS.mem_spec in Hc. congruence.
      - destruct (fundefs_true_fv_aux funmap f5 (PS.add v Scope) FVset) as [Scope' FVset'] eqn:Heq.
        specialize (IHdefs (PS.add v Scope) FVset). rewrite Heq in IHdefs.
        destruct IHdefs as [H1 H2]. split. 
        + split; intros H.
          eapply H1 in H; inv H; eauto. repeat apply_set_specs_ctx; eauto.
          eapply H1. inv H; eauto. left. now apply_set_specs; eauto.
          inv H0; eauto. inv H. left. now apply_set_specs; eauto.
        + intros x H. eapply IHe in H. inv H. inv H0. left. split; eauto.
          eapply Free_Fcons1; eauto.
          intros Hc; subst. eapply H3. eapply union_list_spec.
          left. eapply H1; left. now repeat apply_set_specs; eauto.
          intros Hc. eapply H3. eapply union_list_spec. now right; eauto.
          intros Hc. eapply H3. eapply union_list_spec.
          left. now eapply H1; right; eauto.
          intros Hc; subst. eapply H3. eapply union_list_spec.
          left. eapply H1; left. now repeat apply_set_specs; eauto.
          inv H0; eauto.
          eapply H2 in H. inv H; eauto. inv H0; eauto. left; split; eauto.
          constructor 2; eauto.
          intros Hc; subst. eapply H3. now repeat apply_set_specs; eauto.
          intros Hc; subst. eapply H3. now repeat apply_set_specs; eauto.
      - split. intros x. split; eauto. intros [H1 | H1]; eauto. inv H1.
        intros x. intros H; eauto.
    Qed.

    Corollary fundefs_true_fv_correct B :
      Included var (FromList (PS.elements (fundefs_true_fv funmap B)))
               (Union _ (occurs_free_fundefs B)
                      (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap)))).
    Proof.
      destruct exp_true_fv_fundefs_true_fv_correct as [_ H2].
      unfold fundefs_true_fv. specialize (H2 B PS.empty PS.empty).
      destruct (fundefs_true_fv_aux funmap B PS.empty PS.empty) as [scope fvs].
      intros x H. inv H2.
      assert (Hin : PS.In x fvs).
      { eapply PS.elements_spec1. eapply InA_alt.
        eexists; split; eauto. }
      eapply H1 in Hin. inv Hin.
      inv H2; eauto.
      inv H2; eauto. inv H3.
    Qed.

  End TrueFV_correct.
  
  (** * The lambda lifting algorithm is sound w.r.t. its relational specification *)
  Lemma lambda_lifting_sound :
    (forall (e : exp) (FVmap : VarInfoMap) (FNmap : FunInfoMap) (S : Ensemble var)
       (Hlf : Disjoint _ (LiftedFuns (fun_map FNmap)) (Union _ S (bound_var e)))
       (Hfvs : Disjoint _ (FunsFVs (fun_map FNmap)) (Union _ S (bound_var e)))
       (Hf : Disjoint _ S (Union _ (bound_var e) (occurs_free e)))
       (HD : Disjoint _ (bound_var e) (occurs_free e))
       (Hnin : binding_not_in_map (Union _ S (bound_var e)) FVmap)
       (Hun : unique_bindings e),
       {{ fun s => fresh S (next_var s) }}
         exp_lambda_lift e FVmap FNmap
       {{ fun s e' s' =>
           exists S', Exp_lambda_lift (fun_map FNmap) (rename FVmap) e S e' S' /\
                 fresh S' (next_var s')
        }}) /\
    (forall (B : fundefs) (FVmap : VarInfoMap) (FNmap : FunInfoMap) (S : Ensemble var)
       (Hlf : Disjoint _ (LiftedFuns (fun_map FNmap)) (Union _ S (bound_var_fundefs B)))
       (Hfvs : Disjoint _ (FunsFVs (fun_map FNmap)) (Union _ S (bound_var_fundefs B)))
       (Hf : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B)))
       (HD : Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B))
       (Hin1 : Included _ (name_in_fundefs B) (domain (fun_map FNmap)))
       (Hnin : binding_not_in_map (Union _ S (bound_var_fundefs B)) FVmap)
       (Hun : unique_bindings_fundefs B),
       {{ fun s => fresh S (next_var s) }}
         fundefs_lambda_lift B FVmap FNmap
       {{ fun s B' s' =>     
            exists S', Fundefs_lambda_lift (fun_map FNmap) (rename FVmap) B S B' S' /\
            fresh S' (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; simpl; intros.
    Opaque exp_lambda_lift fundefs_lambda_lift.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Econstr.
          now apply bound_var_occurs_free_Econstr_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Econstr_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
        * eapply binding_not_in_map_antimon; [| eassumption ].
          normalize_bound_var...
      + intros x s1. apply return_triple.
        intros s2 [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        eapply binding_not_in_map_antimon; [| eassumption ].
        normalize_bound_var...
    - eapply return_triple. intros s Hfr.
      eexists. split; eauto. constructor.
    - setoid_rewrite assoc. eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx.
        eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_occurs_free...
        * eapply Disjoint_Included; [| | now apply HD ].
          normalize_occurs_free...
          now eauto with Ensembles_DB.
        * eapply binding_not_in_map_antimon; [| eassumption ].
          normalize_bound_var...
      + intros e' s1. simpl. 
        setoid_rewrite st_eq_Ecase. eapply pre_existential.
        intros S1. eapply pre_curry_l; intros Hll.
        eapply bind_triple.
        * { repeat normalize_bound_var_in_ctx.
            eapply IHl with (FVmap := FVmap) (FNmap := FNmap) (S := S1).
            - eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat;
              [ now eapply Exp_Lambda_lift_free_set_Included; eauto |]...
            - eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat;
              [ now eapply Exp_Lambda_lift_free_set_Included; eauto |]...
            - eapply Disjoint_Included_l.
              now eapply Exp_Lambda_lift_free_set_Included; eauto.
              eapply Disjoint_Included_r; [| eassumption ].
              normalize_occurs_free...
            - eapply Disjoint_Included; [| | now apply HD ].
              normalize_occurs_free...
              now eauto with Ensembles_DB.
            - eapply binding_not_in_map_antimon; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Exp_Lambda_lift_free_set_Included; eauto.
              normalize_bound_var...
            - inv Hun; eauto. }
        * intros e1 s2. eapply pre_existential.
          intros S2. eapply pre_curry_l; intros Hll'.
          edestruct Exp_lambda_lift_Ecase as [P' [Heq Hall]]. eassumption.
          subst. eapply return_triple.
          intros s3 Hfr. eexists. split; eauto.
          econstructor; eauto.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eproj.
          now apply bound_var_occurs_free_Eproj_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eproj_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
        * eapply binding_not_in_map_antimon; [| eassumption ].
          normalize_bound_var...
      + intros x s1. apply return_triple.
        intros s2 [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        eapply binding_not_in_map_antimon; [| eassumption ].
        normalize_bound_var...
    - assert (HFV : Included var (FromList (PS.elements (fundefs_true_fv FNmap f2)))
                             (Union var (occurs_free_fundefs f2)
                                    (Union var (FunsFVs (fun_map FNmap)) (LiftedFuns (fun_map FNmap)))))
        by eapply fundefs_true_fv_correct.
      eapply bind_triple.
      + eapply add_functions_sound.
        eapply binding_not_in_map_antimon; [| eassumption ].
        normalize_bound_var...
      + intros m s1. eapply pre_existential. intros σ'.
        eapply pre_existential. intros ζ'. eapply pre_existential. intros S1.
        eapply pre_curry_l. intros Hadd. eapply pre_curry_l. intros Heq1.
        eapply pre_curry_l. intros Heq2.
        eapply bind_triple.
        * { inv Hun . eapply IHB; eauto.
            - rewrite <- Heq2. eapply Disjoint_Included_l. 
              eapply Add_functions_LiftedFuns_Included_r. eassumption.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var...
              eapply Union_Disjoint_r. now eauto with Ensembles_DB.
              eapply Disjoint_Included; [| | now apply Hf ].
              normalize_bound_var... now eauto with Ensembles_DB.
            - rewrite <- Heq2. eapply Disjoint_Included_l.
              eapply Add_functions_FunsFVs_Included_r. eassumption.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var...
              eapply Disjoint_Included_l; [ eassumption |].
              eapply Union_Disjoint_l.
              eapply Disjoint_sym. eapply Union_Disjoint_l. 
              eapply Disjoint_Included; [| | now apply Hf ].
              normalize_occurs_free...
              now eapply Add_functions_free_set_Included; eauto.
              eapply Disjoint_Included; [| | now apply HD ].
              normalize_occurs_free... normalize_bound_var...
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var...
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var...
            - eapply Disjoint_Included; [| | now apply Hf].
              normalize_bound_var. normalize_occurs_free...
              now eapply Add_functions_free_set_Included; eauto.
            - eapply Disjoint_Included; [| | now apply HD].
              normalize_occurs_free...
              normalize_bound_var...
            - rewrite <- Heq2, <- Funs_Same_set at 1.
              rewrite Add_functions_Funs_Same_set; eauto...
            - eapply binding_not_in_map_antimon; [| eassumption ].
              eapply Included_Union_compat.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var... }
        * intros B' s2. eapply pre_existential. intros S2.
          eapply pre_curry_l. intros Hll.
          eapply bind_triple.
          { inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; eauto.
            - rewrite <- Heq2. eapply Disjoint_Included_l. 
              eapply Add_functions_LiftedFuns_Included_r. eassumption.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              eapply Included_trans.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
              now eauto with Ensembles_DB.
              eapply Union_Disjoint_r.
              eapply Disjoint_Included_r.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eauto with Ensembles_DB.
              eapply Disjoint_Included; [| | now apply Hf ]...
            - rewrite <- Heq2. eapply Disjoint_Included_l.
              eapply Add_functions_FunsFVs_Included_r. eassumption.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat. eapply Included_trans.              
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
              now eauto with Ensembles_DB.
              eapply Disjoint_Included_l; [ eassumption |].
              eapply Union_Disjoint_l.
              eapply Disjoint_sym. eapply Union_Disjoint_l. 
              eapply Disjoint_Included; [| | now apply Hf ].
              normalize_occurs_free...
              eapply Included_trans.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
              eapply Disjoint_Included; [| | now apply HD ].
              normalize_occurs_free... now eauto with Ensembles_DB.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              eapply Included_trans.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto. 
              now eapply Add_functions_free_set_Included; eauto.
              now eauto with Ensembles_DB.
              eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat.
              eapply Included_trans.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
              now eauto with Ensembles_DB.
            - eapply Disjoint_Included; [| | now apply Hf].
              eapply Union_Included. now eauto with Ensembles_DB.
              eapply Included_trans. now eapply occurs_free_Efun_Included.
              eapply Union_Included. now eauto with Ensembles_DB.
              eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
              now eauto with Ensembles_DB.
              eapply Included_trans. now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
            - eapply Disjoint_Included_r.
              now apply occurs_free_Efun_Included.
              eapply Union_Disjoint_r. now eauto with Ensembles_DB.
              eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs. 
              assumption.
            - eapply binding_not_in_map_antimon; [| eassumption ].
              eapply Included_Union_compat.
              eapply Included_trans.
              now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
              now eapply Add_functions_free_set_Included; eauto.
              normalize_bound_var... }
          intros e' s3. eapply return_triple. intros s4 [S3 [Hll' Hfr]].
          eexists; split; eauto. rewrite <- Heq1, <- Heq2 in Hll, Hll'. 
          econstructor; [| | eassumption | eassumption | eassumption ].
          eassumption.
          eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
    - edestruct (M.get v FNmap) as [ [ ? ? ? ] | ] eqn:Heq;
      eapply return_triple; intros s1 Hfr.
      + eexists. split; eauto.
        econstructor. unfold fun_map. rewrite Heq. reflexivity.
      + eexists. split; eauto.
        econstructor. unfold fun_map. rewrite Heq. reflexivity.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eprim.
          now apply bound_var_occurs_free_Eprim_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eprim_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
        * eapply binding_not_in_map_antimon; [| eassumption ].
          normalize_bound_var...
      + intros x s1. apply return_triple.
        intros s2 [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        eapply binding_not_in_map_antimon; [| eassumption ].
        normalize_bound_var...
    - eapply return_triple. intros s1 Hfr. eexists. split; eauto.
      econstructor.
    - edestruct Hin1 as [[[v' ft'] fvs]  Heq]. now left; eauto.
      unfold fun_map in Heq. edestruct (M.get v FNmap) eqn:Heq'; try discriminate.
      destruct f. inv Heq.
      eapply bind_triple.
      + eapply add_free_vars_f_eq. eassumption.
      + intros [ys map'] _. apply pre_curry_l. intros Heq1.
        apply pre_curry_l. intros Hnin'. apply pre_curry_l. intros Hnd.
        apply pre_curry_l. intros Hall. apply pre_curry_l. intros Hlen.
        eapply bind_triple. now eapply get_names_fresh.
        intros xs' s1. apply pre_curry_l. intros Hall'. apply pre_curry_l. intros Hlen'.
        apply pre_curry_l. intros Hnd'. eapply bind_triple.
        * { inv Hun. eapply IHe; eauto.
            - eapply Disjoint_Included_r; [| eassumption ].
              normalize_bound_var...
            - eapply Disjoint_Included_r; [| eassumption ].
              normalize_bound_var...
            - eapply Disjoint_Included; [| | eapply Hf ].
              eapply Union_Included. normalize_bound_var...
              eapply Included_trans. eapply (occurs_free_in_fun v t l e (Fcons v t l e f5)).
              now left; eauto.
              eapply Union_Included. normalize_bound_var...
              eapply Union_Included. eapply Included_Union_preserv_l.
              now apply name_in_fundefs_bound_var_fundefs.
              now eauto with Ensembles_DB. now eauto with Ensembles_DB.
            - eapply Disjoint_Included_r. eapply (occurs_free_in_fun v t l e (Fcons v t l e f5)).
              now constructor. eapply Union_Disjoint_r.
              eassumption. simpl. eapply Union_Disjoint_r. eapply Union_Disjoint_r.
              eapply Disjoint_Singleton_r. eassumption.
              eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
              eassumption. rewrite bound_var_fundefs_Fcons in HD...
            - eapply binding_not_in_map_antimon; [| eassumption ].
              rewrite (Setminus_Disjoint _ (FromList fvs)). normalize_bound_var...
              eapply Disjoint_Included_r_sym with (s3 := FunsFVs (fun_map FNmap)).
              intros x H. repeat eexists; eauto. unfold fun_map. rewrite Heq'. reflexivity.
              eassumption. }
        * { intros e' s2. eapply pre_existential. intros S1.
            eapply pre_curry_l. intros Hll.
            eapply bind_triple.
            - inv Hun. eapply IHB; eauto.
              + eapply Disjoint_Included_r; [| eassumption ].
                normalize_bound_var. eapply Included_Union_compat.
                eapply Included_trans. now eapply Exp_Lambda_lift_free_set_Included; eauto.
                now eauto with Ensembles_DB. now eauto with Ensembles_DB.
              + eapply Disjoint_Included_r; [| eassumption ].
                normalize_bound_var. eapply Included_Union_compat.
                eapply Included_trans. now eapply Exp_Lambda_lift_free_set_Included; eauto.
                now eauto with Ensembles_DB. now eauto with Ensembles_DB.
              + eapply Disjoint_Included; [| | now apply Hf].
                eapply Union_Included. normalize_bound_var...
                eapply Included_trans. now apply occurs_free_fundefs_Fcons_Included.
                normalize_bound_var...
                eapply Included_trans. now eapply Exp_Lambda_lift_free_set_Included; eauto.
                now eauto with Ensembles_DB.
              + eapply Disjoint_Included_r. now apply occurs_free_fundefs_Fcons_Included.
                eapply Union_Disjoint_r. rewrite bound_var_fundefs_Fcons in HD...
                eapply Disjoint_Singleton_r. eassumption.
              + eapply Included_trans; [| eassumption ]...
              + eapply binding_not_in_map_antimon; [| eassumption ].
                eapply Included_Union_compat.
                eapply Included_trans. now eapply Exp_Lambda_lift_free_set_Included; eauto.
                now eauto with Ensembles_DB.  normalize_bound_var...
            - intros B' s3. eapply return_triple.
              intros s4 [S2 [Hll' Hfr]]. eexists; split; eauto.
              econstructor; try eassumption.
              + unfold fun_map. rewrite Heq'. reflexivity.
              + intros x Hl. eapply Forall_forall; [| eassumption ].
                eapply Forall_monotonic; [| eassumption ]. intros y Hfy.
                eapply Hfy. zify; omega.
              + intros x Hl. eapply Forall_forall; [| eassumption ].
                eapply Forall_monotonic; [| eassumption ]. intros y Hfy.
                eapply Hfy. zify; omega.
              + congruence.
              + rewrite extend_lst_app; eauto.
                rewrite Heq1; eauto. rewrite <- rename_not_in_domain_lst_f_eq.
                eassumption.
                eapply binding_not_in_map_antimon; [| eassumption ].
                rewrite (Setminus_Disjoint _ (FromList fvs)). normalize_bound_var...
                eapply Disjoint_Included_r_sym with (s6 := FunsFVs (fun_map FNmap)).
                intros x H. repeat eexists; eauto. unfold fun_map. rewrite Heq'. reflexivity.
                eassumption. }
    - apply return_triple. intros s1 Hfr. eexists; split; eauto.
      constructor.
  Qed.
  
End Lambda_lifting_corresp.
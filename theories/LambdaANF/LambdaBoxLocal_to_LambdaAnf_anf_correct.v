Require Import MetaCoq.Utils.bytestring.
From Coq Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions Classes.Morphisms.
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

Section Bounds.

  (** LambdaBoxLocal fuel and trace *)
  
  Definition fuel_exp (e: expression.exp) : nat :=
    match e with
    | Var_e _ => 0
    | Lam_e _ _ => 1
    | App_e _ _ => 1
    | Let_e _ _ _ => 0
    | Fix_e _ _ => 1

    | Con_e _ es => 1
    | Match_e _ _ brs => 1

    (* Unused *)
    | Prf_e => 0
    | Prim_e x => 0
    | Prim_val_e x => 0
    end.


  Fixpoint max_m_branches (br : branches_e) : nat :=
    match br with
    | brnil_e => 0
    | brcons_e _ (m, _) e br => max (N.to_nat m) (max_m_branches br)
    end.      

  
  (* This is the cost of the CPS-ed program *)
  Definition trace_exp (e: expression.exp) : nat :=
    match e with
    | Var_e _ => 0
    | Lam_e _ _ => 1
    | App_e _ _ => 1
    | Let_e _ _ _ => 0
    | Fix_e _ _ => 1

    | Con_e _ es => 1 + List.length (exps_as_list es)
    | Match_e _ _ brs => 1 + max_m_branches brs

    (* Unused *)
    | Prf_e => 0
    | Prim_e x => 0
    | Prim_val_e x => 0
    end.
    

  Program Instance fuel_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := fuel_exp;
      plus := Nat.add
    }.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Program Instance trace_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := trace_exp;
      plus := Nat.add
    }.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Global Instance LambdaBoxLocal_resource_fuel : @LambdaBoxLocal_resource nat.
  Proof.
    constructor. eapply fuel_resource_LambdaBoxLocal. 
  Defined.   

  Global Instance LambdaBoxLocal_resource_trace : @LambdaBoxLocal_resource nat.
  Proof.
    constructor. eapply trace_resource_LambdaBoxLocal. 
  Defined.   

  

  (** LambdaANF fuel and trace *)

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

  Definition anf_bound (f_src t_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat /\ (* lower bound *) 
      (f2 <= f1 + t_src)%nat (* upper bound *).


  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
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

Section ANF_proof.

  Context (cenv : conId_map) (ctenv : ctor_env).
  Context (func_tag default_tag : positive).

  (** ** ANF value relation *)

  Definition convert_anf_rel := convert_anf_rel func_tag default_tag cenv.
  Definition convert_anf_rel_exps := convert_anf_rel_exps func_tag default_tag cenv.
  Definition convert_anf_rel_efnlst := convert_anf_rel_efnlst func_tag default_tag cenv.
  Definition convert_anf_rel_branches := convert_anf_rel_branches func_tag default_tag cenv.

  Definition eval_fuel_many := @fuel_sem.eval_fuel_many nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.
  Definition eval_env_fuel := @fuel_sem.eval_env_fuel nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.
  Definition eval_env_step := @fuel_sem.eval_env_step nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.

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

      convert_anf_rel S1' e1 (x :: List.rev fnames ++ env) S2 C1 r1 ->

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

     convert_anf_rel S1 e (x::names) S2 C r ->

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

      convert_anf_rel S e env S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv (anf_bound f t) eq_fuel i
                               (e', (M.set x v' rho))
                               (C|[ e' ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel ctenv rho (C|[ e']|) c eval.OOT tt).


  Definition convert_anf_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat)  :=
    forall rho env C x S S' i e',
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->

      occurs_free e' \subset x |: FromList env ->

      anf_env_rel env vs rho ->

      

      convert_anf_rel S e env S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv
                               (anf_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                          (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                               eq_fuel i
                               (e', (M.set x v' rho))
                               (C|[ e' ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e) <= c)%nat /\ bstep_fuel ctenv rho (C|[ e' ]|) c eval.OOT tt).



  Definition convert_anf_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat)  :=
    forall rho env C ys S S' vs2 e' x c,
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length env)) es ->

      Disjoint _ (FromList env) S ->

      occurs_free e' \subset x |: FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel_exps S es env S' C ys ->

      Forall2 (anf_val_rel) vs1 vs2 ->

      exists rho',
        get_list ys rho' = Some vs2 /\
          (* vs2 rho = Some rho' /\ *)
        forall i,
          preord_env_P ctenv eq_fuel (FromList env) i rho rho' /\
          preord_exp ctenv (anf_bound f (t <+> (2 * Datatypes.length (exps_as_list es))%nat))
                     eq_fuel i (Econstr x c ys e', rho') (C |[ Econstr x c ys  e' ]|, rho).

  Lemma convert_anf_rel_same_set S1 e names S1' C x S2:
    convert_anf_rel S1 e names S1' C x ->
    S1 <--> S2 ->
    exists S2',
      S1' <--> S2' /\
      convert_anf_rel S2 e names S2' C x.
  Proof.
  Admitted.
           
  Lemma convert_anf_result_not_fresh S e names S' C x :
    convert_anf_rel S e names S' C x ->
    ~ x \in S'.
  Proof.
  Admitted.

  Definition P := fun e =>
                    forall (S : Ensemble var) (names : list var)
                           (S' : Ensemble var) (C : exp_ctx) 
                           (x : var)
                           (Hanf : convert_anf_rel S e names S' C x),
                      S' \subset S.

  Require Import stemctx.


  Corollary bound_stem_ctx_comp_f c c' :
    bound_stem_ctx (comp_ctx_f c c') <-->
    bound_stem_ctx c :|: bound_stem_ctx c'.
  Proof.
    symmetry. 
    eapply bound_stem_comp_ctx_mut.
  Qed.
    
  Lemma convert_anf_rel_efnlst_names S fns names fs S' fns' :
    convert_anf_rel_efnlst S fns names fs S' fns' ->
    name_in_fundefs fns' <--> FromList fs.
  Proof.
    intros Hanf. induction Hanf; normalize_sets.
    - now sets.
    - simpl. rewrite IHHanf. reflexivity.
  Qed.
    

  Lemma convert_anf_fresh_subset_strong :
        forall e (S : Ensemble var) (names : list var)
               (S' : Ensemble var) (C : exp_ctx) 
               (x : var), 
          convert_anf_rel S e names S' C x -> 
          S' \subset S \\ bound_stem_ctx C. 
  Proof.
    intros e. 
    eapply expression.exp_ind' with (P := fun e => 
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names S' C x),
                                              S' \subset S \\ bound_stem_ctx C)
           (P0 := fun es =>
                    forall S names S' C x
                           (Hanf : convert_anf_rel_exps S es names S' C x),
                      S' \subset S \\ bound_stem_ctx C)
           (P1 := fun fns => forall S names fs S' fns'
                                    (Hanf : convert_anf_rel_efnlst S fns names fs S' fns'),
                      Disjoint _ S (FromList fs) ->
                      NoDup fs -> 
                      S' \subset S)
           (P2 := fun bs => forall S names S' x cl
                                   (Hanf : convert_anf_rel_branches S bs x names S' cl),
                      S' \subset S); intros; inv Hanf; (try now sets);
      try (try rewrite !bound_stem_ctx_comp_f; repeat normalize_bound_stem_ctx; simpl; repeat normalize_sets; simpl). 
    - eapply Included_trans. eapply H. eassumption. now sets.
    - eapply Included_trans. eapply H0. eassumption.
      eapply Included_trans. eapply Included_Setminus_compat. 
      eapply H. eassumption. reflexivity. now sets.
    - eapply Included_trans. eapply H. eassumption. now sets.
    - eapply Included_trans. eapply H0. eassumption.
      eapply Included_trans. eapply H. eassumption.
      rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx. 
      now xsets. 
    - eapply Included_trans. eapply H0. eassumption.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. eassumption. reflexivity.
      now sets. 
    - eapply Included_trans. eapply H. eassumption. now sets. eassumption.
      rewrite convert_anf_rel_efnlst_names; eauto. reflexivity.
    - now sets.
    - now sets.
    - eapply Included_trans. eapply H0. eassumption.
      eapply Included_trans. eapply Included_Setminus_compat. 
      eapply H. eassumption. reflexivity. now sets.
    - inv H2. 
      specialize H with (C := (Efun1_c (Fcons f func_tag [arg] (C1 |[ Ehalt x1 ]|) Fnil) Hole_c)).
      assert (Hseq : S <--> S \\ [set f]).
      { eapply Included_Setminus_Disjoint. now sets. } 
      assert (Hin : S2 \subset S).
      { eapply convert_anf_rel_same_set with (S2 := S :|: [set f] \\ [set arg] \\ [set f]) in H12.
        destructAll. rewrite H2. 
        eapply Included_trans. eapply H. econstructor; [ | | eassumption ]. now sets.
        constructor. now sets.
        intros Heq. inv Heq. eapply H1. constructor. eassumption. now sets.
        repeat normalize_bound_stem_ctx. simpl. repeat normalize_sets. now sets.
        
        rewrite Setminus_Union, Union_commut with (s1 := [set arg]).
        rewrite <- Setminus_Union, !Setminus_Union_distr, Setminus_Same_set_Empty_set.
        repeat normalize_sets. rewrite <- Hseq. reflexivity. }

      eapply Included_trans. eapply H0; try eassumption.
      
      eapply Disjoint_Included_l. eassumption. now sets. eassumption.
    - eapply Included_trans. eapply H. eassumption.
      rewrite Setminus_Union. eapply Included_trans. eapply Included_Setminus_compat.
      eapply H0. eassumption. reflexivity. now sets.
  Qed.

  Lemma convert_anf_fresh_subset e (S : Ensemble var) (names : list var)
        (S' : Ensemble var) (C : exp_ctx) (x : var): 
    convert_anf_rel S e names S' C x -> 
    S' \subset S. 
  Proof.
    intros. eapply Included_trans. eapply convert_anf_fresh_subset_strong.
    eassumption. now sets.
  Qed.    

  Lemma convert_anf_rel_exps_fresh_subset S e names S' C x :
    convert_anf_rel_exps S e names S' C x ->
    S' \subset S.
  Proof.
    intros Hrel. induction Hrel.
    - now sets.
    - eapply Included_trans. eassumption.
      eapply convert_anf_fresh_subset. eapply H.
  Qed.

  Lemma convert_anf_rel_branches_fresh_subset S bs y names S' bs' :
    convert_anf_rel_branches S bs y names S' bs' ->
    S' \subset S.
  Proof.
    intros Hrel. induction Hrel.
    - now sets.
    - eapply Included_trans.
      eapply convert_anf_fresh_subset. eassumption.
      eapply Setminus_Included_Included_Union. eapply Included_trans.
      eassumption. now sets. 
  Qed.

  Lemma convert_anf_rel_efnlst_fresh_subset S bs y names S' bs' :
    convert_anf_rel_efnlst S bs y names S' bs' ->
    S' \subset S.
  Proof.    
    intros Hrel. induction Hrel.
    - now sets.
    - eapply Included_trans. eassumption. 
      eapply Included_trans. eapply convert_anf_fresh_subset. eassumption.
      now sets.
  Qed.

  Lemma convert_anf_in_env S e names S' C x env v f t : 
    convert_anf_rel S e names S' C x ->
    List.In x names -> 
    eval_env_fuel env e (Val v) f t ->
    Disjoint _ (FromList names) S ->
    exists n, nth_error env n = Some v /\ nth_error names n = Some x.
  Proof.
    intros Hrel. revert env v f t.
    eapply convert_anf_rel_ind with (P := fun S e names S' C x =>
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


  Lemma convert_anf_res_included S e names S' C x :
    convert_anf_rel S e names S' C x ->
    x \in FromList names :|: bound_stem_ctx C.
  Proof.
    revert S names S' C x.
    eapply expression.exp_ind' with (P := fun e =>
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names S' C x),
                                              x \in FromList names :|: bound_stem_ctx C)
                                    (P0 := fun es =>
                                             forall S names S' C x
                                                    (Hanf : convert_anf_rel_exps S es names S' C x),
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
      eapply H0 in H10. inv H10; [ | now eauto ].
      normalize_sets. inv H1; [ | now eauto ].
      inv H2.
      eapply H in H9. inv H9; eauto.
    - repeat normalize_bound_stem_ctx.
      right. left. eapply convert_anf_rel_efnlst_names. eassumption.
      eapply nthN_In. eassumption. 
    - normalize_sets. rewrite bound_stem_ctx_comp_f.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply H in H4. inv H4; eauto.
      + eapply H0 in H9. eapply Included_trans; eauto. now sets.
  Qed.      
      
   Lemma convert_anf_exps_res_included S es names S' C x :
     convert_anf_rel_exps S es names S' C x ->
     FromList x \subset FromList names :|: bound_stem_ctx C.
   Proof.
     revert S es names S' C.
     induction x; intros  S es names S' C Hanf; inv Hanf.
     - repeat normalize_sets. now sets.
     - repeat normalize_sets. eapply Union_Included.
       + eapply Singleton_Included.
         eapply convert_anf_res_included in H6.
         rewrite bound_stem_ctx_comp_f. inv H6; eauto.
       + rewrite bound_stem_ctx_comp_f. eapply Included_trans. eapply IHx; eauto. now sets.         
   Qed.

   Lemma occurs_free_make_proj_ctx ctag vars x i C :
     make_proj_ctx ctag vars x i C ->
     occurs_free_ctx C \subset [set x].
   Proof.
     intros Hctx. induction Hctx.
     - normalize_occurs_free_ctx. now sets.
     - normalize_occurs_free_ctx. now sets.
   Qed.
   
   Lemma bound_stem_make_proj_ctx ctag vars x i C :
     make_proj_ctx ctag vars x i C ->
     bound_stem_ctx C <--> FromList vars.
   Proof.
     intros Hctx. induction Hctx.
     - normalize_bound_stem_ctx. now sets.
     - normalize_bound_stem_ctx. repeat normalize_sets.
       now sets.
   Qed.
   
     
  Lemma convert_anf_occurs_free_ctx S e names S' C x :
    convert_anf_rel S e names S' C x ->
    occurs_free_ctx C \subset FromList names.
  Proof.
    revert S names S' C x.
    eapply expression.exp_ind' with (P := fun e =>
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names S' C x),
                                              occurs_free_ctx C \subset FromList names)
                                    (P0 := fun es =>
                                             forall S names S' C x
                                                    (Hanf : convert_anf_rel_exps S es names S' C x),
                                               occurs_free_ctx C \subset FromList names)
                                    (P1 := fun fns => forall S names fs S' fns'
                                                             (Hanf : convert_anf_rel_efnlst S fns names fs S' fns'),
                                               Disjoint _ S (FromList fs) ->
                                               occurs_free_fundefs fns' \subset FromList names \\ name_in_fundefs fns')
                                    (P2 := fun bs => forall S names S' x cl
                                                            (Hanf : convert_anf_rel_branches S bs x names S' cl),
                                               occurs_free (Ecase x cl) \\ [set x] \subset FromList names); intros; inv Hanf;
      try (now normalize_occurs_free_ctx; sets).
    - repeat normalize_occurs_free_ctx; repeat normalize_occurs_free.
      simpl. assert (Hanf := H9).
      eapply H in H9. eapply convert_anf_res_included in Hanf. 
      eapply Union_Included; [ | now sets ]. 
      eapply Union_Included; [ | now sets ]. 
      eapply Setminus_Included_Included_Union. 
      eapply Included_trans. eapply occurs_free_ctx_app.
      normalize_occurs_free.
      eapply Union_Included.
      eapply Included_trans. eassumption. repeat normalize_sets. now sets.
      eapply Setminus_Included_Included_Union. eapply Singleton_Included. 
      repeat normalize_sets. inv Hanf; eauto. inv H0; eauto.
    - eapply Included_trans. eapply occurs_free_ctx_comp.
      eapply Union_Included.
      + eauto.
      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_ctx_comp.
        eapply Union_Included.
        * eapply Included_trans. eapply H0; eauto. now sets.
        * repeat normalize_occurs_free_ctx. 
          rewrite !Setminus_Union_distr. rewrite !Setminus_Empty_set_abs_r. repeat normalize_sets.
          eapply Union_Included.
          -- eapply Setminus_Included_Included_Union.
             eapply Included_trans. eapply Singleton_Included. eapply convert_anf_res_included.
             eassumption. now sets.
          -- eapply Setminus_Included_Included_Union.
             eapply Included_trans. eapply Singleton_Included. eapply convert_anf_res_included.
             eassumption. now sets.
    - eapply Included_trans. eapply occurs_free_ctx_comp.
      eapply Union_Included.
      + eauto.
      + eapply Setminus_Included_Included_Union. repeat normalize_occurs_free_ctx.
        repeat normalize_sets. 
        eapply Included_trans. eapply convert_anf_exps_res_included. eassumption. now sets.
    - repeat normalize_occurs_free_ctx. repeat normalize_occurs_free. simpl.
      repeat normalize_sets.      
      eapply Union_Included.
      + rewrite Union_commut, <- Setminus_Union. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption. now sets.
      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. 
        eapply occurs_free_ctx_comp. eapply Union_Included.
        * eapply Included_trans.
          eapply H. eassumption. now sets.
        * repeat normalize_occurs_free_ctx. repeat normalize_sets.
          eapply Setminus_Included_Included_Union. eapply Union_Included; [ now sets | ].
          eapply Included_trans. eapply Singleton_Included. 
          eapply convert_anf_res_included. eassumption. now sets.
    - eapply Included_trans. 
      eapply occurs_free_ctx_comp. eapply Union_Included.
      + eauto.
      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption. normalize_sets.
        eapply Union_Included; [ | now sets ].
        eapply Singleton_Included. 
        eapply convert_anf_res_included. eassumption.
    - repeat normalize_occurs_free_ctx. repeat normalize_sets.
      eapply Included_trans. eapply H. eassumption.
      now sets. 
      repeat normalize_sets. eapply Setminus_Included_Included_Union.
      eapply Union_Included; [ | now sets ].
      rewrite FromList_rev, convert_anf_rel_efnlst_names; [ | eassumption ]. now sets.
    - repeat normalize_occurs_free_ctx. repeat normalize_sets. now sets.
    - repeat normalize_occurs_free_ctx. now sets.
    - eapply Included_trans. 
      eapply occurs_free_ctx_comp. eapply Union_Included.
      + eauto.
      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption. now sets.
    - repeat normalize_occurs_free. now sets.
    - specialize H with (C :=  (Efun1_c (Fcons f func_tag [arg] (C1 |[ Ehalt x1 ]|) Fnil) Hole_c)).
      assert (Hseq : S <--> S \\ [set f]).
      { eapply Included_Setminus_Disjoint. normalize_sets. now sets. } 
      assert (Hin : occurs_free_ctx
                       (Efun1_c (Fcons f func_tag [arg] (C1 |[ Ehalt x1 ]|) Fnil) Hole_c) \subset
                       FromList names).
      { eapply convert_anf_rel_same_set with (S2 := S :|: [set f] \\ [set arg] \\ [set f]) in H11.
        destructAll.
        eapply H. econstructor; [ | | eassumption ]. now sets.
        constructor. now sets.
        intros Heq. inv Heq. eapply H1. constructor. eassumption. normalize_sets. now sets.
        rewrite Setminus_Union, Union_commut with (s1 := [set arg]).
        rewrite <- Setminus_Union, !Setminus_Union_distr, Setminus_Same_set_Empty_set.
        repeat normalize_sets. rewrite <- Hseq. reflexivity. }

      rewrite occurs_free_Efun1_c in Hin. normalize_occurs_free_in_ctx. simpl in *.
      repeat normalize_sets. 
      repeat normalize_occurs_free.
      eapply Union_Included.
      + rewrite Union_assoc, <- Setminus_Union. eapply Setminus_Included_Included_Union.
        eapply Union_Included_l in Hin.
        eapply Union_Included_l in Hin.
        rewrite <- Setminus_Union with (s3 := name_in_fundefs fdefs).
        rewrite <- Union_Setminus with (S2 := name_in_fundefs fdefs); [ | now tci ].
        eapply Included_Union_Setminus_Included in Hin; [ | now tci ].
        eapply Setminus_Included_Included_Union. eapply Included_trans.
        eassumption.
        rewrite <- !Union_assoc. 
        rewrite <- Union_Included_Union_Setminus with (s3 := [set f]); [ | now tci | ].
        normalize_sets. now sets. now sets.
      + eapply Setminus_Included_Included_Union. eapply Included_trans.
        eapply H0. eassumption.
        eapply Disjoint_Included_l. eapply convert_anf_fresh_subset. eassumption.
        now sets.
        rewrite Union_commut with (s1 := [set f]), <- Setminus_Union, <- Union_Setminus; tci.
        now sets.
    - repeat normalize_occurs_free. now sets.
    - repeat normalize_occurs_free. rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
      eapply Setminus_Included_Included_Union. eapply Union_Included.
      + eapply Included_trans. eapply occurs_free_ctx_app.
        eapply Union_Included.
        * eapply Included_trans. eapply occurs_free_make_proj_ctx. eassumption. now sets.
        * eapply Setminus_Included_Included_Union.
          eapply Included_trans. eapply occurs_free_ctx_app.
          eapply Union_Included.
          eapply Included_trans. eapply H. eassumption.
          repeat normalize_sets.
          rewrite bound_stem_make_proj_ctx; [ | eassumption ]. now sets.

          repeat normalize_occurs_free.
          eapply Setminus_Included_Included_Union.
          eapply Included_trans. eapply Singleton_Included.
          eapply convert_anf_res_included. eassumption.
          repeat normalize_sets.
          rewrite bound_stem_make_proj_ctx with (C := Cproj); [ | eassumption ]. now sets.          
      + rewrite Union_commut. eapply Included_Union_Setminus_Included. now tci.
        eapply H0. eassumption.
  Qed.

  Lemma convert_anf_bound_stem_ctx S e names S' C x :
    convert_anf_rel S e names S' C x ->
    bound_stem_ctx C \subset S \\ S'.
  Proof.
    revert S names S' C x.
    eapply expression.exp_ind' with (P := fun e =>
                                            forall S names S' C x
                                                   (Hanf : convert_anf_rel S e names S' C x),
                                              bound_stem_ctx C \subset S \\ S')
                                    (P0 := fun es =>
                                             forall S names S' C x
                                                    (Hanf : convert_anf_rel_exps S es names S' C x),
                                               bound_stem_ctx C \subset S \\ S')
                                    (P1 := fun fns => forall S names fs S' fns'
                                                             (Hanf : convert_anf_rel_efnlst S fns names fs S' fns'),
                                               True)
                                    (P2 := fun bs => forall S names S' x cl
                                                            (Hanf : convert_anf_rel_branches S bs x names S' cl),
                                               True); intros; inv Hanf;
      try (now normalize_bound_stem_ctx; sets); try now eauto.
    - repeat normalize_bound_stem_ctx. simpl.
      eapply Union_Included; [ | now sets ]. eapply Union_Included; [ | now sets ].
      eapply Singleton_Included. constructor. inv H4. eassumption.
      eapply convert_anf_fresh_subset in H9. intros Hc. eapply H9. eassumption. reflexivity.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.
      eapply Union_Included; [ | eapply Union_Included ; [ | eapply Union_Included ] ]; try now sets.
      + eapply Included_trans. eapply H. eassumption.
        eapply Included_Setminus_compat. now sets.
        eapply convert_anf_fresh_subset. eassumption.
      + eapply Included_trans. eapply H0. eassumption.
        eapply Included_Setminus_compat.
        eapply Included_trans. eapply convert_anf_fresh_subset. eassumption. now sets. now sets.
      + eapply Singleton_Included. constructor. eassumption. intros Hc.
        eapply convert_anf_fresh_subset in H10. eapply convert_anf_fresh_subset in H5.
        eapply H5. eapply H10. eassumption. reflexivity.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.
      eapply Union_Included; [ | eapply Union_Included  ]; try now sets.
      + eapply Included_trans. eapply H. eassumption.
        eapply Included_Setminus_compat. now sets. reflexivity.
      + eapply Singleton_Included. constructor. eassumption. intros Hc.
        eapply convert_anf_rel_exps_fresh_subset in H9. 
        eapply H9. eassumption. reflexivity.
    - repeat normalize_bound_stem_ctx. simpl.
      eapply Union_Included.
      + eapply Union_Included; try now sets.
        eapply Singleton_Included. constructor; eauto.
        eapply convert_anf_rel_branches_fresh_subset in H13.
        eapply convert_anf_fresh_subset in H12. intros Hc. eapply H13 in Hc.
        eapply H12 in Hc. inv Hc. inv H1. inv H3. eauto.
      + rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.
        eapply Union_Included; [ | eapply Union_Included  ]; try now sets.
        eapply Included_trans. eapply H. eassumption.

        eapply Included_Setminus_compat. now sets.
        eapply convert_anf_rel_branches_fresh_subset. eassumption.
        inv H7. inv H1. eapply Singleton_Included. constructor; eauto.
        intros Hc.
        eapply convert_anf_rel_branches_fresh_subset in H13.
        eapply convert_anf_fresh_subset in H12. eapply H12.
        eapply H13. eassumption. reflexivity.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.
      eapply Union_Included.
      + eapply Included_trans. eapply H. eassumption.
        eapply Included_Setminus_compat. now sets.        
        eapply convert_anf_fresh_subset. eassumption.
      + eapply Included_trans. eapply H0. eassumption. 
        eapply Included_Setminus_compat. 
        eapply convert_anf_fresh_subset. eassumption. now sets.
    - repeat normalize_bound_stem_ctx. normalize_sets.
      rewrite convert_anf_rel_efnlst_names; [ | eassumption ].
      eapply Included_Setminus; [ | eauto ].
      eapply Disjoint_Included_r.
      eapply convert_anf_rel_efnlst_fresh_subset. eassumption.
      now sets.
    - repeat normalize_bound_stem_ctx. normalize_sets.
      eapply Included_Setminus; now sets.
    - repeat normalize_bound_stem_ctx. normalize_sets.
      eapply Included_Setminus; now sets.
    - rewrite !bound_stem_ctx_comp_f. repeat normalize_bound_stem_ctx.
      eapply Union_Included.
      + eapply Included_trans. eapply H. eassumption.
        eapply Included_Setminus_compat. now sets.        
        eapply convert_anf_rel_exps_fresh_subset. eassumption.
      + eapply Included_trans. eapply H0. eassumption. 
        eapply Included_Setminus_compat. 
        eapply convert_anf_fresh_subset. eassumption. now sets.
  Qed.
  
  Lemma cps_val_rel_exists v :
    well_formed_val v ->
    exists v', anf_val_rel v v'. 
  Proof.
    induction v using value_ind'; intros Hwf; inv Hwf.
    - induction vs.
      + eexists (Vconstr (dcon_to_tag default_tag dcon cenv) []). now econstructor. 
      + inv H. inv H1. edestruct IHvs. eassumption. eassumption.
        inv H. destruct H3. eassumption. exists (Vconstr (dcon_to_tag default_tag dcon cenv) (x :: vs')).
        econstructor. econstructor. eassumption. eassumption. reflexivity.
    - (* TODO needs correspondence proof *)
  Admitted. 
  
  
  (* TODO move *) 
  Ltac destruct_tuples :=
    try match goal with
        | [ X : ?A * ?B |- _ ] => destruct X; destruct_tuples
        end.


  (* TODO generalize *)
  Definition one_step : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + 1)%nat = f2.
  
  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.
  

  Lemma preord_exp_Efun_red k e B rho :          
    preord_exp ctenv one_step eq_fuel k (e, def_funs B B rho rho) (Efun B e, rho).
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
    preord_exp ctenv one_step eq_fuel k (e', rho2) (Eapp f ft xs , rho).
  Proof.
    intros r cin cout Hleq Hbstep Hget Hf Hgetl Hsetl.
    do 3 eexists. split. econstructor 2. econstructor; eauto. 
    split. simpl. unfold_all. lia. 
    eapply preord_res_refl; tci.
  Qed.


  Lemma preord_exp_Econstr_red k x ctag ys e rho vs :
    get_list ys rho = Some vs ->
    preord_exp ctenv one_step eq_fuel k (e, M.set x (Vconstr ctag vs) rho) (Econstr x ctag ys e, rho).
  Proof.
    intros Hgvs r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto. 
    split. simpl. unfold_all. lia. 
    eapply preord_res_refl; tci.
  Qed.

  
  Lemma convert_anf_correct :
      forall vs e r f t, eval_env_fuel vs e r f t -> convert_anf_correct_exp vs e r f t.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := convert_anf_correct_exp)
                                     (P0 := convert_anf_correct_exps)
                                     (P := convert_anf_correct_exp_step).
      - (* Con_e *)
        intros es vs r dc fs ts Heval IH1.
        intros rho names C x S1 S2 i e' Hwf Hwfexp Hdis  Hfv Hanf Hcvt.
        split; [ | congruence ].
        intros v v' Heq Hvrel. subst. inv Hcvt. inv Hwfexp. inv Heq.
        inv Hvrel.
        edestruct IH1 with (e' := e'); [ | | | | | eassumption | | ]; try eassumption.
        * now sets.
        (* * repeat normalize_occurs_free. *)
        (*   eapply Union_Included. now sets. *)
        (*   eapply Setminus_Included_Included_Union. *)
          (* eapply Included_trans. eassumption. now sets. *)
        * destructAll. 
          eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
              2:{ intros. rewrite <- app_ctx_f_fuse. simpl. eapply H0. }
              eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
              2:{ intros m. eapply preord_exp_Econstr_red. eassumption. } 
              eapply preord_exp_refl. now eapply eq_fuel_compat.
              eapply preord_env_P_extend.
              2:{ eapply preord_val_refl. now eapply eq_fuel_compat. }

              eapply preord_env_P_antimon. eapply H0.
              eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
              now sets. }
          
          { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *.
            unfold fuel_exp, trace_exp. admit. (* TODO change bound *) (* lia. *) }
          
      - (* Con_e OOT *) admit.

      - (* App_e *) admit.

      - (* App_e OOT 1 *) admit.
        
      - (* App_e OOT 2 *) admit.

      - (* Let_e *)
        intros e1 e2 v1 r env na f1 f2 t1 t2.
        intros Heval1 IH1 Heval2 IH2.
        intros rho names C x S1 S2 i e' Hwf Hwfexp Hdis  Hfv Hanf Hcvt.
        split.

        + intros v v' Heq Hvrel. subst. inv Hcvt. inv Hwfexp.
          
          destruct (Decidable_FromList names). destruct (Dec x1); [ | ].
          * (* x1 \in names *)
            assert (Hin := f).
            rewrite <- app_ctx_f_fuse. 
            eapply preord_exp_post_monotonic.
            2:{ eapply convert_anf_in_env in f; [ | eassumption | eassumption | eassumption ].
                destruct f as [n [Hnth' Hnth]].
                
                assert (Hrel := All_Forall.Forall2_nth_error _ _ _ Hanf Hnth' Hnth).
                
                destruct Hrel as [v1'' [Hget'' Hrel'']].
                
                eapply preord_exp_trans. now tci.
                now eapply eq_fuel_idemp.
                2:{ intros. eapply IH1; [ | | | | | | reflexivity | ]; try eassumption.
                  eapply Included_trans. eapply occurs_free_ctx_app.
                  eapply Union_Included.
                    - eapply Included_trans. eapply convert_anf_occurs_free_ctx. eassumption.
                      normalize_sets. now sets.
                    - eapply Included_trans. eapply Included_Setminus_compat.
                      eassumption. reflexivity.
                      rewrite Setminus_Union_distr.
                      eapply Union_Included; [ |  now sets ].
                      eapply Setminus_Included_Included_Union.
                      eapply Included_trans. eapply Singleton_Included. eapply convert_anf_res_included.
                      eassumption. normalize_sets. now sets. }
                
                eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. unfold convert_anf_correct_exp in IH2.
                    eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                    - constructor; eauto. eapply All_Forall.nth_error_forall; eassumption.
                    - simpl.
                      replace (N.pos (Pos.of_succ_nat (length names))) with
                        (1 + N.of_nat (length names)) by lia. eassumption.
                    - normalize_sets.
                      eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                      eassumption. 
                      eapply Disjoint_Included_l; [ | eassumption ].
                      now sets.
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
                eapply preord_val_refl. now eapply eq_fuel_compat. }

            { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
              intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
              destructAll. destruct_tuples. subst. simpl in *.
              unfold fuel_exp, trace_exp. lia. }
            
          *  (* not (x1 \in names) *)
            assert (Hwfv: well_formed_val v1).
            { eapply (@eval_env_step_preserves_wf _ LambdaBoxLocal_resource_fuel); try reflexivity.
              eapply Heval1. eassumption.
              unfold well_formed_in_env. erewrite Forall2_length; [ | eassumption ]. eassumption. }
            
            assert (Hex : exists v1', anf_val_rel v1 v1').
            { eapply cps_val_rel_exists. eassumption. } 
            
            destruct Hex.                  
            
            rewrite <- app_ctx_f_fuse. eapply preord_exp_post_monotonic.
            2:{ eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. eapply IH1; [ | | | | | | reflexivity | ]; try eassumption.
                    eapply Included_trans. eapply occurs_free_ctx_app.
                    eapply Union_Included.
                    - eapply Included_trans. eapply convert_anf_occurs_free_ctx.
                      eassumption. normalize_sets. now sets.
                    - eapply Included_trans. eapply Included_Setminus_compat.
                      eassumption. reflexivity.
                      rewrite Setminus_Union_distr.
                      eapply Union_Included; [ |  now sets ].
                      eapply Setminus_Included_Included_Union.
                      eapply Included_trans. eapply Singleton_Included.
                      eapply convert_anf_res_included. eassumption.
                      normalize_sets. now sets. }
                
                eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. unfold convert_anf_correct_exp in IH2.
                    eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                    - constructor; eauto.
                    - simpl.
                      replace (N.pos (Pos.of_succ_nat (length names))) with
                        (1 + N.of_nat (length names)) by lia. eassumption.
                    - normalize_sets.
                      eapply Union_Disjoint_l.
                      2:{ eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                          eassumption. now sets. }
                      
                      eapply Disjoint_Included_l.
                      eapply Singleton_Included. eapply convert_anf_res_included. eassumption.
                      eapply Union_Disjoint_l.
                      eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                      eassumption. now sets.
                      
                      eapply Disjoint_Included_l. eapply convert_anf_bound_stem_ctx. eassumption.
                      now sets.
                    - eapply Included_trans. eassumption.
                      normalize_sets. now sets.
                    - constructor.
                      + eexists. split. rewrite M.gss. reflexivity. eassumption.
                      + eapply Forall2_monotonic_strong; [ | eassumption ].
                        intros z1 z2 Hin1 Hin2 Hex. simpl in *. destructAll.
                        eexists. split. rewrite M.gso. eassumption.
                        now intro; subst; eauto.
                        eassumption.  }

                eapply preord_exp_refl. now eapply eq_fuel_compat.
                eapply preord_env_P_extend.
                2:{ eapply preord_val_refl. now eapply eq_fuel_compat. }
                intros z Hinz vz Hget. eexists vz. split.
                rewrite M.gso. now eassumption. intros Heq. subst. eapply n.
                inv Hinz. eapply Hfv in H0. inv H0. congruence. eassumption.
                eapply preord_val_refl. now eapply eq_fuel_compat. }
                     
            { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
              intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
              destructAll. destruct_tuples. subst. simpl in *.
              unfold fuel_exp, trace_exp. lia. }         

        + (* Let_e OOT why is this here *)
          intros Heq. subst. inv Hcvt. inv Hwfexp.
          assert (Hwfv: well_formed_val v1).
          { eapply (@eval_env_step_preserves_wf _ LambdaBoxLocal_resource_fuel); try reflexivity.
            eapply Heval1. eassumption.
            unfold well_formed_in_env. erewrite Forall2_length; [ | eassumption ]. eassumption. }
          
          assert (Hex : exists v1', anf_val_rel v1 v1').
          { eapply cps_val_rel_exists. eassumption. } 

          edestruct IH1 with (e' := C2 |[ e' ]|); [ | | | | | eassumption | ]; eauto.
          admit. admit.
          
      -  (* Let_e OOT *) admit.


      - (* Lam_e *) admit.

      - (* Match_e *) admit.

      - (* Match_e OOT *) admit.

      - (* enil *)
        intros env. unfold convert_anf_correct_exps.
        intros rho names C rs S S' vs e Hwfenv ctag Hwf Hexpwf Hdis Hfv Henv Hanf Hall.
        inv Hall. inv Hanf.
        exists rho. split; eauto. 
        split. 
        intros k. eapply preord_env_P_refl. eapply eq_fuel_compat.
        eapply preord_exp_refl. admit. (* bounds *) 
        eapply preord_env_P_refl. eapply eq_fuel_compat.
        
      -  (* econs *)
        intros env. intros e es v vs f fs t ts Heval IHe Hevalm IHes.
        intros rho names C xs S S' vs' e' x ctag Hwfenv Hwf Hdis Hfv Henv Hanf Hall.
        inv Hall. inv Hanf. inv Hwf.
        rewrite <- app_ctx_f_fuse.
        repeat normalize_sets.
        destruct (Decidable_FromList names). destruct (Dec x0); [ | ].
        { (* x \in names *)
          assert (Hin := f0).
          eapply convert_anf_in_env in f0; [ | eassumption | eassumption | eassumption ].
          destruct f0 as [n [Hnth' Hnth]].
          assert (Hrel := All_Forall.Forall2_nth_error _ _ _ Henv Hnth' Hnth).
          (* simpl in *.       *)
          (* destruct Hrel as [v1'' [Hget'' Hrel'']]. *)
          edestruct IHes with (e' :=  e') (rho := M.set x0 y rho) as [rho' [Hget Hpre]]; [ | | | | | eassumption | eassumption | ]; try eassumption.
          + admit. (* easy sets *)
          + admit.
          + eexists (M.set x0  y rho'). split. simpl. erewrite M.gss.
            admit. (* why same? *)
            
            intros i. split.
            now eapply Hpre. 
             
            eapply preord_exp_post_monotonic.
            2:{ eapply preord_exp_trans. now tci.
                now eapply eq_fuel_idemp.
                2:{ intros. eapply IHe; [ | | | | | | reflexivity | ]; try eassumption.
                    - repeat normalize_occurs_free. admit. 
                      
                }
                

                                2:{ intros. unfold convert_anf_correct_exp in IH2.
                    eapply IH2 with (env := x1 :: names); [ | | | | (* |  *)eassumption | reflexivity | eassumption ].
                    - constructor; eauto. eapply All_Forall.nth_error_forall; eassumption.
                    - simpl.
                      replace (N.pos (Pos.of_succ_nat (length names))) with
                        (1 + N.of_nat (length names)) by lia. eassumption.
                    - normalize_sets.
                      eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                      eassumption. 
                      eapply Disjoint_Included_l; [ | eassumption ].
                      now sets.
                    (* - eapply Included_trans. eassumption. *)
                    (*   normalize_sets. now sets. *)
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
                eapply preord_val_refl. now eapply eq_fuel_compat. }

            { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
              intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
              destructAll. destruct_tuples. subst. simpl in *.

                
                  eapply Included_trans. eapply occurs_free_ctx_app.
                  eapply Union_Included.
                    - eapply Included_trans. eapply convert_anf_occurs_free_ctx. eassumption.
                      normalize_sets. now sets.
                    - eapply Included_trans. eapply Included_Setminus_compat.
                      eassumption. reflexivity.
                      rewrite Setminus_Union_distr.
                      eapply Union_Included; [ |  now sets ].
                      eapply Setminus_Included_Included_Union.
                      eapply Included_trans. eapply Singleton_Included. eapply convert_anf_res_included. 
                      eassumption. normalize_sets. now sets. } 
                
                eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. unfold convert_anf_correct_exp in IH2.
                    eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                    - constructor; eauto. eapply All_Forall.nth_error_forall; eassumption.
                    - simpl.
                      replace (N.pos (Pos.of_succ_nat (length names))) with
                        (1 + N.of_nat (length names)) by lia. eassumption.
                    - normalize_sets.
                      eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                      eassumption. 
                      eapply Disjoint_Included_l; [ | eassumption ].
                      now sets.
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
                eapply preord_val_refl. now eapply eq_fuel_compat. }

            { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
              intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
              destructAll. destruct_tuples. subst. simpl in *.
              unfold fuel_exp, trace_exp. lia. }
            
          *  (* not (x1 \in names) *)
            assert (Hwfv: well_formed_val v1).
            { eapply (@eval_env_step_preserves_wf _ LambdaBoxLocal_resource_fuel); try reflexivity.
              eapply Heval1. eassumption.
              unfold well_formed_in_env. erewrite Forall2_length; [ | eassumption ]. eassumption. }
            
            assert (Hex : exists v1', anf_val_rel v1 v1').
            { eapply cps_val_rel_exists. eassumption. } 
            
            destruct Hex.                  
            
            rewrite <- app_ctx_f_fuse. eapply preord_exp_post_monotonic.
            2:{ eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. eapply IH1; [ | | | | |  | reflexivity | ]; try eassumption.
                    eapply Included_trans. eapply occurs_free_ctx_app.
                    eapply Union_Included.
                    - eapply Included_trans. eapply convert_anf_occurs_free_ctx.
                      eassumption. normalize_sets. now sets.
                    - eapply Included_trans. eapply Included_Setminus_compat.
                      eassumption. reflexivity.
                      rewrite Setminus_Union_distr.
                      eapply Union_Included; [ |  now sets ].
                      eapply Setminus_Included_Included_Union.
                      eapply Included_trans. eapply Singleton_Included.
                      eapply convert_anf_res_included. eassumption.
                      normalize_sets. now sets. }
                
                eapply preord_exp_trans. now tci. now eapply eq_fuel_idemp.
                2:{ intros. unfold convert_anf_correct_exp in IH2.
                    eapply IH2 with (env := x1 :: names); [ | | | | | eassumption | reflexivity | eassumption ].
                    - constructor; eauto.
                    - simpl.
                      replace (N.pos (Pos.of_succ_nat (length names))) with
                        (1 + N.of_nat (length names)) by lia. eassumption.
                    - normalize_sets.
                      eapply Union_Disjoint_l.
                      2:{ eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                          eassumption. now sets. }
                      
                      eapply Disjoint_Included_l.
                      eapply Singleton_Included. eapply convert_anf_res_included. eassumption.
                      eapply Union_Disjoint_l.
                      eapply Disjoint_Included_r. eapply convert_anf_fresh_subset.
                      eassumption. now sets.
                      
                      eapply Disjoint_Included_l. eapply convert_anf_bound_stem_ctx. eassumption.
                      now sets.
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
                eapply preord_val_refl. now eapply eq_fuel_compat. }

            { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
              intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
              destructAll. destruct_tuples. subst. simpl in *.
              unfold fuel_exp, trace_exp. lia. }         
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
            assert (Hoot' : bstep_fuel x8 (Efun (Fcons k1 kon_tag [x9] es' Fnil) e'0) (x4 + 1)%nat OOT tt).
            { replace tt with (tt <+> tt) by reflexivity. econstructor 2. econstructor. simpl. eassumption. }
            
            edestruct H9. reflexivity. eassumption. destructAll.
            eexists. split.
            2:{ replace tt with (tt <+> tt).
                destruct x6; [ | contradiction ]. destruct x11. eassumption.
                reflexivity. } 
            
            simpl. unfold anf_bound, one, one_i in *; simpl; unfold_all.
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
          { unfold inclusion, comp, eq_fuel, one_step, anf_bound, one_i.
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
            
            simpl. unfold anf_bound, one, one_i in *; simpl; unfold_all.
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




    

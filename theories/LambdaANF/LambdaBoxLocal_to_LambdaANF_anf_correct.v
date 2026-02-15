(* Correctness of the ANF transformation from LambdaBoxLocal to LambdaANF *)
(* Follows the same proof technique as LambdaBoxLocal_to_LambdaANF_correct.v (CPS) *)

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
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util
        LambdaANF.tactics identifiers bounds cps_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


(** * ANF Bounds *)

Section Bounds.

  (** LambdaBoxLocal fuel and trace *)

  Definition fuel_exp (e: expression.exp) : nat :=
    match e with
    | Let_e _ _ _ => 0  (* ANF Let_e is just context composition, no overhead *)
    | _ => 1
    end.

  Fixpoint max_m_branches (br : branches_e) : nat :=
    match br with
    | brnil_e => 0
    | brcons_e _ (m, _) e br => max (N.to_nat m) (max_m_branches br)
    end.

  (* This is the cost of the ANF-ed program.
     ANF is more efficient than CPS because there are no continuation calls. *)
  Definition anf_trace_exp (e: expression.exp) : nat :=
    match e with
    | Var_e _ => 1  (* Ehalt *)
    | Lam_e _ _ => 2 (* Efun + Ehalt *)
    | App_e _ _ => 2 (* Eletapp + Ehalt *)
    | Let_e _ _ _ => 0 (* context composition, no overhead *)
    | Fix_e _ _ => 2 (* Efun + Ehalt *)

    | Con_e _ es => 2  (* Econstr + Ehalt *)
    | Match_e _ _ brs => 4 + max_m_branches brs (* Efun + Eletapp + Ecase + projections + Ehalt *)

    | Prf_e => 2 (* Econstr + Ehalt *)
    | Prim_e x => 0
    | Prim_val_e x => 2 (* Eprim_val + Ehalt *)
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
      one_i := anf_trace_exp;
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


(** * ANF Correctness *)

Section Correct.

  Context (prim_map : M.t (kername * string (* C definition *) * bool * nat (* arity *))).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)
          (cenv : ctor_env).

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.


  Definition anf_cvt_rel := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel func_tag default_tag.
  Definition anf_cvt_rel_exps := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_exps func_tag default_tag.
  Definition anf_cvt_rel_efnlst := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_efnlst func_tag default_tag.
  Definition anf_cvt_rel_branches := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_branches func_tag default_tag.


  (** ** ANF value relation *)

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v',  M.get x rho = Some v' /\ P v v') vs vn.

  Inductive anf_fix_rel (fnames : list var) (names : list var) : Ensemble var -> list var -> efnlst -> fundefs -> Ensemble var -> Prop :=
  | anf_fix_fnil :
      forall S, anf_fix_rel fnames names S [] eflnil Fnil S
  | anf_fix_fcons :
      forall S1 S1' S2 S2' S3 fnames' e1 C1 r1 n n' efns B f x,
        Disjoint _ S1 (FromList fnames :|: FromList names) ->
        x \in S1 ->
        S1' \subset S1 \\ [set x] ->
        S2' \subset S2 ->

        anf_cvt_rel S1' e1 (x :: List.rev fnames ++ names) cnstrs S2 C1 r1 ->

        anf_fix_rel fnames names S2' fnames' efns B S3 ->
        anf_fix_rel fnames names S1 (f :: fnames') (eflcons n' (Lam_e n e1) efns)
                    (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) B) S3.


  Inductive anf_val_rel : value -> val -> Prop :=
  | anf_rel_Con :
      forall vs vs' dc c_tag,
        Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
        dcon_to_tag default_tag dc cnstrs = c_tag ->
        anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | anf_rel_Clos :
      forall vs rho names na x f e C1 r1 S1 S2,
        anf_env_rel' anf_val_rel names vs rho ->

        NoDup names ->

        Disjoint var (x |: (f |: FromList names)) S1 ->

        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->

        anf_cvt_rel S1 e (x :: names) cnstrs S2 C1 r1 ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho efns Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->

        NoDup names ->
        NoDup fnames ->

        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (FromList names) (FromList fnames) ->

        nth_error fnames (N.to_nat n) = Some f ->

        anf_fix_rel fnames names S1 fnames efns Bs S2 ->

        anf_val_rel (ClosFix_v vs efns n) (Vfun rho Bs f).


  Definition anf_env_rel : list var -> list value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.


  (** ** Helper lemmas for environment relations *)

  Lemma anf_env_rel_weaken vnames vs x v rho :
    anf_env_rel vnames vs rho ->
    ~ x \in FromList vnames ->
    anf_env_rel vnames vs (M.set x v rho).
  Proof.
    intros Henv Hnin. unfold anf_env_rel, anf_env_rel' in *.
    eapply Forall2_monotonic_strong; [ | eassumption ].
    simpl. intros x1 x2 Hin1 Hin2 Hr. rewrite M.gso; eauto.
    intros Hc; subst; auto.
  Qed.

  Lemma anf_env_rel_extend vnames vs x v v' rho :
    anf_env_rel vnames vs rho ->
    M.get x rho = Some v' ->
    anf_val_rel v v' ->
    anf_env_rel (x :: vnames) (v :: vs) rho.
  Proof.
    intros Henv Hget Hval. unfold anf_env_rel, anf_env_rel' in *.
    econstructor; eauto.
  Qed.

  Lemma anf_env_rel_extend_weaken vnames vs x v v' rho :
    anf_env_rel vnames vs rho ->
    anf_val_rel v v' ->
    ~ x \in FromList vnames ->
    anf_env_rel (x :: vnames) (v :: vs) (M.set x v' rho).
  Proof.
    intros Henv Hval Hnin. unfold anf_env_rel, anf_env_rel' in *.
    econstructor; eauto.
    - rewrite M.gss. eexists. split; eauto.
    - eapply anf_env_rel_weaken; eauto.
  Qed.


  Lemma anf_env_rel_nth_error vnames vs rho n y v :
    anf_env_rel vnames vs rho ->
    nth_error vnames n = Some y ->
    nth_error vs n = Some v ->
    exists v', M.get y rho = Some v' /\ anf_val_rel v v'.
  Proof.
    intros Hrel. revert n y v; induction Hrel; intros n z v Hnth1 Hnth2.
    - destruct n; simpl in *; congruence.
    - destruct n; simpl in *.
      + inv Hnth1. inv Hnth2. destructAll. eauto.
      + eauto.
  Qed.


  (** ** Reduction lemmas *)

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

  Lemma preord_exp_Econstr_red k x ctag ys e rho vs :
    get_list ys rho = Some vs ->
    preord_exp cenv one_step eq_fuel k (e, M.set x (Vconstr ctag vs) rho) (Econstr x ctag ys e, rho).
  Proof.
    intros Hgvs r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  Lemma preord_exp_Eproj_red k x ctag n y e rho v vs :
    M.get y rho = Some (Vconstr ctag vs) ->
    nthN vs n = Some v ->
    preord_exp cenv one_step eq_fuel k (e, M.set x v rho) (Eproj x ctag n y e, rho).
  Proof.
    intros Hget Hnth r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  (* Note: no preord_exp_Eprim_val_red because bstep has no constructor for Eprim_val.
     Eprim_val expressions always OOT in bstep_fuel (BStepf_OOT only).
     See preord_exp_prim_val_compat in logical_relations.v for the vacuous compatibility lemma. *)

  Lemma eq_fuel_idemp :
    inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
  Proof.
    clear. unfold comp, eq_fuel. intro; intros.
    destruct x as [[[? ?] ?] ?].
    destruct y as [[[? ?] ?] ?]. destructAll.
    destruct x as [[[? ?] ?] ?]. congruence.
  Qed.


  (** ** Subset lemma for ANF relation *)

  Lemma Setminus_Included_preserv_alt :
    forall {A: Type} (S1 S2 S3: Ensemble A),
      S1 \subset S2 \\ S3 -> S1 \subset S2.
  Proof.
    intros A S1 S2 S3 H x Hin. apply H in Hin. destruct Hin. assumption.
  Qed.

  Lemma anf_cvt_rel_subset :
    (forall S e vn tgm S' C x,
        anf_cvt_rel S e vn tgm S' C x -> S' \subset S) /\
    (forall S es vn tgm S' C xs,
        anf_cvt_rel_exps S es vn tgm S' C xs -> S' \subset S) /\
    (forall S efns vn fnames tgm S' fdefs,
        anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs -> S' \subset S) /\
    (forall S bs vn r tgm S' pats,
        anf_cvt_rel_branches S bs vn r tgm S' pats -> S' \subset S).
  Proof.
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hrel. inv Hrel. eapply Included_refl.
    - (* Lam_e *)
      intros na e IH S vn tgm S' C x Hrel. inv Hrel.
      fold anf_cvt_rel in *. eapply IH in H9.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* App_e *)
      intros e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      eapply IHe1 in H5. eapply IHe2 in H8.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans. eassumption. eassumption.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_exps in *.
      eapply IH in H8.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - (* Match_e *)
      intros e IHe pars bs IHbs S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      eapply IHe in H8. eapply IHbs in H9.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* Let_e *)
      intros na e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      eapply IHe1 in H3. eapply IHe2 in H6.
      eapply Included_trans. eassumption. eassumption.
    - (* Fix_e *)
      intros efns IHefns n S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_efnlst in *.
      eapply IHefns in H9.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - (* Prf_e *)
      intros S vn tgm S' C x Hrel. inv Hrel.
      eapply Setminus_Included.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hrel. inv Hrel.
      eapply Setminus_Included.
    - (* Prim_e *)
      intros p S vn tgm S' C x Hrel. inv Hrel.
    - (* enil *)
      intros S vn tgm S' C xs Hrel. inv Hrel. eapply Included_refl.
    - (* econs *)
      intros e IHe es IHes S vn tgm S' C xs Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      eapply IHe in H3. eapply IHes in H6.
      eapply Included_trans. eassumption. eassumption.
    - (* eflnil *)
      intros S vn fnames tgm S' fdefs Hrel. inv Hrel. eapply Included_refl.
    - (* eflcons *)
      split.
      + intros na' e' Hlam IHe' efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
        inv H0.
        eapply IHe' in H9. eapply IHefns in H10.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. eapply Setminus_Included.
      + intros Hnot IHe efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. unfold isLambda in Hnot. contradiction.
    - (* brnil *)
      intros S vn r tgm S' pats Hrel. inv Hrel. eapply Included_refl.
    - (* brcons *)
      intros dc p e IHe bs IHbs S vn r tgm S' pats Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      eapply IHe in H13. eapply IHbs in H10.
      eapply Setminus_Included_preserv_alt in H13.
      eapply Included_trans. eassumption. eassumption.
  Qed.


  Lemma anf_cvt_exp_subset S e vn tgm S' C x :
    anf_cvt_rel S e vn tgm S' C x -> S' \subset S.
  Proof. eapply (proj1 anf_cvt_rel_subset). Qed.



  Lemma anf_cvt_rel_efnlst_all_fun_name S efns vn fnames tgm S' fdefs :
    anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs ->
    all_fun_name fdefs = fnames.
  Proof.
    intros H. induction H.
    - reflexivity.
    - simpl. congruence.
  Qed.


  (** ** Alpha-equivalence for ANF values *)

  (* Two target values related to the same source value are preord_val-related.
     Analogous to cps_cvt_val_alpha_equiv in LambdaBoxLocal_to_LambdaANF_util.v. *)
  Lemma anf_cvt_val_alpha_equiv :
    forall k v v1 v2,
      anf_val_rel v v1 -> anf_val_rel v v2 ->
      preord_val cenv eq_fuel k v1 v2.
  Proof. Admitted.


  (* Every well-formed source value has a related target value. *)
  Lemma anf_val_rel_exists :
    forall v, well_formed_val v -> exists v', anf_val_rel v v'.
  Proof. Admitted.


  (* If x1 is a fresh variable (from S, disjoint from vnames), then
     x1 is in the consumed set (S \ S') and not the result variable x2. *)
  Lemma anf_cvt_result_in_consumed S1 S2 e vn tgm C x :
    anf_cvt_rel S1 e vn tgm S2 C x ->
    (x \in FromList vn \/ x \in S1).
  Proof. Admitted.


  (** ** Correctness statements *)

  (* The key insight: correctness is stated for an arbitrary continuation e_k,
     not just Ehalt x. This is necessary because when composing contexts
     (e.g. Let_e produces comp_ctx_f C1 C2), the IH for C1 needs to work
     with C2 |[ e_k ]| as the continuation, not Ehalt x1.

     The disjointness condition ensures e_k doesn't reference intermediate
     variables bound by C (except the result variable x).
     All bound variables of C come from the fresh set S, so requiring
     disjointness with (S \\ S') \\ [set x] captures exactly the right condition. *)

  Definition anf_cvt_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      NoDup vnames ->

      Disjoint _ (FromList vnames) S ->

      anf_env_rel vnames vs rho ->

      anf_cvt_rel S e vnames cnstrs S' C x ->

      forall e_k,
        (* e_k may reference x (the result) but not intermediate vars consumed from S *)
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = (Val v) -> anf_val_rel v v' ->
         preord_exp cenv (anf_bound f t) eq_fuel i
                    (e_k, M.set x v' rho)
                    (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  Definition anf_cvt_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      NoDup vnames ->

      Disjoint _ (FromList vnames) S ->

      anf_env_rel vnames vs rho ->

      anf_cvt_rel S e vnames cnstrs S' C x ->

      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = (Val v) -> anf_val_rel v v' ->
                      preord_exp cenv
                                 (anf_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                            (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                                 eq_fuel i
                                 (e_k, M.set x v' rho)
                                 (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  (* P0: correctness for expression lists. For now a placeholder. *)
  Definition anf_cvt_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat) :=
    True.


  (** ** Main Correctness Theorem *)

  (* The proof proceeds by mutual induction using eval_env_fuel_ind'.
     The scheme requires goals in order:
       P  (eval_env_step):   10 cases
       P0 (eval_fuel_many):  2 cases
       P1 (eval_env_fuel):   5 cases
     Total: 17 cases *)

  Lemma anf_cvt_correct :
    forall vs e r f t,
      @eval_env_fuel _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace vs e r f t ->
      anf_cvt_correct_exp vs e r f t.
  Proof.
    eapply eval_env_fuel_ind' with (P1 := anf_cvt_correct_exp)
                                   (P0 := anf_cvt_correct_exps)
                                   (P := anf_cvt_correct_exp_step).

    (** ** eval_env_step cases (P = anf_cvt_correct_exp_step) *)

    - (* 1. eval_Con_step: Con_e terminates *)
      admit.

    - (* 2. eval_Con_step_OOT: Con_e diverges *)
      intros es es1 es2 e0 vs0 rho0 dc0 fs0 f0 t0 ts0 Hexps Hmany IH_many Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 3. eval_App_step: App_e with Clos_v *)
      intros e1' e2' e_body v2 r0 na0 rho0 rho_clos f1' f2' f3' t1' t2' t3'
             Heval1 IH1 Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
      (* After inv (anf_App):
         C = comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r0 x1 func_tag [x2] Hole_c))
         x = r0  (the result variable)
         Hcvt_e1 : anf_cvt_rel S e1' vnames cnstrs S2 C1 x1
         Hcvt_e2 : anf_cvt_rel S2 e2' vnames cnstrs S3 C2 x2
         H_r_in : r0 \in S3 *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          He2 : anf_cvt_rel _ e2' vnames _ _ _ _,
          Hr : x \in _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2; rename Hr into Hr_in
      end.
      rewrite <- !app_ctx_f_fuse.
      split.
      + (* Termination case *)
        intros v v' Heq Hrel. subst r0.
        (* Get target values for Clos_v and v2 *)
        assert (Hwf_clos : well_formed_val (Clos_v rho_clos na0 e_body)) by admit.
        destruct (anf_val_rel_exists _ Hwf_clos) as [clos_v' Hrel_clos].
        assert (Hwf_v2 : well_formed_val v2) by admit.
        destruct (anf_val_rel_exists _ Hwf_v2) as [v2' Hrel_v2].
        (* Chain: IH1 + env bridge + IH2 + env bridge + Eletapp reduction *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1: C1 layer *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                                               ((S \\ S2) \\ [set x1])) by admit.
                edestruct IH1 as [IH1_val _].
                - eassumption.
                - admit. (* exp_wf *)
                - eassumption.
                - eassumption.
                - eassumption.
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH2: C2 layer, in env with x1 bound *)
            2:{ intros m.
                assert (Henv_x1 : anf_env_rel vnames rho0 (M.set x1 clos_v' rho)) by admit.
                assert (Hdis_letapp : Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                                                 ((S2 \\ S3) \\ [set x2])) by admit.
                edestruct IH2 as [IH2_val _].
                - eassumption.
                - admit. (* exp_wf *)
                - eassumption.
                - admit. (* Disjoint vnames S2 *)
                - exact Henv_x1.
                - exact Hcvt_e2.
                - exact Hdis_letapp.
                - eapply IH2_val; eauto. }
            (* Eletapp step + body evaluation + env bridging *)
            admit. (* The Eletapp reduction: needs IH3 for body, function lookup, etc. *) }
        (* inclusion *)
        admit.
      + (* Divergence case *)
        intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 4. eval_App_step_OOT1: App_e, e1 diverges *)
      intros e1' e2' rho0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 5. eval_App_step_OOT2: App_e, e2 diverges *)
      intros e1' e2' v0 rho0 f1' f2' t1' t2' Heval1 IH1 Hoot2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 6. eval_Let_step: Let_e terminates *)
      intros e1' e2' v1 r0 rho0 na0 f1' f2' t1' t2' Heval1 IH1 Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
      (* After inv (anf_Let):
         C = comp_ctx_f C1 C2, x = x2
         Hcvt_e1 : anf_cvt_rel S e1' vnames cnstrs S2 C1 x1
         Hcvt_e2 : anf_cvt_rel S2 e2' (x1::vnames) cnstrs S' C2 x2 *)
      (* Name the hypotheses from inv *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          He2 : anf_cvt_rel _ e2' (_ :: vnames) _ _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2
      end.
      rewrite <- app_ctx_f_fuse.
      split.
      + intros v v' Heq Hrel. subst r0.
        (* Get v1' with anf_val_rel v1 v1' *)
        assert (Hwfv1 : well_formed_val v1) by admit.
        destruct (anf_val_rel_exists v1 Hwfv1) as [v1' Hrel1].
        (* Chain: env bridging + IH2 + IH1 via preord_exp_trans *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1 for e1, with e_k' = C2|[e_k]| *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S \\ S2) \\ [set x1])) by admit.
                edestruct IH1 as [IH1_val _].
                - eassumption. (* well_formed_env *)
                - admit. (* exp_wf *)
                - eassumption. (* NoDup *)
                - eassumption. (* Disjoint vnames S *)
                - eassumption. (* anf_env_rel *)
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            (* env bridging + IH2 *)
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH2 for e2, in extended env *)
            2:{ intros m.
                assert (Hnd' : NoDup (x1 :: vnames)) by admit.
                assert (Hdis' : Disjoint _ (FromList (x1 :: vnames)) S2) by admit.
                assert (Henv' : anf_env_rel (x1 :: vnames) (v1 :: rho0) (M.set x1 v1' rho)) by admit.
                assert (Hwfe' : exp_wf (N.of_nat (Datatypes.length (x1 :: vnames))) e2') by admit.
                assert (Hdis_ek' : Disjoint _ (occurs_free e_k) ((S2 \\ S') \\ [set x])).
                { eapply Disjoint_Included_r.
                  2: eassumption.
                  intros z Hz. destruct Hz as [Hz1 Hz2].
                  constructor.
                  - constructor.
                    + eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt_e1).
                      destruct Hz1. eassumption.
                    + destruct Hz1. eassumption.
                  - eassumption. }
                edestruct IH2 as [IH2_val _].
                - admit. (* well_formed_env (v1::rho0) *)
                - exact Hwfe'.
                - exact Hnd'.
                - exact Hdis'.
                - exact Henv'.
                - exact Hcvt_e2.
                - exact Hdis_ek'.
                - eapply IH2_val; eauto. }
            (* env bridging: M.set x2 v' rho ≤ M.set x2 v' (M.set x1 v1' rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq2 | Hneq2].
            * subst. intros v1x Hget.
              rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              eapply preord_val_refl. tci.
            * intros v1x Hget. rewrite M.gso in Hget; auto.
              destruct (Pos.eq_dec y x1) as [Heq1 | Hneq1].
              -- (* y = x1: possible if x1 ∈ vnames (Var_e case) *)
                 subst. eexists. split.
                 { rewrite M.gso; auto. rewrite M.gss. reflexivity. }
                 admit. (* preord_val via alpha-equiv *)
              -- eexists. split.
                 { rewrite M.gso; auto. rewrite M.gso; eauto. }
                 eapply preord_val_refl. tci. }
        (* inclusion: comp eq_fuel (comp (anf_bound f2' t2') (anf_bound f1' t1'))
           ⊆ anf_bound (f1'+f2') (t1'+t2') *)
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?].
        intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
        unfold_all. destruct p. destructAll. simpl in *. lia.
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 7. eval_Let_step_OOT: Let_e, e1 diverges *)
      intros e1' e2' rho0 na0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 8. eval_FixApp_step: App_e with ClosFix_v *)
      admit.

    - (* 9. eval_Match_step: Match_e terminates *)
      admit.

    - (* 10. eval_Match_step_OOT: Match_e, e1 diverges *)
      intros e1' rho0 n0 br0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    (** ** eval_fuel_many cases (P0 = anf_cvt_correct_exps) *)

    - (* 11. eval_many_enil *)
      unfold anf_cvt_correct_exps. intros. exact I.

    - (* 12. eval_many_econs *)
      unfold anf_cvt_correct_exps. intros. exact I.

    (** ** eval_env_fuel cases (P1 = anf_cvt_correct_exp) *)

    - (* 13. eval_Var_fuel *)
      intros vs1 n v Hnth.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. (* anf_Var: C = Hole_c, x = v0, S' = S *)
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        (* C = Hole_c, so C |[ e_k ]| = e_k. S' = S so (S\S')\{x} = empty.
           Need: preord_exp (anf_bound 0 0) eq_fuel i (e_k, M.set x v' rho) (e_k, rho).
           By anf_env_rel, x already maps to some v'_old in rho with anf_val_rel v v'_old.
           By alpha-equiv, preord_val eq_fuel i v' v'_old. Then use preord_exp_refl. *)
        eapply preord_exp_post_monotonic.
        2:{ (* preord_exp eq_fuel eq_fuel i ... *)
          eapply preord_exp_refl. now eapply eq_fuel_compat.
          (* preord_env_P eq_fuel (occurs_free e_k) i (M.set x v' rho) rho *)
          intros y Hy.
          destruct (Pos.eq_dec y x) as [Heq | Hneq].
          - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
            edestruct anf_env_rel_nth_error as [v'_old [Hget_old Hrel_old]]; eauto.
            eexists. split. eassumption.
            eapply anf_cvt_val_alpha_equiv; eassumption.
          - intros v1 Hget. rewrite M.gso in Hget; auto.
            eexists. split. eassumption.
            eapply preord_val_refl. tci. }
        (* inclusion eq_fuel (anf_bound <0> <0>) *)
        unfold inclusion, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?]. intros. subst.
        unfold_all. simpl in *. lia.
      + intros Habs. congruence. (* Var_e never OOTs with 0 fuel *)

    - (* 14. eval_Lam_fuel *)
      intros vs1 e1 na1.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt.
      (* After inv: x is the function name, C = Efun1_c (Fcons x func_tag [x1] (C1 |[ Ehalt r1 ]|) Fnil) Hole_c
         Hypotheses from anf_Lam:
           H1 : x1 \in S
           H3 : x \in S \\ [set x1]
           H9 : anf_cvt_rel (S \\ [set x1] \\ [set x]) vs1 (x1 :: vnames) cnstrs S' C1 r1 *)
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { cbn [def_funs]. rewrite M.gss. reflexivity. }
              eapply anf_cvt_val_alpha_equiv. eassumption.
              eapply anf_rel_Clos with (names := vnames); eauto.
              * (* Disjoint var (x1 |: (x |: FromList vnames)) (S \\ [set x1] \\ [set x]) *)
                eapply Union_Disjoint_l.
                { eapply Disjoint_Singleton_l. intros [[_ Habs] _]. apply Habs. constructor. }
                eapply Union_Disjoint_l.
                { eapply Disjoint_Singleton_l. intros [_ Habs]. apply Habs. constructor. }
                eapply Disjoint_Included_r.
                { eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included. }
                eassumption.
              * (* ~ x1 \in x |: FromList vnames *)
                intros Hc. inv Hc.
                -- (* x1 = x *) inv H. destruct H3 as [_ Habs]. apply Habs. constructor.
                -- (* x1 \in FromList vnames *) eapply Hdis. constructor; eauto.
              * (* ~ x \in FromList vnames *)
                intros Hc. eapply Hdis. constructor; eauto.
                destruct H3. assumption.
            - intros v1 Hget. rewrite M.gso in Hget; eauto.
              eexists. split.
              { cbn [def_funs]. rewrite M.gso; eauto. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. simpl in *. lia.
      + intros Habs. congruence.

    - (* 15. eval_Fix_fuel *)
      intros vs1 n1 fnlst1.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
      (* After inv (anf_Fix):
         C = Efun1_c fdefs Hole_c, x = f
         H_fnames_sub : FromList fnames ⊆ S
         H_nodup : NoDup fnames
         H_len : length fnames = efnlength fnlst1
         H_efnlst : anf_cvt_rel_efnlst ... fnlst1 (rev fnames ++ vnames) fnames cnstrs S' fdefs
         H_nth : nth_error fnames (N.to_nat n1) = Some f *)
      match goal with
      | [ Hsub : FromList ?fn \subset S,
          Hnodup : NoDup ?fn,
          Hefn : anf_cvt_rel_efnlst _ _ _ ?fn _ _ _,
          Hnth : nth_error ?fn _ = Some ?f |- _ ] =>
        rename Hsub into Hfnames_sub; rename Hnodup into Hnodup_fnames;
        rename Hefn into Hcvt_efn; rename Hnth into Hnth_f
      end.
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        (* Chain: one_step via Efun_red + eq_fuel via env bridging *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Efun_red. }
            (* env bridging: (e_k, M.set f v' rho) ≤eq_fuel (e_k, def_funs fdefs fdefs rho rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - (* y = f (the selected function name) *)
              subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { eapply def_funs_eq. eapply name_fds_same.
                rewrite (anf_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ _ Hcvt_efn).
                eapply nth_error_In. eassumption. }
              eapply anf_cvt_val_alpha_equiv. eassumption.
              eapply anf_rel_ClosFix with (names := vnames); eauto.
              * (* Disjoint _ (FromList vnames :|: FromList fnames) S1 *)
                admit.
              * (* Disjoint _ (FromList vnames) (FromList fnames) *)
                eapply Disjoint_Included_r. eapply Hfnames_sub. eassumption.
              * (* anf_fix_rel fnames vnames S1 fnames fnlst1 fdefs S2 *)
                admit. (* needs lemma: anf_cvt_rel_efnlst → anf_fix_rel *)
            - (* y ≠ f: y cannot be in FromList fnames because of disjointness *)
              intros v1 Hget. rewrite M.gso in Hget; auto.
              assert (Hnotfn : ~ name_in_fundefs fdefs y).
              { intros Hc. apply name_fds_same in Hc.
                rewrite (anf_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ _ Hcvt_efn) in Hc.
                eapply Hdis_ek. constructor; eauto.
                constructor.
                - constructor.
                  + eapply Hfnames_sub. exact Hc.
                  + intros Hin. admit. (* S' ⊆ S \ FromList fnames, so fnames ∩ S' = ∅ *)
                - intros Habs. inv Habs. congruence. }
              eexists. split.
              { rewrite def_funs_neq; eauto. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. simpl in *. lia.
      + intros Habs. congruence.
      

    - (* 16. eval_OOT *)
      intros vs1 e1 f1 t1 Hlt.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split.
      + intros v v' Heq _. congruence.
      + intros _.
        eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 17. eval_step: wraps eval_env_step into eval_env_fuel *)
      now eauto.

  Admitted.

End Correct.

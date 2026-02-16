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


  (** Setting a variable preserves env_rel when the value is related
      at every position where the variable appears in vnames.
      This generalizes anf_env_rel_weaken (which requires x ∉ vnames). *)
  Lemma anf_env_rel_set vnames vs x v' rho :
    anf_env_rel vnames vs rho ->
    (forall k, nth_error vnames k = Some x ->
      exists v, nth_error vs k = Some v /\ anf_val_rel v v') ->
    anf_env_rel vnames vs (M.set x v' rho).
  Proof.
    unfold anf_env_rel, anf_env_rel'.
    intros Henv Hdup.
    revert vs Henv Hdup.
    induction vnames as [ | y vnames' IH]; intros vs Henv Hdup.
    - inv Henv. constructor.
    - destruct vs as [ | v_s vs']; [inv Henv | ].
      inv Henv. constructor.
      + destruct (Pos.eq_dec y x) as [-> | Hneq].
        * rewrite M.gss.
          destruct (Hdup 0%nat eq_refl) as [v_src [Hnth Hrel]].
          simpl in Hnth. inv Hnth.
          eexists; eauto.
        * rewrite M.gso; [ | auto]. assumption.
      + eapply IH; [assumption | ].
        intros k Hnth. exact (Hdup (S k) Hnth).
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


  Lemma anf_env_rel_length vnames vs rho :
    anf_env_rel vnames vs rho ->
    Datatypes.length vnames = Datatypes.length vs.
  Proof.
    unfold anf_env_rel, anf_env_rel'. intros H.
    induction H; simpl; auto.
  Qed.

  Lemma well_formed_val_from_eval vs e v f t :
    eval_env_fuel vs e (Val v) f t ->
    well_formed_env vs ->
    exp_wf (N.of_nat (Datatypes.length vs)) e ->
    well_formed_val v.
  Proof.
    intros Heval Hwf_env Hwf_e.
    eapply eval_env_step_preserves_wf; eauto.
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

  Definition eq_fuel_n (n : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + n)%nat = f2.

  Lemma preord_exp_Ecase_red k rho ctag vs P e n y :
    M.get y rho = Some (Vconstr ctag vs) ->
    find_tag_nth P ctag e n ->
    preord_exp cenv one_step eq_fuel k (e, rho) (Ecase y P, rho).
  Proof.
    intros Hget Hnth r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    admit. (* caseConsistent — same admit as CPS version *)
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Admitted.

  Lemma ctx_bind_proj_preord_exp :
    forall vars C k r n e rho rho' vs vs' ctag,
      n = (List.length vars) ->
      ~ r \in FromList vars ->
      ctx_bind_proj ctag r vars n = C ->
      M.get r rho = Some (Vconstr ctag (vs ++ vs')) ->
      set_lists (rev vars) vs rho = Some rho' ->
      preord_exp cenv (eq_fuel_n n) eq_fuel k (e, rho') (C |[ e ]|, rho).
  Proof.
    (* Same proof as in LambdaBoxLocal_to_LambdaANF_correct.v lines 993-1050 *)
    Admitted.


  (** ** Subset lemma for ANF relation *)

  Lemma Setminus_Included_preserv_alt :
    forall {A: Type} (S1 S2 S3: Ensemble A),
      S1 \subset S2 \\ S3 -> S1 \subset S2.
  Proof.
    intros A S1 S2 S3 H x Hin. apply H in Hin. destruct Hin. assumption.
  Qed.

  (* Helper tactic: apply an IH to the matching relation hypothesis *)
  Local Ltac apply_cvt_IH IH e :=
    match goal with
    | [ H : anf_cvt_rel _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_exps _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_efnlst _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_branches _ e _ _ _ _ _ |- _ ] => eapply IH in H
    end.

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
    enough (H :
      (forall e S vn tgm S' C x, anf_cvt_rel S e vn tgm S' C x -> S' \subset S) /\
      (forall es S vn tgm S' C xs, anf_cvt_rel_exps S es vn tgm S' C xs -> S' \subset S) /\
      (forall efns S vn fnames tgm S' fdefs, anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs -> S' \subset S) /\
      (forall bs S vn r tgm S' pats, anf_cvt_rel_branches S bs vn r tgm S' pats -> S' \subset S)).
    { destruct H as [H1 [H2 [H3 H4]]]. repeat split; intros; eauto. }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hrel. inv Hrel. eapply Included_refl.
    - (* Lam_e *)
      intros na e IH S vn tgm S' C x Hrel. inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IH e.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* App_e *)
      intros e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans; eassumption.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_exps in *.
      apply_cvt_IH IH es.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - (* Match_e *)
      intros e IHe pars bs IHbs S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHbs bs.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* Let_e *)
      intros na e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans; eassumption.
    - (* Fix_e *)
      intros efns IHefns n S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_efnlst in *.
      apply_cvt_IH IHefns efns.
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
      apply_cvt_IH IHe e. apply_cvt_IH IHes es.
      eapply Included_trans; eassumption.
    - (* eflnil *)
      intros S vn fnames tgm S' fdefs Hrel. inv Hrel. eapply Included_refl.
    - (* eflcons *)
      split.
      + intros na' e' Hlam IHe' efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
        (* inv any remaining Lam_e equalities *)
        repeat match goal with
        | [ H : Lam_e _ _ = Lam_e _ _ |- _ ] => inv H
        end.
        apply_cvt_IH IHe' e'. apply_cvt_IH IHefns efns.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. eapply Setminus_Included.
      + intros Hnot IHe efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. unfold isLambda in Hnot. contradiction.
    - (* brnil *)
      intros S vn r tgm S' pats Hrel. inv Hrel. eapply Included_refl.
    - (* brcons *)
      intros dc p e IHe bs IHbs S vn r tgm S' pats Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHbs bs.
      match goal with
      | [ H : _ \subset _ \\ _ |- _ ] => eapply Setminus_Included_preserv_alt in H
      end.
      eapply Included_trans; eassumption.
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


  (** ** Result variable is consumed by ANF conversion *)

  (* The result variable of an ANF conversion is NOT in the output set S'.
     This is because:
     - For Var_e: result ∈ FromList vn, and Disjoint gives result ∉ S = S'.
     - For all other constructors: result is consumed from S during conversion. *)
  Lemma anf_cvt_result_not_in_output :
    forall e S vn tgm S' C x,
      anf_cvt_rel S e vn tgm S' C x ->
      Disjoint _ (FromList vn) S -> ~ x \in S'.
  Proof.
    enough (H :
      (forall (e : expression.exp) S vn tgm S' C x,
          anf_cvt_rel S e vn tgm S' C x ->
          Disjoint _ (FromList vn) S -> ~ x \in S') /\
      (forall (es : exps), True) /\
      (forall (efns : efnlst), True) /\
      (forall (bs : branches_e), True)).
    { exact (proj1 H). }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt.
      intros Hin. eapply Hdis. constructor; eauto.
      eapply nth_error_In. eassumption.
    - (* Lam_e *)
      intros na e IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      intros Hin.
      assert (S' \subset S \\ [set x1] \\ [set x])
        by (eapply anf_cvt_exp_subset; eassumption).
      apply H in Hin. inv Hin. inv H0. eauto.
    - (* App_e *)
      intros e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      intros Hin. inv Hin. eauto.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      intros Hin.
      assert (S' \subset S \\ [set x])
        by (eapply (proj1 (proj2 anf_cvt_rel_subset)); eassumption).
      apply H in Hin. inv Hin. eauto.
    - (* Match_e *)
      intros e1 IH1 n bs IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      intros Hin. inv Hin. eauto.
    - (* Let_e *)
      intros na e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      eapply IH2; [ eassumption | ].
      rewrite FromList_cons.
      eapply Union_Disjoint_l.
      + eapply Disjoint_Singleton_l.
        eapply IH1; eassumption.
      + eapply Disjoint_Included_r.
        eapply anf_cvt_exp_subset. eassumption.
        eassumption.
    - (* Fix_e *)
      intros efns IH n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_efnlst in *.
      intros Hin.
      assert (Hsub : S' \subset S \\ FromList fnames)
        by (eapply (proj1 (proj2 (proj2 anf_cvt_rel_subset))); eassumption).
      apply Hsub in Hin. inv Hin. apply H0.
      eapply nth_error_In. eassumption.
    - (* Prf_e *)
      intros S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_e *) intros. inv H. (* no ANF conversion for Prim_e *)
    - (* enil *) exact I.
    - (* econs *) intros; exact I.
    - (* eflnil *) exact I.
    - (* eflcons *)
      split; intros; exact I.
    - (* brnil *) exact I.
    - (* brcons *) intros; exact I.
  Qed.


  (** ** Environment consistency and variable lookup *)

  (* Two positions in vn that map to the same variable also map to
     the same value in rho. This is a weaker property than NoDup
     that propagates through Let_e extensions. *)
  Definition env_consistent (vn : list var) (rho : list value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.

  Lemma NoDup_env_consistent (vn : list var) (rho : list value) :
    NoDup vn -> env_consistent vn rho.
  Proof.
    intros Hnd i j x Hi Hj.
    assert (Heq : i = j).
    { clear rho. revert j vn Hnd Hi Hj. induction i; intros j vn Hnd Hi Hj.
      - destruct vn; simpl in *; [ discriminate | ]. inv Hi.
        destruct j; [ reflexivity | ].
        simpl in Hj. inv Hnd. exfalso. apply H1. eapply nth_error_In. eassumption.
      - destruct vn; simpl in *; [ discriminate | ].
        destruct j; simpl in *.
        + inv Hnd. inv Hj. exfalso. apply H1. eapply nth_error_In. eassumption.
        + inv Hnd. f_equal. eapply IHi; eassumption. }
    subst. reflexivity.
  Qed.

  Lemma env_consistent_extend vn rho x1 v1 :
    env_consistent vn rho ->
    (forall k, nth_error vn k = Some x1 -> nth_error rho k = Some v1) ->
    env_consistent (x1 :: vn) (v1 :: rho).
  Proof.
    intros Hcons Hx1 i j y Hi Hj.
    destruct i as [ | i'], j as [ | j']; simpl in *.
    - reflexivity.
    - inv Hi. specialize (Hx1 j' Hj). rewrite Hx1. reflexivity.
    - inv Hj. specialize (Hx1 i' Hi). rewrite Hx1. reflexivity.
    - eapply Hcons; eassumption.
  Qed.

  (* Helper: result of non-Var ANF conversion is in S, hence not in FromList vn. *)
  Local Ltac anf_result_in_S :=
    match goal with
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S |- _ ] =>
      exfalso; eapply Hdis; constructor; [ exact Hin | exact Hmem ]
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S2,
        Hsub : ?S2 \subset ?S |- _ ] =>
      exfalso; eapply Hdis; constructor; [ exact Hin | eapply Hsub; exact Hmem ]
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S3,
        Hsub2 : ?S3 \subset ?S2,
        Hsub1 : ?S2 \subset ?S |- _ ] =>
      exfalso; eapply Hdis; constructor;
      [ exact Hin | eapply Hsub1; eapply Hsub2; exact Hmem ]
    end.

  (** If the result variable of an ANF conversion equals vn[i],
      then the evaluation result equals rho[i].
      Proof by mutual induction on the evaluation derivation. *)
  Lemma anf_cvt_rel_var_lookup :
    forall rho e r f t,
      @eval_env_fuel _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                     rho e r f t ->
      forall v, r = Val v ->
      forall S vn tgm S' C x i,
        anf_cvt_rel S e vn tgm S' C x ->
        Disjoint _ (FromList vn) S ->
        env_consistent vn rho ->
        nth_error vn i = Some x ->
        nth_error rho i = Some v.
  Proof.
    pose (Plookup := fun (rho : fuel_sem.env) (e : expression.exp)
                          (r : result) (f : nat) (t : nat) =>
      forall v, r = Val v ->
      forall S vn tgm S' C x i,
        anf_cvt_rel S e vn tgm S' C x ->
        Disjoint _ (FromList vn) S ->
        env_consistent vn rho ->
        nth_error vn i = Some x ->
        nth_error rho i = Some v).
    intros rho e r f t Heval.
    eapply @eval_env_fuel_ind' with
      (Hf := LambdaBoxLocal_resource_fuel)
      (Ht := LambdaBoxLocal_resource_trace)
      (P := Plookup)
      (P0 := fun _ _ _ _ _ => True)
      (P1 := Plookup);
    try (unfold Plookup; clear Plookup).

    (** eval_env_step cases (P) *)

    - (* 1. eval_Con_step *)
      intros es vs0 rho0 dc fs ts Hmany _ v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      anf_result_in_S.

    - (* 2. eval_Con_step_OOT *)
      intros. congruence.

    - (* 3. eval_App_step *)
      intros e1 e2 e1' v2 r0 na rho0 rho' f1 f2 f3 t1 t2 t3
             Heval1 IH1 Heval2 IH2 Heval3 IH3
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      assert (Hsub2 : S3 \subset S2)
        by (eapply anf_cvt_exp_subset; eassumption).
      assert (Hsub1 : S2 \subset S)
        by (eapply anf_cvt_exp_subset; eassumption).
      anf_result_in_S.

    - (* 4. eval_App_step_OOT1 *) intros. congruence.
    - (* 5. eval_App_step_OOT2 *) intros. congruence.

    - (* 6. eval_Let_step — the key case *)
      intros e1 e2 v1 r0 rho0 na f1 f2 t1 t2
             Heval1 IH1 Heval2 IH2
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      subst. inv Hcvt. fold anf_cvt_rel in *.
      (* We have:
         H8 : anf_cvt_rel S e1 vn tgm S2 C1 x1
         H9 : anf_cvt_rel S2 e2 (x1::vn) tgm S' C2 x
         Heval1 : eval_env_fuel rho0 e1 (Val v1) f1 t1
         Heval2 : eval_env_fuel (v1::rho0) e2 (Val v) f2 t2
         Hnth : nth_error vn i = Some x *)
      eapply IH2 with (i := Datatypes.S i).
      + reflexivity.
      + eassumption.
      + (* Disjoint (FromList (x1::vn)) S2 *)
        rewrite FromList_cons.
        eapply Union_Disjoint_l.
        * eapply Disjoint_Singleton_l.
          eapply anf_cvt_result_not_in_output; eassumption.
        * eapply Disjoint_Included_r.
          eapply anf_cvt_exp_subset. eassumption.
          eassumption.
      + (* env_consistent (x1::vn) (v1::rho0) *)
        eapply env_consistent_extend; [ exact Hcons | ].
        intros k Hk. eapply IH1; [ reflexivity | eassumption .. ].
      + (* nth_error (x1::vn) (S i) = Some x *)
        simpl. exact Hnth.

    - (* 7. eval_Let_step_OOT *) intros. congruence.

    - (* 8. eval_FixApp_step *)
      intros e1 e2 e' rho0 rho' rho'' n na fnlst v2 r0
             f1 f2 f3 t1 t2 t3
             Heval1 IH1 _ _ Heval2 IH2 Heval3 IH3
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      assert (Hsub2 : S3 \subset S2)
        by (eapply anf_cvt_exp_subset; eassumption).
      assert (Hsub1 : S2 \subset S)
        by (eapply anf_cvt_exp_subset; eassumption).
      anf_result_in_S.

    - (* 9. eval_Match_step *)
      intros e1 e' rho0 dc vs0 n brnchs r0 f1 f2 t1 t2
             Heval1 IH1 _ Heval2 IH2
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      (* x = r ∈ S3. Chain: S3 ⊆ S2 ⊆ S_body ⊆ S *)
      match goal with
      | [ Hbr : anf_cvt_rel_branches _ _ _ _ _ ?S3 _,
          He1 : anf_cvt_rel _ _ _ _ ?S2 _ _,
          Hr : _ \in ?S3 |- _ \in ?S ] =>
        eapply Setminus_Included; eapply Setminus_Included;
        eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ He1);
        eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset)) _ _ _ _ _ _ _ Hbr);
        exact Hr
      end.

    - (* 10. eval_Match_step_OOT *) intros. congruence.

    (** eval_fuel_many cases (P0 = True) *)
    - (* 11. eval_many_enil *) intros. exact I.
    - (* 12. eval_many_econs *) intros. exact I.

    (** eval_env_fuel cases (P1) *)

    - (* 13. eval_Var_fuel *)
      intros n rho0 v0 Hnth_rho v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth_vn.
      inv Hv. inv Hcvt.
      unfold env_consistent in Hcons.
      match goal with
      | [ Hnth_src : nth_error ?vn (N.to_nat ?n) = Some ?x |- _ ] =>
        rewrite (Hcons i (N.to_nat n) x Hnth_vn Hnth_src)
      end.
      exact Hnth_rho.

    - (* 14. eval_Lam_fuel *)
      intros e0 rho0 na v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hv. inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      eapply Setminus_Included.
      match goal with
      | [ H : _ \in _ |- _ \in _ ] => exact H
      end.

    - (* 15. eval_Fix_fuel *)
      intros n rho0 fnlst v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hv. inv Hcvt. fold anf_cvt_rel_efnlst in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      match goal with
      | [ H : FromList _ \subset _ |- _ \in _ ] =>
        eapply H; eapply nth_error_In; eassumption
      end.

    - (* 16. eval_OOT *) intros. congruence.
    - (* 17. eval_step *)
      intros rho0 e0 r0 f0 t0 Hstep IH. exact IH.
    - (* derivation *) exact Heval.
  Unshelve. all: exact 0%nat.
  Qed.


  (** Exps version: if xs[j] = vn[i], then vs[j] = rho[i]. *)
  Lemma anf_cvt_rel_exps_var_lookup rho es vs f t :
    @eval_fuel_many _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                    rho es vs f t ->
    forall S vn tgm S' C xs,
      anf_cvt_rel_exps S es vn tgm S' C xs ->
      Disjoint _ (FromList vn) S ->
      env_consistent vn rho ->
      forall j i x,
        nth_error xs j = Some x ->
        nth_error vn i = Some x ->
        exists v, nth_error vs j = Some v /\ nth_error rho i = Some v.
  Proof.
    intros Hmany. induction Hmany as [ | rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval Hmany IH].
    - (* eval_many_enil *)
      intros S vn tgm S' C xs Hcvt Hdis Hcons j i x Hj Hi.
      inv Hcvt. destruct j; simpl in Hj; discriminate.
    - (* eval_many_econs *)
      intros S vn tgm S' C xs Hcvt Hdis Hcons j i x Hj Hi.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      destruct j as [ | j']; simpl in Hj.
      + (* j = 0: xs[0] = x1 *)
        inv Hj. exists v0. split; [ reflexivity | ].
        eapply anf_cvt_rel_var_lookup; [ eassumption | reflexivity | eassumption .. ].
      + (* j > 0: use IH on the tail *)
        eapply IH; [ eassumption | | exact Hcons | exact Hj | exact Hi ].
        eapply Disjoint_Included_r.
        eapply anf_cvt_exp_subset. eassumption.
        exact Hdis.
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


  (* A fresh result variable (x ∈ S) is consumed by the conversion: x ∉ S'. *)
  Lemma anf_cvt_result_consumed S e vn tgm S' C x :
    anf_cvt_rel S e vn tgm S' C x ->
    Disjoint _ (FromList vn) S ->
    x \in S -> ~ x \in S'.
  Proof. Admitted.


  (* If the result variable x of a conversion is in vnames (Var_e case),
     then the ANF value at x in the environment is related to the
     evaluation result via anf_val_rel. *)
  Lemma anf_cvt_result_in_vnames_eval S e vn tgm S' C x vs rho v f t v' :
    anf_env_rel vn vs rho ->
    NoDup vn ->
    Disjoint _ (FromList vn) S ->
    anf_cvt_rel S e vn tgm S' C x ->
    x \in FromList vn ->
    @eval_env_fuel nat LambdaBoxLocal_resource_fuel
                   LambdaBoxLocal_resource_trace vs e (Val v) f t ->
    M.get x rho = Some v' ->
    anf_val_rel v v'.
  Proof. Admitted.


  (** ** Branch extraction and Ecase helpers *)

  (* Extract branch data from the branches relation:
     given find_branch finds a source branch, extract the ANF conversion data
     (projection vars, body context, find_tag_nth position). *)
  Lemma anf_cvt_rel_branches_find_branch S1 brs vn r S2 pats dc e tg n_arity :
    anf_cvt_rel_branches S1 brs vn r cnstrs S2 pats ->
    find_branch dc n_arity brs = Some e ->
    tg = dcon_to_tag default_tag dc cnstrs ->
    exists vars S_mid S_out C_br r_br ctx_p m,
      FromList vars \subset S_mid /\
      List.length vars = N.to_nat n_arity /\
      NoDup vars /\
      ctx_bind_proj tg r vars (List.length vars) = ctx_p /\
      find_tag_nth pats tg (app_ctx_f ctx_p (C_br |[ Ehalt r_br ]|)) m /\
      anf_cvt_rel (S_mid \\ FromList vars) e (vars ++ vn) cnstrs S_out C_br r_br /\
      S_mid \subset S1.
  Proof.
    (* By induction on anf_cvt_rel_branches, matching on find_branch *)
    Admitted.

  Lemma find_branch_max_m_branches dc n brs e :
    find_branch dc n brs = Some e ->
    (N.to_nat n <= max_m_branches brs)%nat.
  Proof.
    intros Hfind. induction brs as [ | d' p e' brs' IH]. 
    - discriminate. 
    - destruct p as [m lnames]. simpl in Hfind. simpl.
      match type of Hfind with
      | context [if ?c then _ else _] => destruct c
      end.
      + destruct (N.eq_dec m n).
        * subst. apply Nat.le_max_l.
        * unfold nargs in Hfind. simpl in Hfind. destruct (N.eq_dec m n); [congruence | discriminate].
      + etransitivity; [exact (IH Hfind) | apply Nat.le_max_r].
  Qed.

  (* Helper: extract a specific function entry from an anf_fix_rel bundle.
     Given the nth function name and the nth source body, find_def locates
     the corresponding ANF function definition in the bundled fundefs. *)
  Lemma anf_fix_rel_find_def :
    forall fnames0 names0 S1 fnames_list efns Bs S2 idx f na e_body,
      anf_fix_rel fnames0 names0 S1 fnames_list efns Bs S2 ->
      nth_error fnames_list idx = Some f ->
      enthopt idx efns = Some (Lam_e na e_body) ->
      NoDup fnames_list ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel S_body1 e_body (x_pc :: List.rev fnames0 ++ names0) cnstrs S_body2 C_body r_body.
  Proof.
    intros fnames0 names0 S1 fnames_list efns Bs S2 idx f na e_body
      Hrel Hnth Henth Hnd.
    revert idx f na e_body Hnth Henth Hnd.
    induction Hrel; intros idx0 f0 na0 e_body0 Hnth Henth Hnd.
    - (* anf_fix_fnil: fnames_list = [], impossible *)
      destruct idx0; discriminate.
    - (* anf_fix_fcons *)
      destruct idx0 as [ | idx'].
        (* idx = 0: this function *)
      + simpl in Hnth. inv Hnth.
        simpl in Henth. inv Henth.
        do 5 eexists. split.
        * simpl. destruct (M.elt_eq f0 f0); [ reflexivity | congruence ].
        * eassumption.
      + (* idx = S idx': later function *)
        simpl in Hnth. simpl in Henth.
        inv Hnd.
        edestruct IHHrel as (x_pc' & C_body' & r_body' & S_body1' & S_body2' & Hfind' & Hcvt').
        * exact Hnth.
        * exact Henth.
        * assumption.
        * do 5 eexists. split.
          -- simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
             ++ exfalso. subst. apply H6. eapply nth_error_In. exact Hnth.
             ++ exact Hfind'.
          -- exact Hcvt'.
  Qed.


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


  (** ** Helper: set_many *)
  Fixpoint set_many (xs : list var) (vs : list val) (rho : M.t val) : M.t val :=
    match xs, vs with
    | x :: xs', v :: vs' => M.set x v (set_many xs' vs' rho)
    | _, _ => rho
    end.

  Lemma get_list_set_many xs vs rho :
    NoDup xs ->
    Datatypes.length xs = Datatypes.length vs ->
    get_list xs (set_many xs vs rho) = Some vs.
  Proof.
    revert vs. induction xs; intros vs Hnd Hlen; destruct vs; simpl in *; try lia.
    - reflexivity.
    - inv Hnd. rewrite M.gss.
      rewrite get_list_set_neq.
      + rewrite IHxs; auto.
      + intros Hc. apply H1. assumption.
  Qed.

  Lemma set_many_get_neq xs vs rho y :
    ~ List.In y xs ->
    M.get y (set_many xs vs rho) = M.get y rho.
  Proof.
    revert vs. induction xs; intros vs Hnin; destruct vs; simpl in *; auto.
    rewrite M.gso. apply IHxs. tauto. intros Heq; subst. apply Hnin. left; auto.
  Qed.

  Lemma set_many_set_comm x v xs vs rho :
    ~ List.In x xs ->
    forall y, M.get y (M.set x v (set_many xs vs rho)) =
              M.get y (set_many xs vs (M.set x v rho)).
  Proof.
    revert vs. induction xs; intros vs Hnin y; destruct vs; simpl in *; auto.
    assert (Ha : a <> x) by tauto.
    assert (Hx : ~ List.In x xs) by tauto.
    destruct (Pos.eq_dec y a).
    - subst.
      destruct (Pos.eq_dec a x).
      + exfalso; tauto.
      + rewrite M.gso. 2: auto. rewrite !M.gss. reflexivity.
    - destruct (Pos.eq_dec y x).
      + subst. rewrite M.gss.
        rewrite M.gso. 2: intro Hc; subst; tauto.
        rewrite set_many_get_neq. 2: auto.
        rewrite M.gss. reflexivity.
      + rewrite M.gso; auto. rewrite M.gso; auto. rewrite M.gso; auto.
        rewrite <- (IHxs vs Hx y). rewrite M.gso; auto.
  Qed.


  (** Looking up the first occurrence of x in set_many returns the
      corresponding value from vs. *)
  Lemma set_many_get_first xs vs rho x k :
    Datatypes.length xs = Datatypes.length vs ->
    nth_error xs k = Some x ->
    (forall (j : nat), (j < k)%nat -> nth_error xs j <> Some x) ->
    exists v, nth_error vs k = Some v /\
      M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k Hlen Hnth Hfirst.
    - destruct k; simpl in Hnth; discriminate.
    - destruct vs as [ | v0 vs'].
      { simpl in Hlen; lia. }
      simpl in Hlen.
      destruct k as [ | k'].
      + simpl in Hnth. inv Hnth. simpl.
        rewrite M.gss. eexists; eauto.
      + simpl in Hnth. simpl.
        assert (Ha_neq : a <> x).
        { intros ->. eapply (Hfirst 0%nat). lia. simpl. reflexivity. }
        rewrite M.gso. 2: now apply not_eq_sym.
        apply IH.
        * lia.
        * exact Hnth.
        * intros j Hj. apply (Hfirst (S j)). lia.
  Qed.

  (** Changing the base env for a key different from z doesn't affect
      M.get z through set_many. *)
  Lemma set_many_set_neq_base z x v xs vs rho :
    z <> x ->
    M.get z (set_many xs vs (M.set x v rho)) = M.get z (set_many xs vs rho).
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hneq.
    - simpl. rewrite M.gso; auto.
    - destruct vs as [ | va vs'].
      + simpl. rewrite M.gso; auto.
      + simpl. destruct (Pos.eq_dec z a) as [-> | Hza].
        * rewrite !M.gss. reflexivity.
        * rewrite !M.gso by auto. apply IH. exact Hneq.
  Qed.


  (** Every variable in xs is bound in set_many xs vs rho. *)
  Lemma set_many_get_in x xs vs rho :
    List.In x xs ->
    Datatypes.length xs = Datatypes.length vs ->
    exists v, M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hin Hlen.
    - destruct Hin.
    - destruct vs as [ | v vs']. { simpl in Hlen; lia. }
      simpl. destruct Hin as [-> | Hin'].
      + exists v. apply M.gss.
      + destruct (Pos.eq_dec x a) as [-> | Hneq].
        * exists v. apply M.gss.
        * rewrite M.gso by auto. apply IH. assumption. simpl in Hlen; lia.
  Qed.

  (** Variables not in xs are unaffected by set_many. *)
  Lemma set_many_get_notin y xs vs (rho : M.t val) :
    ~ List.In y xs ->
    M.get y (set_many xs vs rho) = M.get y rho.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hnin.
    - reflexivity.
    - destruct vs as [ | v vs']. { reflexivity. }
      simpl. rewrite M.gso by (intro; apply Hnin; left; auto).
      apply IH. intro; apply Hnin; right; auto.
  Qed.

  (** If every variable in xs is bound in rho, get_list succeeds. *)
  Lemma get_list_exists xs (rho : M.t val) :
    (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
    exists vs, get_list xs rho = Some vs.
  Proof.
    induction xs as [ | a xs' IH]; intros Hbound.
    - exists []. reflexivity.
    - destruct (Hbound a (or_introl eq_refl)) as [v Hv].
      destruct (IH (fun x Hin => Hbound x (or_intror Hin))) as [vs_rest Hvs].
      exists (v :: vs_rest). simpl. rewrite Hv, Hvs. reflexivity.
  Qed.

  (** Adding M.set a v on top of rho preserves get_list when:
      - positions where xs has a already have value v in vs. *)
  Lemma get_list_set_shadow xs a v (rho : M.t val) vs :
    get_list xs rho = Some vs ->
    (forall (k : nat), nth_error xs k = Some a -> nth_error vs k = Some v) ->
    get_list xs (M.set a v rho) = Some vs.
  Proof.
    revert vs. induction xs as [ | b xs' IH]; intros vs Hgl Hshadow.
    - exact Hgl.
    - simpl in Hgl.
      destruct (M.get b rho) eqn:Hb; [ | discriminate].
      destruct (get_list xs' rho) eqn:Hrest; [ | discriminate].
      inv Hgl. simpl.
      destruct (Pos.eq_dec b a) as [-> | Hneq].
      + rewrite M.gss.
        assert (Hv := Hshadow 0%nat eq_refl). simpl in Hv. inv Hv.
        assert (Hgl' : get_list xs' (M.set a v rho) = Some l).
        { eapply IH. reflexivity. intros k Hk. exact (Hshadow (S k) Hk). }
        rewrite Hgl'. reflexivity.
      + rewrite M.gso by auto. rewrite Hb.
        assert (Hgl' : get_list xs' (M.set a v rho) = Some l).
        { eapply IH. reflexivity. intros k Hk. exact (Hshadow (S k) Hk). }
        rewrite Hgl'. reflexivity.
  Qed.

  (** get_list xs (set_many xs vs rho) = Some vs, provided duplicate
      positions in xs carry the same value in vs. *)
  Lemma get_list_set_many_dup xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    (forall (i j : nat), (i < j)%nat ->
       nth_error xs i = nth_error xs j ->
       nth_error xs i <> None ->
       nth_error vs i = nth_error vs j) ->
    get_list xs (set_many xs vs rho) = Some vs.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hlen Hdup.
    - destruct vs; [ reflexivity | simpl in Hlen; lia].
    - destruct vs as [ | v vs']. { simpl in Hlen; lia. }
      simpl. rewrite M.gss.
      assert (Hgl : get_list xs' (M.set a v (set_many xs' vs' rho)) = Some vs').
      { eapply get_list_set_shadow.
        - eapply IH.
          + simpl in Hlen; lia.
          + intros i j Hij Hnth Hnn.
            apply (Hdup (S i) (S j)). lia. exact Hnth. exact Hnn.
        - intros k Hk.
          assert (H0Sk := Hdup 0%nat (S k) ltac:(lia) ltac:(simpl; symmetry; exact Hk) ltac:(discriminate)).
          simpl in H0Sk. congruence. }
      rewrite Hgl. reflexivity.
  Qed.

  (** Replace values in vs with values from rho where available.
      For each position i, if M.get xs[i] rho = Some v, use v; otherwise use vs[i].
      This ensures duplicate positions in xs get the same value (since M.get is deterministic). *)
  Fixpoint replace_with_rho (xs : list var) (vs : list val) (rho : M.t val) : list val :=
    match xs, vs with
    | x :: xs', v :: vs' =>
      (match M.get x rho with Some v' => v' | None => v end) :: replace_with_rho xs' vs' rho
    | _, _ => nil
    end.

  Lemma replace_with_rho_length xs vs rho :
    Datatypes.length (replace_with_rho xs vs rho) =
    Nat.min (Datatypes.length xs) (Datatypes.length vs).
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros [ | v vs']; simpl;
      try reflexivity; destruct (M.get a rho); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma replace_with_rho_length_eq xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    Datatypes.length (replace_with_rho xs vs rho) = Datatypes.length xs.
  Proof.
    intros Hlen. rewrite replace_with_rho_length. lia.
  Qed.

  Lemma replace_with_rho_nth_some xs vs rho k y v :
    nth_error xs k = Some y ->
    M.get y rho = Some v ->
    nth_error (replace_with_rho xs vs rho) k = Some v.
  Proof.
  Admitted.
    (* revert vs k. induction xs as [ | a xs' IH]; intros vs k.
    - destruct k; simpl; intros; discriminate.
    - destruct vs as [ | w vs']; [ destruct k; simpl; intros; congruence | ].
      destruct k as [ | k']; simpl.
      + intros Hnth Hget. inversion Hnth; subst. rewrite Hget. reflexivity.
      + intros Hnth Hget. destruct (M.get a rho); eapply IH; eassumption.
  Qed. *)

  Lemma replace_with_rho_nth_none xs vs rho k y :
    nth_error xs k = Some y ->
    M.get y rho = None ->
    Datatypes.length xs = Datatypes.length vs ->
    nth_error (replace_with_rho xs vs rho) k = nth_error vs k.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k.
    - destruct k; simpl; intros; congruence.
    - destruct vs as [ | w vs']; [ destruct k; simpl; intros; try congruence; lia | ].
      destruct k as [ | k']; simpl.
      + intros Hnth Hget Hlen. inversion Hnth; subst. rewrite Hget. reflexivity.
      + intros Hnth Hget Hlen. destruct (M.get a rho); eapply IH; try eassumption; simpl in Hlen; lia.
  Qed.

  (** set_many with replace_with_rho preserves all existing rho bindings *)
  Lemma set_many_replace_preserves y xs vs (rho : M.t val) v :
    M.get y rho = Some v ->
    Datatypes.length xs = Datatypes.length vs ->
    M.get y (set_many xs (replace_with_rho xs vs rho) rho) = Some v.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros [ | w vs'] Hget Hlen; simpl in *.
    - exact Hget.
    - exact Hget.
    - exact Hget.
    - destruct (Pos.eq_dec y a) as [-> | Hneq].
      + rewrite M.gss. rewrite Hget. reflexivity.
      + rewrite M.gso by auto. eapply IH. exact Hget. lia.
  Qed.

  (** Duplicate condition: when M.get is Some for the duplicate key,
      replace_with_rho produces equal values. *)
  Lemma replace_with_rho_dup xs vs rho i j :
    Datatypes.length xs = Datatypes.length vs ->
    (i < j)%nat ->
    nth_error xs i = nth_error xs j ->
    nth_error xs i <> None ->
    (forall y, nth_error xs i = Some y -> M.get y rho <> None) ->
    nth_error (replace_with_rho xs vs rho) i = nth_error (replace_with_rho xs vs rho) j.
  Proof.
    intros Hlen Hlt Heq Hnn Hrho.
    destruct (nth_error xs i) as [y | ] eqn:Hy; [ | congruence].
    destruct (M.get y rho) as [v | ] eqn:Hget.
    - erewrite replace_with_rho_nth_some by eassumption.
      (* erewrite replace_with_rho_nth_some by (rewrite <- Heq; eassumption).
      reflexivity.
    - exfalso. eapply Hrho; eauto. *)
  Admitted.

  (** If every xs[i] is in the domain of set_many xs vs rho, get_list succeeds. *)
  Lemma get_list_set_many_exists xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    exists vs', get_list xs (set_many xs vs rho) = Some vs'.
  Proof.
    intros Hlen.
    eapply get_list_exists.
    intros y Hy. eapply set_many_get_in; eauto.
  Qed.

  Lemma eval_fuel_many_length vs es vs1 f1 t1 :
    @eval_fuel_many _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                    vs es vs1 f1 t1 ->
    Datatypes.length vs1 = N.to_nat (exps_length es).
  Proof.
    intros Hrel. induction Hrel.
    - reflexivity.
    - simpl. rewrite IHHrel.
      destruct (exps_length es); try lia. destruct p; lia.
  Qed.

  Lemma anf_cvt_rel_exps_length S es vn S' C xs :
    anf_cvt_rel_exps S es vn cnstrs S' C xs ->
    Datatypes.length xs = N.to_nat (exps_length es).
  Proof.
    unfold anf_cvt_rel_exps.
    intros H. induction H as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? IH].
    - reflexivity.
    - simpl. rewrite IH.
      destruct (exps_length es); try lia. destruct p; lia.
  Qed.

  (* P0: correctness for expression lists.
     Note: xs may have duplicates (from anf_Var) and may overlap with vnames.
     This is sound because:
     - Duplicates in xs always come from the same Var_e reference,
       so they have the same value in vs'.
     - Fresh variables in xs (from non-Var expressions) are unique
       and disjoint from vnames (since S ∩ vnames = ∅). *)
  Definition anf_cvt_correct_exps (vs_env : fuel_sem.env) (es : expression.exps)
             (vs1 : list value) (f t : nat) :=
    forall rho vnames C xs S S' i,
      well_formed_env vs_env ->
      NoDup vnames ->
      Disjoint _ (FromList vnames) S ->
      anf_env_rel vnames vs_env rho ->
      anf_cvt_rel_exps S es vnames cnstrs S' C xs ->
      forall e_k vs',
        Forall2 anf_val_rel vs1 vs' ->
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->
        preord_exp cenv (anf_bound f t) eq_fuel i
                   (e_k, set_many xs vs' rho)
                   (C |[ e_k ]|, rho).


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
      intros es vs0 vs' dc fs ts Hmany IH_many.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      match goal with
      | [ Hes : anf_cvt_rel_exps _ es _ _ _ _ _ |- _ ] => rename Hes into Hcvt_es
      end.
      rewrite <- app_ctx_f_fuse.
      split.
      + intros v v' Heq Hrel. inv Heq. inv Hrel.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply IH_many.
                - eassumption.
                - eassumption.
                - eapply Disjoint_Included_r. eapply Setminus_Included. eassumption.
                - eassumption.
                - exact Hcvt_es.
                - eassumption. (* Forall2 anf_val_rel *)
                - (* Disjoint (occurs_free (Econstr ...)) ... *)
                  simpl. rewrite occurs_free_Econstr.
                  eapply Union_Disjoint_l.
                  + eapply Disjoint_Setminus_r. eapply Included_refl.
                  + eapply Setminus_Disjoint_preserv_l.
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included_r.
                    2: exact Hdis_ek.
                    intros y [[Hy_S Hy_nx] Hy_nS'].
                    split; [split; [exact Hy_S | exact Hy_nS'] | exact Hy_nx]. }
            (* Prove length xs = length vs'0 *)
            assert (Hlen_xs_vs0 : Datatypes.length xs = Datatypes.length vs0).
            { pose proof (anf_cvt_rel_exps_length _ _ _ _ _ _ Hcvt_es).
              assert (Datatypes.length vs0 = N.to_nat (exps_length es))
                by (clear -Hmany; induction Hmany;
                    [ reflexivity
                    | simpl; rewrite IHHmany;
                      destruct (exps_length es); try lia; destruct p; lia ]).
              lia. }
            assert (Hlen_xs_vs'0 : Datatypes.length xs = Datatypes.length vs'0)
              by (pose proof (Forall2_length _ _ _ H1); lia).
            (* Establish get_list existence for Econstr_red *)
            destruct (get_list_set_many_exists xs vs'0 rho Hlen_xs_vs'0)
              as [vs_new Hvs_new].
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Econstr_red. exact Hvs_new. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy v1 Hget.
            destruct (Pos.eq_dec y x) as [Heq|Hneq].
            * subst. rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              rewrite preord_val_eq. simpl. split; eauto. 
              (* preord_val (Vconstr ctag l) (Vconstr ctag vs_new):
                 Both l and vs_new are componentwise anf_val_rel to
                 the same source values vs0 (vs_new[i] = l[first_occ(xs[i])]).
                 For duplicate positions, this needs alpha-equiv. *)
              admit. (* requires anf_cvt_val_alpha_equiv *)
            * rewrite M.gso in Hget; auto.
              destruct (in_dec Pos.eq_dec y xs) as [Hyin | Hynin].
              -- (* y in xs: both rho and set_many bindings are
                    anf_val_rel to the same source value, needs alpha-equiv *)
                 admit. (* requires anf_cvt_val_alpha_equiv *)
              -- (* y not in xs: set_many does not affect y *)
                 eexists. split. rewrite M.gso; auto.
                 rewrite set_many_get_notin; auto. eassumption.
                 eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?].
        intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
        unfold_all. destruct p. destructAll. simpl in *. lia.
      + intros Habs. congruence.

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
        assert (Hwf_clos : well_formed_val (Clos_v rho_clos na0 e_body)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_clos) as [clos_v' Hrel_clos].
        assert (Hwf_v2 : well_formed_val v2).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval2. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
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
                - inversion Hwfe; subst; eassumption. (* exp_wf *)
                - eassumption.
                - eassumption.
                - eassumption.
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3' + 2) (t3' + 2)).
            tci. eapply eq_fuel_idemp.
            (* IH2: C2 layer, in env with x1 bound *)
            2:{ intros m.
                assert (Henv_x1 : anf_env_rel vnames rho0 (M.set x1 clos_v' rho)) by admit.
                assert (Hdis_letapp : Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                                                 ((S2 \\ S3) \\ [set x2])) by admit.
                edestruct IH2 as [IH2_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption. (* exp_wf *)
                - eassumption.
                - eapply Disjoint_Included_r; [eapply (proj1 anf_cvt_rel_subset); exact Hcvt_e1 | exact Hdis].
                - exact Henv_x1.
                - exact Hcvt_e2.
                - exact Hdis_letapp.
                - eapply IH2_val; eauto. }
            (* Eletapp step + body evaluation + env bridging *)
            (* Extract closure structure from Hrel_clos *)
            assert (Hclos_inv :
              exists rho_fc names_fc x_pc f_cc C_bc r_bc S1_bc S2_bc,
                clos_v' = Vfun rho_fc (Fcons f_cc func_tag [x_pc]
                            (C_bc |[ Ehalt r_bc ]|) Fnil) f_cc /\
                anf_env_rel' anf_val_rel names_fc rho_clos rho_fc /\
                NoDup names_fc /\
                Disjoint var (x_pc |: (f_cc |: FromList names_fc)) S1_bc /\
                ~ x_pc \in f_cc |: FromList names_fc /\
                ~ f_cc \in FromList names_fc /\
                anf_cvt_rel S1_bc e_body (x_pc :: names_fc) cnstrs S2_bc C_bc r_bc).
            { inversion Hrel_clos; try discriminate; subst.
              do 8 eexists.
              repeat split; try reflexivity; try eassumption. apply H4. }
            destruct Hclos_inv as (rho_fc & names_fc & x_pc & f_cc & C_bc & r_bc &
              S1_bc & S2_bc & Hclos_eq & Henv_fc & Hnd_fc &
              Hdis_fc & Hxpc_nin & Hfcc_nin & Hcvt_bc).
            subst clos_v'.
            set (defs_cc := Fcons f_cc func_tag [x_pc] (C_bc |[ Ehalt r_bc ]|) Fnil) in *.
            set (rho_bc := M.set x_pc v2' (def_funs defs_cc defs_cc rho_fc rho_fc)).
            (* Get body evaluation from IH3 *)
            assert (Henv_bc : anf_env_rel (x_pc :: names_fc) (v2 :: rho_clos) rho_bc) by admit.
            (* Apply IH3 to get body correctness *)
            assert (IH3_full :
              (forall v0 v'0, Val v = Val v0 -> anf_val_rel v0 v'0 ->
               preord_exp cenv (anf_bound f3' t3') eq_fuel (i + 1)%nat
                          (Ehalt r_bc, M.set r_bc v'0 rho_bc)
                          (C_bc |[ Ehalt r_bc ]|, rho_bc)) /\
              (Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C_bc |[ Ehalt r_bc ]|) c eval.OOT tt)).
            { eapply IH3 with (vnames := x_pc :: names_fc).
              - (* well_formed_env (v2 :: rho_clos) *)
                constructor; [exact Hwf_v2 | inversion Hwf_clos; assumption].
              - (* exp_wf (N.of_nat (length (x_pc :: names_fc))) e_body *)
                inv Hwf_clos. unfold well_formed_in_env in *. 
                specialize (H3 v2). eapply Forall2_length in Henv_fc.
                simpl in *. unfold var, M.elt. rewrite <- Henv_fc. eauto.   
              - (* NoDup (x_pc :: names_fc) *)
                constructor 2.
                { intros Hin. apply Hxpc_nin. right. exact Hin. }
                { exact Hnd_fc. }
              - (* Disjoint (FromList (x_pc :: names_fc)) S1_bc *)
                eapply Disjoint_Included_l. 2: exact Hdis_fc.
                intros z Hz. inv Hz. now left. right. now right.
              - exact Henv_bc.
              - exact Hcvt_bc.
              - (* Disjoint (occurs_free (Ehalt r_bc)) ((S1_bc \\ S2_bc) \\ [set r_bc]) *)
                constructor. intros z Hz. inv Hz.
                (* H : occurs_free (Ehalt r_bc) z → z = r_bc *)
                inversion H; subst.
                (* H0 : In ((S1_bc \\ S2_bc) \\ [set r_bc]) r_bc — impossible *)
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel).
            (* IH3_val : preord_exp (anf_bound f3' t3') eq_fuel (i+1)
                 (Ehalt r_bc, M.set r_bc v' rho_bc) (C_bc |[ Ehalt r_bc ]|, rho_bc) *)
            (* Extract body evaluation from IH3_val *)
            (* First build the Ehalt bstep_fuel with existential fuel/trace *)
            (* Directly specialize IH3_val: Ehalt r_bc evaluates in 1 step *)
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                                         (M.set r_bc v' rho_bc) (Ehalt r_bc) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_bc v' rho_bc) (Ehalt r_bc) (Res v') 0%nat tt
                (BStept_halt cenv r_bc v' (M.set r_bc v' rho_bc) (M.gss r_bc v' rho_bc))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            destruct (IH3_val (Res v') 1%nat tt Hle_h Hehalt)
              as (v_body_res & cin_bc & cout_bc & Hbstep_bc & Hpost_bc & Hres_bc).
            (* Body result must be Res (not OOT) *)
            destruct v_body_res as [ | v_bc ].
            { simpl in Hres_bc. contradiction. }
            simpl in Hres_bc.
            (* Hres_bc : preord_val cenv eq_fuel i v' v_bc *)
            (* Unfold preord_exp' and construct the proof directly *)
            intros v1 cin cout Hle_cin Hbstep_ek.
            (* Use preord_exp_refl for continuation environment bridge *)
            assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                      (e_k, M.set x v' rho)
                      (e_k, M.set x v_bc (M.set x2 v2' (M.set x1 (Vfun rho_fc defs_cc f_cc) rho)))).
            { eapply preord_exp_refl. now eapply eq_fuel_compat.
              intros y Hy.
              destruct (Pos.eq_dec y x) as [-> | Hneq_x].
              - (* y = x: v' vs v_bc *)
                unfold preord_var_env. intros v0 Hget0.
                rewrite M.gss in Hget0. inv Hget0.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hres_bc. lia.
              - (* y ≠ x *)
                unfold preord_var_env. intros v0 Hget0.
                rewrite M.gso in Hget0 by auto.
                eexists. split.
                + assert (Hneq_x2 : y <> x2) by admit.
                  assert (Hneq_x1 : y <> x1) by admit.
                  rewrite M.gso by auto.
                  rewrite M.gso by auto.
                  rewrite M.gso by auto.
                  exact Hget0.
                + eapply preord_val_refl. tci. }
            (* Get continuation evaluation from preord_exp_refl *)
            edestruct Hrefl as (v_cont & cin_cont & cout_cont & Hbstep_cont & Heq_cont & Hres_cont).
            { exact Hle_cin. }
            { exact Hbstep_ek. }
            (* Construct the full Eletapp evaluation *)
            do 3 eexists. split.
            { assert (Hneq_x2_x1 : x1 <> x2) by admit.
              econstructor 2. eapply BStept_letapp.
              - (* M.get x1 = Vfun ... *)
                rewrite M.gso by auto.
                rewrite M.gss. reflexivity.
              - (* get_list [x2] = [v2'] *)
                simpl. rewrite M.gss. reflexivity.
              - (* find_def f_cc defs_cc *)
                simpl. destruct (M.elt_eq f_cc f_cc); [reflexivity | congruence].
              - (* set_lists [x_pc] [v2'] (def_funs ...) = Some rho_bc *)
                reflexivity.
              - (* body evaluates *)
                exact Hbstep_bc.
              - (* continuation evaluates *)
                exact Hbstep_cont. }
            split.
            { (* PostT: anf_bound (f3' + 2) (t3' + 2) *)
              unfold anf_bound in Hpost_bc |- *.
              unfold eq_fuel in Heq_cont. simpl in Heq_cont, Hpost_bc.
              destruct Hpost_bc as [Hlb_bc Hub_bc].
              simpl. unfold one, one_i in *; simpl; unfold_all. lia.  }
            { (* preord_res: same as from refl *)
              exact Hres_cont. } }
        (* inclusion: comp (comp (anf_bound (f3'+2) (t3'+2)) (anf_bound f2' t2')) (anf_bound f1' t1')
                     ⊆ anf_bound (f1'+f2'+f3'+1) (t1'+t2'+t3'+2) *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
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
        assert (Hwfv1 : well_formed_val v1).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists v1 Hwfv1) as [v1' Hrel1].
        (* Chain: env bridging + IH2 + IH1 via preord_exp_trans *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1 for e1, with e_k' = C2|[e_k]| *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S \\ S2) \\ [set x1])) by admit.
                edestruct IH1 as [IH1_val _].
                - eassumption. (* well_formed_env *)
                - inversion Hwfe; subst; eassumption. (* exp_wf e1' *)
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
                assert (Hwfe' : exp_wf (N.of_nat (Datatypes.length (x1 :: vnames))) e2').
                { assert (Hwf_let := Hwfe). clear -Hwf_let.
                  simpl Datatypes.length.
                  replace (N.of_nat (S (Datatypes.length vnames)))
                    with (1 + N.of_nat (Datatypes.length vnames))%N by lia.
                  inversion Hwf_let; subst; assumption. }
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
                - constructor; assumption. (* well_formed_env (v1::rho0) *)
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
              -- (* y = x1: either x1 ∈ vnames (Var_e case) or x1 ∈ S (contradiction) *)
                 subst.
                 destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                 ++ (* x1 ∈ vnames: use alpha-equiv *)
                    eexists. split.
                    { rewrite M.gso; auto. rewrite M.gss. reflexivity. }
                    assert (Hrel_v1x : anf_val_rel v1 v1x).
                    { eapply (anf_cvt_result_in_vnames_eval
                                S e1' vnames cnstrs S2 C1 x1 rho0 rho v1 f1' t1' v1x).
                      - exact Henv.
                      - exact Hnd.
                      - exact Hdis.
                      - exact Hcvt_e1.
                      - exact Hin_vn.
                      - exact Heval1.
                      - exact Hget. }
                    eapply anf_cvt_val_alpha_equiv; eauto.
                 ++ (* x1 ∈ S: x1 is fresh, contradiction with Hy via Hdis_ek *)
                    exfalso.
                    assert (Hx1_not_S' : ~ x1 \in S2).
                    { eapply (anf_cvt_result_consumed S e1' vnames cnstrs S2 C1 x1).
                      - exact Hcvt_e1.
                      - exact Hdis.
                      - exact Hin_S. }
                    assert (Hx1_not_S'2 : ~ x1 \in S').
                    { intro Hin. apply Hx1_not_S'.
                      eapply anf_cvt_exp_subset. exact Hcvt_e2. exact Hin. }
                    destruct Hdis_ek as [Hdis_ek'].
                    apply (Hdis_ek' x1). constructor.
                    { exact Hy. }
                    { constructor.
                      - constructor; assumption.
                      - intros Hin_x. inv Hin_x. congruence. }
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
      intros e1' e2' e_body rho0 rho_fix rho_rec n0 na0 fnlst0 v2 r0 f1' f2' f3' t1' t2' t3'
             Heval1 IH1 Hnth Hrec Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
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
        assert (Hwf_fix : well_formed_val (ClosFix_v rho_fix fnlst0 n0)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_fix) as [fix_v' Hrel_fix].
        assert (Hwf_v2 : well_formed_val v2).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval2. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_v2) as [v2' Hrel_v2].
        (* Chain: IH1 + IH2 + Eletapp reduction + IH3 *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1: C1 layer *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                                               ((S \\ S2) \\ [set x1])) by admit.
                edestruct IH1 as [IH1_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption.
                - eassumption.
                - eassumption.
                - eassumption.
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3' + 2) (t3' + 2)).
            tci. eapply eq_fuel_idemp.
            (* IH2: C2 layer *)
            2:{ intros m.
                assert (Henv_x1 : anf_env_rel vnames rho0 (M.set x1 fix_v' rho)) by admit.
                assert (Hdis_letapp : Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                                                 ((S2 \\ S3) \\ [set x2])) by admit.
                edestruct IH2 as [IH2_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption.
                - eassumption.
                - eapply Disjoint_Included_r; [eapply (proj1 anf_cvt_rel_subset); exact Hcvt_e1 | exact Hdis].
                - exact Henv_x1.
                - exact Hcvt_e2.
                - exact Hdis_letapp.
                - eapply IH2_val; eauto. }
            (* Eletapp reduction + IH3 for body *)
            (* Step 1: Extract fix closure structure from Hrel_fix *)
            assert (Hfix_inv :
              exists rho_fc names_fc fnames_fc Bs_fix f_fc S1_fc S2_fc,
                fix_v' = Vfun rho_fc Bs_fix f_fc /\
                anf_env_rel' anf_val_rel names_fc rho_fix rho_fc /\
                NoDup names_fc /\
                NoDup fnames_fc /\
                Disjoint _ (FromList names_fc :|: FromList fnames_fc) S1_fc /\
                Disjoint _ (FromList names_fc) (FromList fnames_fc) /\
                nth_error fnames_fc (N.to_nat n0) = Some f_fc /\
                anf_fix_rel fnames_fc names_fc S1_fc fnames_fc fnlst0 Bs_fix S2_fc).
            { inversion Hrel_fix; try discriminate; subst.
              do 7 eexists.
              split; [reflexivity | ].
              repeat (split; [eassumption | ]).
              eassumption. }
            destruct Hfix_inv as (rho_fc & names_fc & fnames_fc & Bs_fix & f_fc &
              S1_fc & S2_fc & Hfix_eq & Henv_fc & Hnd_names & Hnd_fnames &
              Hdis_fix & Hdis_nf & Hnth_fix & Hfix_rel).
            subst fix_v'.
            (* Get specific function from the fix bundle *)
            edestruct (anf_fix_rel_find_def _ _ _ _ _ _ _ _ _ _ _ Hfix_rel Hnth_fix Hnth Hnd_fnames)
              as (x_pc & C_bc & r_bc & S_body1 & S_body2 & Hfind_fc & Hcvt_bc).
            set (rho_bc := M.set x_pc v2' (def_funs Bs_fix Bs_fix rho_fc rho_fc)).
            (* Step 2: Body environment relation *)
            assert (Henv_bc : anf_env_rel (x_pc :: List.rev fnames_fc ++ names_fc)
                                          (v2 :: make_rec_env_rev_order fnlst0 rho_fix) rho_bc) by admit.
            (* Step 3: Apply IH3 to get body correctness *)
            assert (IH3_full :
              (forall v0 v'0, Val v = Val v0 -> anf_val_rel v0 v'0 ->
               preord_exp cenv (anf_bound f3' t3') eq_fuel (i + 1)%nat
                          (Ehalt r_bc, M.set r_bc v'0 rho_bc)
                          (C_bc |[ Ehalt r_bc ]|, rho_bc)) /\
              (Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C_bc |[ Ehalt r_bc ]|) c eval.OOT tt)).
            { eapply IH3 with (vnames := x_pc :: List.rev fnames_fc ++ names_fc).
              - (* well_formed_env (v2 :: make_rec_env_rev_order fnlst0 rho_fix) *)
                admit. (* from Hwf_v2 + make_rec_env_preserves_wf *)
              - (* exp_wf *)
                admit. (* from well_formed_val (ClosFix_v ...) *)
              - (* NoDup (x_pc :: rev fnames_fc ++ names_fc) *)
                admit. (* from Hxpc_in, Hdis_entry, Hnd_names, Hnd_fnames, Hdis_nf *)
              - (* Disjoint (FromList (x_pc :: rev fnames_fc ++ names_fc)) S_body1 *)
                admit. (* from Hdis_entry, Hsub_body, Hxpc_in *)
              - exact Henv_bc.
              - exact Hcvt_bc.
              - (* Disjoint (occurs_free (Ehalt r_bc)) ((S_body1 \\ S_body2) \\ [set r_bc]) *)
                constructor. intros z Hz. inv Hz.
                inversion H; subst.
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel).
            (* Step 4: Build Ehalt bstep_fuel *)
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                                         (M.set r_bc v' rho_bc) (Ehalt r_bc) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_bc v' rho_bc) (Ehalt r_bc) (Res v') 0%nat tt
                (BStept_halt cenv r_bc v' (M.set r_bc v' rho_bc) (M.gss r_bc v' rho_bc))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            destruct (IH3_val (Res v') 1%nat tt Hle_h Hehalt)
              as (v_body_res & cin_bc & cout_bc & Hbstep_bc & Hpost_bc & Hres_bc).
            (* Body result must be Res (not OOT) *)
            destruct v_body_res as [ | v_bc ].
            { simpl in Hres_bc. contradiction. }
            simpl in Hres_bc.
            (* Step 5: Continuation bridge via preord_exp_refl *)
            intros v1 cin cout Hle_cin Hbstep_ek.
            assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                      (e_k, M.set x v' rho)
                      (e_k, M.set x v_bc (M.set x2 v2' (M.set x1 (Vfun rho_fc Bs_fix f_fc) rho)))).
            { eapply preord_exp_refl. now eapply eq_fuel_compat.
              intros y Hy.
              destruct (Pos.eq_dec y x) as [-> | Hneq_x].
              - (* y = x *)
                unfold preord_var_env. intros v0 Hget0.
                rewrite M.gss in Hget0. inv Hget0.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hres_bc. lia.
              - (* y ≠ x *)
                unfold preord_var_env. intros v0 Hget0.
                rewrite M.gso in Hget0 by auto.
                eexists. split.
                + assert (Hneq_x2 : y <> x2) by admit. (* freshness *)
                  assert (Hneq_x1 : y <> x1) by admit. (* freshness *)
                  rewrite M.gso by auto.
                  rewrite M.gso by auto.
                  rewrite M.gso by auto.
                  exact Hget0.
                + eapply preord_val_refl. tci. }
            (* Step 6: Get continuation evaluation *)
            edestruct Hrefl as (v_cont & cin_cont & cout_cont & Hbstep_cont & Heq_cont & Hres_cont).
            { exact Hle_cin. }
            { exact Hbstep_ek. }
            (* Step 7: Construct the full Eletapp evaluation *)
            do 3 eexists. split.
            { assert (Hneq_x2_x1 : x1 <> x2) by admit. (* freshness *)
              econstructor 2. eapply BStept_letapp.
              - (* M.get x1 = Vfun rho_fc Bs_fix f_fc *)
                rewrite M.gso by auto.
                rewrite M.gss. reflexivity.
              - (* get_list [x2] = [v2'] *)
                simpl. rewrite M.gss. reflexivity.
              - (* find_def f_fc Bs_fix *)
                exact Hfind_fc.
              - (* set_lists [x_pc] [v2'] (def_funs ...) = Some rho_bc *)
                reflexivity.
              - (* body evaluates *)
                exact Hbstep_bc.
              - (* continuation evaluates *)
                exact Hbstep_cont. }
            split.
            { (* PostT: anf_bound (f3' + 2) (t3' + 2) *)
              unfold anf_bound in Hpost_bc |- *.
              unfold eq_fuel in Heq_cont. simpl in Heq_cont, Hpost_bc.
              destruct Hpost_bc as [Hlb_bc Hub_bc].
              simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
            { (* preord_res *)
              exact Hres_cont. } }
        (* inclusion: comp (comp (anf_bound (f3'+2) (t3'+2)) (anf_bound f2' t2')) (anf_bound f1' t1')
                     ⊆ anf_bound (f1'+f2'+f3'+1) (t1'+t2'+t3'+2) *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 9. eval_Match_step: Match_e terminates *)
      intros e1' e_br rho0 dc0 vs_con n0 brnchs0 r0 f1' f2' t1' t2' Heval1 IH1 Hfind Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      (* After inversion of anf_Match:
         f \in S, y \in S \ {f}
         Hcvt_e1 : anf_cvt_rel (S \ {f} \ {y}) e1' vnames cnstrs S2 C1 x1
         Hcvt_brs : anf_cvt_rel_branches S2 brnchs0 vnames y cnstrs S3 pats
         x \in S3, S' = S3 \ {x}
         Target: Efun (Fcons f func_tag [y] (Ecase y pats) Fnil)
                      (C1 |[ Eletapp x f func_tag [x1] e_k ]|) *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          Hbrs : anf_cvt_rel_branches _ brnchs0 vnames _ _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename Hbrs into Hcvt_brs
      end.
      split.
      + (* Termination case *)
        intros v v' Heq Hrel. subst r0.
        (* Well-formedness of constructor value *)
        assert (Hwf_con : well_formed_val (Con_v dc0 vs_con)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_con) as [con_v' Hrel_con].
        (* Subset from scrutinee conversion *)
        assert (HS2 : S2 \subset S \\ [set f] \\ [set y]).
        { eapply anf_cvt_exp_subset. eassumption. }
        (* Extract constructor shape early — needed for Hbody *)
        assert (Hcon_shape : exists c_tag vs_anf,
          con_v' = Vconstr c_tag vs_anf /\
          dcon_to_tag default_tag dc0 cnstrs = c_tag /\
          Forall2 anf_val_rel vs_con vs_anf).
        { inv Hrel_con. eexists _, _. eauto. }
        destruct Hcon_shape as (c_tag & vs_anf & Hcon_eq & Htag_eq & Hvs_rel).
        subst con_v'.
        (* Extract branch data from the branches conversion *)
        edestruct (anf_cvt_rel_branches_find_branch
                     S2 brnchs0 vnames y S3 pats dc0 e_br
                     (dcon_to_tag default_tag dc0 cnstrs)
                     (N.of_nat (Datatypes.length vs_con)))
          as (vars & S_mid & S_out & C_br & r_br & ctx_p_br & m_br &
              Hvars_sub & Hvars_len & Hvars_nd & Hctx_p & Hfind_tag & Hcvt_br & HS_mid_sub).
        { exact Hcvt_brs. }
        { exact Hfind. }
        { reflexivity. }
        set (n_vars := List.length vars).
        assert (Hn_le : (n_vars <= max_m_branches brnchs0)%nat).
        { unfold n_vars. rewrite Hvars_len.
          eapply find_branch_max_m_branches. exact Hfind. }
        (* The target expression unfolds as:
             Efun (Fcons f func_tag [y] (Ecase y pats) Fnil)
                  (C1 |[ Eletapp x f func_tag [x1] e_k ]|) *)
        simpl app_ctx_f. rewrite <- app_ctx_f_fuse.
        set (defs := Fcons f func_tag [y] (Ecase y pats) Fnil).
        set (rho_efun := def_funs defs defs rho rho).
        set (rho_match := M.set y (Vconstr c_tag vs_anf) rho_efun).
        (* Assert projection bindings succeed *)
        assert (Hset_proj : exists rho_proj,
          set_lists (rev vars) vs_anf rho_match = Some rho_proj).
        { admit. (* follows from |rev vars| = |vs_anf| via Hvars_len + Forall2 length *) }
        destruct Hset_proj as [rho_proj Hset_proj].
        (* Main proof: compose three reduction steps *)
        eapply preord_exp_post_monotonic with
          (P1 := comp (comp (anf_bound (f2' + n_vars + 3) (t2' + n_vars + 3))
                            (anf_bound f1' t1'))
                      one_step).
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* Step 1: Efun_red — defines match function f *)
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* Step 2: IH1 — evaluates scrutinee through C1, binds x1 *)
            2:{ intros m.
                assert (Hdis_ek_IH : Disjoint _
                  (occurs_free (Eletapp x f func_tag [x1] e_k))
                  (((S \\ [set f] \\ [set y]) \\ S2) \\ [set x1])) by admit.
                assert (Henv_efun : anf_env_rel vnames rho0 rho_efun) by admit.
                assert (Hdis_efun : Disjoint _ (FromList vnames) (S \\ [set f] \\ [set y])).
                { eapply Disjoint_Included_r.
                  eapply Included_trans; eapply Setminus_Included.
                  exact Hdis. }
                edestruct IH1 as [IH1_val _].
                - exact Hwf.
                - inversion Hwfe; subst; eassumption.
                - exact Hnd.
                - exact Hdis_efun.
                - exact Henv_efun.
                - exact Hcvt_e1.
                - exact Hdis_ek_IH.
                - eapply IH1_val; eauto. }

            (* Step 3: Eletapp — compositional Ecase body proof *)
            intros v1 cin cout Hle_cin Hbstep_ek.

            (* == Compositionally build Ecase body preord_exp == *)
            (* Use index i+1 so that after Ehalt (1 step), preord_val is at i *)
            (* Compose: IH2 → ctx_bind_proj → Ecase_red *)
            assert (Hpre_ecase : preord_exp cenv
              (comp (comp (anf_bound f2' t2') (eq_fuel_n n_vars)) one_step)
              eq_fuel (i + 1)%nat
              (Ehalt r_br, M.set r_br v' rho_proj)
              (Ecase y pats, rho_match)).
            { eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              (* Ecase_red: case dispatch *)
              2:{ intros m'. eapply preord_exp_Ecase_red.
                  - unfold rho_match. rewrite M.gss. reflexivity.
                  - rewrite <- Htag_eq. exact Hfind_tag. }
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              (* ctx_bind_proj: bind constructor fields via projections *)
              2:{ intros m'. eapply ctx_bind_proj_preord_exp with (vs' := []).
                  - reflexivity.
                  - admit. (* ~ y \in FromList vars — freshness *)
                  - subst ctx_p_br. unfold n_vars. reflexivity.
                  - unfold rho_match. rewrite M.gss. rewrite <- Htag_eq. rewrite app_nil_r. reflexivity.
                  - exact Hset_proj. }
              (* IH2: branch body evaluation *)
              intros m'.
              edestruct IH2 as [IH2_val _]; [ | | | | | exact Hcvt_br | | eapply IH2_val; eauto ].
              - admit. (* well_formed_env (List.rev vs_con ++ rho0) *)
              - admit. (* exp_wf ... e_br *)
              - admit. (* NoDup (vars ++ vnames) *)
              - admit. (* Disjoint (FromList (vars ++ vnames)) (S_mid \\ FromList vars) *)
              - admit. (* anf_env_rel (vars ++ vnames) (List.rev vs_con ++ rho0) rho_proj *)
              - constructor. intros z0 Hz0. inv Hz0. inv H.
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            (* Extract bstep from Ecase preord_exp using Ehalt source evaluation *)
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                     (M.set r_br v' rho_proj) (Ehalt r_br) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_br v' rho_proj) (Ehalt r_br) (Res v') 0%nat tt
                (BStept_halt cenv r_br v' (M.set r_br v' rho_proj) (M.gss r_br v' rho_proj))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            edestruct Hpre_ecase as
              (v_body & cin_ecase & cout_ecase & Hbstep_ecase & Hpost_ecase & Hres_ecase).
            { exact Hle_h. }
            { exact Hehalt. }

            (* Extract fuel bounds from the composed post *)
            unfold comp, anf_bound, eq_fuel_n, one_step in Hpost_ecase.
            destruct Hpost_ecase as
              [[[[e_z1 rho_z1] f_z1] t_z1]
               [[[[[e_z2 rho_z2] f_z2] t_z2] [[Hlb_f2 Hub_f2] Heq_fn]] Hone_f]].
            simpl in Hlb_f2, Hub_f2, Heq_fn, Hone_f.
            (* Derived: f2' + n_vars + 2 <= cin_ecase <= t2' + n_vars + 2 *)

            (* v_body is a res; extract the actual val *)
            destruct v_body as [ | v_bc].
            { (* OOT case: contradiction *)
              simpl in Hres_ecase. contradiction. }
            (* Extract preord_val from preord_res *)
            simpl in Hres_ecase.
            rename Hres_ecase into Hrel_body.
            (* Hrel_body : preord_val cenv eq_fuel ((i+1) - to_nat 1) v' v_bc = preord_val ... i v' v_bc *)

            (* Build env bridge for continuation *)
            assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
              (e_k, M.set x v' rho)
              (e_k, M.set x v_bc (M.set x1 (Vconstr c_tag vs_anf) rho_efun))).
            { eapply preord_exp_refl. now eapply eq_fuel_compat.
              intros z Hz.
              destruct (Pos.eq_dec z x) as [-> | Hneq_x].
              - (* z = x: v' vs v_bc *)
                intros vz Hgetz. rewrite M.gss in Hgetz. inv Hgetz.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hrel_body. lia.
              - (* z ≠ x: freshness *)
                intros vz Hgetz. rewrite M.gso in Hgetz by auto.
                eexists. split.
                + assert (Hneq_x1 : z <> x1) by admit. (* freshness *)
                  rewrite M.gso by auto. rewrite M.gso by auto.
                  admit. (* M.get z rho_efun = M.get z rho — freshness *)
                + eapply preord_val_refl. tci. }

            edestruct Hrefl as (v_cont & cin_cont & cout_cont & Hbstep_cont & Heq_cont & Hres_cont).
            { exact Hle_cin. }
            { exact Hbstep_ek. }

            (* Construct the full Eletapp bstep *)
            do 3 eexists. split.
            { econstructor 2. eapply BStept_letapp.
              - (* M.get f (M.set x1 ... rho_efun) = Vfun rho defs f *)
                assert (Hneq_x1f : x1 <> f) by admit. (* freshness *)
                rewrite M.gso by (intro Heq'; apply Hneq_x1f; auto).
                unfold rho_efun, defs. simpl. rewrite M.gss. reflexivity.
              - (* get_list [x1] (M.set x1 ... rho_efun) = [Vconstr c_tag vs_anf] *)
                simpl. rewrite M.gss. reflexivity.
              - (* find_def f defs = (func_tag, [y], Ecase y pats) *)
                subst defs. simpl. destruct (M.elt_eq f f); [reflexivity | congruence].
              - (* set_lists [y] [Vconstr c_tag vs_anf] (def_funs ...) = Some rho_match *)
                reflexivity.
              - (* body evaluates: Ecase y pats *)
                exact Hbstep_ecase.
              - (* continuation evaluates *)
                exact Hbstep_cont. }
            split.
            { (* PostT: anf_bound (f2' + n_vars + 3) (t2' + n_vars + 3) *)
              unfold anf_bound. unfold eq_fuel in Heq_cont.
              simpl in Heq_cont. subst.
              simpl. 
              unfold one, one_i in *; simpl; unfold_all. lia. }
            { exact Hres_cont. } }
        (* Step 4: Inclusion — compose bounds *)
        { unfold inclusion, comp, eq_fuel, anf_bound, one_step.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] ?]].
          unfold_all. simpl in *. split; lia. }
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 10. eval_Match_step_OOT: Match_e, e1 diverges *)
      intros e1' rho0 n0 br0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    (** ** eval_fuel_many cases (P0 = anf_cvt_correct_exps) *)

    - (* 11. eval_many_enil *)
      intros vs0.
      unfold anf_cvt_correct_exps.
      intros rho vnames C xs S S' i Hwf Hnd Hdis Henv Hcvt e_k vs' Hrel_vs Hdis_ek.
      inv Hcvt. inv Hrel_vs. simpl.
      intros v1 cin cout Hleq Hstep.
      exists v1, cin, cout. split. exact Hstep. split.
      { unfold anf_bound. unfold_all. simpl. lia. }
      { destruct v1; simpl; auto. eapply preord_val_refl. tci. }

    - (* 12. eval_many_econs *)
      intros vs_env e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval_e IH_e Heval_es IH_es.
      unfold anf_cvt_correct_exps in IH_es |- *.
      unfold anf_cvt_correct_exp in IH_e.
      intros rho vnames C xs S S' i Hwf Hnd Hdis Henv Hcvt e_k vs' Hrel_vs Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      inv Hrel_vs.
      (* After inv: C = comp_ctx_f C1 C2, xs = x1 :: xs_rest,
         vs' = v1' :: vs_tl', with:
         Hcvt_e  : anf_cvt_rel S e0 vnames cnstrs S2 C1 x1
         Hcvt_es : anf_cvt_rel_exps S2 es0 vnames cnstrs S' C2 xs_rest
         Hrel_v  : anf_val_rel v0 v1'
         Hrel_rest : Forall2 anf_val_rel vs0 vs_tl' *)
      simpl set_many. rewrite <- app_ctx_f_fuse.
      (* Chain: env_bridge(eq_fuel) + IH_es(anf_bound fs0 ts0) + IH_e(anf_bound f0 t0) *)
      eapply preord_exp_post_monotonic.
      2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
          (* Right step: IH_e with continuation C2|[e_k]| *)
          2:{ intros m.
              edestruct IH_e as [IH_val _]; [ exact Hwf | admit | exact Hnd | exact Hdis | exact Henv | eassumption | admit | ].
              eapply IH_val; eauto. }
          eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
          (* Right step: IH_es with env M.set x1 v1' rho *)
          2:{ intros m.
              eapply IH_es; [ exact Hwf | exact Hnd | | | eassumption | eassumption | admit ].
              - eapply Disjoint_Included_r; [eapply (proj1 anf_cvt_rel_subset); eassumption | exact Hdis].
              - (* anf_env_rel vnames vs_env (M.set x1 v1' rho) *)
                eapply anf_env_rel_set; [exact Henv | intros k Hnth_k; admit]. }
          (* Leftmost: env bridge —
             M.set x1 v1' (set_many xs_rest vs_tl' rho) ≈
             set_many xs_rest vs_tl' (M.set x1 v1' rho)
             This holds for preord_var_env because:
             - At y ≠ x1: both sides agree (set_many dominates for y ∈ xs_rest,
               otherwise M.get y rho since y ≠ x1)
             - At y = x1: LHS gives v1' (M.gss), RHS gives v1' if x1 ∉ xs_rest,
               or the set_many value if x1 ∈ xs_rest. In the latter case,
               both values translate the same source value (preord_val_refl). *)
          eapply preord_exp_refl. now eapply eq_fuel_compat.
          intros z Hz v1 Hget.
          (* env bridge: M.set x1 v1' (set_many xs vs rho) ≈ set_many xs vs (M.set x1 v1' rho) *)
          destruct (Pos.eq_dec z x1) as [Heq_z | Hneq_z].
          + subst z. rewrite M.gss in Hget.
            inv Hget.
            destruct (in_dec Pos.eq_dec x1 xs0) as [Hin_xs | Hnin_xs].
            * admit. (* x1 ∈ xs_rest: needs anf_cvt_val_alpha_equiv *)
            * eexists; split.
              -- rewrite set_many_get_neq; auto. rewrite M.gss. reflexivity.
              -- eapply preord_val_refl. tci.
          + rewrite M.gso in Hget; auto.
            eexists; split.
            * rewrite set_many_set_neq_base; auto. exact Hget.
            * eapply preord_val_refl. tci. }
      (* inclusion: comp (comp eq_fuel (anf_bound fs0 ts0)) (anf_bound f0 t0) ⊆ anf_bound (f0+fs0) (t0+ts0) *)
      unfold inclusion, comp, eq_fuel, anf_bound.
      intros [[[? ?] ?] ?] [[[? ?] ?] ?].
      intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
      unfold_all. destruct p. destructAll. simpl in *. lia.

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

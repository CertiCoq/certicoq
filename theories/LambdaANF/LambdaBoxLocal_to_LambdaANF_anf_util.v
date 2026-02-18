(* Utility definitions and lemmas for ANF correctness proof.
   Follows the pattern of LambdaBoxLocal_to_LambdaANF_util.v (CPS version).
   Contains the ANF value relation, and the alpha-equivalence proof. *)

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


(** * ANF Value Relation *)

Section ANF_Val.

  Context (func_tag default_tag : positive)
          (cnstrs : conId_map).

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


  Definition env_consistent (vn : list var) (rho : list value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.

  Inductive anf_val_rel : value -> val -> Prop :=
  | anf_rel_Con :
      forall vs vs' dc c_tag,
        Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
        dcon_to_tag default_tag dc cnstrs = c_tag ->
        anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | anf_rel_Clos :
      forall vs rho names na x f e C1 r1 S1 S2,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->

        Disjoint var (x |: (f |: FromList names)) S1 ->

        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->

        anf_cvt_rel S1 e (x :: names) cnstrs S2 C1 r1 ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho efns Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->
        NoDup fnames ->

        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (FromList names) (FromList fnames) ->

        nth_error fnames (N.to_nat n) = Some f ->

        anf_fix_rel fnames names S1 fnames efns Bs S2 ->

        anf_val_rel (ClosFix_v vs efns n) (Vfun rho Bs f).


  Definition anf_env_rel : list var -> list value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.


  (** ** Helper lemmas for fix relation *)

  Lemma anf_fix_rel_fnames_length fnames names S1 fnames_list efns Bs S2 :
    anf_fix_rel fnames names S1 fnames_list efns Bs S2 ->
    List.length fnames_list = efnlength efns.
  Proof.
    intros Hrel. induction Hrel; simpl; congruence.
  Qed.

  Lemma anf_fix_rel_names fnames names S1 fnames_list efns Bs S2 :
    anf_fix_rel fnames names S1 fnames_list efns Bs S2 ->
    all_fun_name Bs = fnames_list.
  Proof.
    intros H. induction H; simpl; congruence.
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

  (* Extended version of anf_fix_rel_find_def that also provides the
     Disjoint property for the body's state set and freshness of x_pc *)
  Lemma anf_fix_rel_find_def_ext :
    forall fnames0 names0 S1 fnames_list efns Bs S2 idx f na e_body,
      anf_fix_rel fnames0 names0 S1 fnames_list efns Bs S2 ->
      nth_error fnames_list idx = Some f ->
      enthopt idx efns = Some (Lam_e na e_body) ->
      NoDup fnames_list ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel S_body1 e_body (x_pc :: List.rev fnames0 ++ names0) cnstrs S_body2 C_body r_body /\
        Disjoint _ (x_pc |: (FromList fnames0 :|: FromList names0)) S_body1 /\
        ~ x_pc \in (FromList fnames0 :|: FromList names0).
  Proof.
    intros fnames0 names0 S1 fnames_list efns Bs S2 idx f na e_body
      Hrel Hnth Henth Hnd.
    revert idx f na e_body Hnth Henth Hnd.
    induction Hrel; intros idx0 f0 na0 e_body0 Hnth Henth Hnd.
    - destruct idx0; discriminate.
    - destruct idx0 as [ | idx'].
      + simpl in Hnth. inv Hnth.
        simpl in Henth. inv Henth.
        do 5 eexists. split; [ | split; [ | split ] ].
        * simpl. destruct (M.elt_eq f0 f0); [ reflexivity | congruence ].
        * eassumption.
        * eapply Disjoint_Included_r; [ eassumption | ].
          eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l. intros Hc. destruct Hc as [_ Hc]. apply Hc. constructor.
          -- eapply Disjoint_Included_r; [ eapply Setminus_Included | ].
             eapply Disjoint_sym. assumption.
        * intros Habs.
          match goal with
          | [ Hdis : Disjoint _ _ (FromList fnames0 :|: FromList names0),
              Hin : _ \in _ |- _ ] =>
            eapply Hdis; constructor; [ exact Hin | exact Habs ]
          end.
      + simpl in Hnth. simpl in Henth.
        inv Hnd.
        edestruct IHHrel as (x_pc' & C_body' & r_body' & S_body1' & S_body2' &
                              Hfind' & Hcvt' & Hdis' & Hfresh').
        * exact Hnth.
        * exact Henth.
        * assumption.
        * do 5 eexists. split; [ | split; [ | split ] ].
          -- simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
             ++ exfalso. subst.
                match goal with
                | [ Hnotin : ~ List.In _ _ |- _ ] =>
                  apply Hnotin; eapply nth_error_In; exact Hnth
                end.
             ++ exact Hfind'.
          -- exact Hcvt'.
          -- exact Hdis'.
          -- exact Hfresh'.
  Qed.

  Lemma eq_fuel_idemp :
    inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
  Proof.
    clear. unfold comp, eq_fuel. intro; intros.
    destruct x as [[[? ?] ?] ?].
    destruct y as [[[? ?] ?] ?]. destructAll.
    destruct x as [[[? ?] ?] ?]. congruence.
  Qed.

  (** ** Alpha-equivalence for ANF values *)

  Context (cenv : ctor_env)
          (dcon_to_tag_inj :
            forall tgm dc dc',
              dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Definition anf_cvt_val_alpha_equiv_statement k :=
    forall v v1 v2,
      anf_val_rel v v1 -> anf_val_rel v v2 ->
      preord_val cenv eq_fuel k v1 v2.

  Definition anf_cvt_env_alpha_equiv_statement k :=
    forall names1 names2 vs rho1 rho2 f,
      anf_env_rel names1 vs rho1 ->
      anf_env_rel names2 vs rho2 ->
      preord_env_P_inj cenv eq_fuel (FromList names1) k (f <{ names1 ~> names2 }>) rho1 rho2.

  Lemma preord_env_P_inj_get S k f rho1 rho2 x y v1 v2 :
    preord_env_P_inj cenv eq_fuel (S \\ [set x]) k f rho1 rho2 ->
    M.get x rho1 = Some v1 ->
    M.get y rho2 = Some v2 ->
    preord_val cenv eq_fuel k v1 v2 ->
    preord_env_P_inj cenv eq_fuel S k (f {x ~> y}) rho1 rho2.
  Proof.
    intros Henv Hg1 Hg2 Hval z HS v Hgetz. destruct (Coqlib.peq x z).
    - subst. repeat subst_exp. rewrite extend_gss. eauto.
    - rewrite extend_gso; eauto. eapply Henv; eauto.
      constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma anf_cvt_env_alpha_equiv_pre k :
    anf_cvt_val_alpha_equiv_statement k ->
    anf_cvt_env_alpha_equiv_statement k.
  Proof.
    intros IH n1 n2 vs.
    revert n1 n2. induction vs; intros n1 n2 rho1 rho2 f Hrel1 Hrel2.
    - inv Hrel1; inv Hrel2. simpl. repeat normalize_sets.
      intros x Hin. inv Hin.
    - inv Hrel1; inv Hrel2. destructAll.
      simpl. eapply preord_env_P_inj_get; eauto.
      repeat normalize_sets. eapply preord_env_P_inj_antimon.
      eapply IHvs. eassumption. eassumption. sets.
  Qed.

  (** ** Expression-level alpha equivalence *)

  (* Two ANF conversions of the same source expression produce related
     target expressions, given related environments.
     The continuation-passing formulation: given a continuation hypothesis
     that e_k1 and e_k2 are related when the result variables are bound to
     related values, then C1|[e_k1]| and C2|[e_k2]| are related. *)

  Definition anf_cvt_exp_alpha_equiv k :=
    forall e C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel S1 e vars1 cnstrs S2 C1 r1 ->
      anf_cvt_rel S3 e vars2 cnstrs S4 C2 r2 ->
      List.length vars1 = List.length vars2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      preord_env_P_inj cenv eq_fuel (FromList vars1) m
                       (id <{ vars1 ~> vars2 }>) rho1 rho2 ->
      (forall j v1 v2 rho1' rho2',
        (j <= m)%nat ->
        M.get r1 rho1' = Some v1 ->
        M.get r2 rho2' = Some v2 ->
        preord_val cenv eq_fuel j v1 v2 ->
        preord_env_P_inj cenv eq_fuel (FromList vars1) j
                         (id <{ vars1 ~> vars2 }>) rho1' rho2' ->
        preord_exp cenv eq_fuel eq_fuel j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv eq_fuel eq_fuel m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_exps_alpha_equiv k :=
    forall es C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel_exps S1 es vars1 cnstrs S2 C1 xs1 ->
      anf_cvt_rel_exps S3 es vars2 cnstrs S4 C2 xs2 ->
      List.length vars1 = List.length vars2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      preord_env_P_inj cenv eq_fuel (FromList vars1) m
                       (id <{ vars1 ~> vars2 }>) rho1 rho2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        Forall2 (preord_var_env cenv eq_fuel j rho1' rho2') xs1 xs2 ->
        preord_env_P_inj cenv eq_fuel (FromList vars1) j
                         (id <{ vars1 ~> vars2 }>) rho1' rho2' ->
        preord_exp cenv eq_fuel eq_fuel j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv eq_fuel eq_fuel m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_alpha_equiv_statement k :=
    anf_cvt_exp_alpha_equiv k /\
    anf_cvt_exps_alpha_equiv k.

  (* The expression-level alpha equivalence is a large proof by mutual
     structural induction on source expressions, with well-founded induction
     on the step index k. We admit it for now and prove it separately. *)
  Lemma anf_cvt_alpha_equiv :
    forall k, anf_cvt_alpha_equiv_statement k.
  Proof.
  Admitted.


  (** ** Value-level alpha equivalence *)

  Lemma anf_cvt_val_alpha_equiv :
    forall k, anf_cvt_val_alpha_equiv_statement k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1. intros v.
    set (P := fun (v : value) =>
      forall v1 v2 : val,
        anf_val_rel v v1 -> anf_val_rel v v2 ->
        preord_val cenv eq_fuel k v1 v2).
    eapply value_ind' with (P := P); subst P; simpl.

    - (* Con_v *)
      intros dcon vs IH v1 v2 Hrel1 Hrel2.
      inv Hrel1; inv Hrel2.
      rewrite preord_val_eq. simpl. split.
      + congruence.
      + match goal with
        | [ H1 : Forall2 _ vs ?vs1, H2 : Forall2 _ vs ?vs2 |- Forall2 _ ?vs1 ?vs2 ] =>
          revert vs1 vs2 H1 H2;
          induction IH; intros vs1 vs2 Hvs1 Hvs2;
            [ inv Hvs1; inv Hvs2; constructor
            | inv Hvs1; inv Hvs2; constructor; eauto ]
        end.

    - (* Clos_v *)
      intros vs_clos na e_body Hall v1 v2 Hrel1 Hrel2.
      inv Hrel1; inv Hrel2.

      (* Name the key hypotheses from the two inversions *)
      match goal with
      | [ Henv1 : anf_env_rel' _ ?names1 _ ?rho1,
          Hcons1 : env_consistent ?names1 _,
          Hdis1 : Disjoint _ (?x1 |: (?f1 |: FromList ?names1)) ?S1_val,
          Hnin_x1 : ~ _ \in ?f1 |: FromList ?names1,
          Hnin_f1 : ~ _ \in FromList ?names1,
          Hcvt1 : anf_cvt_rel ?S1_val _ (?x1 :: ?names1) _ _ ?C_1 ?r_1,
          Henv2 : anf_env_rel' _ ?names2 _ ?rho2,
          Hcons2 : env_consistent ?names2 _,
          Hdis2 : Disjoint _ (?x2 |: (?f2 |: FromList ?names2)) ?S2_val,
          Hnin_x2 : ~ _ \in ?f2 |: FromList ?names2,
          Hnin_f2 : ~ _ \in FromList ?names2,
          Hcvt2 : anf_cvt_rel ?S2_val _ (?x2 :: ?names2) _ _ ?C_2 ?r_2
        |- preord_val _ _ _ (Vfun ?rho1 (Fcons ?f1 _ [?x1] _ Fnil) ?f1)
                             (Vfun ?rho2 (Fcons ?f2 _ [?x2] _ Fnil) ?f2) ] =>

      assert (Hlen_names : Datatypes.length names1 = Datatypes.length names2)
        by (pose proof (Forall2_length Henv1); pose proof (Forall2_length Henv2); lia);

      eapply preord_val_fun;
      [ simpl; destruct (M.elt_eq f1 f1); [ reflexivity | congruence ]
      | simpl; destruct (M.elt_eq f2 f2); [ reflexivity | congruence ]
      | intros rho1' j vs1 vs2 Hlen Hset1;
        destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence;
        destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence;
        inv Hset1;
        eexists; split; [ reflexivity | ];
        intros Hlt Hall_args; inv Hall_args;
        match goal with
        | [ Hva : preord_val _ _ _ v_arg1 v_arg2 |- _ ] =>

          destruct (anf_cvt_alpha_equiv j) as [Hexp _];
          eapply Hexp with (vars1 := x1 :: names1) (vars2 := x2 :: names2);
          [ lia
          | eassumption
          | eassumption
          | simpl; congruence
          | (* Disjoint side 1 *)
            eapply Union_Disjoint_l;
            [ eapply Disjoint_Singleton_l; intros Hc; eapply Hdis1; constructor;
              [ left; eassumption | eassumption ]
            | eapply Disjoint_Included_r; [ eapply Setminus_Included | ];
              eapply Disjoint_Included_r; [ eapply Setminus_Included | ];
              eapply Disjoint_sym; eassumption ]
          | (* Disjoint side 2 *)
            eapply Union_Disjoint_l;
            [ eapply Disjoint_Singleton_l; intros Hc; eapply Hdis2; constructor;
              [ left; eassumption | eassumption ]
            | eapply Disjoint_Included_r; [ eapply Setminus_Included | ];
              eapply Disjoint_Included_r; [ eapply Setminus_Included | ];
              eapply Disjoint_sym; eassumption ]
          | (* Environment mapping *)
            simpl;
            eapply preord_env_P_inj_set_alt;
            [ eapply preord_env_P_inj_set_not_In_P_l;
              eapply preord_env_P_inj_set_not_In_P_r;
              eapply preord_env_P_inj_antimon;
              [ eapply anf_cvt_env_alpha_equiv_pre; [ eapply IHk; eauto | eassumption | eassumption ]
              | now sets ]
            | rewrite extend_gss; eexists; split; [ rewrite M.gss; reflexivity | eapply preord_val_monotonic; [ eassumption | lia ] ]
            | eapply preord_val_monotonic; [ eassumption | lia ]
            | intros Hc;
              eapply image_extend_Included' in Hc; inv Hc;
              [ eapply image_extend_lst_Included in H; eauto;
                rewrite image_id in H;
                assert (Hseq : (x1 |: FromList names1) \\ [set x1] \\ FromList names1 <--> Empty_set _) by xsets;
                rewrite Hseq in H; inv H
              | inv H; eauto ]
            | intros Hc; inv Hc; eauto ]
          | (* Continuation: Ehalt *)
            intros j0 v1' v2' rho1'' rho2'' Hle Hget1 Hget2 Hval_cont Henv_cont;
            eapply preord_exp_halt_compat;
            [ eapply (eq_fuel_compat cenv)
            | eapply (eq_fuel_compat cenv)
            | intros v_halt Hg; rewrite Hget1 in Hg; inv Hg;
              eexists; split; eassumption ]
          ]
        end
      ]
      end.

    - (* ClosFix_v *)
      intros vs_clos fnl n_idx Hall v1 v2 Hrel1 Hrel2.
      inv Hrel1; inv Hrel2.

      (* Use match to robustly find the fix_rel and nth_error hypotheses *)
      match goal with
      | [ Hfix1 : anf_fix_rel _ ?names1 _ _ _ ?Bs1 _,
          Hfix2 : anf_fix_rel _ ?names2 _ _ _ ?Bs2 _,
          Hnth1 : nth_error _ (N.to_nat n_idx) = Some ?f1,
          Hnth2 : nth_error _ (N.to_nat n_idx) = Some ?f2,
          Henv1 : anf_env_rel' _ ?names1 _ _,
          Henv2 : anf_env_rel' _ ?names2 _ _,
          Hnd1 : NoDup _,
          Hnd2 : NoDup _,
          Hdis_fn1 : Disjoint _ (FromList ?names1 :|: _) _,
          Hdis_fn2 : Disjoint _ (FromList ?names2 :|: _) _,
          Hdis_n1 : Disjoint _ (FromList ?names1) (FromList _),
          Hdis_n2 : Disjoint _ (FromList ?names2) (FromList _)
        |- _ ] =>

      assert (Hname1 := Hfix1); eapply anf_fix_rel_names in Hname1;
      assert (Hname2 := Hfix2); eapply anf_fix_rel_names in Hname2; subst;

      assert (Hlen_names : Datatypes.length names1 = Datatypes.length names2)
        by (pose proof (Forall2_length Henv1); pose proof (Forall2_length Henv2); lia);
      assert (Hlen_fnames : Datatypes.length (all_fun_name Bs1) = Datatypes.length (all_fun_name Bs2))
        by (erewrite anf_fix_rel_fnames_length by exact Hfix1;
            erewrite anf_fix_rel_fnames_length by exact Hfix2; reflexivity);

      revert f1 f2 Hnth1 Hnth2; generalize (N.to_nat n_idx);
      induction k as [m_fix IHm_fix] using lt_wf_rec;
      intros f1 f2 Hnth1_fix Hnth2_fix;

      edestruct (anf_fix_rel_find_def_ext _ _ _ _ _ _ _ _ _ _ _ Hfix1 Hnth1_fix) as
        (x1 & C_1 & r_1 & S_b1 & S_b1' & Hfind1 & Hcvt1 & Hdis_b1 & Hfresh_b1); eauto;
      edestruct (anf_fix_rel_find_def_ext _ _ _ _ _ _ _ _ _ _ _ Hfix2 Hnth2_fix) as
        (x2 & C_2 & r_2 & S_b2 & S_b2' & Hfind2 & Hcvt2 & Hdis_b2 & Hfresh_b2); eauto;

      eapply preord_val_fun; [ exact Hfind1 | exact Hfind2 | ];
      intros rho1' j vs1 vs2 Hlen Hset1;
      destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence;
      destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence;
      inv Hset1;
      eexists; split; [ reflexivity | ];
      intros Hlt Hall_args; inv Hall_args;
      match goal with
      | [ Hva : preord_val _ _ _ v_arg1 v_arg2 |- _ ] =>

        destruct (anf_cvt_alpha_equiv j) as [Hexp _];
        eapply Hexp with
          (vars1 := x1 :: rev (all_fun_name Bs1) ++ names1)
          (vars2 := x2 :: rev (all_fun_name Bs2) ++ names2);
        [ lia
        | eassumption
        | eassumption
        | simpl; rewrite !length_app, !length_rev; congruence
        | (* Disjoint side 1 *)
          eapply Union_Disjoint_l;
          [ eapply Disjoint_Singleton_l; intros Hc;
            eapply Hdis_b1; constructor; [ left; eassumption | eassumption ]
          | eapply Disjoint_Included_r; [ eassumption | ];
            eapply Disjoint_Included_l;
            [ intros z Hz; right; eapply in_app_or in Hz; destruct Hz as [Hz | Hz];
              [ left; rewrite FromList_rev; eapply in_rev in Hz; exact Hz
              | right; exact Hz ]
            | eapply Disjoint_sym; eassumption ] ]
        | (* Disjoint side 2 *)
          eapply Union_Disjoint_l;
          [ eapply Disjoint_Singleton_l; intros Hc;
            eapply Hdis_b2; constructor; [ left; eassumption | eassumption ]
          | eapply Disjoint_Included_r; [ eassumption | ];
            eapply Disjoint_Included_l;
            [ intros z Hz; right; eapply in_app_or in Hz; destruct Hz as [Hz | Hz];
              [ left; rewrite FromList_rev; eapply in_rev in Hz; exact Hz
              | right; exact Hz ]
            | eapply Disjoint_sym; eassumption ] ]
        | (* Environment mapping *)
          simpl;
          eapply preord_env_P_inj_set_alt;
          [ eapply preord_env_P_inj_set_not_In_P_l;
            eapply preord_env_P_inj_set_not_In_P_r;
            rewrite extend_lst_app; rewrite extend_lst_rev; eauto;
            eapply preord_env_P_inj_def_funs_Vfun; try eassumption;
            [ eapply preord_env_P_inj_antimon;
              [ eapply anf_cvt_env_alpha_equiv_pre;
                [ eapply IHk; eauto | eassumption | eassumption ]
              | rewrite Same_set_all_fun_name; rewrite FromList_rev; now xsets ]
            | eapply Disjoint_Included_l;
              [ eapply image_extend_lst_Included; eassumption | ];
              rewrite image_id; rewrite !Same_set_all_fun_name; rewrite FromList_rev;
              assert (Hseq1 : x1 |: (FromList (all_fun_name Bs1) :|: FromList names1) \\ [set x1] \\
                                FromList (all_fun_name Bs1) \\ FromList names1 <--> Empty_set _) by xsets;
              rewrite Hseq1; eapply Union_Disjoint_l; sets
            | intros; subst; repeat subst_exp; eapply IHm_fix; eauto;
              [ intros; eapply IHk; lia
              | eapply Forall_impl; [ | eassumption ]; simpl; intros;
                eapply preord_val_monotonic; [ eassumption | lia ] ]
            | rewrite !length_rev; eassumption
            | intros Hc; eapply image_extend_lst_Included in Hc;
              [ repeat normalize_sets; rewrite image_id in Hc; rewrite !FromList_rev in Hc;
                assert (Hseq2 : x1 |: (FromList (all_fun_name Bs1) :|: FromList names1) \\ [set x1] \\
                                  (FromList (all_fun_name Bs1) :|: FromList names1) <--> Empty_set _) by xsets;
                rewrite Hseq2 in Hc; repeat normalize_sets; now inv Hc; eauto
              | rewrite !length_app, !length_rev; congruence ]
            | intros Hc; eapply image_extend_Included' in Hc;
              inv Hc;
              [ eapply image_extend_lst_Included in H;
                [ repeat normalize_sets; rewrite image_id in H; rewrite !FromList_rev in H;
                  assert (Hseq3 : x1 |: (FromList (all_fun_name Bs1) :|: FromList names1) \\ [set x1] \\
                                    (FromList (all_fun_name Bs1) :|: FromList names1) <--> Empty_set _) by xsets;
                  rewrite Hseq3 in H; repeat normalize_sets; now inv H; eauto
                | rewrite !length_app, !length_rev; congruence ]
              | inv H; eauto ]
            | intros Hc; subst; eauto
            | intros Hc; subst; eauto
            | intros Hc; eapply in_app_or in Hc; inv Hc; eauto; eapply in_rev in H; eauto
            | intros Hc; eapply in_app_or in Hc; inv Hc; eauto; eapply in_rev in H; eauto
            | rewrite !length_app, !length_rev; congruence ]
          | rewrite extend_gss; eexists; split;
            [ rewrite M.gss; reflexivity
            | eapply preord_val_monotonic; [ eassumption | lia ] ]
          | eapply preord_val_monotonic; [ eassumption | lia ]
          | intros Hc; eapply image_extend_Included' in Hc; inv Hc;
            [ eapply image_extend_lst_Included in H;
              [ rewrite image_id in H; rewrite FromList_app, FromList_rev in H;
                assert (Hseq4 : (x1 |: (FromList (all_fun_name Bs1) :|: FromList names1)) \\
                                [set x1] \\ (FromList (all_fun_name Bs1) :|: FromList names1)
                                <--> Empty_set _) by xsets;
                rewrite Hseq4 in H; inv H
              | rewrite !length_app, !length_rev; congruence ]
            | inv H; eauto ]
          | intros Hc; inv Hc; eauto ]
        | (* Continuation: Ehalt *)
          intros j0 v1' v2' rho1'' rho2'' Hle Hget1 Hget2 Hval_cont Henv_cont;
          eapply preord_exp_halt_compat;
          [ eapply (eq_fuel_compat cenv)
          | eapply (eq_fuel_compat cenv)
          | intros v_halt Hg; rewrite Hget1 in Hg; inv Hg;
            eexists; split; eassumption ]
        ]
      end
      end.
  Qed.

End ANF_Val.

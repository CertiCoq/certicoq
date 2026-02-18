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

  (* Like cps_fix_rel_exists: derives enthopt from anf_fix_rel + nth_error,
     without requiring enthopt as a premise. *)
  Lemma anf_fix_rel_exists :
    forall fnames0 names0 S1 fnames_list efns Bs S2 idx f,
      anf_fix_rel fnames0 names0 S1 fnames_list efns Bs S2 ->
      nth_error fnames_list idx = Some f ->
      NoDup fnames_list ->
      exists na e_body x_pc C_body r_body S_body1 S_body2,
        enthopt idx efns = Some (Lam_e na e_body) /\
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel S_body1 e_body (x_pc :: List.rev fnames0 ++ names0) cnstrs S_body2 C_body r_body /\
        Disjoint _ (x_pc |: (FromList fnames0 :|: FromList names0)) S_body1 /\
        ~ x_pc \in (FromList fnames0 :|: FromList names0).
  Proof.
    intros fnames0 names0 S1 fnames_list efns Bs S2 idx f
      Hrel Hnth Hnd.
    revert idx f Hnth Hnd.
    induction Hrel; intros idx0 f0 Hnth Hnd.
    - destruct idx0; discriminate.
    - destruct idx0 as [ | idx'].
      + simpl in Hnth. inv Hnth.
        do 7 eexists. split; [ | split; [ | split; [ | split ] ] ].
        * simpl. reflexivity.
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
      + simpl in Hnth.
        inv Hnd.
        edestruct IHHrel as (na0 & e_body0 & x_pc' & C_body' & r_body' & S_body1' & S_body2' &
                              Henth' & Hfind' & Hcvt' & Hdis' & Hfresh').
        * exact Hnth.
        * assumption.
        * do 7 eexists. split; [ | split; [ | split; [ | split ] ] ].
          -- simpl. exact Henth'.
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

  (** ** Subset and structural lemmas for anf_cvt_rel *)

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
    - intros n S vn tgm S' C x Hrel. inv Hrel. eapply Included_refl.
    - intros na e IH S vn tgm S' C x Hrel. inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IH e.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - intros e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans; eassumption.
    - intros dc es IH S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_exps in *.
      apply_cvt_IH IH es.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - intros e IHe pars bs IHbs S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHbs bs.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - intros na e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans; eassumption.
    - intros efns IHefns n S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_efnlst in *.
      apply_cvt_IH IHefns efns.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - intros S vn tgm S' C x Hrel. inv Hrel. eapply Setminus_Included.
    - intros p S vn tgm S' C x Hrel. inv Hrel. eapply Setminus_Included.
    - intros p S vn tgm S' C x Hrel. inv Hrel.
    - intros S vn tgm S' C xs Hrel. inv Hrel. eapply Included_refl.
    - intros e IHe es IHes S vn tgm S' C xs Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHes es.
      eapply Included_trans; eassumption.
    - intros S vn fnames tgm S' fdefs Hrel. inv Hrel. eapply Included_refl.
    - split.
      + intros na' e' Hlam IHe' efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
        repeat match goal with
        | [ H : Lam_e _ _ = Lam_e _ _ |- _ ] => inv H
        end.
        apply_cvt_IH IHe' e'. apply_cvt_IH IHefns efns.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. eapply Setminus_Included.
      + intros Hnot IHe efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. unfold isLambda in Hnot. contradiction.
    - intros S vn r tgm S' pats Hrel. inv Hrel. eapply Included_refl.
    - intros dc p e IHe bs IHbs S vn r tgm S' pats Hrel.
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

  Lemma anf_cvt_exps_subset S es vn tgm S' C xs :
    anf_cvt_rel_exps S es vn tgm S' C xs -> S' \subset S.
  Proof. eapply (proj1 (proj2 anf_cvt_rel_subset)). Qed.

  Lemma anf_cvt_efnlst_subset S efns vn fnames tgm S' fdefs :
    anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs -> S' \subset S.
  Proof. eapply (proj1 (proj2 (proj2 anf_cvt_rel_subset))). Qed.

  Lemma anf_cvt_branches_subset S bs vn r tgm S' pats :
    anf_cvt_rel_branches S bs vn r tgm S' pats -> S' \subset S.
  Proof. eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))). Qed.

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
        by (eapply anf_cvt_exps_subset; eassumption).
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
        by (eapply anf_cvt_efnlst_subset; eassumption).
      apply Hsub in Hin. inv Hin. apply H0.
      eapply nth_error_In. eassumption.
    - (* Prf_e *)
      intros S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_e *) intros. inv H.
    - (* enil *) exact I.
    - (* econs *) intros; exact I.
    - (* eflnil *) exact I.
    - (* eflcons *) split; intros; exact I.
    - (* brnil *) exact I.
    - (* brcons *) intros; exact I.
  Qed.

  Lemma anf_cvt_rel_efnlst_all_fun_name S efns vn fnames tgm S' fdefs :
    anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs ->
    all_fun_name fdefs = fnames.
  Proof.
    intros H. induction H.
    - reflexivity.
    - simpl. congruence.
  Qed.

  Lemma anf_cvt_rel_branches_ctor_tag S1 S2 S3 S4 bs vn1 vn2 y1 y2 pats1 pats2 :
    anf_cvt_rel_branches S1 bs vn1 y1 cnstrs S2 pats1 ->
    anf_cvt_rel_branches S3 bs vn2 y2 cnstrs S4 pats2 ->
    Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') pats1 pats2.
  Proof.
    revert S1 S2 S3 S4 vn1 vn2 y1 y2 pats1 pats2.
    induction bs; intros S1 S2 S3 S4 vn1 vn2 y1 y2 pats1 pats2 Hrel1 Hrel2.
    - inv Hrel1; inv Hrel2; eauto.
    - inv Hrel1; inv Hrel2; eauto.
  Qed.

  (* When vars1 has duplicates, extend_lst maps to the first occurrence's
     target. The consistent condition ensures all duplicates in vars1 have
     the same target in vars2, making extend_lst agree with nth_error. *)
  Lemma extend_lst_get_nth_error_consistent :
    forall vars1 vars2 n (f : positive -> positive) r1 r2,
      (forall i j x, nth_error vars1 i = Some x -> nth_error vars1 j = Some x ->
                      nth_error vars2 i = nth_error vars2 j) ->
      List.length vars1 = List.length vars2 ->
      nth_error vars1 n = Some r1 ->
      nth_error vars2 n = Some r2 ->
      (f <{ vars1 ~> vars2 }>) r1 = r2.
  Proof.
    induction vars1 as [ | a vars1' IH]; intros vars2 n f r1 r2 Hcon Hlen Hn1 Hn2.
    - destruct n; simpl in Hn1; discriminate.
    - destruct vars2 as [ | b vars2']; [simpl in Hlen; discriminate | ].
      destruct n as [ | n'].
      + (* n = 0 *)
        simpl in Hn1, Hn2. inv Hn1. inv Hn2.
        simpl. rewrite extend_gss. reflexivity.
      + (* n = S n' *)
        simpl in Hn1, Hn2.
        simpl. destruct (Coqlib.peq r1 a) as [Heq | Hneq].
        * (* r1 = a: duplicate *)
          subst. rewrite extend_gss.
          assert (Htmp := Hcon O (S n') a).
          simpl in Htmp. specialize (Htmp eq_refl Hn1).
          rewrite Hn2 in Htmp. inv Htmp. reflexivity.
        * (* r1 ≠ a *)
          rewrite extend_gso; [ | exact Hneq].
          eapply IH.
          -- intros i j x Hi Hj.
             exact (Hcon (S i) (S j) x Hi Hj).
          -- simpl in Hlen. lia.
          -- exact Hn1.
          -- exact Hn2.
  Qed.

  (* Extract from Forall2 given nth_error on the left list. *)
  Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 k a :
    Forall2 R l1 l2 ->
    nth_error l1 k = Some a ->
    exists b, nth_error l2 k = Some b /\ R a b.
  Proof.
    intros HF. revert k. induction HF; intros k Hn.
    - destruct k; discriminate.
    - destruct k as [ | k']; simpl in Hn.
      + inv Hn. eexists. split; [reflexivity | assumption].
      + eapply IHHF. exact Hn.
  Qed.

  (* Build Forall2 from pointwise nth_error-based relation. *)
  Lemma Forall2_from_nth_error {A B : Type} (R : A -> B -> Prop)
        (l1 : list A) (l2 : list B) :
      Datatypes.length l1 = Datatypes.length l2 ->
      (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
      Forall2 R l1 l2.
  Proof.
    revert l2. induction l1 as [ | x xs IH]; intros l2 Hlen Hnth.
    - destruct l2; [constructor | simpl in Hlen; discriminate].
    - destruct l2 as [ | y ys]; [simpl in Hlen; discriminate | ].
      constructor.
      + apply (Hnth 0%nat); reflexivity.
      + apply IH.
        * simpl in Hlen. lia.
        * intros k a b Hk1 Hk2. apply (Hnth (S k)); assumption.
  Qed.

  (** ** Alpha-equivalence for ANF values *)

  Section Alpha_Equiv.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel}
          {trace : Type} {Htrace : @trace_resource trace}.
  Context (P1 : PostT) (PG : PostGT)
          (cenv : ctor_env)
          (Hprops : Post_properties cenv P1 P1 PG)
          (HpropsG : Post_properties cenv PG PG PG)
          (Hincl : inclusion _ (comp P1 P1) P1)
          (HinclG : inclusion _ P1 PG).
  Context (dcon_to_tag_inj :
            forall tgm dc dc',
              dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Definition anf_cvt_val_alpha_equiv_statement k :=
    forall v v1 v2,
      anf_val_rel v v1 -> anf_val_rel v v2 ->
      preord_val cenv PG k v1 v2.

  Definition anf_cvt_env_alpha_equiv_statement k :=
    forall names1 names2 vs rho1 rho2 f,
      anf_env_rel names1 vs rho1 ->
      anf_env_rel names2 vs rho2 ->
      preord_env_P_inj cenv PG (FromList names1) k (f <{ names1 ~> names2 }>) rho1 rho2.

  Lemma preord_env_P_inj_get S k f rho1 rho2 x y v1 v2 :
    preord_env_P_inj cenv PG (S \\ [set x]) k f rho1 rho2 ->
    M.get x rho1 = Some v1 ->
    M.get y rho2 = Some v2 ->
    preord_val cenv PG k v1 v2 ->
    preord_env_P_inj cenv PG S k (f {x ~> y}) rho1 rho2.
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

  (* Forall2 preord_var_env is monotonic in the step index. *)
  Lemma Forall2_preord_var_env_monotonic k j rho1 rho2 vars1 vars2 :
    (j <= k)%nat ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    Forall2 (preord_var_env cenv PG j rho1 rho2) vars1 vars2.
  Proof.
    intros Hle. eapply Forall2_monotonic.
    intros x y Hpve. eapply preord_var_env_monotonic; eassumption.
  Qed.

  (* Forall2 preord_var_env is preserved under M.set on both sides,
     when the set variables are not in the Forall2 lists. *)
  Lemma Forall2_preord_var_env_set k rho1 rho2 x1 x2 v1 v2 vars1 vars2 :
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    ~ x1 \in FromList vars1 ->
    ~ x2 \in FromList vars2 ->
    Forall2 (preord_var_env cenv PG k (M.set x1 v1 rho1) (M.set x2 v2 rho2))
            vars1 vars2.
  Proof.
    intros HF Hni1 Hni2. induction HF.
    - constructor.
    - constructor.
      + eapply preord_var_env_extend_neq.
        * exact H.
        * intros Heq. apply Hni1. subst. now left.
        * intros Heq. apply Hni2. subst. now left.
      + eapply IHHF.
        * intros Hc. apply Hni1. now right.
        * intros Hc. apply Hni2. now right.
  Qed.

  (* Forall2 preord_var_env is preserved under def_funs on both sides,
     when the Forall2 list variables are disjoint from fundefs names. *)
  Lemma Forall2_preord_var_env_def_funs k B1 B2 rho1 rho2 vars1 vars2 :
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    Disjoint _ (FromList vars1) (name_in_fundefs B1) ->
    Disjoint _ (FromList vars2) (name_in_fundefs B2) ->
    Forall2 (preord_var_env cenv PG k
               (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
            vars1 vars2.
  Proof.
    intros HF Hd1 Hd2. induction HF.
    - constructor.
    - constructor.
      + eapply preord_var_env_def_funs_not_In_r.
        * intros Hc. eapply Hd2. constructor.
          now left. exact Hc.
        * eapply preord_var_env_def_funs_not_In_l.
          -- intros Hc. eapply Hd1. constructor.
             now left. exact Hc.
          -- exact H.
      + eapply IHHF.
        * eapply Disjoint_Included_l; [ | exact Hd1 ].
          intros z Hz. now right.
        * eapply Disjoint_Included_l; [ | exact Hd2 ].
          intros z Hz. now right.
  Qed.

  (* Build Forall2 (preord_var_env) from anf_env_rel' on both sides,
     using anf_cvt_val_alpha_equiv to relate values at each position. *)
  Lemma anf_cvt_env_alpha_equiv_Forall2 k :
    anf_cvt_val_alpha_equiv_statement k ->
    forall vs nms_a nms_b rho_a rho_b,
      anf_env_rel' anf_val_rel nms_a vs rho_a ->
      anf_env_rel' anf_val_rel nms_b vs rho_b ->
      Forall2 (preord_var_env cenv PG k rho_a rho_b) nms_a nms_b.
  Proof.
    intros Hval. induction vs; intros nms_a nms_b rho_a rho_b Hrel1 Hrel2.
    - inv Hrel1. inv Hrel2. constructor.
    - inv Hrel1. inv Hrel2. destructAll. constructor.
      + intros v1 Hget1.
        match goal with
        | [ H1 : M.get ?x1 rho_a = Some ?w1,
            H2 : M.get ?x2 rho_b = Some ?w2,
            Hv1 : anf_val_rel a ?w1,
            Hv2 : anf_val_rel a ?w2 |- _ ] =>
          rewrite H1 in Hget1; inv Hget1;
          eexists; split; [ exact H2 | eapply Hval; eassumption ]
        end.
      + eapply IHvs; eassumption.
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
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        preord_var_env cenv PG j rho1' rho2' r1 r2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_exps_alpha_equiv k :=
    forall es C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel_exps S1 es vars1 cnstrs S2 C1 xs1 ->
      anf_cvt_rel_exps S3 es vars2 cnstrs S4 C2 xs2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') xs1 xs2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_efnlst_alpha_equiv k :=
    forall efns B1 B2 fnames1 fnames2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4,
      (m <= k)%nat ->
      anf_cvt_rel_efnlst S1 efns vars1 fnames1 cnstrs S2 B1 ->
      anf_cvt_rel_efnlst S3 efns vars2 fnames2 cnstrs S4 B2 ->
      NoDup fnames1 ->
      NoDup fnames2 ->
      List.length fnames1 = List.length fnames2 ->
      Disjoint _ (FromList fnames1 :|: FromList vars1) S1 ->
      Disjoint _ (FromList fnames2 :|: FromList vars2) S3 ->
      Disjoint _ (FromList fnames1) (FromList vars1) ->
      Disjoint _ (FromList fnames2) (FromList vars2) ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      Forall2 (preord_var_env cenv PG m
                 (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
              fnames1 fnames2.

  Definition anf_cvt_branches_alpha_equiv k :=
    forall bs pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
      (m <= k)%nat ->
      anf_cvt_rel_branches S1 bs vars1 y1 cnstrs S2 pats1 ->
      anf_cvt_rel_branches S3 bs vars2 y2 cnstrs S4 pats2 ->
      Disjoint _ ([set y1] :|: FromList vars1) S1 ->
      Disjoint _ ([set y2] :|: FromList vars2) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_var_env cenv PG m rho1 rho2 y1 y2 ->
      preord_exp cenv P1 PG m (Ecase y1 pats1, rho1) (Ecase y2 pats2, rho2).

  Definition anf_cvt_alpha_equiv_statement k :=
    anf_cvt_exp_alpha_equiv k /\
    anf_cvt_exps_alpha_equiv k /\
    anf_cvt_efnlst_alpha_equiv k /\
    anf_cvt_branches_alpha_equiv k.

  Lemma anf_cvt_alpha_equiv :
    forall k, anf_cvt_alpha_equiv_statement k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1.
    unfold anf_cvt_alpha_equiv_statement.
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2. simpl.
      eapply Hk; [lia | | exact Henv | intros ? ? H _ _; exact H].
      match goal with
      | [ Hfa : Forall2 _ ?l1 _, Hn : nth_error ?l1 _ = Some _ |- _ ] =>
        destruct (Forall2_nth_error_l _ _ _ _ _ Hfa Hn) as [? [Hn2 ?]]
      end.
      match goal with
      | [ H1 : nth_error ?l ?k = Some ?a, H2 : nth_error ?l ?k = Some ?b |- _ ] =>
        rewrite H1 in H2; inv H2
      end. assumption.
    - (* Lam_e *) admit.
    - (* App_e *)
      intros e1 IH1 e2 IH2 C1 C2 r1 r2 m vars1 vars2 rho1 rho2
             S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2.
      rewrite <- !app_ctx_f_fuse. simpl.
      eapply IH1.
      + exact Hm.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Henv.
      + (* continuation for e1: env has x1 bound *)
        intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres1.
        eapply IH2.
        * lia.
        * eassumption.
        * eassumption.
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * exact Henv_vars.
        * (* continuation for e2: env has x1, x2 bound *)
          intros j' rho1'' rho2'' Hle' Hvar_x2 Henv_vars' Hpres2.
          eapply preord_exp_letapp_compat.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- (* function: x1 preserved through C2 using Hpres2 *)
             eapply Hpres2.
             ++ eapply preord_var_env_monotonic. exact Hvar_x1. lia.
             ++ eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis1].
             ++ eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis2].
          -- constructor. exact Hvar_x2. constructor.
          -- (* letapp callback: r is bound to the call result *)
             intros m'' v1 v2 Hlt Hval.
             eapply Hk.
             ++ lia.
             ++ (* preord_var_env for r1/r2 = result of app *)
                intros w1 Hgr1. rewrite M.gss in Hgr1. inv Hgr1.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hval. lia.
             ++ (* Forall2 for vars: r doesn't interfere (fresh), preserved by M.set r *)
                eapply Forall2_preord_var_env_set.
                ** eapply Forall2_preord_var_env_monotonic with (k := j'); [lia | exact Henv_vars'].
                ** intros Hr1_vars.
                   assert (H65 : S6 \subset S5) by (eapply anf_cvt_exp_subset; eassumption).
                   assert (H51 : S5 \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                   eapply Hdis1. constructor. exact Hr1_vars. apply H51. apply H65. eassumption.
                ** intros Hr2_vars.
                   assert (H72 : S7 \subset S2) by (eapply anf_cvt_exp_subset; eassumption).
                   assert (H23 : S2 \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                   eapply Hdis2. constructor. exact Hr2_vars. apply H23. apply H72. eassumption.
             ++ (* preservation through all three contexts + letapp binding *)
                intros a b Hvar_ab Ha Hb.
                eapply preord_var_env_extend_neq.
                ** eapply preord_var_env_monotonic.
                   --- eapply Hpres2.
                       +++ eapply Hpres1. exact Hvar_ab. exact Ha. exact Hb.
                       +++ intro Hc. apply Ha.
                           assert (Hs51 : S5 \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                           exact (Hs51 _ Hc).
                       +++ intro Hc. apply Hb.
                           assert (Hs23 : S2 \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                           exact (Hs23 _ Hc).
                   --- lia.
                ** intros Heq. subst. apply Ha.
                   assert (H65 : S6 \subset S5) by (eapply anf_cvt_exp_subset; eassumption).
                   assert (H51 : S5 \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                   apply H51. apply H65. eassumption.
                ** intros Heq. subst. apply Hb.
                   assert (H72 : S7 \subset S2) by (eapply anf_cvt_exp_subset; eassumption).
                   assert (H23 : S2 \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                   apply H23. apply H72. eassumption.
    - (* Con_e *) admit.
    - (* Match_e *) admit.
    - (* Let_e *)
      intros na e1 IH1 e2 IH2 C1 C2 r1 r2 m vars1 vars2 rho1 rho2
             S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2.
      rewrite <- !app_ctx_f_fuse.
      eapply IH1.
      + exact Hm.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Henv.
      + intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres.
        (* e2 is converted with x1 added to var list *)
        eapply IH2.
        * lia.
        * eassumption.
        * eassumption.
        * rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l.
             eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis1].
          -- eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l.
             eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis2].
          -- eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * (* Forall2 for x1::vars1, x1'::vars2 in rho1', rho2' *)
          constructor.
          -- exact Hvar_x1.
          -- exact Henv_vars.
        * (* continuation for e2 *)
          intros j' rho1'' rho2'' Hle' Hvar_r2 Henv_vars2 Hpres'.
          eapply Hk.
          -- lia.
          -- exact Hvar_r2.
          -- inv Henv_vars2. eassumption.
          -- (* preservation: compose Hpres then Hpres' *)
             intros a b Hvar_ab Ha Hb.
             eapply Hpres'.
             ++ eapply Hpres. exact Hvar_ab. exact Ha. exact Hb.
             ++ intro Hc. apply Ha.
                assert (Hsub1 : _ \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub1 _ Hc).
             ++ intro Hc. apply Hb.
                assert (Hsub2 : _ \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub2 _ Hc).
    - (* Fix_e *) admit.
    - (* Prf_e *)
      intros C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2. simpl.
      eapply preord_exp_constr_compat.
      + eapply Hprops.
      + eapply Hprops.
      + constructor.
      + intros m0 vs1 vs2 Hlt Hvals.
        eapply Hk.
        * lia.
        * (* preord_var_env for result: r1=x, r2=x0, in M.set env *)
          intros v1 Hg1. rewrite M.gss in Hg1. inv Hg1.
          eexists. split. { rewrite M.gss. reflexivity. }
          rewrite preord_val_eq. simpl. split; [reflexivity | eassumption].
        * (* Forall2 preserved by M.set: fresh vars don't affect existing bindings *)
          eapply Forall2_preord_var_env_set.
          -- eapply Forall2_preord_var_env_monotonic; [ | eassumption ]. lia.
          -- intros Hin. eapply Hdis1. constructor; eassumption.
          -- intros Hin. eapply Hdis2. constructor; eassumption.
        * (* preservation *)
          intros a b Hvar Ha Hb.
          eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic. eassumption. lia.
          -- intros Heq. subst. eapply Ha. eassumption.
          -- intros Heq. subst. eapply Hb. eassumption.
    - (* Prim_val_e *)
      intros p C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2. simpl.
      eapply preord_exp_prim_val_compat. eapply Hprops.
    - (* Prim_e *)
      intros p C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1.
    - (* enil *)
      intros C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2. simpl.
      eapply Hk; [lia | constructor | eassumption | intros ? ? H _ _; exact H].
    - (* econs *)
      intros e IH_e es IH_es C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2
             S1 S2 S3 S4 e_k1 e_k2
             Hm He1 He2 Hdis1 Hdis2 Henv Hk.
      inv He1. inv He2.
      rewrite <- !app_ctx_f_fuse.
      eapply IH_e.
      + exact Hm.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Henv.
      + (* continuation for head expression *)
        intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres.
        eapply IH_es.
        * lia.
        * eassumption.
        * eassumption.
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * exact Henv_vars.
        * (* continuation for tail expression list *)
          intros j' rho1'' rho2'' Hle' Hxs_tail Henv_vars' Hpres'.
          eapply Hk.
          -- lia.
          -- (* Forall2 for x1 :: xs_tail *)
             constructor.
             ++ (* head: x1 preserved through tail context using Hpres' *)
                eapply Hpres'.
                ** eapply preord_var_env_monotonic. exact Hvar_x1. lia.
                ** eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis1].
                ** eapply anf_cvt_result_not_in_output; [eassumption | exact Hdis2].
             ++ exact Hxs_tail.
          -- exact Henv_vars'.
          -- (* preservation: compose Hpres then Hpres' *)
             intros a b Hvar_ab Ha Hb.
             eapply Hpres'.
             ++ eapply Hpres. exact Hvar_ab. exact Ha. exact Hb.
             ++ intro Hc. apply Ha.
                assert (Hsub1 : _ \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub1 _ Hc).
             ++ intro Hc. apply Hb.
                assert (Hsub2 : _ \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub2 _ Hc).
    - (* eflnil *)
      intros B1 B2 fnames1 fnames2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4
             Hm He1 He2 Hnd1 Hnd2 Hlen_fn
             Hdis1 Hdis2 Hdis_fn1 Hdis_fn2 Henv.
      inv He1. inv He2. constructor.
    - (* eflcons *) admit.
    - (* brnil_e *)
      intros pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
             Hm He1 He2 Hdis1 Hdis2 Henv Hvar.
      inv He1. inv He2.
      eapply preord_exp_case_nil_compat. eapply Hprops.
    - (* brcons_e *) admit.
  Admitted.


  (** ** Value-level alpha equivalence *)

  Lemma anf_cvt_val_alpha_equiv :
    forall k, anf_cvt_val_alpha_equiv_statement k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1. intros v.
    set (P := fun (v : value) =>
      forall v1 v2 : val,
        anf_val_rel v v1 -> anf_val_rel v v2 ->
        preord_val cenv PG k v1 v2).
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
      inv Hrel1. inv Hrel2.
      eapply preord_val_fun.
      + simpl. rewrite Coqlib.peq_true. reflexivity.
      + simpl. rewrite Coqlib.peq_true. reflexivity.
      + intros rho1' j vs1 vs2 Hlen Hset1.
        destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence.
        destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence.
        inv Hset1.
        eexists. split; [reflexivity | ].
        intros Hlt Hall_args. inv Hall_args.
        eapply preord_exp_post_monotonic. now eapply HinclG.
        destruct (anf_cvt_alpha_equiv j) as [Hexp [_ [_ _]]].
        eapply Hexp; [lia | eassumption | eassumption | | | | ].
        * (* Disjoint side 1 *)
          eapply Disjoint_Included_l; [ | eassumption ].
          normalize_sets. now sets.
        * (* Disjoint side 2 *)
          eapply Disjoint_Included_l; [ | eassumption ].
          normalize_sets. now sets.
        * (* Forall2 (preord_var_env) for x :: names and x0 :: names0 *)
          constructor.
          -- (* head: x x0 in M.set env *)
             eapply preord_var_env_extend_eq. eassumption.
          -- (* tail: names names0, env is M.set x _ (M.set f _ rho) *)
             eapply Forall2_preord_var_env_set.
             ++ (* peel f/f0 M.set *)
                eapply Forall2_preord_var_env_set.
                ** eapply anf_cvt_env_alpha_equiv_Forall2.
                   --- eapply IHk. lia.
                   --- eassumption.
                   --- eassumption.
                ** (* ~ f \in FromList names *)
                   assumption.
                ** (* ~ f0 \in FromList names0 *)
                   assumption.
             ++ (* ~ x \in FromList names *)
                match goal with
                | [ H : ~ ?y \in _ |: FromList ?ns |- ~ ?y \in FromList ?ns ] =>
                  intros Hc; apply H; right; exact Hc
                end.
             ++ (* ~ x0 \in FromList names0 *)
                match goal with
                | [ H : ~ ?y \in _ |: FromList ?ns |- ~ ?y \in FromList ?ns ] =>
                  intros Hc; apply H; right; exact Hc
                end.
        * (* Continuation: Ehalt *)
          intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _.
          eapply preord_exp_halt_compat.
          -- eapply Hprops.
          -- eapply Hprops.
          -- exact Hvar_cont.

    - (* ClosFix_v *)
      intros vs_clos fnl n_idx Hall v1 v2 Hrel1 Hrel2.
      inv Hrel1; inv Hrel2.

      (* Name the fix_rel hypotheses using the goal to disambiguate *)
      match goal with
      | [ H : anf_fix_rel _ _ _ _ _ ?B _ |- preord_val _ _ _ (Vfun _ ?B _) _ ] =>
        rename H into Hfix1
      end.
      match goal with
      | [ H : anf_fix_rel _ _ _ _ _ ?B _ |- preord_val _ _ _ _ (Vfun _ ?B _) ] =>
        rename H into Hfix2
      end.

      assert (Hname1 := Hfix1); eapply anf_fix_rel_names in Hname1.
      assert (Hname2 := Hfix2); eapply anf_fix_rel_names in Hname2. subst.

      assert (Hlen_fnames : Datatypes.length (all_fun_name Bs) = Datatypes.length (all_fun_name Bs0))
        by (erewrite anf_fix_rel_fnames_length by exact Hfix1;
            erewrite anf_fix_rel_fnames_length by exact Hfix2; reflexivity).

      (* Revert nth_error hypotheses for induction *)
      match goal with
      | [ H1 : nth_error _ (N.to_nat n_idx) = Some ?g1,
          H2 : nth_error _ (N.to_nat n_idx) = Some ?g2
          |- preord_val _ _ _ (Vfun _ _ ?g1) (Vfun _ _ ?g2) ] =>
        revert g1 g2 H1 H2
      end.
      generalize (N.to_nat n_idx).
      induction k as [m_fix IHm_fix] using lt_wf_rec.
      intros n_fix f1 f2 Hnth1_fix Hnth2_fix.

      edestruct (anf_fix_rel_exists _ _ _ _ _ _ _ _ _ Hfix1 Hnth1_fix) as
        (na1 & e_body1 & x1 & C_1 & r_1 & S_b1 & S_b1' & Henth1 & Hfind1 & Hcvt1 & Hdis_b1 & Hfresh_b1).
      { assumption. }
      edestruct (anf_fix_rel_exists _ _ _ _ _ _ _ _ _ Hfix2 Hnth2_fix) as
        (na2 & e_body2 & x2 & C_2 & r_2 & S_b2 & S_b2' & Henth2 & Hfind2 & Hcvt2 & Hdis_b2 & Hfresh_b2).
      { assumption. }

      (* Both enthopt results are for the same index into the same efnlst,
         so the source expressions must be equal. *)
      assert (Hbody_eq : Lam_e na1 e_body1 = Lam_e na2 e_body2) by congruence.
      inv Hbody_eq.

      eapply preord_val_fun.
      + exact Hfind1.
      + exact Hfind2.
      + intros rho1' j vs1 vs2 Hlen Hset1.
        destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence.
        destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence.
        inv Hset1.
        eexists. split. { reflexivity. }
        intros Hlt Hall_args. inv Hall_args.

        eapply preord_exp_post_monotonic. { now eapply HinclG. }
        destruct (anf_cvt_alpha_equiv j) as [Hexp [_ [_ _]]].

        (* Build the Forall2 env relation *)
        assert (HenvF :
          Forall2 (preord_var_env cenv PG j
                     (M.set x1 v_arg1 (def_funs Bs Bs rho rho))
                     (M.set x2 v_arg2 (def_funs Bs0 Bs0 rho0 rho0)))
                  (x1 :: rev (all_fun_name Bs) ++ names)
                  (x2 :: rev (all_fun_name Bs0) ++ names0)).
        { constructor.
          - (* head: x1, x2 — function args *)
            eapply preord_var_env_extend_eq. eassumption.
          - (* tail: rev fnames ++ names *)
            eapply Forall2_preord_var_env_set.
            + (* Forall2 at def_funs level *)
              eapply Forall2_app.
              * (* rev fnames: closures related by inner IH *)
                eapply All_Forall.Forall2_rev.
                eapply Forall2_from_nth_error.
                -- exact Hlen_fnames.
                -- intros n_cl f1_cl f2_cl Hn1_cl Hn2_cl.
                   intros v1_cl Hget1_cl.
                   assert (Hni1 : name_in_fundefs Bs f1_cl)
                     by (rewrite name_fds_same; eapply nth_error_In; eassumption).
                   rewrite (def_funs_eq _ _ _ _ _ Hni1) in Hget1_cl.
                   inv Hget1_cl.
                   assert (Hni2 : name_in_fundefs Bs0 f2_cl)
                     by (rewrite name_fds_same; eapply nth_error_In; eassumption).
                   eexists. split.
                   ++ exact (def_funs_eq _ _ _ _ _ Hni2).
                   ++ (* preord_val for closure pair — from inner IH *)
                      eapply IHm_fix.
                      ** lia.
                      ** intros m0 Hm0. eapply IHk. lia.
                      ** { rewrite Forall_forall. intros v0 _. intros v1' v2' Hr1 Hr2.
                           exact (IHk j Hlt v0 v1' v2' Hr1 Hr2). }
                      ** exact Hn1_cl.
                      ** exact Hn2_cl.
              * (* names: captured env *)
                eapply Forall2_preord_var_env_def_funs.
                -- eapply anf_cvt_env_alpha_equiv_Forall2.
                   ++ eapply IHk. lia.
                   ++ eassumption.
                   ++ eassumption.
                -- eapply Disjoint_Included_r;
                     [exact (proj1 (Same_set_all_fun_name _)) | assumption].
                -- eapply Disjoint_Included_r;
                     [exact (proj1 (Same_set_all_fun_name _)) | assumption].
            + (* ~ x1 \in FromList (rev fnames ++ names) *)
              rewrite FromList_app, FromList_rev. exact Hfresh_b1.
            + (* ~ x2 \in FromList (rev fnames0 ++ names0) *)
              rewrite FromList_app, FromList_rev. exact Hfresh_b2. }

        eapply Hexp with
          (vars1 := x1 :: rev (all_fun_name Bs) ++ names)
          (vars2 := x2 :: rev (all_fun_name Bs0) ++ names0);
        [ lia
        | eassumption
        | eassumption
        | (* Disjoint side 1 *)
          eapply Disjoint_Included_l; [ | exact Hdis_b1 ];
          rewrite FromList_cons, FromList_app, FromList_rev; now sets
        | (* Disjoint side 2 *)
          eapply Disjoint_Included_l; [ | exact Hdis_b2 ];
          rewrite FromList_cons, FromList_app, FromList_rev; now sets
        | (* Forall2 env *)
          exact HenvF
        | (* Continuation: Ehalt *)
          intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _;
          eapply preord_exp_halt_compat;
          [ eapply Hprops
          | eapply Hprops
          | exact Hvar_cont ]
        ].
  Qed.

  End Alpha_Equiv.

End ANF_Val.

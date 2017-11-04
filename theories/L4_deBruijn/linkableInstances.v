Require Import L4.instances.
Require Import L4.L3_to_L4.
Require Import L4.L4_5_to_L5.
Require Import L4.L4_2_to_L4_5.
Require Import L4.variables.
Require Import L4.varInterface.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import Coq.Lists.List.
Require Import Common.certiClasses.
Require Import Common.certiClasses2.
Require Import Common.certiClasses3.
Require Import Common.certiClassesLinkable.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
Require Import Program.
Require Import Btauto.

Import ListNotations.

Section LocalInstances.

  Local Instance L4_5bs : BigStepOpSem (prod ienv L4_5_Term).
  apply dummyEnvBigStep. eauto with typeclass_instances.
  Defined.
  Local Instance L5bs : BigStepOpSem (prod ienv (@NTerm NVar L5Opid)).
  apply dummyEnvBigStep. eauto with typeclass_instances.
  Defined.


Local Instance L4_5MkApply : MkApply  (ienv * L4_5_Term) :=
    fun f a => let (senv,f) := f in let (_, a) := a in (senv, App_e f a).

  Definition extractL5Core (t:L5Term) :=
    match t with
      (*  L4_5_to_L5.Ret_c core haltCont => core *)
      oterm CRet [bterm [] core; _] => core
      | _ => oterm CRet [] (* impossible, hence garbage *)
    end.

  Local Instance L5MkApply : MkApply  (ienv * L5Term) :=
    fun f a => let (senv,f) := f in
            let (_, a) := a in
            let a := extractL5Core a in
            (senv, mkAppHalt (val_outer f) a).
  
  (*TODO: re add after ending sections *)

  Hint Unfold L5bs  bigStepEval : certiclasses.

  (* Move *)
  
(*
Lemma evalc_terminal
     : forall e v,
      eval_c e v -> eval_c v v.
Proof using.
  intros ? ? Heval.
  induction Heval; auto;[]. (* eval_halt_c case. fix. require some kind of an is_value.
A ugly hacky way would be to require that it is the vps_cvt_val of something. *)
Abort.

Lemma evalc_halt
     : forall hv v,
      eval_c (Halt_c hv) v <-> eval_c hv v.
Proof using.
  intros.
  split; intros Hyp.
  - inversion Hyp. subst. eapply evalc_terminal; eauto.
  - (* need the is_value hyp? *)
Abort.    
 *)

Lemma goodSubterms25 : forall o lbt,
    @goodTerm L4_5_Term _ (oterm o lbt)
    -> forall nt, In (bterm [] nt) lbt  -> goodTerm nt.
Proof using.
  intros ? ? Hg ? Hin. autounfold with certiclasses eval in *.
  unfold closed in *. simpl in *.
  repnd.
  rewrite  list.flat_map_empty in Hg2.
  autorewrite with SquiggleEq in Hg0.
  specialize (Hg2 _ Hin).
  simpl in *.
  dands; auto.
  - intros ? Hc. apply Hg0. apply in_flat_map. eexists; dands; eauto.
  - ntwfauto.
  - rewrite Bool.andb_true_iff in Hg. apply proj2 in Hg.
    rewrite list.ball_true in Hg. apply Hg.
    apply in_map_iff. eexists; dands; eauto. reflexivity.
Qed. 

Require Import SquiggleEq.list.
Lemma goodSubtermsApp : forall (a b: L4_5_Term),
    goodTerm a
    -> goodTerm b
    -> goodTerm (App_e a b).
Proof using.
  autounfold with certiclasses in *.
  intros ? ? H1g H2g.
  unfold App_e. 
  rwsimplC. unfold compose. simpl.
  unfold isprogram, closed in *.
  simpl. rwsimplC. repnd.
  dands; eauto with SquiggleEq.
  - rwHyps. refl.
  - ntwfauto. rewrite  or_false_r in HntwfIn. subst. ntwfauto.
Qed.


Lemma value_cps_val (v : L4_5_Term) :
  is_value v -> closed v -> eval_c (cps_cvt_val v) (cps_cvt_val v).
Proof using.
  intros Hisv Hcl.
  destruct Hisv; try (apply eval_Val_c; reflexivity).
  inversion Hcl.
Qed. (** need to fix eval_c to make this true *)

Lemma value_cps_val_only (v : L4_5_Term) vc:
  eval_c (cps_cvt_val v) vc -> vc= (cps_cvt_val v).
Proof using.
  intros Hev.
  destruct v.
  inversion Hev;subst. invertsn H.
  rename l into o.
  destruct o; invertsna Hev Hevv; auto; provefalse.
  - destruct l0; invertsn Hevv. destruct b. destruct l; invertsn Hevv.
    destruct l; invertsn Hevv. destruct l0; invertsn Hevv.
  - clear Hevv.  rename Hevv0 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv.  rename Hevv0 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv Hevv0.  rename Hevv1 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv Hevv0 Hevv1.  rename Hevv2 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
Qed.

Lemma L5DetBigStep :
  deterministicBigStep (ienv * L5Term).
Admitted.

Lemma obsLinkableL45:
  compObsPreservingLinkable  (ienv * L4_5_Term) (ienv * L5Term).
Proof.
  intros s Hgood. simpl. constructor.
  apply toCoInd; [ apply L5DetBigStep | ].
  intros cm.
  revert dependent s.
  induction cm as [ | cm obsLinkableL45];constructor.
  intros ? Heval.
  simpl.
  destruct Heval as [Heq Heval].
  destruct s as [senv s].
  destruct sv as [? sv]. symmetry in Heq.
  simpl in *. subst.
  exists (senv, (cps_cvt_val sv)).
  pose proof (evalPreservesGood _ _ Heval Hgood) as Hgoodsv.
  pose proof (eval_yields_value' _ _ Heval) as Hvalue.
  repeat progress autounfold with certiclasses.
  simpl in *. 
  dands; [ reflexivity | | | | ].

  + simpl in Hgood. autounfold with certiclasses in Hgood. simpl in Hgood.
    simpl in Hgood. autounfold with certiclasses in Hgood. simpl in Hgood.
    repnd.
    destruct Hgood1 as [Hclosed Hwf].
    rename Hgood0 into Hvc. rename Hgood into Hfixwf.    pose proof
         (cps_cvt_corr _ _ Hwf Hfixwf Hvc Heval
                       Hclosed haltCont
                       eq_refl
                       ((cps_cvt_val sv)))
      as Hcps.
    apply Hcps. clear Hcps.
    hnf in Heval.
    rewrite (cps_val_ret_flip sv); try split; eauto with eval typeclass_instances.
    unfold haltCont.
    apply haltContAp.
  + hnf in Heval. apply eval_yields_value' in Heval.
    revert Heval. clear. intros Hisv.
    let tac := compute; intros qn;  destruct qn; constructor in
    induction Hisv; simpl; [tac | tac |  | tac].
    unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    destruct q; auto. unfold implb. btauto.
  + clear dependent s. intros n.
    unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    inversion Hvalue;
    (* Not induction. Even though the arguments of constructors are all values, 
     they may be lambdas, and after application, they may need computation *)
    simpl; try (clear obsLinkableL45; compute; constructor; constructor; fail). subst.
    repeat rewrite List.map_map.
    repeat rewrite nth_error_map.
    remember (List.nth_error es n) as esso.
    destruct esso as [ess | ]; try constructor.
    specialize (obsLinkableL45 (senv, ess)).
    symmetry in Heqesso. apply nth_error_In in Heqesso.
    assert (ident : goodTerm (senv, ess)) by
      (eapply goodSubterms25;[apply Hgoodsv | apply in_map; assumption]).
    specialize (obsLinkableL45 ident).
    unfold translateT, certiL4_5_to_L5 in obsLinkableL45.
    revert obsLinkableL45.
    assert (Hp:forall A B, (A<->B)->(A->B)) by tauto.
    apply Hp. clear Hp. simpl.
    eapply compObsLeLinkNRespectsSameVal;[ reflexivity | ].
    intros ?.
    apply and_iff_compat_l.
    simpl.  unfold haltCont.
    repeat (autounfold with certiclasses eval in ident;  simpl in ident). repnd. simpl.
    setoid_rewrite (cps_val_ret_flip ess); unfold isprogram; eauto; try reflexivity.
    simpl.
    rewrite eval_ret. simpl. unfold subst. simpl.
    split; intros Hyp.
    * inversion Hyp; try (inversion H0; fail); subst. apply value_cps_val; eauto.
    * apply value_cps_val_only in Hyp; eauto. subst. apply eval_Halt_c.

  + intros Hq ? Hga. unfold mkApp, L4_5MkApply, L5MkApply. simpl.
    destruct svArg as [clear  svArg]. simpl. hnf in Hga. simpl in *. clear clear.
    (* apply the coinduction hypothesis to the full app *)
    specialize (obsLinkableL45 (senv, App_e sv svArg)).
    assert (ident : goodTerm (senv, App_e sv svArg)) by (apply goodSubtermsApp; auto).
    specialize (obsLinkableL45 ident).
    unfold translateT, certiL4_5_to_L5 in obsLinkableL45.
    simpl in *. unfold mkAppHalt. unfold cps_cvt_apply in obsLinkableL45. simpl.
    constructor.
    revert obsLinkableL45.
    assert (Hp:forall A B, (A<->B)->(A->B)) by tauto.
    apply Hp. clear Hp.
    eapply compObsLeLinkNRespectsSameVal;[ reflexivity | ].
    unfold sameValues. intros v. simpl. 
    apply and_iff_compat_l. 
    simpl. autounfold with certiclasses. simpl.
    rewrite eval_ret. (* setoid_rewrite does more rewriting *)
    simpl.
    assert (forall (l1 l2 r: L5Term), l1=l2 -> (eval_c l1 r <-> eval_c l2 r)) as Hp by (intros;subst;tauto).
    apply Hp. clear Hp.
    Local Transparent ssubst_aux ssubst_bterm_aux sub_filter.
    unfold subst.
    autounfold with certiclasses in Hgoodsv.
    unfold isprogram, closed in *.
    assert (free_vars (cps_cvt sv) = []) as Hs.
      (symmetry; rewrite cps_cvt_aux_fvars ; repnd; auto).
    assert (free_vars (cps_cvt svArg) = []) as Hsa by
      (symmetry; rewrite cps_cvt_aux_fvars ; repnd; auto; congruence). repnd.
    change_to_ssubst_aux8; [  | simpl; disjoint_reasoningv2 ].
    simpl.
    rewrite (fst ssubst_aux_trivial5) at 1; [ | simpl; rewrite Hs; apply list.disjoint_nil_l ].
    rewrite (fst ssubst_aux_trivial5); [ | simpl; rewrite Hsa; apply list.disjoint_nil_l ].
    unfold cps_cvt_apply_aux,  L4_5_to_L5.Ret_c,  L4_5_to_L5.KLam_c.
    repeat f_equal.
    apply cps_val_outer. apply is_valueb_corr. eapply eval_yields_value'; eauto.
    Fail idtac.
    Unshelve.
    apply goodPres45.
    apply goodPres45.
Qed.

Lemma appArgCongrL5 : @appArgCongr (ienv*L5Term) _ _ _ _ _ .
Proof using.
  cofix.
  intros ? ? ? H1g H2g Hle.
  unfold leObsId in *.
  constructor.
  invertsn Hle. 
  intros sv Hev. autounfold with certiclasses in Hev.
  unfold dummyEnvBigStep in Hev.
  destruct tt1 as [env tt1]. destruct ff as [envv ff].
  destruct sv as [envvv sv].
  simpl in Hev. repnd. subst.
  autounfold with certiclasses in Hev.
  induction Hev.
Abort.


End LocalInstances.
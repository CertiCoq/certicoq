Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L2k.compile.
Require Import L4.L3_to_L4.
Require Import L4.L3_to_L3_eta.
Require Import L4.L3_eta_crct.
Require Import L4.L3_to_L3_eta_correct.
Require Import L4.L3_to_L4_correct.
Require L2k.
Require Import L2k.instances.

Require Import BinNat.
Require Import certiClasses2.

Definition L3_eta_Program := Program Term.
Typeclasses Opaque L3_eta_Program.

Instance bigStepOpSemL3_etaTerm:
  BigStepOpSem L3_eta_Program L3_eta_Program.
Proof.
  intros s sv. destruct s, sv. exact (L2k.wcbvEval.WcbvEval env main main0 /\ env = env0).
                                      (* L3_to_L4_correct.WcbvEval_env env env0). *)
Defined.

Global Instance ObsSubtermL3_eta : ObserveNthSubterm L3_eta_Program :=
  L2k.instances.ObsSubtermL2kTerm.

Global Instance QuestionHeadTermL3_eta : QuestionHead L3_eta_Program :=
  L2k.instances.QuestionHeadL2kTerm.

Instance WfL3_etaTerm : GoodTerm L3_eta_Program :=
  fun p : Program Term => L4.L3_eta_crct.crctTerm (AstCommon.env p) 0 (main p).

Global Instance certiL3_eta: CerticoqLanguage L3_eta_Program := {}.

Global Instance certiL3_to_L3_eta:
  CerticoqTranslation (cTerm certiL2k) (cTerm certiL3_eta) :=
  fun o p =>
    (AstCommon.timePhase "L2 to L3")
      (fun (_:Datatypes.unit) => (Ret (L3_to_L3_eta.Program_Program p))).

Lemma L3_crctEnv_inv d e : L2k.program.crctEnv (d :: e) -> L2k.program.crctEnv e.
Proof.
  intros. inv H. apply L2k.program.Crct_CrctEnv in H4. easy. auto.
Qed.
Hint Resolve L3_crctEnv_inv.

Lemma leb_refl b : Bool.leb b b.
Proof.
  now destruct b.
Qed.

Lemma obs_prevervation : forall p, p ⊑ Program_Program p.
Proof.
  intros [m e]; simpl.
  revert e.
  apply (TrmTrmsBrsDefs_ind
           (fun (main : Term) => forall e,
                {| main := main; AstCommon.env := e |} ⊑ {| main := trans main; AstCommon.env := transEnv e |})
             (fun ts => forall e i n n0,
                 obsLeOp (observeNthSubterm n0 {| main := TConstruct i n ts; AstCommon.env := e |})
                         (observeNthSubterm n0 {| main := trans (TConstruct i n ts);
                                                    AstCommon.env := transEnv e |}))
             (fun _ => True) (fun _ => True));
        try constructor;
        try (match goal with |- yesPreserved _ _ => intros q; destruct q end);
        intros; try red; trivial; try constructor.

  simpl.
  - unfold questionHead, observeNthSubterm, QuestionHeadL2kTerm, QuestionHeadTermL3_eta; simpl.
    apply Bool.leb_implb, leb_refl.
  - simpl.
    unfold observeNthSubterm, ObsSubtermL3_eta, ObsSubtermL2kTerm. simpl.
    destruct n0. constructor. apply H. apply (H0 e i n0).
Qed.

Lemma trans_pres_Crct env main :
  L2k.program.crctTerm env 0 main -> crctTerm env 0 main.
Proof.
  (* TODO *)
Admitted.

Lemma trans_pres_Crct_env env :
  L2k.program.crctEnv env -> crctEnv env.
Proof.
  intros Henv. induction Henv; constructor; auto.
  now apply trans_pres_Crct.
Qed.

Global Instance certiL3_to_L3_eta_correct :
  CerticoqTranslationCorrect certiL2k certiL3_eta.
Proof.
  split; intros ? *; unfold goodTerm, certiClasses.translate, certiL3_to_L3_eta, goodTerm, WfL2Term, WfL3_etaTerm.
  - destruct s; simpl in *.
    intros H. apply trans_pres_Crct in H.
    rewrite timePhase_id.
    now apply L3_to_L3_eta_correct.trans_pres_Crct.

  - intros Hcrct Hred.
    exists (L3_to_L3_eta.Program_Program sv). split; auto.
    destruct s as [main e], sv as [main' e'].
    simpl in *. hnf in Hred. destruct Hred as [evenv evmain].
    + hnf. rewrite timePhase_id.
      split; subst; auto.
      apply L3_to_L3_eta_correct.translate_correct_subst; eauto.
      apply L2k.program.Crct_CrctEnv in Hcrct; auto.
      now apply trans_pres_Crct_env.
      now eapply trans_pres_Crct.
      (* apply L2k.program.Crct_CrctEnv in Hcrct. *)
      (* clear evenv main main'. *)
      (* induction e' in Hcrct |- *. *)
      (* ++ constructor. *)
      (* ++ simpl. destruct a. destruct e. *)
      (*    econstructor. apply IHe'; eauto. *)
      (*    apply L3_to_L3_eta_correct.translate_correct_subst; eauto. *)
      (*    now inv Hcrct. *)

      (* constructor. constructor. *)

    + apply obs_prevervation.
Qed.

Definition dummyEnvBigStep {E T: Type}  (bt : BigStepOpSem T T)
: BigStepOpSem (E * T) (E * T) :=
  (fun e v => (fst e) = (fst v) /\ (snd e) ⇓ (snd v)).

Definition dummyEnvWf {E T: Type}  (bt : GoodTerm T)
: GoodTerm (E * T) :=
  (fun e => goodTerm (snd e)).

(* very low priority *)
Existing Instance dummyEnvBigStep | 1000000.
(* very low priority *)
Existing Instance dummyEnvWf | 1000000.

Let L4Term := prod ienv  L4.expression.exp.

Instance certiL4eval: BigStepOpSem L4.expression.exp L4.expression.exp := eval.
Global Instance L4_evaln : BigStepOpSemExec (ienv * L4.expression.exp)
                                            (ienv * L4.expression.exp) :=
  fun n p => match  (eval_n n (snd p)) with
             | Some v => Result (fst p,v)
             | None => Error "None" None
                           end.


Instance certiL4wf: GoodTerm L4.expression.exp :=
 L4.expression.exp_wf (0%N).

Definition question_head (Q : Question) (ie : ienv) (e : L4.expression.exp) :=
  match Q with
  | Abs => match e with
            Lam_e _ _ => true
          | _ => false
          end
  | Cnstr i n =>
    match e with
    | Con_e (i', n') args =>
      if eq_dec i i' then N.eqb (N.of_nat n) n' else false
    | _ => false
    end
  end.

Global Instance QuestionHeadTermL4 : QuestionHead (ienv * L4.expression.exp) :=
  fun q t => question_head q (fst t) (snd t).

(* Move to expression.v *)
Fixpoint exps_nthopt (n:nat) (xs:exps): option exp :=
  match n, xs with 
    | 0%nat, expression.econs h _ => Some h
    | S n, expression.econs _ t => exps_nthopt n t
    | _, _ => None
  end.


Definition observe_nth_subterm n (e : exp) :=
  match e with
  | Con_e _ args => exps_nthopt n args
  | _ => None
  end.

Global Instance ObsSubtermTermL4 : ObserveNthSubterm (ienv * L4.expression.exp) :=
  fun n t => match observe_nth_subterm n (snd t) with
          | None => None
          | Some e => Some (fst t, e)
          end.

Global Instance certiL4: CerticoqLanguage (ienv * L4.expression.exp) := {}.

Global  Instance certiL3_eta_to_L4: 
  CerticoqTranslation (cTerm certiL3_eta) (cTerm certiL4)  :=
  fun o p =>
    (AstCommon.timePhase "L3 to L4")  (fun (_:Datatypes.unit) => (Ret (L4.L3_to_L4.inductive_env (AstCommon.env p),
                                                                    (L3_to_L4.translate_program (AstCommon.env p) (main p))))).

Require Import L4.L3_to_L4_correct.

Lemma same_args_same_obs n t e t' :
  same_args same_obs t e = true -> L2k.term.tnth n t = Some t' ->
  exists e', exps_nthopt n e = Some e' /\ same_obs t' e' = true.
Proof.
  clear.
  revert t e t'; induction n; intros *; simpl.
  destruct t; simpl; intros; try destruct e; try discriminate.
  injection H0. intros ->. exists e. now apply andb_prop in H as [Ht' Ha].

  intros Ha Ht. destruct t; destruct e; try discriminate.
  simpl in Ha. apply andb_prop in Ha as [Hte Ht0].
  eapply IHn; eauto.
Qed.

Global Instance certiL3_eta_to_L4_correct :
  CerticoqTranslationCorrect certiL3_eta certiL4.
Proof.
  split.
{ red; unfold certiClasses.translate, goodTerm, WfL3_etaTerm.
  intros.
  pose proof (proj1 Crct_CrctEnv _ _ _ H).
  unfold certiL3_eta_to_L4. hnf.
  simpl. destruct s. simpl in *.
  unfold L3_to_L4.translate_program. simpl.
  unfold translate. simpl.
  rewrite timePhase_id.
  now apply exp_wf_lets. }

{ red; unfold certiClasses.translate, goodTerm, WfL3_etaTerm. intros.
  assert(He:=proj1 Crct_CrctEnv _ _ _ H).
  repeat red in H0.
  destruct s. destruct sv.
  destruct H0; subst env0.
  pose proof (L3_to_L4_correct.translate_correct' env env _ main0 He H).
  simpl in H1. unfold certiL3_eta_to_L4.
  forward H1. (* TODO: need WcbvEval_env env env' assumption *)
  specialize (H1 H0).
  destruct H1 as [sv' [evsv obs]].
  eexists (inductive_env env, sv').
  rewrite timePhase_id.
    split. repeat red. split. simpl; auto. simpl.
  { apply evsv. }
  clear evsv He H0 H. revert main0 sv' obs. clear.
  apply (TrmTrmsBrsDefs_ind
             (fun (main : Term) => forall (sv' : exp),
                  same_obs main sv' = true ->
                  {| main := main; AstCommon.env := env |} ⊑ (inductive_env env, sv'))
             (fun ts => forall d i n n0 es, same_args same_obs ts es = true ->
                 obsLeOp (observeNthSubterm n0 {| main := TConstruct i n ts; AstCommon.env := env |})
                         (observeNthSubterm n0 (inductive_env env, Con_e d es)))
             (fun _ => True) (fun _ => True));
        try constructor;
        try (match goal with |- yesPreserved _ _ => intros q; destruct q end);
        intros; try red; trivial; try constructor.
  rename H0 into obs.
  simpl in *; unfold questionHead. simpl.
  destruct sv'; trivial; intros; simpl in *; try discriminate.
  apply andb_prop in obs. destruct d; simpl in *.
  destruct obs. apply andb_prop in H0. destruct H0.
  unfold eq_decb in *. repeat destruct eq_dec; destruct inductive_dec; simpl; subst; auto;
  unfold DecidableClass.Decidable_witness. simpl.
  destruct (UsefulTypes.deceq i1 i1); simpl; trivial.
  destruct Decidable_witness. simpl.
  destruct (PeanoNat.Nat.eqb_spec n0 (N.to_nat n1)); subst. simpl. subst.
  rewrite Nnat.N2Nat.id. apply N.eqb_refl. auto. auto.
  destruct (UsefulTypes.deceq i0 i1); simpl; trivial.
  destruct Decidable_witness. simpl.
  destruct (PeanoNat.Nat.eqb_spec n0 (N.to_nat n1)); subst. simpl. subst.
  intuition auto. auto. auto.

  destruct sv'; try discriminate. apply H. simpl in H0.
  apply andb_prop in H0. destruct d; simpl in *.
  destruct H0. apply andb_prop in H0. destruct H0. apply H1.

  destruct es; simpl in H1; try discriminate.
  apply andb_prop in H1 as [Ht Ht0].
  destruct n0; simpl.
  constructor. apply (H _ Ht).

  specialize (H0 d i n n0 es Ht0).
  unfold observeNthSubterm in *.
  unfold observe_nth_subterm in *. simpl in H0. apply H0.
Admitted.

Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_2_to_L4_5.
Require Import DecidableClass.

Global Instance L4_2_eval : BigStepOpSem L4_2_Term L4_2_Term := fun t v =>
exists n, eval42 n t = Some v.

Require Import Common.TermAbs.

Global Instance L4_2_evaln
  : BigStepOpSemExec (ienv * L4_2_Term) (ienv * L4_2_Term) :=
  fun n e => match (@polyEval.eval_n (Named.TermAbsImpl variables.NVar polyEval.L4Opid) n (snd e)) with
          | None => Error "None" None
          | Some v => Result (fst e, v)
          end.

Require Import L4_to_L4_2_correct.
Global Instance : GoodTerm L4_2_Term :=
  fun e  => isprogram e
            /\ L42.fixwf e = true
            /\ varsOfClass (all_vars e) true.

Global Instance QuestionHeadTermL42 : QuestionHead (prod ienv L4_2_Term) :=
fun q t =>
match q, getOpid (snd t) with
| Cnstr ind ci, Some (polyEval.NDCon dc _) =>
  let (ind2, ci2) := dc in
  (if inductive_dec ind ind2 then N.of_nat ci =? ci2 else false)
| Abs, Some polyEval.NLambda => true
| _, _ => false
end.



Global Instance ObsSubtermTermL42 : ObserveNthSubterm (prod ienv L4_2_Term) :=
  fun n t =>
    let (env, t) := t in
    match t with
    | oterm (polyEval.NDCon dc _) lbt =>
      List.nth_error  (List.map (fun b => (env, get_nt b)) lbt) n
    | _ => None
    end.

Global Instance certiL4_2: CerticoqLanguage (prod ienv L4_2_Term) := {}.

Global Instance certiL4_to_L4_2: 
  CerticoqTotalTranslation (cTerm certiL4) (cTerm certiL4_2) :=
  fun o p => (AstCommon.timePhase "L4 to L4_2") (fun (_:Datatypes.unit) =>(fst p, (tL4_to_L4_2 (snd p)))).


Global Program Instance : BigStepOpSem L4_5_Term L4_5_Term := eval.

(** all variables must be user variables *)
Global Program Instance : GoodTerm L4_5_Term :=
  fun e  => varsOfClass (all_vars e) true /\ isprogram e /\  L4_5_to_L5.fixwf e = true.

Require Import DecidableClass.
Global Instance QuestionHeadTermL45 : QuestionHead (prod ienv L4_5_Term) :=
fun q t =>
match q, snd t with
| Cnstr ind ci, oterm (NDCon dc _) _ =>
  let (ind2, ci2) := dc in
  (if inductive_dec ind ind2 then N.of_nat ci =? ci2 else false)
| Abs, oterm NLambda _ => true
| _, _ => false
end.

Global Instance ObsSubtermTermL45 : ObserveNthSubterm (prod ienv L4_5_Term) :=
  fun n t =>
    let (env, t) := t in
    match t with
    | oterm (NDCon dc _) lbt =>
      List.nth_error  (List.map (fun b => (env, get_nt b)) lbt) n
    | _ => None
    end.

Global Instance certiL4_5: CerticoqLanguage (prod ienv L4_5_Term) := {}.


Global Instance certiL4_2_to_L4_5: 
  CerticoqTotalTranslation (cTerm certiL4_2) (cTerm certiL4_5) :=
  fun o p => (AstCommon.timePhase "L4_2 to L_5") (fun (_:Datatypes.unit) => (fst p, (L4_2_to_L4_5  (snd p)))).


Require Import L4.variables.

Definition L5Term :Type := (@NTerm NVar L5Opid).

Global Instance L4_5_evaln
  : BigStepOpSemExec (ienv * L4_5_Term) (ienv * L4_5_Term) :=
  fun n e => match (@L4_2_to_L4_5.eval_n (Named.TermAbsImpl variables.NVar L4_5Opid) n (snd e)) with
          | None => Error "None" None
          | Some v => Result (fst e, v)
          end.

Global Program Instance : BigStepOpSem L5Term L5Term := eval_c.

(* may need to strengthened: consider adding the predicated nt_wf and fixwf.
It seems that there is currently there is no proof that cps_cvt nt_wf.
A more direct alternative to nt_wf could be the predicate that says that the conversion from
L5 to L5a succeeds.  *)
Global Program Instance : GoodTerm L5Term := closed (*isprogram *).

Global Instance L5_evaln
  : BigStepOpSemExec (ienv * L5Term) (ienv * L5Term) :=
  fun n e => match (@L4_5_to_L5.eval_n (Named.TermAbsImpl variables.NVar L5Opid) n (snd e)) with
          | Result v => Result (fst e, v)
          | Error s t => Error s (option_map (fun p => (fst e, p)) t)
          | OutOfTime t => OutOfTime (fst e, t)
          end.

Global Instance QuestionHeadTermL5 : QuestionHead (ienv * L5Term) :=
fun q t =>
match q, snd t with
| Cnstr ind ci, oterm (CDCon dc _) _ =>
  let (ind2, ci2) := dc in
  (if inductive_dec ind ind2 then N.of_nat ci =? ci2 else false)
| Abs, oterm CLambda _ => true
| _, _ => false
end.

Global Instance ObsSubtermTermL5 : ObserveNthSubterm (ienv * L5Term) :=
  fun n t =>
    let (env, t) := t in
    match t with
    | oterm (CDCon dc _) lbt =>
      List.nth_error  (List.map (fun b => (env, get_nt b)) lbt) n
    | _ => None
    end.

Global Instance certiL5: CerticoqLanguage (ienv * L5Term) := {}.


Lemma haltContAp (t: L5Term):  eval_c (ContApp_c haltCont t) t.
Proof.
  unfold haltCont.
  rewrite eval_ret.
  simpl. unfold subst. simpl.
  apply eval_Halt_c.
Qed.

Global Instance certiL4_5_to_L5:
  CerticoqTotalTranslation (cTerm certiL4_5) (cTerm certiL5):=
  (fun o x => (AstCommon.timePhase "L4_5 to L5") (fun (_:Datatypes.unit) => (fst x, ContApp_c (cps_cvt (snd x)) haltCont))).

Definition oldTranslation : (cTerm certiL4_5) -> (cTerm certiL5):=
  (fun x => (fst x, (cps_cvt (snd x)))).

Require Import SquiggleEq.tactics.
Require Import ExtLib.Data.ListNth.

(* Move to L4_5_to_L5 *)
Hint Unfold isprogram : eval.
Hint Resolve @eval_yields_value' @eval_preseves_varclass 
  @eval_preseves_wf @eval_preserves_closed conj
  @cps_cvt_val_closed @cps_cvt_closed @eval_preserves_fixwf @eval_end
  @eval_preserves_closed : eval.

Require Import L4.variables.
Require Import L4.varInterface.


  Hint Unfold certiClasses.translate liftTotal bigStepEval certiClasses.bigStepEval
       liftBigStepException translateT certiL4_5_to_L5  bigStepEval dummyEnvBigStep
       yesPreserved questionHead QuestionHeadTermL45 QuestionHeadTermL5
       BigStepOpSem_instance_1  BigStepOpSem_instance_0
       goodTerm dummyEnvWf goodTerm GoodTerm_instance_0
       GoodTerm_instance_1 ObsSubtermTermL4 ObsSubtermTermL42 QuestionHeadTermL42
       observeNthSubterm : certiclasses.

  Require Import Morphisms.

(* all variants of the correctness property need this part *)
Lemma goodPres45 : goodPreserving (ienv * L4_5_Term) (ienv * L5Term).
Proof using.
  simpl. red. intros s o Hgood.
  unfold certiClasses.translate, liftTotal, bigStepEval,
  liftBigStepException, translateT, certiL4_5_to_L5.
  rewrite timePhase_id.
  simpl.
  simpl. hnf. simpl.
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_1, isprogram, closed in Hgood.
  destruct s as [? s]; simpl in *. repnd.
  hnf. simpl. symmetry.  rewrite cps_cvt_aux_fvars; auto. rewrite Hgood2. refl.
Qed.

Global Instance IsValueL45 : IsValue (cTerm certiL4_5) :=
  fun t => L4_5_to_L5.is_value (snd t).
Require Import Btauto.

  Require Import SquiggleEq.list.
  Require Import List.


(* Move to L4_to_L4_2_correct.v *)
Lemma  exps_nthopt_translate n es:
option_map tL4_to_L4_1 (exps_nthopt n es) = nth_error (ltL4_to_L4_1 es) n.
Proof using.
 revert es.
 induction n; simpl; destruct es as [ | he es]; simpl; eauto.
Qed.

Lemma  exps_nthopt_isval: forall (es : exps) (n : nat) (e : exp),
    are_values es -> Some e = exps_nthopt n es -> expression.is_value e.
Proof using.
  induction es; intros ? ? Hav Heq; destruct n; invertsn Heq; invertsn Hav; eauto.
Qed.

Require Import L4.L4_to_L4_2_correct.

Lemma alpha_EqObs_L4_2 senv :
 forall a (b: L4_2_Term), expression.is_value  a-> alpha_eq (tL4_to_L4_2 a) b -> (senv, (tL4_to_L4_2 a)) ⊑ (senv, b).
Proof using.
  intros ? ? Hisv Hal.
  apply toCoInd. (* productivity check is too unreliable *)
  intros ?.
  revert dependent a.
  revert dependent b.
  induction m; [ constructor | ].
  intros ? ? Hisv Hal. constructor.
- unfold yesPreserved.
  intros q.
  autounfold with certiclasses.
  simpl. destruct q;
  rewrite Hal; unfold implb; btauto.
- autounfold with certiclasses.
  intros ?.
  invertsn Hal; [ constructor | ].
  invertsn  Hisv; invertsn H0; try constructor.
  repeat rewrite list.map_map in *. unfold Basics.compose in *.
  simpl in *. do 2 rewrite list.nth_error_map.
  autorewrite with list in H2.
  autorewrite with list in Hal.
  specialize (H2 n).
  remember  (List.nth_error (ltL4_to_L4_1 es) n) as tl.
  symmetry in Heqtl.
  unfold selectbt in H2.
  pose proof Heqtl as Hl.
  destruct tl as [tl | ]; try constructor.
  apply nth_error_length_lt in Hl.
  set (def:=(termsDB.oterm polyEval.NApply []): L4_1_Term).
  rewrite map_nth2 with (d:=def)in H2 by assumption.
  specialize (H2 Hl).
  pose proof Hl as Hnth.
  apply nth_select1 with (def0:= def)  in Hnth.
  setoid_rewrite Heqtl in Hnth.
  invertsn Hnth.  
  pose proof (exps_nthopt_translate n es) as He.
  remember (exps_nthopt n es) as e.
  setoid_rewrite Heqtl in He.
  destruct e as [e | ];invertsn He. 
  clear Heqtl.
  rewrite <- He in H2.
  rewrite Hal in Hl.
  set (def2 := bterm [] ((vterm nvarx):L4_2_Term)).
  apply nth_select1 with (def0:=def2) in Hl.
  setoid_rewrite Hl.
  fold def2 in H2.
  remember ((nth n lbt2 def2)) as tr.
  clear Heqtr. clear Hl.
  constructor.
  rename H2 into Halb.
  apply alphaeqbt_nilv in Halb.
  exrepnd. subst. simpl.
  apply IHm; [ | assumption].
  revert Heqe. revert Hisv. clear.
  apply exps_nthopt_isval.
Qed.
    

Require Import Basics.
(*Move to the top *)
Global Instance isValL4: IsValue (cTerm certiL4) := (expression.is_value ∘ snd).

Lemma obsNthCommuteL4_L4_2:  valuePredTranslateObserveNthCommute (ienv * exp) (cTerm certiL4_2).
Proof using.
  intros o ? ? ? Hisv.
  destruct sv as [senv v]. 
  hnf in Hisv.
  simpl in *.
  intros Hev.
  invertsn Hev.
  autounfold with certiclasses.
  simpl. unfold certiL4_to_L4_2. 
  rewrite timePhase_id.
  invertsn Hisv; simpl; try auto.
  revert n.
  induction Hisv.
  + destruct n; simpl; auto.
  + destruct n; simpl; auto.
    unfold translateT. rewrite timePhase_id. auto.
Qed.    
  
Lemma yesCommuteL4_L4_2:  valuePredTranslateYesPreserved (ienv * exp) (cTerm certiL4_2).
Proof using.
  intros o ? ? Hisv.
  destruct sv as [senv v].
  hnf in Hisv.
  simpl in *.
  intros Hev.
  invertsn Hev.
  autounfold with certiclasses. unfold certiL4_to_L4_2. rewrite timePhase_id.
  simpl. intros q.
  invertsn Hisv; simpl; destruct q as [qi qn| ]; try auto.
  destruct d. simpl.
  autounfold with certiclasses.
  simpl. unfold implb.
  btauto.
Qed.



Global Instance certiL4_to_L4_2Correct:
  CerticoqTranslationCorrect certiL4 certiL4_2.
Proof using.
  split.
  - intros ? o Hg.
    hnf. 
    unfold translateT; unfold certiL4_to_L4_2; rewrite timePhase_id.    
    destruct s as [? s]. simpl.
    hnf in Hg. simpl in Hg.
  clear i.
  unfold isprogram.
  dands; eauto using ntwfL4_to_L42, fixwfL4_to_L42, closedL4_to_L42,vcL4_to_L42. 
- intros s ? ? Hg Hev.
  destruct s as [? s].
  destruct sv as [senv sv]. 
  hnf in Hev. simpl in Hev.
  repnd. subst.
  hnf in Hev.
  pose proof Hev as Hvl.
  apply expression.eval_yields_value' in Hvl.
  apply eval_evalns in Hev.
  exrepnd. hnf in Hg. simpl in Hg.
  eapply L4_to_L4_2_corr in Hev0; eauto.
  exrepnd. simpl in vt.
  fold L4_2_Term in vt.
  rename vt into v2t.
  exists (s1, v2t).
  simpl.
  dands.
  + hnf.
    simpl.
    unfold translateT; unfold certiL4_to_L4_2; rewrite timePhase_id.    
   dands; try refl;[].
   hnf. eexists; eauto.
  + symmetry in Hev1.
    apply alpha_EqObs_L4_2 with (senv:=s1) in Hev1; auto;[].
    eapply @obsLeTrns with (InterValue := cTerm certiL4_2);[ | apply Hev1].
    (* eapply (fun p1 p2 a b v eq => valuePredTranslateLe_suff _ _ p1 p2 a b v eq); auto;[ | ]; clear; *)
    (*   [apply obsNthCommuteL4_L4_2 | apply yesCommuteL4_L4_2]. *)

    (* Grab Existential Variables. *)
    (* exact (Flag 0).  *)
(* Qed. *)
Admitted.


Section DemoDelete.
  Definition composeDemo:
    CerticoqTranslationCorrect certiL3_eta certiL4_2.
  Proof using.
    eauto with typeclass_instances.
  Qed.
End DemoDelete.
(*
Print Assumptions certiL4_to_L4_2Correct.

ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
eval_ns_monotone : forall (n : nat) (e f : exp),
                   eval_ns n e = Some f ->
                   forall m : nat, eval_ns (n + m) e = Some f
EqIfRL4Opid : TermAbs_parametricity.EqIfR L4_to_L4_2_correct.L4Opid_R
*)

Lemma goodPres4_2_to_4_5 : goodPreserving (ienv * L4_2_Term) (ienv * L4_5_Term).
Proof using.
  - intros ? o Hg. hnf.
    unfold translateT; unfold L4_2_to_L4_5; unfold certiL4_2_to_L4_5; rewrite timePhase_id.    
  destruct s as [? s]. simpl.
  hnf in Hg. simpl in Hg.
  unfold isprogram, closed in *. repnd.
  dands; try rewrite L4_2_to_L4_5_fvars;
    eauto using L4_2_to_L4_5_ntwf, fixwf_commute, L4_2_to_L4_5_vc.
Qed.

Lemma certiL4_2_to_L4_5_evalPres:
  bigStepPreserving (cTerm certiL4_2) (cTerm certiL4_5).
Proof using.
  intros ? ? ?.
  destruct s as [? s].
  destruct sv as [senv sv]. 
  autounfold with certiclasses. simpl.
  autounfold with certiclasses. simpl.
  intros Hgood Heval. repnd. subst.
  simpl in *. repnd. destruct Hgood1 as [Hclosed Hwf].
   unfold L4_2_to_L4_5; unfold certiL4_2_to_L4_5; rewrite timePhase_id. rewrite timePhase_id.    
  dands; auto.
  pose proof L4_2_to_L4_5_correct.
  hnf in Heval. exrepnd.
  
  eapply H; eauto.
Qed.
  
Require Import SquiggleEq.LibTactics.

Global Instance IsValueL42 : IsValue (cTerm certiL4_2) :=
  fun t => True. (* suffices for our purposes so far. we only need completeness of IsValue in the proof below (certiL4_2_to_L4_5_Correct)*)


Global Instance certiL4_2_to_L4_5_Correct:
  CerticoqTranslationCorrect certiL4_2 certiL4_5.
Proof using.
  apply certicoqTranslationCorrect_suff3; try firstorder auto.
  - apply certiL4_2_to_L4_5_evalPres.
  - apply goodPres4_2_to_4_5.
  - intros o ? ? Hsv Heq. clear Hsv. inverts Heq.
      destruct sv as [? ev]. hnf.
      autounfold with certiclasses in *. simpl.
      destruct ev as [ | o2 lbt]; simpl; intros q; destruct q; auto;[ | ].
    +  destruct o2; auto;[].
       destruct dc.
       unfold certiL4_2_to_L4_5; unfold L4_2_to_L4_5; rewrite timePhase_id.
       simpl. unfold implb.
       
       btauto.
    + unfold certiL4_2_to_L4_5; unfold L4_2_to_L4_5; rewrite timePhase_id.

      destruct o2; auto.
  - intros o ? ? ? Hsv Heq. inverts Heq.
    destruct sv as [? ev]. hnf.
    autounfold with certiclasses. clear Hsv.
    unfold certiL4_2_to_L4_5; unfold L4_2_to_L4_5; rewrite timePhase_id. simpl.
    destruct ev as [ | o2 lbt]; auto;[].
    destruct o2; auto; [].
    simpl.
    repeat rewrite List.map_map.
    repeat rewrite nth_error_map.
    remember (List.nth_error lbt n) as esso.
    destruct esso as [ess | ]; simpl; auto;[].
    simpl. split; hnf; auto.
    do 2 f_equal.
    destruct ess; auto.
Admitted.    
(* Qed. *)

(*
Print Assumptions certiL4_2_to_L4_5_Correct.
Closed under the global context
 *)

(* this proof, which was developed later, uses lemmas in the certiclasses library *)
Module SimplerProof.

Let certiL4_5_to_L5Val:
  CerticoqTranslation (cTerm certiL4_5) (cTerm certiL5):=
  @liftTotal _ _ (fun o x => (fst x, (cps_cvt_val (snd x)))).

  Lemma certiL4_5_to_L5Correct_evalPres:
    @bigStepPreserving (cTerm certiL4_5) (cTerm certiL5) _ _ _ (certiL4_5_to_L5Val) _ _ _ .
  Proof using.
    intros ? ? ?.
    destruct s as [? s].
    destruct sv as [senv sv]. 
    autounfold with certiclasses. simpl.
    autounfold with certiclasses. simpl.
    intros Hgood Heval.
    rewrite timePhase_id.
    repnd. subst.
    simpl in *. repnd. destruct Hgood1 as [Hclosed Hwf].
    rename Hgood0 into Hvc. rename Hgood into Hfixwf.
    dands;[auto | ].
    pose proof
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
  Qed.


  Lemma certiL4_5_to_L5Correct:
    CerticoqTranslationCorrect certiL4_5 certiL5.
  Proof.
    eapply (@certicoqTranslationCorrect_suff3
             _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ certiL4_5_to_L5Val).
    - apply certiL4_5_to_L5Correct_evalPres.
    - apply goodPres45.
    - intros ? ? ? Hsv Heq. inverts Heq.
      destruct sv as [? ev]. hnf.
      autounfold with certiclasses in *.
      inverts Hsv; simpl in *; subst.
      + intros q.  destruct q; constructor.
      + intros q.  destruct q; constructor.
      + intros q.  destruct q; try auto;[]; simpl.
        unfold implb; btauto.
      + intros q.  destruct q; constructor.
    - intros ? ? ? ? Hsv Heq. inverts Heq.
      destruct sv as [? ev]. hnf.
      autounfold with certiclasses.
      inverts Hsv; simpl in *; subst; simpl; [ | | | ]; try auto; [].
      simpl.
      repeat rewrite List.map_map.
      repeat rewrite nth_error_map.
      remember (List.nth_error es n) as esso.
      destruct esso as [ess | ]; simpl; auto;[].
      simpl. split; auto.
      symmetry in Heqesso.
      apply List.nth_error_In in Heqesso.
      apply H. simpl. assumption.
    - intros ? ? ?. destruct t, v. simpl in *.
      eapply eval_yields_value'. apply H.
   Qed.
End SimplerProof.

SearchAbout isprogram (bterm []).
Ltac isprogd :=
unfold apply_bterm in *;
unfold subst in *;
(repeat match goal with
| [ H: isprogram (vterm _) |- _ ] => apply proj2 in H; inverts H
| [ H: isprogram _ |- _ ] => apply isprogram_ot_iff in H; simpl in H; repnd; dLin_hyp
| [ H: isprogram_bt (bterm [] _) |- _ ] => apply isprogram_bt_nobnd in H
end
).
Ltac isclosedD :=
unfold apply_bterm in *;
unfold subst in *;
(repeat match goal with
| [ H: closed (vterm _) |- _ ] => apply proj2 in H; inverts H
| [ H: closed _ |- _ ] => setoid_rewrite closed_nt in H; simpl in H; repnd; dLin_hyp
end
).

(*
Global Instance pp1: Proper (zetaCEquiv ==> eq ==>  zetaCEquiv ==> zetaCEquiv) subst.
intros ? ? ? ? ? ? ? ?. subst.
apply properSubstZ.
auto.
Qed. *)

(* Move to L4_5_to_L5 *)
Lemma eval_preserves_isprog :
  forall (e v : L4_5_Term),  eval e v ->  isprogram e -> isprogram v.
Proof using.
  unfold isprogram. split.  repnd. eauto with eval.

  (* Move to L4_5_to_L5 *)
Lemma eval_preserves_isprog :
  forall (e v : L4_5_Term),  eval e v ->  isprogram e -> isprogram v.
Proof using.
  unfold isprogram. split.  repnd. eauto with eval.
Abort.

Global Instance evalPreservesGood :
  Proper (eval ==> Basics.impl) (@goodTerm L4_5_Term _).
Proof using.
  intros e v Hev Hg.
  hnf. autounfold with certiclasses eval in *. repnd.
  dands; eauto with eval typeclass_instances.
Qed.

Module OldProof.
  (* this proof is by induction, but the above proof uses the lemma
     certiClasses2.certicoqTranslationCorrect_suff3, where the corresponding part
     is provem by coinduction (not induction) *)
Lemma valueObsEq (senv: ienv) : forall (sv:L4_5_Term), is_value sv ->
                                                  (senv, sv) ⊑ (senv, cps_cvt_val sv).
Proof using.
  intros ? Hisv.
  induction Hisv; simpl. (* this is proof by induction, not coinduction *)
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor.
  + unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    destruct q; auto. unfold implb. btauto.
  + clear H. rename H0 into Hind. intros ?. cbn.
    repeat rewrite List.map_map.
    repeat rewrite nth_error_map.
    remember (List.nth_error es n) as esso.
    destruct esso as [ess | ]; try constructor.
    simpl. apply Hind.
    eapply List.nth_error_In.
    symmetry. eassumption.
- constructor; compute; intros qn; [ destruct qn | ]; try constructor.
Qed.
                                                  

Global Instance certiL4_5_to_L5Correct: CerticoqTranslationCorrect certiL4_5 certiL5.
(* Again, proof by induction *)
Proof.
  constructor.
- exact goodPres45.
- red. intros ? ? ? Hgood Heval.
  destruct Heval as [Heq Heval].
  destruct s as [senv s].
  destruct sv as [? sv]. symmetry in Heq.
  simpl in *. subst.
  exists (senv, (cps_cvt_val sv)).
  unfold certiClasses.translate, liftTotal, bigStepEval,
  liftBigStepException, translateT, certiL4_5_to_L5. simpl.
  repeat progress (unfold bigStepEval, dummyEnvBigStep; simpl).
  unfold BigStepOpSem_instance_1. simpl.
  simpl. unfold bigStepEval, dummyEnvBigStep. simpl.
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_1 in Hgood.
  simpl in *. repnd. destruct Hgood1 as [Hclosed Hwf].
  rename Hgood0 into Hvc. rename Hgood into Hfixwf.
  rewrite timePhase_id.
  dands;[reflexivity | | ].
  + pose proof
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
    revert Heval. clear.
    apply valueObsEq.
Qed.
End OldProof.

(* OS 05/19 - We no longer use L5a, going instead from L5 -> L6
Require Import L4.L5a.

(* Fix. Define subst and evaluation on L5a by going to L5 via a bijection? *)
Global Program Instance : BigStepOpSem L4.L5a.cps  L4.L5a.cps :=
  fun _ _ => True.

(** Fix *)
Global Program Instance : GoodTerm L4.L5a.cps := fun x => False.

(* FIX!! *)
Global Instance QuestionHeadTermL5a : QuestionHead (ienv * L4.L5a.cps) :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermTermL5a: ObserveNthSubterm (ienv * L4.L5a.cps) :=
fun n t => None.

Global Instance certiL5a: CerticoqLanguage (ienv * L4.L5a.cps) := {}.

Global Instance certiL5_to_L5a: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL5a)  :=
  fun e =>
   match L4.L5a.translateCPS (snd e) with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e5a => exceptionMonad.Ret (fst e, e5a)
  end.

Definition certiL5_to_L5aOld : 
  CerticoqTranslation (cTerm certiL5) (ienv * L4.L5a.val_c)  :=
  fun e =>
   match L4.L5a.translateVal (snd e) with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e5a => exceptionMonad.Ret (fst e, e5a)
  end.


Require Import L1g.instances.
Require Import Program.

Definition ctranslateEvalL5a `{F:utils.Fuel}
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm certiL5)}
   (p: Template.Ast.program) (n:nat) : bigStepResult (option L5a.cps)  (option L5a.val_c) :=
  mapBigStepRes (L5a.translateCPS ∘ snd) (L5a.translateVal ∘ snd) (ctranslateEval certiL5 p n).

*)


(*
Require Import Template.Template.
Open Scope nat_scope.
Quote Recursively Definition p0L1 := (fun vl vr:nat => vl + vr). 

Require Import L2.instances.

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)
Open Scope string_scope.


Fixpoint even (n:nat) : bool :=
  match n with
    | O => true
    | (S n') => odd n'
  end
with odd n : bool :=
  match n with
    | O => false
    | (S n') => even n'
  end.

Require Import String.
Require Import List.
Import ListNotations.


Definition print4 (t: cTerm certiL4_5) : string :=
(tprint "" NVar2string  L4_5_to_L5.L4_5OpidString  (snd t)).

Definition print5 (t: cTerm certiL5) : string :=
(tprint "" NVar2string  L4_5_to_L5.L5OpidString  (snd t)).
 *)


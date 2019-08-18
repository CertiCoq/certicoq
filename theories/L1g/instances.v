Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.
Require Import Common.classes.
Require Import certiClasses2.

Instance bigStepOpSemL1gTerm: BigStepOpSem (Program Term) (Program Term).
Proof.
  intros s sv. destruct s, sv. exact (WcbvEval env main main0 /\ env = env0).
Defined.

(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL1gTerm: GoodTerm (Program L1g.compile.Term) :=
  fun P:Program Term =>
    match P with
      mkPgm trm env => WFapp trm /\ WFaEnv env
    end.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Lemma nth_pres_WFapp:
  forall (us:list Term),
    WFapps us -> forall n t, List.nth_error us n = Some t -> WFapp t.
Proof.
  induction 1; destruct n; intros.
  - discriminate.
  - cbn in H. discriminate.
  - cbn in H1. myInjection H1. assumption.
  - cbn in H1. eapply IHWFapps. eassumption.
Qed.

Function flattenApp (t:Term): (Term * (list Term)) :=
  match t with
    | TApp fn arg =>
      let '(fn, args) := flattenApp fn in
      (fn, args ++ [arg])
    | s => (s, nil)
  end.

Lemma args_pres_WFapp:
  forall (t:Term), L1g.term.WFapp t ->
       WFapp (fst (flattenApp t)) /\ WFapps (snd (flattenApp t)).
Proof.
  induction 1; cbn; intros; repeat econstructor; try assumption.
  - destruct (flattenApp fn). intuition.
  - destruct (flattenApp fn); simpl in *.
    apply append_pres_WFapps; intuition.
Qed.

Global Instance QuestionHeadL1gTerm: QuestionHead (Program L1g.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _ _ =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL1gTerm:
  ObserveNthSubterm (Program L1g.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ _, subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Instance certiL1g: CerticoqLanguage (Program L1g.compile.Term):= {}.

Local Generalizable Variable Lj.

Definition translateTo `{CerticoqTranslation (Program L1g.compile.Term) Lj}
  (p:Template.Ast.program): exception Lj :=
  let l1g:= L1g.compile.program_Program p in
  translate (Program L1g.compile.Term) Lj l1g.

Arguments translateTo Lj {H} p.

Require Import certiClasses.

Definition ctranslateTo {Term Value BigStep WF QH ObsS }
  (Lj: @CerticoqLanguage Term Value BigStep WF QH ObsS)
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm Lj)}
  : Template.Ast.program -> exception (cTerm Lj) :=
  translateTo (cTerm Lj).

Arguments ctranslateTo {Term0} {Value} {BigStep} {WF} {QH} {ObsS} Lj {H} p.

Definition ctranslateEval {Term Value BigStep WF QH ObsS }
  (Lj: @CerticoqLanguage Term Value BigStep WF QH ObsS)
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm Lj)}
   `{BigStepOpSemExec (cTerm Lj) (cValue Lj)}
  (p: Template.Ast.program) (n:nat) : bigStepResult (cTerm Lj) (cValue Lj) :=
  match translateTo (cTerm Lj) p with
  | Ret e => bigStepEvaln n e
  | Exc s => Error s None 
  end.

Arguments ctranslateEval {Term0} {Value} {BigStep} {WF} {QH} {ObsS} Lj {H} {H0} p n.

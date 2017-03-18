Require Import L1g.compile.
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
  fun _  => True.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L1g.compile.Term):
  (L1g.compile.Term * (list L1g.compile.Term)) :=
  match t with
    | TApp fn arg args => (fn, cons arg (Terms_list args))
    | s => (s, nil)
  end.

Global Instance QuestionHeadL1gTerm: QuestionHead (Program L1g.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL1gTerm:
  ObserveNthSubterm (Program L1g.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ , subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Instance certiL1g: CerticoqLanguage (Program L1g.compile.Term):= {}.

Local Generalizable Variable Lj.

Definition translateTo `{CerticoqTranslation (Program L1g.compile.Term) Lj}
  (p:program): exception Lj :=
  let l1g:= L1g.compile.program_Program p in
  translate (Program L1g.compile.Term) Lj l1g.


Arguments translateTo Lj {H} p.

Require Import certiClasses.

Definition ctranslateTo {Term Value BigStep WF QH ObsS } 
  (Lj: @CerticoqLanguage Term Value BigStep WF QH ObsS)
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm Lj)}
  : program -> exception (cTerm Lj) :=
  translateTo (cTerm Lj).

Arguments ctranslateTo {Term0} {Value} {BigStep} {WF} {QH} {ObsS} Lj {H} p.

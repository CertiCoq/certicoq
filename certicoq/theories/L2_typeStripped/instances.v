Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.
Require Import L1g.instances.
Require Import certiClasses2.
Require Import stripEvalCommute.

Instance bigStepOpSemL2Term: BigStepOpSem (Program L2.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL2Term: GoodTerm (Program L2.compile.Term) :=
  fun _  => True.


Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L2.compile.Term) :
  (L2.compile.Term * (list L2.compile.Term)) :=
  match t with
    | TApp fn arg args => (fn, cons arg (Terms_list args))
    | s => (s, nil)
  end.

Global Instance QuestionHeadL2Term: QuestionHead (Program L2.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL2Term :
  ObserveNthSubterm (Program L2.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ , subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Global Instance certiL2Eval: BigStepOpSem (Program L2.compile.Term).
  apply BigStepOpWEnv.
  apply WcbvEval.
Defined.

Global Instance certiL2: CerticoqLanguage (Program L2.compile.Term).

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.


Global Instance certiL1g_to_L2Correct :
  CerticoqTranslationCorrect certiL1g certiL2.
Proof.
  split.
  - intros ? ?. cbn. unfold translateT, certiL1g_to_L2. trivial.
    (* The GoodTerm instance of L1g and L2 may need to be strengthened 
       to complete the next subgoal. Currently, they evaluete to True.
     *)
  - intros ? ?. 
    repeat progress (unfold bigStepEval, bigStepEvalSame,
                     liftBigStepException, bigStepOpSemL1gTerm,
                     translate, translateT, BigStepOpWEnv,
                     liftTotal, certiL2Eval, certiL1g_to_L2).
    cbn. intros. destruct H0.
    exists (stripProgram sv). cbn. repeat split.
    + apply (proj1 (stripEvalCommute.WcbvEval_hom (env s)) _ _ H0).
    + destruct s, sv. cbn in H1. rewrite H1. cbn. reflexivity.
    + admit.
    + intros. unfold observeNthSubterm,
              ObsSubtermL2Term, instances.ObsSubtermL2Term.
      destruct sv. cbn. unfold flattenApp, instances.flattenApp.
      induction main; cbn; try constructor.
      *

Admitted.    

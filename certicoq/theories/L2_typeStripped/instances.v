Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.
Require Import L1g.instances.
Require Import certiClasses2.

Instance bigStepOpSemL2Term : BigStepOpSem (Program L2.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** If the compiler only correctly compiles terms with some properties, add them here. *)
Instance WfL2Term : GoodTerm (Program L2.compile.Term) :=
  fun _  => True.


Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L2.compile.Term) : (L2.compile.Term * (list L2.compile.Term)).
Admitted.

Global Instance QuestionHeadL2Term : QuestionHead (Program L2.compile.Term) :=
fun q t =>
match q, fst (flattenApp (main t)) with
| Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
  andb (decide (ind=ind2)) (decide (ci=ci2))
| Abs, TLambda _ _ => true
| _, _ => false 
end.

Global Instance ObsSubtermL2Term : ObserveNthSubterm (Program L2.compile.Term) :=
fun n t =>
match  (flattenApp (main t)) with
| (TConstruct _ _ _ , subterms) =>
  match List.nth_error subterms  n with
  | Some st => Some {| env := env t; main := st |}
  | None => None
  end
| _ => None
end.

Global Instance certiL2Eval : BigStepOpSem (Program L2.compile.Term).
  apply BigStepOpWEnv.
  apply WcbvEval.
Defined.

Global Instance certiL2 : CerticoqLanguage (Program L2.compile.Term).

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.


Global Instance certiL1g_to_L2Correct :  CerticoqTranslationCorrect certiL1g certiL2.
Proof.
  split.
  - intros ? ?. simpl. unfold translateT, certiL1g_to_L2.
    (* The GoodTerm instance of  L1g and L2 may need to be strengthened to complete the next
      subgoal. Currently, they evaluete to True, which is trivial.
      unfold goodTerm in *. 

     *) admit.
  - intros ? ?. 
    repeat progress (unfold bigStepEval, bigStepEvalSame,
                     liftBigStepException, bigStepOpSemL1gTerm, translate, translateT, BigStepOpWEnv,
                     liftTotal, certiL2Eval, certiL1g_to_L2). simpl.
Admitted.    

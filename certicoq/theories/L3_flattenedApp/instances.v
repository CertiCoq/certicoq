Require Import L3.compile.
Require Import L3.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.

Instance bigStepOpSemL3Term:
  BigStepOpSem (Program Term) (Program Term).
Proof.
  intros s sv. destruct s, sv.
  exact (WcbvEval_env env env0 /\ WcbvEval env main main0).
Defined.

Instance WfL3Term : GoodTerm (Program L3.compile.Term) :=
  fun p  => L3.program.crctTerm (env p) 0 (main p).

Require Import certiClasses2.
(* FIX!! *)

Definition question_head (Q : Question) (p : Program L3.compile.Term) := 
  match Q with
  | Abs => match main p with
            TLambda _ _ => true
          | _ => false
          end
  | Cnstr i n =>
    match main p with
    | TConstruct i' n' args =>
      if eq_dec i i' then if eq_dec n n' then true else false else false
    | _ => false
    end
  end.
(* FIX!! *)

Global Instance QuestionHeadTermL : QuestionHead (Program L3.compile.Term) :=
  question_head.

(* FIX!! *)

Fixpoint tnth (n : nat) (t : Terms) :=
  match t with
  | tnil => None
  | tcons t ts =>
    match n with
    | 0 => Some t
    | S n => tnth n ts
    end
  end.

Definition observe_nth_subterm (n : nat) (p : Program L3.compile.Term) := 
  match main p with
  | TConstruct i' n' args =>
    match tnth n args with
    | None => None
    | Some t => Some {| env := env p; main := t|}
    end
  | _ => None
  end.
    
Global Instance ObsSubtermL : ObserveNthSubterm (Program L3.compile.Term) :=
  observe_nth_subterm.

Instance certiL3 : CerticoqLanguage (Program L3.compile.Term) := {}.

Instance certiL2_to_L3: 
  CerticoqTranslation (Program L2_5.compile.Term) (Program L3.compile.Term) :=
fun x => Ret (L3.compile.stripProgram x).

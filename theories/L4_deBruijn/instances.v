Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L3.compile.
Require Import L4.L3_to_L4.
Require Import L3.instances.

Require Import BinNat.

Definition dummyEnvBigStep {E T: Type}  (bt : BigStepOpSem T)
: BigStepOpSem (E * T) :=
  (fun e v => (fst e) = (fst v) /\ (snd e) ⇓ (snd v)).

Definition dummyEnvWf {E T: Type}  (bt : WellFormed T)
: WellFormed (E * T) :=
  (fun e => wf (snd e)).

(* very low priority *)
Existing Instance dummyEnvBigStep | 1000000.
(* very low priority *)
Existing Instance dummyEnvWf | 1000000.

Let L4Term := prod ienv  L4.expression.exp.

Instance certiL4eval : BigStepOpSem L4.expression.exp := eval.


Instance certiL4wf: WellFormed L4.expression.exp :=
 L4.expression.exp_wf (0%N).


Global Instance certiL4: CerticoqLanguage (ienv * L4.expression.exp) := {}.

Global  Instance certiL3_to_L4: 
  CerticoqTranslation (cTerm certiL3) (cTerm certiL4)  :=
fun p => Ret ( L4.L3_to_L4.inductive_env (AstCommon.env p),
   (L3_to_L4.translate_program (AstCommon.env p) (main p))).

Global  Instance failed: 
  CerticoqTranslationCorrect (Program L3.compile.Term) L4Term.
constructor.
- admit.
- intros ? ? Hwf He.
  destruct Hwf.
  unfold certiClasses.translate,
    certiL3_to_L4, liftBigStepException, bigStepEval.
  unfold translate_program.
(*  Fail eapply L3_to_L4_correct.translate_correct.  *)
(* not applicable!! do we need to change the end to end correctness property?, 
  or can the L3_to_L4 translation syntactically preserve big step eval? *)
Abort.

Require Import L4_to_L4a.
Require Import L4a_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.


Global  Program Instance : BigStepOpSem L4aTerm := eval.

(** all variables must be user variables *)
Global Program Instance : WellFormed L4aTerm :=
  fun e  => varsOfClass (all_vars e) true /\ isprogram e.

Global Instance certiL4a: CerticoqLanguage (prod ienv L4aTerm) := {}.


Global Instance certiL4_to_L4a: 
  CerticoqTotalTranslation (cTerm certiL4) (cTerm certiL4a) :=
  (fun p => (fst p, (L4_to_L4a (0)%N (snd p)))).

Require Import L4.variables.

Definition L5Term :Type := (@NTerm NVar L5Opid).

Global Program Instance : BigStepOpSem L5Term := eval_c.

Global Program Instance : WellFormed L5Term := isprogram.

Global Instance certiL5: CerticoqLanguage (ienv * L5Term) := {}.

Global Instance certiL4a_to_L5:
  CerticoqTotalTranslation (cTerm certiL4a) (cTerm certiL5):=
  (fun x => (fst x,  (cps_cvt (snd x)))).


Require Import L4.L5a.

(* Fix. Define subst and evaluation on L5a by going to L5 via a bijection? *)
Global Program Instance : BigStepOpSem L4.L5a.val_c := fun _ _ => True.

(** Fix *)
Global Program Instance : WellFormed L4.L5a.val_c := fun x => False.

Global Instance certiL5a: CerticoqLanguage (ienv * L4.L5a.val_c) := {}.

Global Instance certiL5_to_L5a: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL5a)  :=
  fun e =>
   match L4.L5a.translateVal (snd e) with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e5a => exceptionMonad.Ret (fst e, e5a)
  end.


Require Import Template.Template.
Quote Recursively Definition p0L1 := 0. 

Require Import L2.instances.

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)
Open Scope string_scope.

Eval vm_compute in (translateTo (cTerm certiL5a) p0L1).
(*
     = Ret
         ([("Coq.Init.Datatypes.nat", 0,
           [{|
            itypNm := "nat";
            itypCnstrs := [{| CnstrNm := "O"; CnstrArity := 0 |},
                          {| CnstrNm := "S"; CnstrArity := 1 |}] |}])],
         Cont_c 5%positive
           (Ret_c (KVar_c 5%positive) (Con_c (mkInd "Coq.Init.Datatypes.nat" 0, 0%N) nil)))
     : exception (cTerm certiL5a)
*)


  










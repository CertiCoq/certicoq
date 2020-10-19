From Coq Require Import ZArith. 
From CertiCoq Require Import L6.toplevel L7.L6_to_Clight L7.L6_to_Clight_stack.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.

(* Identifiers *)
Definition argsIdent:positive := 26.
Definition allocIdent:positive := 28.
Definition nallocIdent:positive := 92.
Definition limitIdent:positive := 29.
Definition gcIdent:positive := 80.
Definition mainIdent:positive := 81.
Definition bodyIdent:positive := 90.
Definition threadInfIdent:positive := 31.
Definition tinfIdent:positive := 91.
Definition heapInfIdent:positive := 95.
Definition numArgsIdent:positive := 97.
Definition isptrIdent:positive := 82.
Definition caseIdent:positive := 83.

Definition stackframeTIdent:positive := 78. (* the stack_frame type *)
Definition frameIdent:positive := 79. (* the stack frame of the current function *)
Definition rootIdent:positive := 84. (* live roots array *)
Definition spIdent:positive := 85. (* stack pointer *)
Definition fpIdent:positive := 86. (* frame pointer *)
(* Fields of stack_frame struct *)
Definition nextFld:positive := 87.
Definition rootFld:positive := 88.
Definition prevFld:positive := 89.


Let Cprogram := (cps_util.name_env * Clight.program * Clight.program)%type.

Definition Clight_trans (args : nat) (t : toplevel.L6_FullTerm) : error Cprogram :=
  let '(_, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  let p := L6_to_Clight.compile
             argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent
             tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
             args prog cenv nenv in
  match p with
  | exceptionMonad.Ret p =>
    Ret (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p))
  | Exc s => Err s
  end.


(* TODO unify with the one above, propagate errors *)
Definition Clight_trans_fast (args : nat) (t : toplevel.L6_FullTerm) : error Cprogram :=
  let '(_, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  let p := L6_to_Clight.compile_fast
             argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent
             tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
             args prog cenv nenv in
  Ret (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p)).


Definition Clight_trans_ANF (args : nat) (t : toplevel.L6_FullTerm) : error Cprogram * string :=
  let '(_, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  L6_to_Clight_stack.compile
    argsIdent allocIdent nallocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent
    tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
    args
    stackframeTIdent frameIdent rootIdent fpIdent nextFld rootIdent prevFld
    false (* args optimization *)
    prog cenv nenv.

Definition compile_Clight : CertiCoqTrans toplevel.L6_FullTerm Cprogram :=
  fun s =>
    debug_msg "Translating from L6 to C" ;;
    opts <- get_options ;;
    let args := c_args opts in
    let cps := negb (direct opts) in
    if cps then 
      LiftErrorLogCertiCoqTrans "L7" (Clight_trans_ANF args) s
    else
      LiftErrorLogCertiCoqTrans "L7" (Clight_trans_ANF args) s.

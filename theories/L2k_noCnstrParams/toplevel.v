Require Import L2k.compile.
Require Import L2k.wcbvEval.
Require Import L2k.term.
Require Import L2k.stripEvalCommute.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import L1g.toplevel.
From ExtLib Require Import Monads.

Import MonadNotation.


Instance L2k_Lang : Lang (Program L2k.compile.Term) :=
  { Value := Term;
    TermWf := fun P => L2k.program.crctTerm (AstCommon.env P) 0 (main P);
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.


Definition compile_L2k
  : CertiCoqTrans (Program L1g.compile.Term) (Program L2k.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiCoqTrans stripProgram src).


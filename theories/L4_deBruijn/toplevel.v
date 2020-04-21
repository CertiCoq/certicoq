Require Import L4.expression.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import L2k.compile.
Require Import L4.L3_to_L4.
Require Import L4.L3_to_L3_eta.
Require Import L4.L3_eta_crct.
Require Import L4.L3_to_L3_eta_correct.
Require Import L4.L3_to_L4_correct.
Require L2k.
Require Import BinNat.
Require Import L4_5_to_L5.
Require Import L4.L4_to_L4_1_to_L4_2 L4.variables.
Require Import L4.L4_2_to_L4_5.

Import Monads.

Import MonadNotation.


Definition L3_eta_Program := Program L2k.compile.Term.
Typeclasses Opaque L3_eta_Program.

Definition compile_L2k_eta
  : CertiCoqTrans (Program L2k.compile.Term) L3_eta_Program:=
  fun src =>
    debug_msg "Translating from L2k to L2k - eta expansion" ;;
    (LiftCertiCoqTrans "L2k_eta" L3_to_L3_eta.Program_Program src).

(* TODO instance for correctness proof *)

Let L4Term := prod ienv L4.expression.exp.

Instance L4_Lang : Lang L4Term :=
  { Value := L4.expression.exp ;
    TermWf := fun P => L4.expression.exp_wf (0%N) (snd P);
    BigStep := fun P Res => exists n, L4.expression.eval_n n (snd P) = Some Res
  }.

Definition compile_L4 : CertiCoqTrans L3_eta_Program L4Term :=
  fun src =>
    debug_msg "Translating from L2k to L4" ;;
    LiftCertiCoqTrans "L4" (fun p =>  
                              (L3_to_L4.inductive_env (AstCommon.env p),
                               L3_to_L4.translate_program (AstCommon.env p)(main p))) src.

Let L4_2_FullTerm := (prod ienv L4_2_Term).

Instance L4_2_Lang : Lang L4_2_FullTerm :=
  { Value := L4_2_Term ;
    TermWf := fun P => terms.isprogram (snd P)
                       /\ L4_to_L4_2_correct.L42.fixwf (snd P) = true
                       /\ varInterface.varsOfClass (terms.all_vars (snd P)) true;
    BigStep := fun P Res => exists n, eval42 n (snd P) = Some Res
  }.

Definition compile_L4_2 : CertiCoqTrans L4Term L4_2_FullTerm :=
  fun src =>
    debug_msg "Translating from L4 to L4_2" ;;
    LiftCertiCoqTrans "L4_2" (fun p => (fst p, tL4_to_L4_2 (snd p))) src.


Definition L4_5_FullTerm := prod ienv L4_5_Term.

Instance L4_5_Lang : Lang L4_5_FullTerm :=
  { Value := L4_5_Term;
    TermWf := fun P => varInterface.varsOfClass (terms.all_vars (snd P)) true /\
                       terms.isprogram (snd P) /\ L4_5_to_L5.fixwf (snd P) = true;
    BigStep := fun P Res => eval (snd P) Res
  }.

Definition compile_L4_5 : CertiCoqTrans L4_2_FullTerm L4_5_FullTerm :=
  fun src =>
    debug_msg "Translating from L4_2 to L4_5" ;;
    LiftCertiCoqTrans "L4_5" (fun p => (fst p, L4_2_to_L4_5 (snd p))) src.

Definition L5_Term := @terms.NTerm NVar L5Opid.
Definition L5_FullTerm := prod ienv L5_Term.


Instance L5_Lang : Lang L5_FullTerm :=
  { Value := L5_Term;
    TermWf := fun P => terms.closed (snd P);
    BigStep := fun P Res => eval_c (snd P) Res
  }.

Definition compile_L5 : CertiCoqTrans L4_5_FullTerm L5_FullTerm :=
  fun src =>
      debug_msg "Translating from L4_5 to L5" ;;
      LiftCertiCoqTrans "L5" (fun p => (fst p, ContApp_c (cps_cvt (snd p)) haltCont)) src.

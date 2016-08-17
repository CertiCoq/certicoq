
Require Import cps.
Require Import cps_util.


Require Import certiClasses.
Require Import Common.Common.
Require Import L6.eval.
(* 
Let L6env : Type := prims * cEnv * env.

*)


Require Import Coq.Unicode.Utf8.

(* Should p c e be particular values? The translation from L5a doesn't produce
  these values. If it did, we could make the terms contain this information, as in L3 *)
Instance bigStepOpSemL3Term : BigStepHetero cps.exp cps.val :=
  λ s v,
    ∀ p c e, 
    ∃ (n:nat), (L6.eval.bstep_e p c e s v n).

(* Fix *)
Instance WfL3Term : WellFormed (*L6env*) cps.exp :=
  fun p  => True .

Instance certiL6 : CerticoqLanguage (*L6env*)cps.exp := {}.

Require Import L4.instances.
Require Import L5_to_L6.

Instance certiL5a_t0_L6: 
  CerticoqTotalTranslation L5a.val_c cps.exp := 
  fun v => convert_top (L5a.Halt_c v).






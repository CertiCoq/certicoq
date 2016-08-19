
Require Import L6.cps.
Require Import L6.cps_util.
Require Import L6.eval.

Require Import Common.certiClasses.
Require Import Common.Common.

Require Import Coq.Unicode.Utf8.

Let L6env : Type := prims * cEnv * eval.env.


(* A: Should pr cenv env be particular values? The translation from L5a doesn't produce
  these values. If it did, we could make the terms contain this information, as in L3 *)
(* Z: pr is the primitive functions map. I don't know where it's populated or it's purpose
   in general. cenv is the tag map which maps constructor tags to info such as arity and
   which type they belong to. env is the environment that contains valuations for the free
   variables of a term.
 *)
Instance bigStepOpSemL3Term : BigStepHetero (L6env * cps.exp) cps.val :=
  λ p v,
  let '(pr, cenv, env, e) := p in
  ∃ (n:nat), (L6.eval.bstep_e pr cenv env e v n).

(* Fix *)
Instance WfL3Term : WellFormed (L6env * cps.exp) :=
  fun p  => True .

Instance certiL6 : CerticoqLanguage (L6env * cps.exp) := {}.

Require Import L4.instances.
Require Import L5_to_L6.

Instance certiL5a_t0_L6: 
  CerticoqTotalTranslation L5a.val_c cps.exp := 
  fun v => convert_top (L5a.Halt_c v).







Require Import L6.cps.
Require Import L6.cps_util.
Require Import L6.eval.
 
Require Import L4.instances. 
Require Import L6.L5_to_L6.
Require Import L6.shrink_cps.

Require Import Common.certiClasses.
Require Import Common.Common.

Require Import Coq.Unicode.Utf8.

Require Import ZArith.
Require Import uncurry closure_conversion hoisting L6_to_Clight.



(* 1 - environment of primitive operations
   2 - environment of constructors (from which datatypes can be reconstructed)
  3 - evaluation environment mapping free variables to values
  4 - name environment mapping variables to their original name if it exists
*)
Let L6env : Type := prims * cEnv * eval.env * nEnv.


(* A: Should pr cenv env be particular values? The translation from L5a doesn't produce
  these values. If it did, we could make the terms contain this information, as in L3 *)
(* Z: pr is the primitive functions map. I don't know where it's populated or it's purpose
   in general. cenv is the tag map which maps constructor tags to info such as arity and
   which type they belong to. env is the environment that contains valuations for the free
   variables of a term.
 *)
Instance bigStepOpSemL3Term : BigStepHetero (L6env * cps.exp) cps.val :=
  λ p v,
  let '(pr, cenv, env, nenv,  e) := p in
  ∃ (n:nat), (L6.eval.bstep_e pr cenv env e v n).

(* Fix *)
Instance WfL3Term : GoodTerm (L6env * cps.exp) :=
  fun p  => True .

Instance certiL6 : CerticoqLanguage (L6env * cps.exp) := {}.




Open Scope positive_scope.

Definition bogus_cTag := 1000%positive.
Definition bogus_iTag := 2000%positive.
Definition bogus_cloTag := 1500%positive.
Definition bogus_cloiTag := 1501%positive.

Definition default_cTag := 1%positive.
Definition default_iTag := 1%positive.
Definition fun_fTag := 3%positive.
Definition kon_fTag := 2%positive.

Instance certiL5a_t0_L6: 
  CerticoqTotalTranslation (cTerm certiL5a) (cTerm certiL6) := 
  fun v =>
    match v with
        | pair venv vt => 
          let '(cenv, nenv, t) := convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, L5a.Halt_c vt) in
         let '(cenv',nenv', t') :=  closure_conversion_hoist
                                   bogus_cloTag
                                  (shrink_top t)  
                                   bogus_cTag
                                   bogus_iTag
                                   cenv nenv in
          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), M.empty _, nenv'), shrink_top  t')          
(*          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv), M.empty _, nenv),   t)           *)
    end.





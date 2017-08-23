
 
Require Import L4.instances. 


Require Import Common.certiClasses.
Require Import Common.Common.

Require Import Coq.Unicode.Utf8.

Require Import ZArith.
From L6 Require Import cps cps_util eval shrink_cps L5_to_L6 beta_contraction uncurry closure_conversion hoisting.
From L7 Require Import L6_to_Clight.



(* 1 - environment of primitive operations
   2 - environment of constructors (from which datatypes can be reconstructed)
  3 - name environment mapping variables to their original name if it exists
  4 - a map from function tags to information about that class of function
*)
Let L6env : Type := prims * cEnv *  nEnv * fEnv.


 (*  - evaluation environment mapping free variables to values
     - expression *) 
Let L6term: Type := eval.env * cps.exp.


Let L6val: Type := cps.val.

(* A: Should pr cenv env be particular values? The translation from L5a doesn't produce
  these values. If it did, we could make the terms contain this information, as in L3 *)
(* Z: pr is the primitive functions map. I don't know where it's populated or it's purpose
   in general. cenv is the tag map which maps constructor tags to info such as arity and
   which type they belong to. env is the environment that contains valuations for the free
   variables of a term.
 *)
Instance bigStepOpSemL6Term : BigStepOpSem (L6env * L6term) L6val :=
  λ p v,
  let '(pr, cenv, nenv, fenv, (env, e)) := p in

  (* should not modify pr, cenv and nenv 
  let '(pr', cenv', env', nenv', val) := v in *)
  ∃ (n:nat), (L6.eval.bstep_e pr cenv env e v n).

Require Import certiClasses2.







(* Probably want some fact about the wellformedness of L6env w.r.t. L6term *)
  Instance WfL6Term : GoodTerm (L6env * L6term) :=
   fun p =>  let '(pr, cenv, nenv, fenv, (env, e)) := p in
           identifiers.unique_bindings e.



(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead  L6val :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermL : ObserveNthSubterm L6val :=
fun n t => None.

Instance certiL6 : CerticoqLanguage (L6env * L6term) := {}.
Eval compute in cValue certiL6.

Instance L6_evaln: BigStepOpSemExec (cTerm certiL6) (cValue certiL6) :=
  fun n p =>
    let '((penv, cenv, nenv, fenv), (rho, e)) := p in 
    match bstep_f penv cenv rho e n with
    | exceptionMonad.Exc s => Error s None
    | Ret (inl t) => OutOfTime ((penv,cenv,nenv, fenv), t)
    | Ret (inr v) => Result v
    end.




Open Scope positive_scope.



(* starting tags for L5_to_L6, anything under default is reserved for special constructors/types *)
Definition default_cTag := 99%positive.
Definition default_iTag := 99%positive.

(* assigned for the constructor and the type of closures *)
Definition bogus_cloTag := 15%positive.
Definition bogus_cloiTag := 16%positive.

(* tags for functions and continuations *)
Definition fun_fTag := 3%positive.
Definition kon_fTag := 2%positive.

Instance certiL5a_t0_L6: 
  CerticoqTotalTranslation (cTerm certiL5a) (cTerm certiL6) := 
  fun v =>
    match v with
        | pair venv vt => 
          let '(cenv, nenv, fenv, next_cTag, next_iTag, e) := convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) in
          let '(e, (d, s), fenv) := uncurry_fuel 100 (shrink_cps.shrink_top e) fenv in  
 (*         let e := postuncurry_contract e s d in            *)
(*          let e := shrink_cps.shrink_top e in  *)
(*          let e :=  inlinesmall_contract e 10 10 in *)
(*          let e := inline_uncurry_contract e s 10 10 in  *)
          let e := shrink_cps.shrink_top e in    
          let '(cenv',nenv', t') :=  closure_conversion_hoist
                                   bogus_cloTag
                                   e
                                   next_cTag
                                   next_iTag
                                   cenv nenv in
          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), nenv', fenv),  (M.empty _,   shrink_top t')) 
    end.





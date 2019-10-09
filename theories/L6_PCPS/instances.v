
 
Require Import L4.instances. 


From CertiCoq.Common Require Import certiClasses certiClassesLinkable Common.

Require Import Coq.Unicode.Utf8.

Require Import ZArith.
From CertiCoq.L6 Require Import cps cps_util state eval shrink_cps L5_to_L6 beta_contraction uncurry closure_conversion
     closure_conversion2 hoisting dead_param_elim lambda_lifting.
From CertiCoq.L7 Require Import L6_to_Clight.



(*
   Environment for L6 programs: 
   1 - environment of primitive operations
   2 - environment of constructors (from which datatypes can be reconstructed)
   3 - name environment mapping variables to their original name if it exists
   4 - a map from function tags to information about that class of function
*)
Let L6env : Type := prims * cEnv *  nEnv * fEnv.

Let L6term: Type := env * cps.exp.

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
  let '(pr, cenv, nenv, fenv, (rho, e)) := p in
  (* should not modify pr, cenv and nenv *)
  ∃ (n:nat), L6.eval.bstep_e pr cenv rho e v n.

Require Import certiClasses2.


(* Probably want some fact about the wellformedness of L6env w.r.t. L6term *)
Instance WfL6Term : GoodTerm (L6env * L6term) :=
  fun p =>  let '(pr, cenv, nenv, fenv, (rho, e)) := p in
         identifiers.closed_exp e /\
         identifiers.unique_bindings e.

(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead L6val :=
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

Require Import ExtLib.Data.Monads.OptionMonad.

Require Import ExtLib.Structures.Monads.



(** * Definition of L6 backend pipelines *)



Definition L6_pipeline (e : cTerm certiL5) : exception (cTerm certiL6) :=  
  match e with
  | pair venv vt =>
    match convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) with
    | Some r =>
      let '(c_env, n_env, f_env, next_cTag, next_iTag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fTag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_cTag next_iTag next_fTag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in   
      (* inlining *)
      let (e, c_data) := inline_uncurry e s 10 10 c_data in
      (* Shrink reduction *)     
      let e := shrink_cps.shrink_top e in
      (* (* lambda lifting *) *)
      (* let (e, c_data) := lambda_lift' e c_data in *)
      (* Shrink reduction *)      
      let e := shrink_cps.shrink_top e in
      (* Closure conversion *)
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let '(cenv', names', e) :=
          closure_conversion.closure_conversion_hoist bogus_cloTag e ctag itag cenv names in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_cloTag bogus_cloTag bogus_cloiTag cenv') fenv names' log
      in
      (* Closure conversion *)
      (* let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_cloTag bogus_cloiTag e c_data in *)
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Dead parameter elimination *)
      let e := dead_param_elim.eliminate e in
      (* Shrink reduction *)      
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ ,  state.cenv c_data, state.name_env c_data, state.fenv c_data), (M.empty _, (shrink_top e)))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

(* Optimizing L6 pipeline *)
Definition L6_pipeline_opt (e : cTerm certiL5) : exception (cTerm certiL6) :=  
  match e with
  | pair venv vt =>
    match convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) with
    | Some r =>
      let '(c_env, n_env, f_env, next_cTag, next_iTag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fTag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_cTag next_iTag next_fTag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in   
      (* inlining *)
      let (e, c_data) := inline_uncurry e s 10 10 c_data in
      (* Shrink reduction *)     
      let e := shrink_cps.shrink_top e in
      (* (* lambda lifting *) *)
      (* let (e, c_data) := lambda_lift' e c_data in *)
      (* Shrink reduction *)      
      let e := shrink_cps.shrink_top e in
      (* Closure conversion *)
      let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_cloTag (* bogus_cloiTag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_cloTag bogus_cloTag bogus_cloiTag cenv) fenv names log
      in

      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Dead parameter elimination *)
      let e := dead_param_elim.eliminate e in
      (* Shrink reduction *)      
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ ,  state.cenv c_data, state.name_env c_data, state.fenv c_data), (M.empty _, (shrink_top e)))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

(* TODOs for optimized pipeline:
   
   1. Hoist only closed functions 
   2. Run hoisting before CC, to find top-level functions, and not closure convert them
*)

Instance certiL5_t0_L6: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL6) :=
  fun o => match o with
        | Flag 0 => L6_pipeline
        | Flag _ => L6_pipeline_opt
        end.
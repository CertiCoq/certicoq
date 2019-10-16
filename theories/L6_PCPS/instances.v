

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
Let L6env : Type := prims * ctor_env *  cps_util.name_env * fun_env.

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
Definition default_ctor_tag := 99%positive.
Definition default_ind_tag := 99%positive.

(* assigned for the constructor and the type of closures *)
Definition bogus_closure_tag := 15%positive.
Definition bogus_cloind_tag := 16%positive.

(* tags for functions and continuations *)
Definition fun_fun_tag := 3%positive.
Definition kon_fun_tag := 2%positive.

Require Import ExtLib.Data.Monads.OptionMonad.

Require Import ExtLib.Structures.Monads.



(** * Definition of L6 backend pipelines *)


Definition update_var (names : cps_util.name_env) (x : var) : cps_util.name_env :=
  match M.get x names with
  | Some (nNamed _) => names
  | Some nAnon => M.set x (nNamed "x") names
  | None => M.set x (nNamed "x") names
  end.

Definition update_vars names xs :=
  List.fold_left update_var xs names.

(** Adds missing names to name environment for the C translation *)
Fixpoint add_binders_exp (names : cps_util.name_env) (e : exp) : cps_util.name_env :=
  match e with
  | Econstr x _ _ e
  | Eprim x _ _ e
  | Eproj x _ _ _ e => add_binders_exp (update_var names x) e
  | Ecase _ pats =>
    List.fold_left (fun names p => add_binders_exp names (snd p)) pats names
  | Eapp _ _ _
  | Ehalt _ => names
  | Efun B e => add_binders_exp (add_binders_fundefs names B) e
  end
with add_binders_fundefs (names : cps_util.name_env) (B : fundefs) : cps_util.name_env :=
  match B with
  | Fcons f _ xs e1 B1 =>
    add_binders_fundefs (add_binders_exp (update_vars (update_var names f) xs) e1) B1
  | Fnil => names
  end.

Definition L6_pipeline_old (e : cTerm certiL5) : exception (cTerm certiL6) :=
  match e with
  | pair venv vt =>
    match AstCommon.timePhase "L5 to L6" (fun (_:Datatypes.unit) => convert_top default_ctor_tag default_ind_tag fun_fun_tag kon_fun_tag (venv, vt)) with
    | Some r =>
      let '(c_env, n_env, f_env, next_ctor_tag, next_ind_tag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_ctor_tag next_ind_tag next_fun_tag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in
      (* (* inlining *) *)
      let (e, c_data) := inline_uncurry e s 10 10 c_data in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let '(cenv', names', e) :=
          closure_conversion.closure_conversion_hoist bogus_closure_tag e ctag itag cenv names in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv') fenv names' log
      in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Dead parameter elimination *)
      (* let e := dead_param_elim.eliminate e in *)
      (* (* Shrink reduction *)       *)
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ ,  state.cenv c_data, state.nenv c_data, state.fenv c_data), (M.empty _, e))
    | None => Exc "failed converting from L5 to L6"
    end
  end.



Definition L6_pipeline (e : cTerm certiL5) : exception (cTerm certiL6) :=
  match e with
  | pair venv vt =>
    match AstCommon.timePhase "L5 to L6" (fun (_:Datatypes.unit) => convert_top default_ctor_tag default_ind_tag fun_fun_tag kon_fun_tag (venv, vt)) with
    | Some r =>
      let '(c_env, n_env, f_env, next_ctor_tag, next_ind_tag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_ctor_tag next_ind_tag next_fun_tag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in
      (* inlining *)
      let (e, c_data) := inline_uncurry e s 10 10 c_data in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Closure conversion *)
      let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_closure_tag (* bogus_cloind_tag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv) fenv (add_binders_exp names e) log
      in
      (* Shrink reduction *)
      (* let e := shrink_cps.shrink_top e in *)
      (* (* Dead parameter elimination *) *)
      (* let e := dead_param_elim.eliminate e in *)
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ ,  state.cenv c_data, state.nenv c_data, state.fenv c_data), (M.empty _, e))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

(* Optimizing L6 pipeline *)
Definition L6_pipeline_opt (e : cTerm certiL5) : exception (cTerm certiL6) :=
  match e with
  | pair venv vt =>
    match AstCommon.timePhase "L5 to L6" (fun (_:Datatypes.unit) => convert_top default_ctor_tag default_ind_tag fun_fun_tag kon_fun_tag (venv, vt)) with
    | Some r =>
      let '(c_env, n_env, f_env, next_ctor_tag, next_ind_tag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_ctor_tag next_ind_tag next_fun_tag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in
      (* inlining *)
      let (e, c_data) := inline_uncurry e s 10 10 c_data in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* lambda lifting *)
      let (e, c_data) := lambda_lift e c_data in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Closure conversion *)
      let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_closure_tag (* bogus_cloind_tag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv) fenv (add_binders_exp names e) log
      in

      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* (* Dead parameter elimination *) *)
      (* let e := dead_param_elim.eliminate e in *)
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ ,  state.cenv c_data, state.nenv c_data, state.fenv c_data), (M.empty _, (shrink_top e)))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

Instance certiL5_t0_L6:
  CerticoqTranslation (cTerm certiL5) (cTerm certiL6) :=
  fun o => match o with
        | Flag 0 => L6_pipeline
        | Flag 1 => L6_pipeline
        | Flag 2 => L6_pipeline
        | Flag 3 => L6_pipeline
        | Flag 4 => L6_pipeline
        | Flag 5 => L6_pipeline_opt
        | Flag 6 => L6_pipeline_opt
        | Flag 7 => L6_pipeline_opt
        | Flag 8 => L6_pipeline_opt
        | Flag 9 => L6_pipeline_opt
        | Flag 10 => L6_pipeline_old
        | Flag _ => L6_pipeline
        end.

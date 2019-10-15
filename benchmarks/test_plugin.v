Require Import Arith.
Require Import L6.instances.

Require Import Coq.Unicode.Utf8.

Require Import ZArith.
From CertiCoq Require Import CertiCoq.
Unset Template Cast Propositions.

Definition foo := 3 + 4.

CertiCoq Compile Opt 1 foo.


Require Import CertiCoq.Benchmarks.Binom.

Require Import CertiCoq.Benchmarks.vs.
CertiCoq Compile Opt 2 main.

(*

From CertiCoq.Common Require Import certiClasses certiClassesLinkable Common.
From CertiCoq.L6 Require Import cps cps_util state eval shrink_cps L5_to_L6 beta_contraction uncurry closure_conversion
     closure_conversion2 hoisting dead_param_elim lambda_lifting.
From CertiCoq.L7 Require Import L6_to_Clight.
Require Import Compiler.allInstances.

Require Import Color.

Quote Recursively Definition graph := main.

Quote Recursively Definition graph2 := (translateTo (cTerm certiL2k) (Flag 0) main).

Definition my_L6_pipeline (e : cTerm certiL5) : exception (cTerm certiL6) :=  
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
      (* Closure conversion *)
      let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_cloTag (* bogus_cloiTag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (add_cloTag bogus_cloTag bogus_cloiTag cenv) fenv (add_binders_exp names e) log
      in
      (* Shrink reduction
      let e := shrink_cps.shrink_top e in 
      (* Dead parameter elimination 
      let e := dead_param_elim.eliminate e in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in *)  *)
      Ret ((M.empty _ ,  state.cenv c_data, state.name_env c_data, state.fenv c_data), (M.empty _, e))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

Ltac computeExtract f:=
  (let t := eval compute in f in
   match t with
   | Ret ?xx => exact xx
   end).

Definition binom5 := Eval native_compute in (translateTo (cTerm certiL5) (Flag 0) binom).

Definition binom6' : exception (cTerm certiL6).
Proof.
  eapply my_L6_pipeline.
  computeExtract binom5.
Defined.

Definition binom6'' :=  Eval native_compute in binom6'.

Definition binomshrink : L6.cps.exp.
Proof.
  refine (shrink_cps.shrink_top _).
  assert (e : cTerm certiL6) by computeExtract binom6''.
  exact (snd (snd e)).
Defined.

CertiCoq Compile binomshrink.

CertiCoq Compile Opt 1 main.
*)


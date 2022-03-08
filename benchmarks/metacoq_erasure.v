Require Import Arith List String ZArith.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

From MetaCoq.Erasure Require Import Erasure Loader.
From MetaCoq.Template Require Import MCString.

Program Definition erase (p : Ast.Env.program) : eprogram :=
  erase_program p (MCUtils.todo "wf_env and welltyped term").

Program Definition erase_and_print_template_program (p : Ast.Env.program) : string :=
  let (Σ', t) := erase_program p (MCUtils.todo "wf_env and welltyped term") in
  (EPretty.print_term Σ' nil true false t ++ nl ++ "in:" ++ nl ++ EPretty.print_global_context Σ')%string.

MetaCoq Erase true.

MetaCoq Quote Recursively Definition foo := (true, false).
(* ((fun (X : Set) (x : X) (e : x = x) => *)
                  (* match e in eq _ x' return bool with *)
                  (* | eq_refl => true *)
                  (* end)). *)

Definition metacoq_erasure := (erase_and_print_template_program foo).

CertiCoq Compile -O 0 -debug metacoq_erasure.
(*
Definition er := Eval lazy in erase foo.

Require Import CertiCoq.Compiler.pipeline Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.
Definition next_id := 100%positive.

Section Pipeline.

  Definition CertiCoq_pipeline (p : Ast.Env.program) :=
    p <- compile_L2k p ;;
    (* p <- compile_L2k_eta p ;; *)
    p <- compile_L4 [] p ;;
    compile_L6_ANF next_id [] p.
    (* if debug then compile_L6_debug next_id p  For debugging intermediate states of the λanf pipeline *)
    (* else compile_L6 next_id p. *)

End Pipeline.


(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
(*   p <- erase_PCUIC p ;;
 *) CertiCoq_pipeline p.

Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
    run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

  (* compile_Clight prs p. *)
Eval compute in 
    match compile default_opts foo with
    | (compM.Ret a, s) => a
    | (compM.Err s, s') => MCUtils.todo "foo"
    end.*)
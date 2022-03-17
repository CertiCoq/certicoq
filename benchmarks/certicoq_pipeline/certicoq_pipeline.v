Require Import Arith List String ZArith.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

From MetaCoq.Erasure Require Import ERemoveParams Erasure Loader.
From MetaCoq.Template Require Import All MCString EtaExpand.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

Definition test_arg (x : nat) := x.

CertiCoq Compile -time -O 0 -args 1 test_arg.


Program Definition erase (p : Ast.Env.program) : eprogram :=
  erase_program p (MCUtils.todo "wf_env and welltyped term").

Axiom (print_str : string -> unit).
Axiom (print_newline : unit -> unit).
Axiom (print_nat : nat -> unit).

Require Import CertiCoq.Compiler.pipeline.
From CertiCoq.Common Require Import Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.
Definition next_id := 100%positive.

Section Pipeline.
  Definition CertiCoq_pipeline (p : Ast.Env.program) :=
    p <- compile_L2k p ;;
    p <- compile_L4 [] p ;;
    compile_L6_ANF next_id [] p.
    (* if debug then compile_L6_debug next_id p  For debugging intermediate states of the λanf pipeline *)
    (* else compile_L6 next_id p. *)

End Pipeline.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
  CertiCoq_pipeline p.

Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

Time MetaCoq Run (tmBind (tmQuoteRecTransp TemplateToPCUIC.trans false) (tmDefinition "quoted_term")).

Definition certicoq_pipeline := 
  match compile default_opts quoted_term with
  | (compM.Ret (prims, primenv, ctorenv, ctortag, indtag, nameenv, funenv, evalenv, e), s) => 
    let _ := print_str ("CertiCoq pipeline succeeded with: ") in
    let _ := print_newline tt in
    let s := cps_show.show_exp nameenv ctorenv false e in
    print_str s
  | (compM.Err s, s') => 
    let _ := print_str "Error in certicoq erasure" in
    let _ := print_newline tt in
    print_str s
  end.

CertiCoq Compile -time -O 0 certicoq_pipeline
Extract Constants [ 
  (* print_nat => "print_gallina_nat", *)
  print_str => "print_gallina_string",
  print_newline => "print_new_line" ] 
Include [ "print.h" ].
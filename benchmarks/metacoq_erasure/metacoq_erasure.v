Require Import Arith List String ZArith.

From CertiCoq.Plugin Require Import CertiCoq.

From MetaCoq.Erasure Require Import EProgram.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.
Require Import MetaCoq.Utils.bytestring.

Open Scope bs_scope.

Axiom (coq_msg_info : string -> unit).
Axiom (coq_msg_debug : string -> unit).

Set MetaCoq Timing.

Local Existing Instance config.extraction_checker_flags.

Import ListNotations.
Import Kernames.

Definition bool_inductive_mapping : inductives_mapping := 
  let bool_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "bool"); inductive_ind := 0 |} in 
  [ (bool_ind, ("bool", [1; 0]))].

Program Definition erase (p : Ast.Env.program) : eprogram :=
  run_erase_program default_erasure_config (bool_inductive_mapping, p) (MCUtils.todo "wf_env and welltyped term").

Program Definition erase_and_print_template_program (p : Ast.Env.program) : unit :=
  let _ := coq_msg_info ("Erasing program.") in
  let prprog := coq_msg_info (Pretty.print_program false 2 p) in
  let eprog := erase p in
  let _ := coq_msg_info "Erasure terminated with: " in
  coq_msg_info (EPretty.print_program eprog).

Definition metacoq_erasure (p : Ast.Env.program) :=
  erase_and_print_template_program p.

CertiCoq Compile -time -O 1 metacoq_erasure
Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  coq_msg_info => "coq_msg_info",
  PCUICWfEnvImpl.guard_impl => "metacoq_guard_impl" ]
Include [ "print.h" ].

(*
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

(*Extract Constant PCUICTyping.guard_checking => 
"{ guard = (fun _ _ _ _ -> true) }". *)

CertiCoq Compile -O 0 typecheck_program
Extract Constants [ 
  (* coq_msg_debug => "print_msg_debug", *)
  PCUICTyping.guard_checking => "print_msg_info",
  coq_msg_info => "print_msg_info"
   ] 
Include [ "print.h" ].*)

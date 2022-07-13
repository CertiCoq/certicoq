From CertiCoq.Plugin Require Import CertiCoq.
From MetaCoq.Template Require Import utils.
Open Scope bs_scope.


Axiom (coq_msg_info : string -> unit).
Axiom (coq_user_error : string -> unit).
Axiom (coq_msg_debug : string -> unit).

Require Import CertiCoq.Compiler.pipeline.
From CertiCoq.Common Require Import Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.

Section Pipeline.
  Context (next_id : positive)
    (prims : list (Kernames.kername * string * bool * nat * positive))
    (debug : bool).

  Definition CertiCoq_pipeline (p : Ast.Env.program) :=
    p <- compile_L2k p ;;
    p <- compile_L4 prims p ;;
    p <- compile_L6_ANF next_id prims p ;;
    (* if debug then compile_L6_debug next_id p  For debugging intermediate states of the λanf pipeline else *)
    compile_L6 next_id p.
End Pipeline.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)
Definition next_id := 100%positive.

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
  p' <- CertiCoq_pipeline next_id prs p ;;
  compile_Clight prs p'.
  
Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

Definition cps_show (t : L6_FullTerm) :=
  let '(prims, primenv, ctorenv, ctortag, indtag, nameenv, funenv, evalenv, e) := t in
  let s := cps_show.show_exp nameenv ctorenv false e in
  coq_msg_info s.

Definition certicoqc (opts : Options) (p : Template.Ast.Env.program) := 
  let () := coq_msg_info "certicoqc called" in
  compile opts p.
(* CertiCoq Show IR -time -O 1 certicoq_pipeline
Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  coq_msg_info => "print_msg_info"
]. *)

(* From MetaCoq Require Import PCUICWfEnvImpl SafeTemplateChecker.

Definition typecheck_program (p : Template.Ast.Env.program) : bool :=
  match infer_and_print_template_program 
    (cf := config.default_checker_flags) 
    (guard := Erasure.fake_guard_impl) 
    (nor := PCUICSN.default_normalizing)
    p Universes.Monomorphic_ctx with
  | inl ty => let () := coq_msg_info ty in true
  | inr err => let () := coq_user_error err in false
  end.  

Eval compute in "Compiling MetaCoq's type-checker". *)

(*CertiCoq Compile -time -O 1 typecheck_program
Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  coq_msg_info => "print_msg_info",
  coq_user_error => "coq_user_error"
   ] 
Include [ "print.h" ].*)

Eval compute in "Compiling CertiCoq's pipeline".

CertiCoq Compile -time -O 1 certicoqc
Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  coq_msg_info => "print_msg_info"
   ] 
Include [ "print.h" ].

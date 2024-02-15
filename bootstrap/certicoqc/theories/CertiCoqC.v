From MetaCoq.Utils Require Import utils.
Open Scope bs_scope.

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

  Definition CertiCoq_pipeline econf (p : Ast.Env.program) :=
    p <- compile_LambdaBoxMut econf p ;;
    p <- compile_LambdaBoxLocal prims p ;;
    p <- compile_LambdaANF_ANF next_id prims p ;;
    (* if debug then compile_LambdaANF_debug next_id p  For debugging intermediate states of the λanf pipeline else *)
    compile_LambdaANF next_id p.
End Pipeline.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)
Definition next_id := 100%positive.

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  o <- get_options ;;
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
  p' <- CertiCoq_pipeline next_id prs o.(erasure_config) p ;;
  compile_Clight prs p'.
  
Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

Definition certicoqc (opts : Options) (p : Template.Ast.Env.program) := 
  compile opts p.

From MetaRocq.Utils Require Import utils.
Open Scope bs_scope.

Require Import CertiRocq.Compiler.pipeline.
From CertiRocq.Common Require Import Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.

Section Pipeline.
  Context (next_id : positive)
    (prims : list (Kernames.kername * string * bool * nat * positive))
    (debug : bool).

  Definition CertiRocq_pipeline econf im (p : Ast.Env.program) :=
    p <- compile_LambdaBoxMut econf im p ;;
    p <- compile_LambdaBoxLocal prims p ;;
    p <- compile_LambdaANF_ANF next_id prims p ;;
    (* if debug then compile_LambdaANF_debug next_id p  For debugging intermediate states of the λanf pipeline else *)
    compile_LambdaANF next_id p.
End Pipeline.

(** * The main CertiRocq pipeline, with MetaRocq's erasure and C-code generation *)
Definition next_id := 100%positive.

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  o <- get_options ;;
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
  p' <- CertiRocq_pipeline next_id prs o.(erasure_config) o.(inductives_mapping) p ;;
  compile_Clight prs p'.
  
Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

Definition certirocqc (opts : Options) (p : Template.Ast.Env.program) :=
  compile opts p.

From CertiCoq.Plugin Require Import CertiCoq.
From MetaCoq.Template Require Import utils.
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

Set Warnings "-primitive-turned-into-axiom".
(* 
From MetaCoq Require Import Primitive Template.Ast.

Definition certicoqc (opts : Options) (p : Template.Ast.Env.program) := 
  (* let () := coq_msg_info "certicoqc called" in *)
  (* let () := coq_msg_info ("got program: " ++ Pretty.print_program false 100 p) in *)
  match snd p with 
  | Template.Ast.tConst kn _ => 
    match Env.lookup_env (fst p) kn with
    | Some (ConstantDecl {| cst_body := Some (tInt i) |}) => coq_msg_info (string_of_prim_int i)
    | _ => tt
    end
  | _ => tt
  end. *)

CertiCoq Compile -time -O 1 certicoqc.

(** * Simulation invariant for the LambdaANF -> LLVM correctness proof. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import cps cps_util eval identifiers.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Section Simulation.

  (** The program and its runtime. *)
  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.                     (* top-level functions *)
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).

  Let fs := fun_ids fds.

  (** The global environment after initialisation, and the call knot. *)
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).

  (** The [thread_info] pointer, fixed for the whole run. *)
  Variable tinfo : ptr.

  (* ------------------------------------------------------------------ *)
  (** ** Invariants *)

  (** A representation that survives everything the generated code may later
      do to the heap. *)
  Definition stable_repr (st : state) (v : cps.val) (z : Z) : Prop :=
    forall st2, heap_bytes_agree_except st st2 (not_object st tinfo) ->
      repr_val cenv fds G st2 v z.

  (** The runtime-level invariant: heap invariant, well-formed [thread_info],
      and a shadow stack whose roots [rs] represent [vs]. *)
  Definition INV (st : state) (fp : ptr) (rs : list ptr) (vs : list cps.val) : Prop :=
    heap_inv st tinfo /\ tinfo_ok st tinfo /\
    field st tinfo off_fp fp /\ shadow_stack st fp rs /\
    roots_ok cenv fds G st tinfo rs vs.

  (** Source environment vs. Vellvm locals, on the variables [S].  Top-level
      functions are globals; every other variable is held, under its current
      SSA name [env x], as a word that stably represents its value. *)
  Definition env_rel (S : var -> Prop) (rho : M.t cps.val) (env : nenv)
             (sf : stack_frame) (st : state) : Prop :=
    forall x, S x ->
      exists v, M.get x rho = Some v /\
        if is_fun fs x then v = Vfun (M.empty _) fds x
        else exists z, RM.find (env x) (stack_vars sf) = Some (I64 z) /\ stable_repr st v z.

  (** [tinfo] is passed to every emitted function as its [%tinfo] parameter. *)
  Definition tinfo_local (sf : stack_frame) : Prop :=
    RM.find (Name "tinfo") (stack_vars sf) = Some (DVALUE_Base (DVALUE_Pointer tinfo)).

  (** The result of running a compiled expression. *)
  Definition sim_result (st : state) (fp : ptr) (rs : list ptr) (vs : list cps.val)
             (v : cps.val) {X} (t : MCFGbot (Res (X + dvalue))) : Prop :=
    ends_in_oom t \/
    exists st' ls z,
      returns t ((st', ls), inr (I64 z)) /\
      stable_repr st' v z /\
      INV st' fp rs vs.

End Simulation.

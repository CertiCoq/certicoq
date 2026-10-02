(** * Top-level correctness statement for the LambdaANF -> LLVM (Vellvm VIR) backend.

    This file states (but does not yet prove) the end-to-end correctness of the
    code that the pipeline actually emits, [flatten_prog (compile_prog ...)],
    against Vellvm's executable semantics [interp_mcfg], instantiated with
    Vellvm's concrete memory model and 64-bit pointers.

    The only hypothesis is the correctness of the runtime: the garbage
    collector and the [thread_info] initialisation.  Both are linked into the
    program as Vellvm library functions acting on Vellvm's memory.  Their
    specification is concrete: it is stated with the same value relation as the
    conclusion, and the heap invariant the collector may rely on is existentially
    chosen by the runtime but must be preserved by everything the generated code
    does to the heap (see [runtime_correct]).

    Divergence is not covered: the theorem is about terminating source runs. *)

From Stdlib Require Import ZArith NArith List Lia String.
From ITree Require Import ITree Eq.Eqit.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import cps cps_util eval identifiers.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Notation LLprog := (list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) (only parsing).

(** Vellvm's concrete memory model with 64-bit pointers. *)
#[global] Instance Pa64 : Params := @ParamsV IP64Bit IP64BitTheory.
#[global] Existing Instance MemoryModelPrimitivesV.

(* ------------------------------------------------------------------ *)
(** ** What the pipeline emits *)

Definition ord_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_ordinal info | None => 0%N end.
Definition arity_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_arity info | None => 0%N end.

(** Same as [LambdaANF_to_LLVM_Wrapper] in [CodegenLLVM/toplevel.v]. *)
Definition emitted (cenv : ctor_env) (prim_of : positive -> option (string * bool))
           (e : cps.exp) : LLprog :=
  flatten_prog (compile_prog (ord_of cenv) (arity_of cenv) prim_of e).

(* ------------------------------------------------------------------ *)
(** ** Reading Vellvm memory *)

(** [m] runs from memory state [st] to [st'] returning [x], without choices
    or errors (this is exactly what Vellvm's [memM_interp] does on such [m]). *)
Inductive memS_runs {X} : state -> memM X -> state -> X -> Prop :=
| MR_ret st x : memS_runs st (Mret x) st x
| MR_get st k st' x : memS_runs st (k st) st' x -> memS_runs st (Mget k) st' x
| MR_put st st0 k st' x : memS_runs st0 (k tt) st' x -> memS_runs st (Mput st0 k) st' x.

Definition memS_returns {X} (st : state) (m : memM X) (x : X) : Prop :=
  exists st', memS_runs st m st' x.

Definition I64 (z : Z) : dvalue := DVALUE_Base (DVALUE_I 64 (@Integers.repr 64 z)).

Definition reads_word (st : state) (p : ptr) (z : Z) : Prop :=
  memS_returns st (read_dvalue (DTYPE_I 64) p) (I64 z).

(** Pointers read from memory carry wildcard provenance, so only their
    address is meaningful. *)
Definition reads_ptr (st : state) (p q : ptr) : Prop :=
  memS_returns st (read_dvalue DTYPE_Pointer p) (DVALUE_Base (DVALUE_Pointer q)).

Definition writable_word (st : state) (p : ptr) : Prop :=
  forall z, exists st', memS_runs st (write_dvalue (DTYPE_I 64) p (I64 z)) st' tt
                   /\ reads_word st' p z.

(** [p + off] bytes, keeping [p]'s provenance. *)
Definition ptr_off (p : ptr) (off : Z) (q : ptr) : Prop :=
  int_to_ptr (ptr_to_int p + off) (ptr_provenance p) = EOU.raise_ret q.

(** The raw memory and the malloc'd heap blocks of a state. *)
Definition mem_of (st : state) : memory := Memory_stack_memory (state_memory_stack st).
Definition heap_of (st : state) : Heap := Memory_stack_heap (state_memory_stack st).
Definition frames_of (st : state) : Framestack := Memory_stack_frame_stack (state_memory_stack st).

(** [a] is an address inside a malloc'd (heap, not stack) block. *)
Definition in_heap (st : state) (a : Z) : Prop :=
  exists root blk, IntMaps.lookup root (heap_of st) = Some blk /\ In a (map ptr_to_int blk).

(** [st2] has the same bytes as [st] at the heap addresses of [st], except
    possibly at the addresses in [S].  Stack memory is unconstrained. *)
Definition heap_bytes_agree_except (st st2 : state) (S : Z -> Prop) : Prop :=
  forall a, in_heap st a -> ~ S a -> IntMaps.lookup a (mem_of st2) = IntMaps.lookup a (mem_of st).

(** In addition, the set of heap blocks is the same. *)
Definition heap_agree_except (st st2 : state) (S : Z -> Prop) : Prop :=
  heap_of st2 = heap_of st /\ heap_bytes_agree_except st st2 S.

(* ------------------------------------------------------------------ *)
(** ** Value representation (the C runtime's ABI, [values.h])

    - nullary constructor: unboxed word [ord * 2 + 1];
    - n-ary constructor: a pointer [p] to the first field, header
      [arity << 10 | ord] at [p - 8], field [i] at [p + 8 i];
    - primitive integer [n]: unboxed word [n * 2 + 1];
    - function [f] of the top-level block [fds]: the address of [@f]. *)

Section Repr.
  Variable cenv : ctor_env.
  Variable fds : fundefs.            (* the program's top-level functions *)
  Variable genv : global_env.        (* Vellvm's global environment *)
  Variable st : state.               (* Vellvm's memory *)

  Inductive repr_val : cps.val -> Z -> Prop :=
  | Repr_unboxed t :
      arity_of cenv t = 0%N ->
      repr_val (Vconstr t []) (Z.of_N (ord_of cenv t) * 2 + 1)
  | Repr_boxed t vs p ph :
      arity_of cenv t = N.of_nat (length vs) ->
      vs <> [] ->
      ptr_off p (-8) ph ->
      reads_word st ph (Z.of_N (arity_of cenv t) * 1024 + Z.of_N (ord_of cenv t)) ->
      repr_fields vs p 0 ->
      repr_val (Vconstr t vs) (ptr_to_int p)
  | Repr_int n :
      repr_val (Vprim (existT _ primInt n)) (Uint63.to_Z n * 2 + 1)
  | Repr_fun rho f fp :
      RawIdMaps.rid_lookup (Anon (Zpos f)) genv
        = Some (DVALUE_Base (DVALUE_Pointer fp)) ->
      repr_val (Vfun rho fds f) (ptr_to_int fp)
  with repr_fields : list cps.val -> ptr -> Z -> Prop :=
  | Repr_nil p off : repr_fields [] p off
  | Repr_cons v vs p off q z :
      ptr_off p off q ->
      reads_word st q z ->
      repr_val v z ->
      repr_fields vs p (off + 8) ->
      repr_fields (v :: vs) p off.
End Repr.

(* ------------------------------------------------------------------ *)
(** ** The runtime's state: [thread_info] and the shadow stack

    [thread_info] (gc_stack.h): alloc @0, limit @8, heap @16,
    args[1024] @24, fp @8216, nalloc @8224.
    A shadow-stack frame: { roots_end @0; roots_start @8; prev @16 }.
    A null pointer is any pointer whose address is 0 (pointers read from
    memory have wildcard provenance, so they are never Vellvm's [null]). *)

Definition off_alloc  := 0%Z.
Definition off_limit  := 8%Z.
Definition off_fp     := 8216%Z.
Definition off_nalloc := 8224%Z.

Definition field (st : state) (tinfo : ptr) (off : Z) (q : ptr) : Prop :=
  exists a, ptr_off tinfo off a /\ reads_ptr st a q.

Definition field_addr (tinfo : ptr) (off : Z) (a : Z) : Prop :=
  ptr_to_int tinfo + off <= a < ptr_to_int tinfo + off + 8.

(** The root slots [rs] of the shadow stack starting at frame [fp]. *)
Inductive slots_from (st : state) (s e : ptr) : list ptr -> Prop :=
| Slots_done : ptr_to_int s = ptr_to_int e -> slots_from st s e []
| Slots_more s' rs :
    (ptr_to_int s < ptr_to_int e)%Z ->
    ptr_off s 8 s' -> slots_from st s' e rs -> slots_from st s e (s :: rs).

Inductive shadow_stack (st : state) : ptr -> list ptr -> Prop :=
| SS_nil f : ptr_to_int f = 0 -> shadow_stack st f []
| SS_frame f e s prev rs rs' :
    ptr_to_int f <> 0 ->
    reads_ptr st f e ->
    (exists a, ptr_off f 8 a /\ reads_ptr st a s) ->
    (exists a, ptr_off f 16 a /\ reads_ptr st a prev) ->
    slots_from st s e rs ->
    shadow_stack st prev rs' ->
    shadow_stack st f (rs ++ rs').

(** The nursery [alloc, limit) of [st]. *)
Definition nursery (st : state) (tinfo : ptr) (a : Z) : Prop :=
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    ptr_to_int alloc <= a < ptr_to_int limit.

(** The heap addresses the generated code writes: the nursery and the
    [alloc], [fp] and [nalloc] fields of [thread_info]. *)
Definition mutator_writes (st : state) (tinfo : ptr) (a : Z) : Prop :=
  nursery st tinfo a \/ field_addr tinfo off_alloc a \/
  field_addr tinfo off_fp a \/ field_addr tinfo off_nalloc a.

(** Heap objects live outside the nursery and outside [thread_info]. *)
Definition not_object (st : state) (tinfo : ptr) (a : Z) : Prop :=
  nursery st tinfo a \/ (ptr_to_int tinfo <= a < ptr_to_int tinfo + 8232).

(** A well-formed [thread_info]: its fields are writable heap words, and the
    nursery is a word-aligned, writable heap region. *)
Definition tinfo_ok (st : state) (tinfo : ptr) : Prop :=
  (forall off a, In off [off_alloc; off_limit; off_fp; off_nalloc] ->
     ptr_off tinfo off a -> writable_word st a /\
       forall b, field_addr tinfo off b -> in_heap st b) /\
  (exists fp rs, field st tinfo off_fp fp /\ shadow_stack st fp rs) /\
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    (ptr_to_int alloc mod 8 = 0)%Z /\
    ptr_to_int alloc <= ptr_to_int limit /\
    (forall a, ptr_to_int alloc <= a < ptr_to_int limit -> in_heap st a) /\
    (forall i q, 0 <= 8 * i < ptr_to_int limit - ptr_to_int alloc ->
       ptr_off alloc (8 * i) q -> writable_word st q).

(** At least [n] free words in the nursery. *)
Definition room (st : state) (tinfo : ptr) (n : Z) : Prop :=
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    (ptr_to_int limit - ptr_to_int alloc >= 8 * n)%Z.

(** The roots [rs] hold words [zs] representing [vs], and these
    representations only depend on heap bytes outside the nursery and
    [thread_info]: they survive any change of the other bytes (in particular
    everything the generated code writes, and the collector's next run). *)
Definition roots_ok cenv fds genv (st : state) tinfo (rs : list ptr) (vs : list cps.val) : Prop :=
  exists zs,
    Forall2 (reads_word st) rs zs /\
    forall st2, heap_bytes_agree_except st st2 (not_object st tinfo) ->
      Forall2 (repr_val cenv fds genv st2) vs zs.

(* ------------------------------------------------------------------ *)
(** ** Running Vellvm code *)

Definition lift_top {R} (t : MCFGtop R) : CFGtop R :=
  translate (fun _ e => inr1 e) t.

Definition returns {R} (t : MCFGbot R) (r : R) : Prop := t ≈ Ret r.

Definition ends_in_oom {R} (t : MCFGbot R) : Prop :=
  exists (k : void -> MCFGbot R), t ≈ Vis (subevent _ (ThrowOOM tt)) k.

(** [denote_vellvm] from [Semantics/TopLevel.v], with the runtime's
    library functions [rt] added to Vellvm's built-in [_LIBRARIES]. *)
Definition denote_with_runtime
           (rt : list (function_id * function_denotation))
           (ret_typ : dtyp) (entry : function_id) (args : list dvalue)
           (mcfg : CFG.mcfg dtyp) : MCFGtop dvalue :=
  build_global_environment mcfg ;;
  'defns <- map_monad address_one_function (m_definitions mcfg) ;;
  'libraries <- map_monad address_one_library_function
                 (rt ++ library_functions (m_declarations mcfg)) ;;
  'addr <- gread entry ;;
  'rv <- denote_mcfg (IP.of_list (defns ++ libraries)) ret_typ addr args ;;
  match rv with
  | inl e => raiseLLVM e
  | inr rv => ret rv
  end.

Definition initial_fused : FusedS :=
  (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

(** The runtime prelude: [declare void @garbage_collect(ptr)]. *)
Definition gc_decl : declaration typ :=
  mk_declaration (Name "garbage_collect")
    (TYPE_Function TYPE_Void [TYPE_Pointer None] false)
    ([], [[]]) [] [].

Definition runtime_prelude : LLprog := [TLE_Declaration gc_decl].

(** Set up [tinfo], then run [@certirocq_main(tinfo)]. *)
Definition run_program (gc : list dvalue -> MCFGtop (exc + dvalue))
           (make_tinfo : MCFGtop dvalue) (prog : LLprog)
  : MCFGbot (Res dvalue) :=
  interp_mcfg
    (tinfo <- make_tinfo ;;
     denote_with_runtime [(Name "garbage_collect", fun args => lift_top (gc args))]
       (DTYPE_I 64) (Name "certirocq_main") [tinfo]
       (convert_types (CFG.mcfg_of_tle (link runtime_prelude prog))))
    initial_fused.

(* ------------------------------------------------------------------ *)
(** ** The runtime assumptions *)

Section Runtime.
  Variable cenv : ctor_env.
  Variable fds : fundefs.

  (** The runtime chooses a heap invariant [heap_inv].

      - [make_tinfo] establishes it, with a well-formed [thread_info] and an
        empty shadow stack (or runs out of memory).
      - Everything the generated code does to the heap preserves it: it only
        writes the nursery and the [alloc]/[fp]/[nalloc] fields, and only moves
        [alloc] forward within the nursery.  (Stack memory is not constrained.)
      - The collector, called with [heap_inv], a well-formed shadow stack whose
        roots represent [vs], and [nalloc] in [thread_info], re-establishes all
        of this: same shadow stack, roots representing the same [vs], [nalloc]
        words of room.  It does not touch locals, globals or the stack of
        memory frames (or it runs out of memory). *)
  Definition runtime_correct (heap_inv : state -> ptr -> Prop)
             (gc : list dvalue -> MCFGtop (exc + dvalue))
             (make_tinfo : MCFGtop dvalue) : Prop :=
    (ends_in_oom (interp_mcfg make_tinfo initial_fused)
     \/ exists st tinfo fp,
         returns (interp_mcfg make_tinfo initial_fused)
                 ((st, snd initial_fused), DVALUE_Base (DVALUE_Pointer tinfo)) /\
         heap_inv st tinfo /\ tinfo_ok st tinfo /\
         field st tinfo off_fp fp /\ ptr_to_int fp = 0) /\
    (forall st st2 tinfo alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo) /\
    (forall (st : state) ls genv tinfo fp rs vs nalloc,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       field st tinfo off_fp fp ->
       shadow_stack st fp rs ->
       roots_ok cenv fds genv st tinfo rs vs ->
       (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
       ends_in_oom (interp_mcfg (gc [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, (ls, genv)))
       \/ exists st',
           returns (interp_mcfg (gc [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, (ls, genv)))
                   ((st', (ls, genv)), inr (DVALUE_Base DVALUE_None)) /\
           frames_of st' = frames_of st /\
           heap_inv st' tinfo /\ tinfo_ok st' tinfo /\
           field st' tinfo off_fp fp /\
           shadow_stack st' fp rs /\
           roots_ok cenv fds genv st' tinfo rs vs /\
           room st' tinfo nalloc).
End Runtime.

(* ------------------------------------------------------------------ *)
(** ** Source-side restrictions *)

(** No primitive operations, only integer primitive values, and no [Efun]
    except the top-level one. *)
Inductive body_ok : cps.exp -> Prop :=
| BO_constr x t ys e : body_ok e -> body_ok (Econstr x t ys e)
| BO_proj x t n y e : body_ok e -> body_ok (Eproj x t n y e)
| BO_case x bs : Forall (fun b => body_ok (snd b)) bs -> body_ok (Ecase x bs)
| BO_letapp x f ft ys e : body_ok e -> body_ok (Eletapp x f ft ys e)
| BO_app f ft ys : body_ok (Eapp f ft ys)
| BO_prim_val x n e : body_ok e -> body_ok (Eprim_val x (existT _ primInt n) e)
| BO_halt x : body_ok (Ehalt x).

Inductive fundefs_ok : fundefs -> Prop :=
| FO_nil : fundefs_ok Fnil
| FO_cons f ft xs e fds : body_ok e -> fundefs_ok fds -> fundefs_ok (Fcons f ft xs e fds).

(** Constructor tags used by the program are in [cenv], with an ordinal below
    1024 and an arity below 2^54 (the header layout), and ordinals are
    distinct among the nullary resp. non-nullary constructors of an inductive
    (as for the Wasm backend, [cenv_restricted]). *)
Definition tag_ok (cenv : ctor_env) (t : ctor_tag) : Prop :=
  (exists info, M.get t cenv = Some info) /\
  (ord_of cenv t < 1024)%N /\ (arity_of cenv t < 2 ^ 54)%N.

Definition cenv_ok (cenv : ctor_env) : Prop :=
  forall t name iname it a ord,
    M.get t cenv = Some (Build_ctor_ty_info name iname it a ord) ->
    forall t', t <> t' ->
      (a = 0%N -> ~ (exists name' iname', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it 0%N ord))) /\
      ((0 < a)%N -> ~ (exists name' iname' a', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it a' ord))).

(** What the LambdaANF pipeline guarantees before code generation, as for the
    Wasm backend ([LambdaANF_Wasm_related]), plus the restrictions above. *)
Definition llvm_restricted (cenv : ctor_env) (e : cps.exp) : Prop :=
  (exists fds main, e = Efun fds main /\ fundefs_ok fds /\ body_ok main) /\
  (~ exists x, occurs_free e x) /\
  unique_bindings e /\
  cenv_ok cenv /\
  (forall x t ys e', subterm_or_eq (Econstr x t ys e') e ->
     tag_ok cenv t /\ arity_of cenv t = N.of_nat (length ys)) /\
  (forall x bs t e', subterm_or_eq (Ecase x bs) e -> In (t, e') bs -> tag_ok cenv t) /\
  (forall x t n y e', subterm_or_eq (Eproj x t n y e') e ->
     (n < arity_of cenv t)%N).

Definition top_fds (e : cps.exp) : fundefs :=
  match e with Efun fds _ => fds | _ => Fnil end.

(* ------------------------------------------------------------------ *)
(** ** The theorem *)

Theorem LambdaANF_to_LLVM_correct :
  forall (cenv : ctor_env) (pfs : prims) prim_of
         (heap_inv : state -> ptr -> Prop)
         (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
         (e : cps.exp) (v : cps.val) (n : nat),
    runtime_correct cenv (top_fds e) heap_inv gc make_tinfo ->
    llvm_restricted cenv e ->
    bstep_e pfs cenv (M.empty _) e v n ->
    ends_in_oom (run_program gc make_tinfo (emitted cenv prim_of e))
    \/ exists st ls genv z,
        returns (run_program gc make_tinfo (emitted cenv prim_of e))
                ((st, (ls, genv)), I64 z) /\
        repr_val cenv (top_fds e) genv st v z.
Admitted.

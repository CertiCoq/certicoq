# Correctness of the LambdaANF → LLVM (Vellvm VIR) backend

This branch builds on CertiRocq PR #155 (`vir-llvm-backend`), which adds a
LambdaANF → LLVM backend emitting Vellvm's VIR AST. The correctness theorem
shipped with that PR is vacuous: it rests on an axiom `refinement_runs` that
states the result, and on an abstract `Eval_to` unrelated to Vellvm's
semantics. This branch replaces it with a real statement against Vellvm's
executable semantics and proves it: `LambdaANF_to_LLVM_correct` in
`theories/CodegenLLVM/LLVM_sim_exp.v` is closed (Qed) and depends only on
standard-library axioms (see below).

## The statement

`theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v`, definition
`LambdaANF_to_LLVM_correct_statement : Prop`. `LLVM_toplevel_link.v` proves
`main_correct_of_sim : sim_exp_statement -> LambdaANF_to_LLVM_correct_statement`
(Qed, standard library axioms only), where `sim_exp_statement` is the
explicit statement of the main simulation lemma `sim_exp`.
`LLVM_sim_exp.v` proves `sim_exp` by induction on `bstep_e` from the cases in
`LLVM_sim_cases_*.v` (`sim_exp_proof : sim_exp_statement`) and states

    Theorem LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement.
    Proof. exact (LLVM_toplevel_link.main_correct_of_sim sim_exp_proof). Qed.

`Print Assumptions LambdaANF_to_LLVM_correct` (Rocq 9.1) lists only
standard-library axioms and primitive types: `Classical_Prop.classic`,
`functional_extensionality_dep`, `proof_irrelevance`,
`Eqdep.Eq_rect_eq.eq_rect_eq`, `ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`, and the primitives `PrimInt63.int`,
`PrimInt63.lsr`, `PrimInt63.land`, `PrimInt63.eqb`, `PrimFloat.float`,
`PrimString.string` (verbatim output at the end of `LLVM_sim_exp.v`). No
`Admitted`, no `Axiom`, no section hypothesis remains. (Up to commit
16a4e20c, `sim_exp` was an `Admitted` lemma in `LLVM_sim.v` and the theorem
was at the end of `LLVM_toplevel_link.v`; both were removed when the
statement fixes 2a, 2b, 3a and 4a below were made.)

- **Program.** The code the pipeline emits, `flatten_prog (compile_prog …)`, is
  linked with a runtime prelude, converted (`convert_types`), and run with
  Vellvm's `interp_mcfg`. The memory model is Vellvm's concrete model with
  64-bit finite pointers (`ParamsV IP64Bit`).
- **Conclusion.** Either the run ends in out-of-memory, or it returns
  (`eutt Ret`) a word that represents the source value in the final memory.
  The representation follows the C runtime's ABI from `values.h`; a boxed
  object's pointer is word-aligned (the emitted code tells boxed from
  unboxed values by the low bit).
- **Assumptions.**
  - Only the runtime is assumed: the garbage collector and the `thread_info`
    set-up, which are linked as Vellvm library functions. Their specification
    (`runtime_correct`) is concrete. The runtime chooses a heap invariant
    `heap_inv`. A runtime state is well-formed (`rt_ok st tinfo fp rs`) when
    `heap_inv` holds, `thread_info` is well-formed (`tinfo_ok`: its fields
    are writable heap words, and the nursery `[alloc, limit)` is a writable
    heap region with both ends word-aligned), the memory is well-formed
    (`mem_ok_stmt`: heap addresses are allocated, stack-frame addresses are
    not heap addresses), the nursery does not overlap `thread_info`, and
    `fp` heads a shadow stack with root slots `rs`. `runtime_correct` has
    three clauses:
    1. `make_tinfo` runs out of memory, or returns a `thread_info` pointer
       in a well-formed state with an empty shadow stack (`fp = 0`), and
       `thread_info` (8232 bytes) fits in the 64-bit address space.
    2. Everything the generated code does to the heap preserves `heap_inv`:
       writing the nursery and the `alloc`/`fp`/`nalloc` fields, moving
       `alloc` forward within the nursery, word-aligned.
    3. The collector, called in a well-formed state whose roots represent
       values `vs`, with a request for `nalloc` words, `0 <= nalloc < 2^61`
       (the stored 64-bit word only determines `nalloc` modulo 2^64; the
       emitted code requests small constants), runs out of memory or
       returns with the state well-formed again (same `fp`, same root
       slots), the roots representing the same `vs`, `nalloc` words of
       room, and the memory frames unchanged (locals and globals are
       untouched by the signature). Moreover, outside the heap it only writes the root slots
       (a copying collector updates the roots and nothing else on the stack),
       every newly created heap address was unallocated before (new
       to-spaces are fresh `malloc`'d blocks), and the root slots keep their
       Vellvm allocation ids (the collector overwrites them in place; the
       generated code reloads them through the pointer it `alloca`'d). The
       collector may free heap blocks (a copying collector frees its
       from-space): nothing is said about the allocation ids of heap bytes.
  - The source program `Efun fds main` must satisfy
    `llvm_restricted cenv fds main`: `fds` and `main` are `body_ok`
    (no nested `Efun`, no `Eprim`, only integer primitive values;
    constructor tags are in `cenv` with ordinal below 251 and matching
    arity; every allocation chunk, the words requested by one limit check,
    is below 2^64 bytes, as the limit check computes `8 * chunk_words` in
    64-bit arithmetic), the program is closed with unique bindings, and
    `cenv_ok`: two distinct constructors of one inductive with the same
    ordinal are one nullary and one boxed. (Until 2026-10-08 this was the
    Wasm backend's `cenv_restricted` verbatim, whose second clause forbids
    a boxed constructor from sharing its ordinal with *any* other
    constructor. The pipeline, `LambdaBoxLocal_to_LambdaANF.convert_cnstrs`,
    numbers nullary and boxed constructors with two counters both starting
    at 0, so `O` and `S` share ordinal 0 and the hypothesis was
    unsatisfiable for every inductive with both kinds; the theorem was
    vacuous for programs using `nat`, `list` or `option`. The Wasm
    backend's `toplevel_theorem.v` still has that hypothesis.
    `LLVM_nonvacuity.nat_cenv_ok` is the witness that the fixed condition
    holds for a `nat`-shaped environment.)
    No condition on `Eproj` indices is needed: the proof never used the
    former one (an out-of-range projection does not evaluate).
- **Not covered.** Divergence: the theorem is about terminating source runs.

The statement was reviewed three times for vacuity and falsity; the issues
found were fixed (last: the unsatisfiable `cenv_ok`, found 2026-10-08 while
compacting the statement file).

## Runtime contract checking (dynamic)

`tests/llvm/` runs compiled programs end to end against the real C runtime
(`CertiRocq Compile LLVM`, a C driver printing the result as an
S-expression, compared with Rocq's `vm_compute`), also under ASan/UBSan.
`tests/llvm-corpus/` adds GC-stressing programs and
`runtime/gc_stack_checked.c`, a wrapper around the real collector that
asserts the clauses of `runtime_correct` at every collection
(`CONTRACT.md` maps clauses to checks). Findings so far (2026-10-07):

- Boxed constructor ordinals whose low byte is >= 251 are never scanned by
  the collector (`No_scan_tag`); `tag_ok` now requires ordinals < 251, so
  such programs are outside `llvm_restricted`. The C backend has the same
  latent assumption.
- A single allocation chunk larger than the nursery (2^16 words) makes the
  runtime `exit(1)` ("Nursery is too small"), which is neither `room` nor
  `ends_in_oom`. Open decision: bound `chunk_words` by the nursery size in
  `llvm_restricted` (ties the statement to a runtime constant), split
  chunks in the emitter, or let the runtime grow the nursery.
- Tail calls are not eliminated by the emitter, so tail-recursive loops use
  machine stack proportional to their length; the harness runs programs on
  a large thread stack. The Vellvm semantics has an unbounded stack.
- `prim_int63.c` compared tagged words signed in `ltb`/`leb` (Rocq's are
  unsigned), so `max_int <? max_int + 1` was true (corpus c12). Fixed in
  `runtime/prim_int63.c`; the C backend linked the same code.
- Allocating PrimInt63 primitives (`addc`, `mulc`, ...) call the collector
  from C without the caller's live values registered as roots (corpus c13,
  wrong result). This is outside the theorem (`body_ok` excludes `Eprim`);
  the emitter needs a safepoint around allocating primitives before such
  programs can be covered.

Results (2026-10-08, `tests/llvm/RESULTS.md`): the 9 end-to-end tests pass in
all 7 modes (plain, forced final GC, ASan+UBSan, -O2, contract-checked,
ASan+checked, checked with a 2^13-word nursery), with up to 1343 real
collections per run; 14 of the 17 corpus programs pass in all modes; the
three failures are the two runtime gaps above (c07, c15) and the
out-of-theorem c13. No ASan/UBSan report anywhere.

## Non-vacuity

`theories/CodegenLLVM/LLVM_nonvacuity.v` and
`theories/CodegenLLVM/LLVM_nonvacuity_run.v`. The conclusion of the theorem is
"out of memory, or returns a word representing the value", so the theorem is
trivially true whenever the run is guaranteed to run out of memory, and
vacuous when its hypotheses cannot hold. The hypotheses that matter:

- `runtime_correct`, first clause. It allows `make_tinfo` to run out of
  memory. A `make_tinfo` that always does satisfies `runtime_correct` and
  makes every instance of the conclusion true through its OOM disjunct
  (`oom_runtime_correct`, `oom_runtime_vacuous`). The theorem is only
  informative for runtimes taking the `returns` branch. The witness
  `nv_make_tinfo` does: it `malloc`s (Vellvm's `malloc` intrinsic) a
  16432-byte block at address 0, places `thread_info` at address 8 and a
  1024-word nursery at 8240..16432, and stores `alloc`, `limit` and a null
  `fp`. `nv_make_tinfo_returns` proves the whole `returns` branch:
  `tinfo_ok`, empty shadow stack, `mem_ok_stmt`,
  `nursery_tinfo_disjoint_stmt` and the address bound.
  `nv_make_tinfo_not_oom` proves that it does not run out of memory.
- `runtime_correct`, second clause (`heap_inv` preserved by the mutator).
  It is met trivially by `heap_inv := True`. That is the right witness: the
  clause only constrains the runtime's own choice of invariant.
- `runtime_correct`, third clause (the collector). OOM is an allowed
  outcome. The witness `nv_gc` always runs out of memory, so with the
  witness runtime the theorem only says something about runs that never
  call the collector: programs that allocate at most 1024 words in total,
  headers included. A returning collector also meets the clause, since 4a is
  fixed (`nalloc` is bounded, so `room st' tinfo nalloc` is satisfiable)
  and the clause no longer forbids freeing from-space. `nv_gc_check` is
  such a collector: it loads `alloc`, `limit` and `nalloc` from
  `thread_info`; if `limit - alloc >= 8 * nalloc` (integer addresses,
  unsigned value of the `nalloc` word) it returns `inr DVALUE_None` without
  touching memory, and otherwise it runs out of memory.
  `nv_gc_check_run` symbolically runs the three loads and the comparison
  (`room` holds because the word read is `nalloc` by the bound, and the
  branch condition gives the inequality), and
  `nv_runtime_correct_check : runtime_correct cenv fds nv_heap_inv
  nv_gc_check nv_make_tinfo` takes `st' = st`, so every frame clause is
  trivial. This is not a model of CertiRocq's collector, which moves objects
  and updates the roots. It only shows that the contract admits a collector
  that returns. (Before the fix, `runtime_correct_gc_oom` proved that every
  conforming collector runs out of memory; it was deleted with the fix.)
- `llvm_restricted` and `bstep_e`. Both hold for
  `Efun Fnil (Econstr x C [] (Ehalt x))` with a one-constructor `cenv`
  (`ex_restricted`, `ex_eval`). `ex_hypotheses` collects all three
  hypotheses for this program and the witness runtime. `ex_correct`
  instantiates the proved theorem `LambdaANF_to_LLVM_correct`
  (unconditionally; standard-library axioms only): the compiled program runs
  out of memory or returns `1` (the encoding `0 * 2 + 1` of the nullary
  constructor).
  `LLVM_nonvacuity_run.v` proves that it returns `1` (`ex_returns`), so
  the OOM disjunct does not hold (`ex_not_oom`). The proof symbolically runs
  the whole program in Vellvm's concrete memory model (`ex_whole_runs`, for
  any collector, since the program never calls it). The steps are
  `nv_make_tinfo`, global initialisation (one 8-byte `alloca` per declared
  name), `push_call_frame` (a `mem_push` and a 0-byte varargs `alloca`),
  the single block `%-6 = shl 0, 1; %1 = or %-6, 1; ret %1` (a nullary
  constructor allocates nothing and needs no shadow-stack frame), and
  `pop_call_frame`. In the concrete model an allocation only runs out of
  memory when the next free address plus the size reaches `2^64`
  (`allocate_dtyp_exists`). The proof tracks an upper bound on the
  allocated addresses (`keys_below`; `blk_ok` records that the `malloc`'d
  block is the only allocated memory after `nv_make_tinfo`). The bound
  stays below `16432 + 32`. `G_ok` for the resulting global environment
  comes from the general `global_init`, because a run cannot also end in
  OOM (`truns_not_toom`, `truns_det`).

## Changes to the emitter (relative to PR #155)

- `LambdaANF_to_LLVM.v`, `Construct_lemmas.v`: `Ptrtoint`/`Inttoptr` are
  wrapped in `CONV_Impure`, as required by the current Vellvm AST.
- `LambdaANF_to_LLVM.v`, `Flatten.v`: generated local names are disjoint by
  construction. `ntmp` uses `-(4n)`, `ssname` uses `-(4n+1)` with Cantor
  pairing, and `flat_id` uses `-(4n+2)`. Before, they could collide in very
  large functions.

## Proof status (`theories/CodegenLLVM/`)

| File | Status |
|---|---|
| `LambdaANF_to_LLVM_statement.v` | statement only (`LambdaANF_to_LLVM_correct_statement`); no proofs. Compacted 2026-10-08: the runtime's well-formed state is one predicate `rt_ok` shared by the three clauses of `runtime_correct`; `body_ok cenv` carries the per-constructor conditions (`tag_ok`, arity, chunk bound) instead of four `subterm_or_eq` clauses, and the unused `Eproj` index bound is gone; `llvm_restricted cenv fds main` takes the program's parts, so `top_fds` is gone. `Repr_boxed` requires a word-aligned object pointer; `tinfo_ok` requires a word-aligned `limit`; `runtime_correct` includes memory well-formedness (`mem_ok_stmt`), nursery/`thread_info` disjointness and the address-space bound for `thread_info`, a bound `0 <= nalloc < 2^61` on the collector's request, and the collector's frame conditions (only heap and root slots written, new heap blocks fresh, root slots keep their allocation ids; heap blocks may be freed); `llvm_restricted` bounds every allocation chunk below 2^64 bytes. `mem_ok_stmt`, `in_frames_stmt`, `frames_ptrs_stmt`, `nursery_tinfo_disjoint_stmt`, `slot_bytes_stmt` are copies of the `LLVM_sim.v` definitions without the suffix (equivalence proved in `LLVM_toplevel_link.v`) |
| `LLVM_interp_lemmas.v` | done (Qed): algebra of `interp_mcfg`, memory/local/global event lemmas |
| `LLVM_call_lemmas.v` | done (Qed): call knot (`interp_mrec`), runtime library calls, OOM propagation |
| `LLVM_convert.v` | done (Qed): `convert_types` on the emitted program |
| `LLVM_exp_lemmas.v` | done (Qed): integer arithmetic, pointer conversions, GEP, `exp_eval` for every expression form the emitter produces |
| `LLVM_mem_lemmas.v` | done (Qed): Vellvm's concrete memory model: reads, writes, frame lemmas, `alloca`, memory frame push/pop |
| `LLVM_emit_syntax.v` | done (Qed): shape equations of `translate_cfg`, label/name discipline (`cfg_ok`), `compile_prog` structure |
| `LLVM_emit_facts.v` | done (Qed): type-conversion equations for the emitter helpers (`store_fields`, `spill_code`, `reload_code`, phis, `call_args`, `header_word`) |
| `LLVM_sim.v` | definitions: invariant (`INV`, `env_rel`, `stable_repr`, `stack_ok`, `mem_ok`), the step relation `mstep`, and their preservation lemmas (`INV_mstep`, `INV_link`, `INV_gc`, `stable_repr_boxed`, `env_rel_bind`, ...) — Qed; object-byte protection derived from `stable_repr` (`stable_repr_protect/header/field`); `flatB` is `Flatten_sem.flat_blockP`; the call knot `ctx_fun`/`ctx_gc` is specified by address (any pointer with the function's address, any call type, `≈`); jump lemma `denote_ocfg_jump`; `env_rel` invariant under flat-name writes; `stable_repr_even` (boxed values are even words). The frame condition `keeps_stack st st' rs` (allocated non-heap bytes stay allocated and non-heap, keep their contents outside the root slots `rs`, and keep their allocation ids) with `keeps_stack_refl/trans/mstep/gc/slots`. `sim_result` (a function activation's result) has the frame clauses: new memory-frame addresses were not allocated stack bytes before (`~ alloc_nonheap st`), and `keeps_stack`. The simulation statement `sim_stmt` is defined here; the lemma `sim_exp` itself is no longer here (its statement is `LLVM_toplevel_link.sim_exp_statement`; its proof goes into `LLVM_sim_exp.v`) |
| `LLVM_sim_cases_read.v` | done (Qed): the `Ehalt`, `Eproj`, `Eprim_val` and `Ecase` cases of `sim_exp`, as `sim_stmt` implications (`sim_case_halt/proj/prim_val/case`), with no extra premises (`sim_case_case` uses `stable_repr_even`, after 3a). Also `tr_env_ext` (translation depends only on the SSA environment at free and bound variables), `env_restrict` and the restriction lemmas used to pass `env_ok` to a continuation with fewer live variables |
| `LLVM_sim_cases_constr.v` | done (Qed; standard-library axioms only, no extra hypotheses): the `Econstr` case (`sim_case_constr`: nullary, chunk member, chunk head with limit check, allocation fast path and the spill/`garbage_collect`/reload path), under the common section hypotheses of `LLVM_sim.Simulation` (`Hmut`, the new `Hgc`, `Htinfo_range`, `ctx_gc`, `G_funs`, `G_gc`, `Hprog`). The frame relation `fext rs st st1` is the new `sim_result` frame clause plus `LLVM_sim.keeps_stack st st1 rs`; the reload after the collection reads root-slot bytes, whose allocation ids the collector keeps (2a); the `nalloc` bound and the limit-check arithmetic come from the chunk-size clause of `llvm_restricted` (`prog_chunk_small`, 2b) |
| `LLVM_sim_cases_call.v` | done (Qed) against the current statement: `Efun` (vacuous under `body_ok`), `Eapp` and `Eletapp`. The cases are proved for a variant `sim_stmt_fr` that differs from `sim_stmt` only by the weaker environment premise `env_ok2` (`env_ok` is not preserved by safepoints); `sim_stmt_fr_weaken` and `sim_stmt_fr_of_sim_stmt` (restriction of the SSA environment to the live variables, `LLVM_sim_cases_read.env_restrict`) make the two interchangeable. The result is `LLVM_sim.sim_result` with its frame condition `LLVM_sim.keeps_stack`. For the assembly: `sim_case_fun`, `sim_case_app`, `sim_case_letapp` in `sim_stmt` form, with the premises of `BStep_fun`/`BStep_app`/`BStep_letapp`. No extra hypotheses beyond the context of `LLVM_sim.Simulation` |
| `Flatten_sem.v` | done (Qed): semantic transport of the flattening pass (`Flatten.v`): atomiser soundness, counter threading (`flat_codeP_app`), block structure (`flat_blockP_spec/prepend`), and transfer lemmas for instructions, calls, terminators and block tails (`flat_tail_instr`, `flat_tail_call`, `flat_tail_term`, `flat_block_tail`, with OOM variants) up to `agree_except` on the fresh `flat_id` names |
| `LLVM_instr_lemmas.v` | done (Qed): execution lemmas (`runs`/`oom`) for every instruction, terminator and phi form the emitter produces, including `alloca` (`instr_alloca_*`, `alloc_post`), calls, `run_exc` commutation, function entry/exit (`push_call_frame_cases`, `pop_call_frame_runs`, `denote_function_runs`, OOM variants), and the straight-line helper sequences (`store_fields_run`, `spill_code_run`, `reload_code_run`). Known gap: no `writable_word` lemma for the slots of a fresh `alloca` (only per-byte `writable_at`) |
| `LLVM_toplevel_link.v` | done (Qed): from Vellvm's top level (`run_program`: runtime set-up, `build_global_environment`, the `denote_mcfg` call knot, `@certirocq_main`) to `LLVM_sim`'s section hypotheses; global initialisation (`alloc_decls_spec`), the knot (`ctx_real_fun`, `ctx_real_gc`), the entry invariant (`INV0`), the activation of `@certirocq_main` (`main_activation`); `runtime_extra_of_correct` derives `LLVM_sim`'s runtime hypotheses (`Hgc`, `Htinfo_range`, entry `mem_ok`/disjointness) from `runtime_correct`; the explicit `sim_exp_statement` (the statement of the main simulation lemma with all section hypotheses of `LLVM_sim.Simulation`); and `main_correct_of_sim : sim_exp_statement -> LambdaANF_to_LLVM_correct_statement`. The top-level theorem moves to `LLVM_sim_exp.v` |
| `LLVM_nonvacuity.v` | done (Qed; standard-library axioms only): a concrete runtime (`nv_make_tinfo` mallocs one block holding `thread_info` and a 1024-word nursery and stores `alloc`/`limit`/null `fp`; `nv_gc` always reports OOM; `nv_heap_inv := True`) satisfies `runtime_correct` (`nv_runtime_correct`) via the `returns` branch of the first clause (`nv_make_tinfo_returns`, `nv_make_tinfo_not_oom`); a returning collector `nv_gc_check` (returns unchanged if the nursery has `nalloc` free words, OOM otherwise) also satisfies it (`nv_gc_check_run`, `nv_runtime_correct_check`); the program `Efun Fnil (Econstr x C [] (Ehalt x))` satisfies all hypotheses of the theorem (`ex_hypotheses`), and the proved theorem `LambdaANF_to_LLVM_correct` then gives "OOM or returns 1" (`ex_correct`); `oom_runtime_correct`/`oom_runtime_vacuous`: the vacuous OOM instance |
| `LLVM_nonvacuity_run.v` | done (Qed; standard-library axioms only): symbolic run of the compiled example program in the concrete memory model (`ex_whole_runs`); it returns `1` (`ex_returns`) and does not run out of memory (`ex_not_oom`); helpers: `allocate_dtyp_exists` (allocation succeeds below `2^64`), `keys_below`/`next_key_bound`/`alloc_keys`, `alloc_decls_runs`, `push_call_frame_runs_keys`, `truns_det`, `truns_not_toom` |
| `LLVM_sim_exp.v` | done (Qed; standard-library axioms only): `sim_exp` by induction on `bstep_e`, each case one of the case lemmas (`Eprim` vacuous by `body_ok`), in a Section re-declaring `LLVM_sim.Simulation`'s context (`Proof using All`, so the closed lemma is exactly `sim_exp_statement`); `sim_exp_proof : LLVM_toplevel_link.sim_exp_statement`; the top-level theorem `LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement`, with its `Print Assumptions` output recorded |
| `MemoryLaws.v`, `LambdaANF_to_LLVM_correct_v3.v`, `Construct_lemmas.v`, `Flatten_correct.v`, `Instantiate_compile.v` | PR #155's old proofs; vacuous and broken against current Vellvm; not in `_CoqProject` |

### Architecture of the proof

The main lemma (`sim_exp`, statement `LLVM_toplevel_link.sim_exp_statement`,
simulation relation `LLVM_sim.sim_stmt`) is proved by induction on the
source big-step relation `bstep_e`.  It symbolically executes the code the
pipeline really emits: the *flattened*, type-converted blocks
`flat_blockP (cblock b) c`, under `interp_mcfg (interp_mrec ctx _)` where
`ctx` is Vellvm's call knot.  There is no separate (coinductive) simulation
between the flattened and unflattened programs through the call knot:
flattening is transported segment by segment inside the induction
(`Flatten_sem.v` proves that the flattening of a call-free code segment
behaves like the original up to the extra `flat_id` locals; a call
instruction is handled directly after evaluating its atomised operands).

The lemma speaks about the *tail* of the entry block of `translate_cfg e`
(its code and terminator, continued in the enclosing function's CFG `B`), and
assumes only that the other blocks of the translation are in `B` in flattened
form.  This makes `prepend_code` (straight-line constructs consing code onto
the continuation's entry block) compositional: the caller of the induction
hypothesis has already executed the prefix.

The invariant threaded through the induction (`LLVM_sim.v`):

- `INV st fp rs vs`: the runtime's heap invariant, a well-formed
  `thread_info`, memory well-formedness, the current shadow-stack frame `fp`
  with root slots `rs` representing `vs`, and the fact that shadow-stack frames
  and slots live in (allocated, non-heap) stack memory;
- `env_rel S rho env sf st`: every live source variable in `S` is either a
  top-level function (a global) or held in the local `env x` as a word that
  *stably* represents its value (`stable_repr`: the representation survives
  any later change of the nursery and of `thread_info`);
- `room st tinfo chunk`: the chunk head's limit check covers the
  allocations of the chunk members.

Calls (`Eapp`, `Eletapp`) use the induction hypothesis for the callee's body,
wrapped in Vellvm's `push_call_frame`/`pop_call_frame`; the result of a
function activation is "out of memory, or a word stably representing the
value, with `INV` re-established, the memory frames only extended (by
addresses that were not allocated stack memory before) and the caller's
stack kept (`keeps_stack`)".

Remaining steps:

1. Done: `Flatten_sem.v` and `LLVM_instr_lemmas.v`.
2. Done. The cases of `sim_exp`: `Ehalt`, `Eproj`, `Eprim_val`, `Ecase`
   (`LLVM_sim_cases_read.v`), `Econstr` (`LLVM_sim_cases_constr.v`),
   `Eapp`/`Eletapp`/`Efun` (`LLVM_sim_cases_call.v`), all against the
   current statement; `LLVM_sim_exp.v` assembles `sim_exp` (induction on
   `bstep_e`), proves `sim_exp_statement` and states
   `Theorem LambdaANF_to_LLVM_correct` (`main_correct_of_sim sim_exp_proof`).
2c. Done. `LLVM_sim.sim_result` has the frame condition `keeps_stack` (the
   caller's allocated non-heap bytes stay allocated and non-heap, keep their
   contents outside the root slots, and keep their allocation ids; nothing
   is said about heap bytes), and `tinfo_ok` keeps the nursery `limit`
   word-aligned (so `Hlimit_aligned` is gone). `env_ok` stays in
   `LLVM_sim.sim_stmt`; the call file keeps its `sim_stmt_fr` (with
   `env_ok2`) locally and bridges `sim_stmt -> sim_stmt_fr`
   (`sim_stmt_fr_of_sim_stmt`) with the environment-restriction lemmas of
   the read file. `LLVM_sim_cases_call.v` uses `LLVM_sim.keeps_stack` and
   `LLVM_sim.sim_result` (`sim_result_fr` is a notation for it), mirrors the
   new `Hgc`, and `INV_pop`/`callee_run` work with the weakened freshness
   clause (`~ alloc_nonheap st`).
2a. Done. The collector clause of `runtime_correct` says that the root
   slots keep their allocation ids (so the reload through the `alloca`'d
   root array is defined), and `sim_result`'s freshness clause only asks
   new memory-frame addresses not to be allocated stack bytes in the
   pre-call state (`~ alloc_nonheap st`), so the collector may free
   from-space. In `LLVM_sim_cases_constr.v`, `Hgc_aid` is gone: `fext`
   carries `keeps_stack` (lemmas `fext_refl/trans/trans_slots`,
   `fext_of_mstep`, `fext_mstep_empty`, `sim_result_ext`), the collector's
   step is `keeps_stack_gc`, and the reload reads are shown to hit
   root-slot bytes (`slot_bytes (rs1 ++ rs)`), whose ids the new `Hgc`
   clause keeps; the inner activation's slots `rs1` are fresh in the
   pre-state by the `alloca`'s `alloc_post` (`fext_trans_slots`).
2b. Done. `body_ok` requires, at every `Econstr x t ys e'`,
   `8 * chunk_words (Econstr x t ys e') < 2^64` (until 2026-10-08 an eighth
   clause of `llvm_restricted` quantifying over subterms; the constructor
   conditions now live in `body_ok`, and `LLVM_sim.prog_body_ok` recovers
   them for any subterm of the program).
   `LLVM_sim_cases_constr.prog_chunk_small` derives the former
   `Hchunk_small` from it; it gives the limit-check arithmetic in
   `sim_case_constr_head` and the `nalloc < 2^61` premise of `Hgc` in
   `gc_path_sim`/`gc_reload_fgoal`.
3. Done (`LLVM_toplevel_link.v`): global initialisation, the call knot of
   `denote_mcfg`, the `certirocq_main` entry point, and the strengthened
   `runtime_correct`.
3a. Done: `Repr_boxed` requires the object pointer to be word-aligned
   (`ptr_to_int p mod 8 = 0`); `LLVM_sim.stable_repr_boxed` has a matching
   premise, and `LLVM_sim.stable_repr_even` gives `sim_case_case` its
   former premise `Heven`.
4. Done (`LLVM_nonvacuity.v`, `LLVM_nonvacuity_run.v`): non-vacuity check;
   see "Non-vacuity" above.
4a. Done: the collector clause of `runtime_correct` has the premise
   `0 <= nalloc < 2^61`, so a returning collector can provide
   `room st' tinfo nalloc`; `runtime_correct_gc_oom` (which showed that
   every conforming collector had to run out of memory) is deleted.

What is left (none of it needed for the theorem):

- Non-vacuity for programs that call the collector, end to end. The
  returning collector witness `nv_gc_check` exists, but no example program
  that calls the collector has been run to its result.
- `theories/CodegenLLVM/LLIR/` (`LambdaANF_to_LLIR.v`, `LambdaANF_to_LLIR_correct.v`, with
  its own `_CoqProject`) is not in the build.
- PR #155's old proof files (`MemoryLaws.v`, `LambdaANF_to_LLVM_correct_v3.v`,
  `Construct_lemmas.v`, `Flatten_correct.v`, `Instantiate_compile.v`) are
  vacuous/broken against current Vellvm and not in `_CoqProject`; they can
  be deleted.
- The rest of CertiRocq (plugins, extraction, benchmarks) was not built on
  this branch.

## Reproducing the build

### 1. Rocq and OCaml packages (opam)

The authoritative description is the frozen switch export
`opam-llvm-proof.export`. Every `dev` package in it is pinned to a commit. To
recreate the switch:

```sh
opam repo add rocq-released  https://rocq-prover.org/opam/released
opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
opam switch import opam-llvm-proof.export --switch llvm-proof   # creates/fills the switch
eval $(opam env --switch=llvm-proof --set-switch)
```

Caveat (2026-10-07): the export does not import verbatim. Its root
`coq-paramcoq.dev` requires `coq >= dev`, so the solver fails. Remove
`coq-paramcoq` and `rocq-verified-extraction` from the export first; neither
is needed here. Alternatively, any switch with Rocq 9.1.0, MetaRocq
1.5.1+9.1, CompCert, ext-lib and Equations only needs `coq-paco.4.2.3` and
`coq-itree.5.2.1` added, then Vellvm from source (step 2). `coq-wasm` is
only needed for `toplevel.v`, not for the proof files.

The packages that matter, and their versions:

| package | version |
|---|---|
| ocaml-variants | 4.14.2+options, with ocaml-option-flambda |
| rocq-core / coq-core | 9.1.0 |
| rocq-stdlib | 9.0.0 |
| coq-compcert | 3.17 |
| coq-flocq | 4.2.2 |
| menhir / coq-menhirlib | 20260209 (CompCert excludes menhir `dev`) |
| rocq-equations | 1.3.1+9.1 |
| rocq-metarocq-* (utils, common, template, pcuic, safechecker, erasure, erasure-plugin) | 1.5.1+9.1 |
| coq-ext-lib | dev @ `ddd03d257f6b85a93bfaa0ed4d03658e0ddf5075` |
| coq-wasm | 2.2.0 (needs coq-mathcomp-ssreflect 2.4.0, wasm 2.0.2, rocq-parseque dev @ `cfe2af79e780e57e9c69b806b140fd55b36ab2f9`) |
| rocq-hierarchy-builder | dev @ `3d40146ac85032f870f4d74729ee4414e609da0d` |
| coq-paco | 4.2.3 |
| coq-itree | 5.2.1 |

The export also contains packages from the switch that this build does not
need (e.g. `rocq-verified-extraction`, which is how MetaRocq was installed).

### 2. Vellvm (from source)

Vellvm is the git submodule `vellvm/`, pinned to commit `b63a28a0`
(Vellvm `3.0.20260707-147-gb63a28a0`). It must be built from source. The
emitter needs the current AST, where `Ptrtoint`/`Inttoptr` are
`CONV_Impure`. The proof needs `Semantics/TopLevel.v` and
`Theory/I2F/*`, which were absent from Vellvm between 2026-05-11 and late July
2026.

Install it with `make`, not with opam. Its opam file requires
`coq-ext-lib < 0.14`, but the switch has ext-lib `dev`, and changing ext-lib
would force a MetaRocq rebuild. Vellvm builds fine against ext-lib `dev`.

```sh
git submodule update --init vellvm
make -C vellvm/src rocq      # the Rocq library only; no extraction/executable
make -C vellvm/src install   # installs Vellvm into the current switch
```

### 3. CertiRocq theories, up to the LLVM backend and its proof

```sh
make theories/Makefile libraries/Makefile
make -C libraries
make -C theories CodegenLLVM/LLVM_sim_exp.vo CodegenLLVM/LLVM_nonvacuity_run.vo
# plus CodegenLLVM/toplevel.vo if coq-wasm is installed
```

All the `CodegenLLVM` files listed in `_CoqProject` were rebuilt from a fresh
clone on 2026-10-07, both in a freshly imported `llvm-proof` switch (export
trimmed as in the caveat of step 1) and in an existing Rocq 9.1 switch with
paco/itree added, with Vellvm `b63a28a0` built from the submodule each time.
Note that the Vellvm `make install` writes to the switch whose `rocq` ran
`rocq makefile`; do not reuse a `RocqMakefile.conf` across switches. The rest of
CertiRocq (plugins, extraction, benchmarks) was not built on this branch.

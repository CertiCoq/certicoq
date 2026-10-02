# Correctness of the LambdaANF → LLVM (Vellvm VIR) backend — work in progress

This branch builds on CertiRocq PR #155 (`vir-llvm-backend`), which adds a
LambdaANF → LLVM backend emitting Vellvm's VIR AST. The correctness theorem
shipped with that PR is vacuous: it rests on an axiom `refinement_runs` that
states the result, and on an abstract `Eval_to` unrelated to Vellvm's
semantics. This branch replaces it with a real statement against Vellvm's
executable semantics and starts its proof.

## The statement

`theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v`, theorem
`LambdaANF_to_LLVM_correct` (currently `Admitted`):

- **Program.** The code the pipeline emits, `flatten_prog (compile_prog …)`, is
  linked with a runtime prelude, converted (`convert_types`), and run with
  Vellvm's `interp_mcfg`. The memory model is Vellvm's concrete model with
  64-bit finite pointers (`ParamsV IP64Bit`).
- **Conclusion.** Either the run ends in out-of-memory, or it returns
  (`eutt Ret`) a word that represents the source value in the final memory.
  The representation follows the C runtime's ABI from `values.h`.
- **Assumptions.**
  - Only the runtime is assumed: the garbage collector and the `thread_info`
    set-up, which are linked as Vellvm library functions. Their specification
    (`runtime_correct`) is concrete. The runtime chooses a heap invariant, and
    the spec states that everything the generated code does to the heap
    preserves it.
  - The source program must satisfy `llvm_restricted`: the same
    constructor-environment conditions as the Wasm backend, and no nested
    `Efun`, no `Eprim`, and only integer primitive values.
- **Not covered.** Divergence: the theorem is about terminating source runs.

The statement was reviewed twice for vacuity and falsity; the issues found
were fixed.

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
| `LambdaANF_to_LLVM_statement.v` | statement; theorem `Admitted` |
| `LLVM_interp_lemmas.v` | done (Qed): algebra of `interp_mcfg`, memory/local/global event lemmas |
| `LLVM_call_lemmas.v` | done (Qed): call knot (`interp_mrec`), runtime library calls, OOM propagation |
| `LLVM_convert.v` | done (Qed): `convert_types` on the emitted program |
| `LLVM_exp_lemmas.v` | compiles, no admits; incomplete (helper agent stopped mid-way) |
| `LLVM_sim.v` | definitions of the simulation invariant; main lemma not yet stated/proved |
| `LLVM_mem_lemmas.v`, `LLVM_emit_syntax.v`, `Flatten_sem.v` | unfinished, **do not compile**, not in `_CoqProject` |
| `MemoryLaws.v`, `LambdaANF_to_LLVM_correct_v3.v`, `Construct_lemmas.v`, `Flatten_correct.v`, `Instantiate_compile.v` | PR #155's old proofs; vacuous and broken against current Vellvm; not in `_CoqProject` |

Plan for the remaining proof:

1. Lemmas for each emitted instruction and expression.
2. The main simulation by induction on `bstep_e`. Calls go through the `mrec`
   knot. The invariant is `INV` + `env_rel` + `stable_repr` in `LLVM_sim.v`.
3. Moving the result from the unflattened code to the flattened code
   (`Flatten_sem.v`).
4. Global initialisation and the `certirocq_main` entry point.
5. A non-vacuity check: a trivial non-moving runtime satisfies
   `runtime_correct`.

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
make -C theories CodegenLLVM/toplevel.vo CodegenLLVM/LLVM_sim.vo CodegenLLVM/LLVM_exp_lemmas.vo CodegenLLVM/LLVM_convert.vo
```

These targets were built in the switch described above. A complete build from
a fresh clone and a freshly imported switch has not been run yet. The rest of
CertiRocq (plugins, extraction, benchmarks) was not built on this branch.

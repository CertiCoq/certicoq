# Task Prompt for Next Agent

## Context

You are continuing work on the CertiRocq compiler. The project is removing two intermediate representations (LambdaBoxMut and LambdaBoxLocal) from the compilation pipeline, going directly from MetaRocq Erasure (`EAst.term`) to LambdaANF.

The new code lives in `theories/LambdaBox_to_LambdaANF/`. Read the CLAUDE.md file at the repo root for build instructions, proof style guidelines, and common pitfalls.

## What Has Been Done

### Fully completed (0 admits):
1. **`fuel_sem.v`** — Big-step resource semantics for EAst.term
2. **`common.v`** — Shared definitions
3. **`ANF.v`** — Monadic ANF conversion + relational spec `anf_cvt_rel`
4. **`anf_util.v`** — Value relations and alpha-equivalence proofs:
   - `anf_val_rel` (value relation with `anf_rel_Con`, `anf_rel_Clos`, `anf_rel_ClosFix`)
   - `anf_cvt_alpha_equiv` — fully proved
   - `anf_cvt_val_alpha_equiv` — fully proved
   - `global_env_rel` — parametric on value relation and kername predicate
   - `cmap_vars_of` — image of kername set under constant map

### Work in progress:
5. **`anf_corresp.v`** — Correspondence proof (monadic ↔ relational):
   - Proved: tRel, tLambda, tLetIn, tApp, tConst (non-prim), tConstruct, tCase, tProj, tPrim, tBox
   - **Blocked on tFix**: MetaRocq's `term_forall_list_ind` gives `P (tLambda na e1)` for fix bodies, but `convert_anf_mfix` calls `convert_anf e1` (the body *under* the lambda). Need `P e1`, not `P (tLambda na e1)`.
   - **Solution decided**: Use well-founded induction on `EInduction.size` (already available in MetaRocq) instead of `term_forall_list_ind`. This gives the IH for ANY strictly smaller term, including `e1`.
   - tConst-prim: no relational constructor for primitive constants exists in `anf_cvt_rel`. Either add one or assume no primitives.
   - Helper lemmas proved: `var_map_correct_*`, `get_named_lst_spec`, `proj_ctx_spec`, `add_fix_names_spec`

6. **`anf_correct.v`** — Main correctness theorem (many admits):
   - `anf_cvt_rel_var_lookup` needs redesign (Disjoint condition with cmap_vars)
   - `anf_cvt_correct` has admits for most cases
   - Context assumptions: `cmap_inj`, `global_env_evaluates`

## What Needs To Be Done

### Immediate (in order of priority):

1. **Fix tFix in `anf_corresp.v`**: Switch from `term_forall_list_ind` to well-founded induction on `EInduction.size`. The old proof (in `theories/LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_corresp.v`) uses `exp_ind_alt_2` which is a mutual induction principle that gives `P e1` for lambda bodies in fix defs. Study the old proof's Fix_e case (around line 471) and branches case (around line 638) for structure.

2. **Handle tConst-prim**: Either add `anf_ConstPrim` constructor to `anf_cvt_rel` in ANF.v, or add a context assumption `forall k, find_prim prims k = None`.

3. **Prove mfix/branches parts of `anf_cvt_sound`**: Currently admitted in `anf_corresp.v`. The mfix part needs the same size-based approach. Branches should be straightforward once the exp part is complete.

4. **Fix `anf_cvt_rel_var_lookup` in `anf_correct.v`**: The current `Disjoint (FromList vn) cmap_vars` condition is wrong — cmap variables CAN appear in `vn` when constants are referenced. The solution is to add a `cmap_env_consistent` invariant that ensures cmap variables in the ANF env map to the correct constant values. Discuss formulation with the user.

5. **Prove `anf_cvt_correct`**: The main correctness theorem. Each case follows the structure: show source evaluation implies target evaluation using the value relation and logical relations.

### Key Technical Details:

- **Old proof reference files** (study these, don't copy blindly):
  - `theories/LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_corresp.v` — old correspondence proof
  - `theories/LambdaANF/LambdaBoxLocal_to_LambdaANF_correct.v` — old correctness proof
  - `theories/LambdaANF/LambdaBoxLocal_to_LambdaANF_util.v` — old utility lemmas + `exp_ind_alt_2`

- **`anf_val_rel` closure constructors** include:
  - `global_env_rel` restricted to `term_global_deps e` (the set of global names referenced by the closure body)
  - `Disjoint _ cmap_vars (x |: (f |: FromList names))` and `Disjoint _ cmap_vars S1`

- **`global_env_rel val_rel D rho`**: for every constant `k` in domain `D` that maps to variable `v` via `cmap`, the ANF env `rho` contains a value at `v` that is related (via `val_rel`) to every possible source evaluation of that constant's body.

- **`wf_glob`** from MetaRocq enforces dependency ordering: each global declaration only references later declarations in the list. This may be needed for the correctness proof.

- **`EInduction.size`** is a `Fixpoint` on `EAst.term` returning `nat`. `EInduction.Wf_size_lt` gives `WellFounded (MR lt size)`. Use `well_founded_induction Wf_size_lt` or Equations' `wf` for size-based induction.

## Rules

1. **Never guess** hypothesis names, lemma existence, or proof claims. Always verify.
2. **Never leave admits**. Every lemma must close with Qed.
3. **Think before writing**: understand the proof before writing tactics.
4. **Study old proofs** for structure and insight, but adapt — don't blindly copy.
5. **Work incrementally**: compile frequently, commit at milestones.
6. **Check with the user** before invasive changes (new context assumptions, restructuring definitions).
7. **Do not commit until work compiles** and represents meaningful progress.
8. **Communicate**: ask questions if anything is unclear, and provide regular updates on progress.
9. **Do not avoid work and difficult cases**: tackle the hard parts head-on.
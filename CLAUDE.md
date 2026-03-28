# CertiRocq — Claude Code Guidelines

## Build

```bash
make -j 10                    # build everything (libraries then theories)
cd theories && make -j 10     # build theories only
```

If `make` fails with "No rule to make target `.Makefile.d'", regenerate:
```bash
cd theories && coq_makefile -f _CoqProject -o Makefile
```

### Reading compilation output
- **Never suppress output** with `grep`, `head`, `tail`, or pipes when debugging errors. These can hide the exact error line, the error message, or the `Show.` output. Always use `make ... 2>&1 | cat` or just `make ...` to see the full output.
- Error messages from Coq include the file, line number, and character range. Always read these to understand where the failure is.

## Rocq/Coq Proof Guidelines

### Never Guess
- **Never guess hypothesis names** after tactics like `inv`, `inversion`, `destruct`. Use `match goal with` patterns or force errors with `exact I` to inspect the actual proof state.
- **Never claim a lemma exists** without searching (use `Grep` or `Search` in Coq).
- **Never claim a hypothesis is sufficient/insufficient** without checking the actual usage.
- **Never claim a proof works without reasoning through the proof structure**.
- **Never copy-paste old proofs without understanding them**.
- **Never use tactics blindly**: always understand what each tactic does and why it is applicable.

### Debugging Tactics
- Use `Set Printing All.` before a failing tactic to see fully explicit terms with all implicit arguments and notations expanded.
- When `eapply` or `apply` fails with unification errors, the printed-all output reveals the actual types.
- **`Show.` to inspect proof state**: Place `Show.` followed by `admit.` at the point you want to inspect. The ENTIRE file must compile (not just up to that point) — `Show.` is a command, not a tactic. ALL goals in the proof must be closed (remaining ones with `admit`, the lemma with `Admitted`). Compile with `make` and read the output. Example:
  ```coq
  - intros. Show. admit.   (* see goal after intros *)
  - admit.                  (* close remaining goals *)
  ...
  Admitted.
  ```
  When compiling to read `Show.` output, do NOT use `grep`, `head`, `tail` or pipes — they can hide the output. Use `make ... 2>&1 | cat` or plain `make`.
- **`inv`/`inversion`/`destruct` on large mutual inductives** (like `anf_cvt_rel`, `eval_env_fuel`) can hang Coq for 54+ minutes. Instead use `remember` + `destruct`:
  ```coq
  remember (EAst.tXxx arg1 arg2) as e_x.
  destruct Hcvt; try discriminate.
  injection Heqe_x as <- <-.
  ```
  WARNING: `injection ... as <- <-` may clear hypotheses. Save critical ones with `rename H into Hsaved` BEFORE injection.

### Proof Style
- **Think before writing**: understand the proof structure before writing tactics. Don't blindly copy old proofs — understand then adapt.
- **No admits**: every proof must close with `Qed`, not `Admitted`.
- **Comments above bullets**, not next to them. Do not overcomment, but comment when necessary.
- **Section Context** hypotheses at the very top of the section, grouped together with comments.
- When studying old proofs: understand the induction structure, what each IH gives, and what the relational spec expects BEFORE writing scripts.

### Common Pitfalls in This Codebase
- `Disjoint` is `Inductive`: use `constructor; intros z Hc; inversion Hc; ...`, not `intros z [Ha Hb]`.
- `Singleton` is inductive with `In_singleton`: use `inv` after inversion.
- `all:` crosses bullet boundaries — use explicit bullets instead of `all: admit`.
- `pre_curry_l` can only extract `Prop` conjuncts from Hoare triple preconditions. State-dependent facts need `pre_strenghtening`.
- `FromList_rev` is in `LambdaBoxLocal_to_LambdaANF_util.v` (not always imported). Use `unfold FromList, In; rewrite <- in_rev` instead.
- `Same_set_all_fun_name` returns a conjunction. Use `apply (proj1 ...)` or `apply (proj2 ...)`.
- MetaRocq's `term_forall_list_ind` for `tFix` gives `All (fun d => P (dbody d)) m`, which provides `P (tLambda na e1)` but NOT `P e1`. For proofs that need `P e1` (like mfix correspondence), use well-founded induction on `EInduction.size` or a custom induction principle.

### Hoare Triple Reasoning (`compM` monad)
Key combinators:
- `bind_triple`: sequence two monadic computations
- `return_triple`: pure return
- `pre_curry_l`: extract a `Prop` conjunct from precondition
- `pre_strenghtening`: weaken/transform precondition
- `pre_existential`: eliminate existential from precondition
- `frame_rule`: frame a precondition through a computation
- `pre_post_copy`: copy precondition to postcondition
- `get_named_spec'` / `get_named_str_spec'`: specs for fresh name generation

Pattern for each monadic step:
```coq
eapply bind_triple. eapply some_spec.
intros result_var state_var.
eapply pre_curry_l. intros Hfact.          (* extract Prop from pre *)
eapply pre_strenghtening.                   (* drop state-dependent facts *)
{ intros ? ? [_ Hfresh]. exact Hfresh. }
(* continue with next step *)
```

## Project Structure (theories/LambdaBox_to_LambdaANF/)

- `fuel_sem.v` — Big-step resource semantics for MetaRocq's EAst.term (source language)
- `common.v` — Shared definitions (dcon, ctx_bind_proj, etc.)
- `ANF.v` — ANF conversion: monadic `convert_anf` and relational spec `anf_cvt_rel`
- `CPS.v` — CPS conversion (analogous to ANF.v)
- `anf_util.v` — Value relations (`anf_val_rel`), alpha-equivalence proofs, helper lemmas
- `anf_correct.v` — Main correctness theorem `anf_cvt_correct` (WIP, has admits)
- `anf_corresp.v` — Correspondence between monadic and relational ANF conversion (WIP)
- `wf.v` — Well-formedness definitions

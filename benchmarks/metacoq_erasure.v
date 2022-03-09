Require Import Arith List String ZArith.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

From MetaCoq.Erasure Require Import ERemoveParams Erasure Loader.
From MetaCoq.Template Require Import MCString EtaExpand.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

From CertiCoq.Benchmarks Require Import ErasureFunction.

Import Transform.

Program Definition erase_pcuic_program (p : pcuic_program) 
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf _) wfΣ) in
  let wfe' := make_wf_env_ext wfe p.1.2 wfΣ in
  let t := ErasureFunction.erase wfe' nil p.2 _ in
  let Σ' := ErasureFunction.erase_global (EAstUtils.term_global_deps t) wfe in
  (EEtaExpanded.GlobalContextMap.make Σ' _, t).
  
Next Obligation.
  sq. destruct wt as [T Ht].
  cbn. now exists T.
Qed.
Next Obligation.
  unfold erase_global.
  eapply wf_glob_fresh. todo "wf".
Qed.

Obligation Tactic := idtac.

Program Definition erase_transform : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ×
       ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥;
    transform p hp := erase_pcuic_program p (map_squash fst hp) (map_squash snd hp) ;
    post p := true;
    obseq g g' v v' := True |}.
Next Obligation.
  intros [Σ t] [[wfext ht]]. exact eq_refl.
Qed.
Next Obligation.
  red. intros. todo "eval".
Qed.

Import Transform.
Local Notation " o ▷ o' " := (Transform.compose o o' _) (at level 50, left associativity).

Local Existing Instance config.default_checker_flags.

Program Definition erasure_pipeline := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform.
  (* ▷ 
  remove_params_fast_optimization _ ▷  *)
Next Obligation.
  intros. todo "foo".
Qed.
Next Obligation.
  intros. todo "foo".
Qed.
Definition erase_program_aux := Transform.run erasure_pipeline.

Definition eta_global_env (g : global_env) := 
  {| universes := g.(universes); declarations := eta_global_env g.(declarations) |}.

Definition eta_program p := 
  let Σ' := eta_global_env p.1 in 
  (Σ', eta_expand Σ'.(declarations) p.2).

Definition erase_program p := erase_program_aux (eta_program p).

Program Definition erase (p : Ast.Env.program) : eprogram_env :=
  erase_program p (MCUtils.todo "wf_env and welltyped term").

Program Definition erase_and_print_template_program (p : Ast.Env.program) : string :=
  let (Σ', t) := erase_program p (MCUtils.todo "wf_env and welltyped term") in
  let Σ' := EEtaExpanded.GlobalContextMap.global_decls Σ' in
  (EPretty.print_term Σ' nil true false t ++ nl ++ "in:" ++ nl ++ EPretty.print_global_context Σ')%string.

(* Program Definition erase_and_print_template_program (p : Ast.Env.program) : string := *)
  (* let (Σ', t) := erase_program p (MCUtils.todo "wf_env and welltyped term") in *)
  (* (PCUICPretty.print_term (TemplateToPCUIC.global_env_ext_map_global_env_ext Σ') false [] true false t ++ nl ++ "in:" ++ nl). *)
   (* PCUICPretty.print_global_env Σ')%string. *)

(* MetaCoq Erase is_arity. *)

From Equations Require Import Equations.

Equations wf_fix (n : nat) (H : n > 0): nat
  by wf n lt :=
  | 0, _ := 1
  | S n, _ := S (wf_fix n _).
Next Obligation. todo "bla". Qed.

MetaCoq Quote Recursively Definition foo := (List.map (fun x => negb x) [true]).
MetaCoq Quote Recursively Definition footy := (ltac:(let ty := type of prod in exact ty)).

Program Definition to_pcuic_pipeline := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform.
(* Next Obligation.
  intros. todo "foo".
Qed. *)

Definition to_pcuic_aux := Transform.run to_pcuic_pipeline.

Axiom (print_nat : nat -> unit).

Axiom sorry : forall {A : Prop}, A.
Local Existing Instance PCUICSN.extraction_normalizing.
Import PCUICErrors PCUICWfEnv.
Definition reduce_to_sort_test := 
  let p := to_pcuic_aux footy (MCUtils.todo "precondition") in
  let wfe := build_wf_env_from_env p.1.1 sorry in
  let wfe' := make_wf_env_ext wfe p.1.2 sorry in
  match PCUICSafeReduce.reduce_to_sort wfe' [] p.2 sorry with
  | Checked_comp s => string_of_sort s.π1
  | TypeError_comp _ _ => 
    let _ := ErasureFunction.pr_term "not a sort" wfe' [] p.2 in "not a sort"
  end.

(* Definition metacoq_erasure := reduce_to_sort_test. *)
Definition metacoq_erasure := (erase_and_print_template_program foo). 
(* Definition metacoq_erasure := 
  let _ := print_str "metacoq_erasure" in
  let _ := print_newline tt in
  print_nat (wf_fix (S (S 0)) sorry). *)

(* MetaCoq Erase wf_fix.   *)
(* Eval lazy in metacoq_erasure. *)
CertiCoq Compile -O 0 metacoq_erasure
Extract Constants [ 
  (* print_nat => "print_gallina_nat", *)
  CertiCoq.Benchmarks.ErasureFunction.print_str => "print_gallina_string",
  CertiCoq.Benchmarks.ErasureFunction.print_newline => "print_new_line" ] 
Include [ "print.h" ]. 
(*
Definition er := Eval lazy in erase foo.

Require Import CertiCoq.Compiler.pipeline Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.
Definition next_id := 100%positive.

Section Pipeline.

  Definition CertiCoq_pipeline (p : Ast.Env.program) :=
    p <- compile_L2k p ;;
    (* p <- compile_L2k_eta p ;; *)
    p <- compile_L4 [] p ;;
    compile_L6_ANF next_id [] p.
    (* if debug then compile_L6_debug next_id p  For debugging intermediate states of the λanf pipeline *)
    (* else compile_L6 next_id p. *)

End Pipeline.


(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
(*   p <- erase_PCUIC p ;;
 *) CertiCoq_pipeline p.

Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
    run_pipeline _ _ opts p pipeline.
  
Transparent compile.compile.

  (* compile_Clight prs p. *)
Eval compute in 
    match compile default_opts foo with
    | (compM.Ret a, s) => a
    | (compM.Err s, s') => MCUtils.todo "foo"
    end.*)
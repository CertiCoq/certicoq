From CertiCoq.Plugin Require Import CertiCoq.
From MetaCoq.Utils Require Import utils.
Open Scope bs_scope.

Import MCMonadNotation.
From MetaCoq.Template Require Import AstUtils Ast Pretty.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl PCUICSafeChecker.
From MetaCoq.PCUIC Require Import PCUICSN. 
From MetaCoq.SafeCheckerPlugin Require Import SafeTemplateChecker.
From MetaCoq.ErasurePlugin Require Import Erasure.
 
(* Program Definition infer_template_program {cf : config.checker_flags} {nor : PCUICSN.normalizing_flags} {guard : abstract_guard_impl}  *)
(*   (p : PCUICAst.PCUICEnvironment.program) φ *)
(*   : EnvCheck_wf_env_ext (∑ A, { X : wf_env_ext | *)
(*     ∥ (p.1, φ) = X.(wf_env_ext_referenced).(referenced_impl_env_ext) × wf_ext (p.1, φ) × (p.1, φ) ;;; [] |- p.2 : A ∥ }) := *)
(*   pp <- typecheck_program (cf := cf) optimized_abstract_env_impl p φ ;; *)
(*   ret (pp.π1 ; (exist (proj1_sig pp.π2) _)). *)
(* Next Obligation.  *)
(*   sq. destruct H; split; eauto. destruct p0; split; eauto. eapply BDToPCUIC.infering_typing; tea. eapply w. constructor. *)
(* Qed. *)

#[local,program] Instance assume_normalization {nor} : @PCUICSN.Normalization config.default_checker_flags nor.
Next Obligation. todo "we should write a Template Monad program to prove normalization for the particular program being inferred, rather than axiomatizing it". Qed.
#[local] Existing Instance PCUICSN.normalization.

Program Definition infer_and_pretty_print_template_program (cf := config.default_checker_flags) {guard : abstract_guard_impl}
  {nor : normalizing_flags}
  (p : Ast.Env.program) φ
  : string + string :=
  let e' := PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env p.1) in
  match infer_template_program (cf:=cf) p φ return string + string with
  | CorrectDecl t =>
    inl ("Environment is well-formed and " ^ Pretty.print_term (empty_ext p.1) [] false p.2 ^
         " has type: " ^ print_term (PCUICAst.PCUICEnvironment.empty_ext e') [] t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.

Definition certicoqchk (p : Template.Ast.Env.program) : bool :=
  let () := coq_msg_info "running type checking on whole program" in
  match infer_and_pretty_print_template_program 
    (guard := Erasure.fake_guard_impl) 
    (nor := PCUICSN.default_normalizing)
    p Universes.Monomorphic_ctx with
  | inl ty => let () := coq_msg_notice ty in true
  | inr err => let () := coq_user_error err in false
  end.

Eval compute in "Compiling MetaCoq's checker".
Set Warnings "-primitive-turned-into-axiom".

CertiCoq Compile -time -O 1 certicoqchk.
CertiCoq Generate Glue -file "glue" [ ].

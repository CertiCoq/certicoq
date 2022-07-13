From CertiCoq.Plugin Require Import CertiCoq.
From MetaCoq.Template Require Import utils.
Open Scope bs_scope.

Axiom (coq_msg_info : string -> unit).
Axiom (coq_user_error : string -> unit).
Axiom (coq_msg_debug : string -> unit).

Import MCMonadNotation.
From MetaCoq Require Import Erasure PCUICAstUtils PCUICPretty PCUICErrors PCUICTyping PCUICWfEnvImpl PCUICSafeChecker SafeTemplateChecker.

Program Definition infer_template_program {cf : config.checker_flags} {nor : PCUICSN.normalizing_flags} {guard : abstract_guard_impl} 
  (p : PCUICAst.PCUICEnvironment.program) φ
  : EnvCheck_wf_env_ext (∑ A, { X : wf_env_ext |
    ∥ (p.1, φ) = X.(wf_env_ext_referenced).(referenced_impl_env_ext) × wf_ext (p.1, φ) × (p.1, φ) ;;; [] |- p.2 : A ∥ }) :=
  pp <- typecheck_program (cf := cf) optimized_abstract_env_impl p φ ;;
  ret (pp.π1 ; (exist (proj1_sig pp.π2) _)).
Next Obligation. 
  sq. destruct H; split; eauto. destruct p0; split; eauto. eapply BDToPCUIC.infering_typing; tea. eapply w. constructor.
Qed.

Program Definition infer_and_pretty_print_template_program {cf : config.checker_flags} {nor : PCUICSN.normalizing_flags} {guard : abstract_guard_impl}
  (p : Ast.Env.program) φ
  : string + string :=
  let p := trans_program p in
  match infer_template_program (cf:=cf) p φ return string + string with
  | CorrectDecl t =>
    inl ("Environment is well-formed and " ^ print_term (empty_ext p.1) [] p.2 ^
         " has type: " ^ print_term (empty_ext p.1) [] t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.

Definition certicoqchk (p : Template.Ast.Env.program) : bool :=
  let () := coq_msg_info "running type checking on whole program" in
  match infer_and_pretty_print_template_program 
    (cf := config.default_checker_flags) 
    (guard := Erasure.fake_guard_impl) 
    (nor := PCUICSN.default_normalizing)
    p Universes.Monomorphic_ctx with
  | inl ty => let () := coq_msg_info ty in true
  | inr err => let () := coq_user_error err in false
  end.  

Eval compute in "Compiling MetaCoq's checker".

CertiCoq Compile -time -O 1 certicoqchk
Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  coq_msg_info => "print_msg_info",
  coq_user_error => "coq_user_error"
   ] 
Include [ "print.h" ].

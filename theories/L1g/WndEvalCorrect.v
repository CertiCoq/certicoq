Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import FunInd.
Require Import Common.Common.
Require Import Common.AstCommon.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wndEval.

From MetaCoq.Erasure Require Import EAst EWndEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*******************************
Goal
  forall (k:kername) (cb:constant_body) (Σ:global_declarations) (t:term),
    cb.(cst_body) = Some t ->   (* not an Axiom *)
    let g := (ConstantDecl k cb :: Σ) in
    program_Pgm_aux (ConstantDecl k cb :: Σ) =
    let decl :=
        match cb.(cst_body) with
            | Some t => pair k (ecTrm (term_Term g t))
            | None => pair k (ecAx Term)
            end in
        cons decl (program_Pgm_aux Σ).
Proof.
  intros. rewrite H. unfold program_Pgm_aux at 1. 

    
          {| Extract.E.cst_type := cst_type; Extract.E.cst_body := cst_body |}
        :: Σ))
Goal
  forall Σ c decl,
    ETyping.lookup_env Σ c = Some (ConstantDecl c decl) ->
    forall body, cst_body decl = Some body ->
                 LookupDfn c (program_Pgm_aux Σ) (term_Term Σ body).
Proof.
  induction Σ; intros.
  - cbn in H. discriminate.
  - destruct a.
    + destruct c0. destruct (string_dec c k).
      * subst. unfold program_Pgm_aux. cbn.






        Section Wnd.
  (* The local context is fixed: we are only doing weak reductions *)
  Context (Σ: global_declarations).
          
  Lemma WndEvalCorrect:
    forall (t u:term),
      EWndEval.Wnd Σ t u ->
      wndEval (program_Pgm_aux Σ) (term_Term Σ t) (term_Term Σ u).
  Proof.
    induction 1; intros.
    - cbn. unfold ETyping.declared_constant in isdecl.
      rewrite isdecl. constructor.

End Wnd.
  

 **********************)

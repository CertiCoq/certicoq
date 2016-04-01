Require Import cps cps_util identifiers.
Require Import Coq.MSets.MSetRBT List.

Import FVSet.

(** static environments *)
Definition senv := FVSet.t.

(** An expression is well scoped in an environment: [Γ |- e] *) 
Inductive well_scoped_exp : senv -> exp -> Prop :=
| WS_constr :
    forall x tau t ys e Γ,
      (forall y, List.In y ys -> In y Γ) ->
      well_scoped_exp (add x Γ) e ->
      well_scoped_exp Γ (Econstr x tau t ys e)
| WS_case :
    forall x tys Γ,
      (forall t y, List.In (t, y) tys -> In y Γ) ->
      In x Γ ->
      well_scoped_exp Γ (Ecase x tys)
| WSproj :
    forall x tau N y e Γ,
      In y Γ ->
      well_scoped_exp (add x Γ) e ->
      well_scoped_exp Γ (Eproj x tau N y e)
| WS_fun :
    forall defs e Γ,
      well_scoped_fundefs Γ defs ->
      well_scoped_exp (union Γ (fundefs_names defs)) e ->
      well_scoped_exp Γ (Efun defs e)
| WS_app :
    forall x ys Γ,
      (forall y, List.In y ys -> In y Γ) ->
      In x Γ ->
      well_scoped_exp Γ (Eapp x ys)
| WS_prim :
    forall x tau f ys e Γ,
      (forall y, List.In y ys -> In y Γ) ->
      well_scoped_exp (add x Γ) e ->
      well_scoped_exp Γ (Eprim x tau f ys e)
with well_scoped_fundefs : senv -> fundefs -> Prop :=
| WS_fcons :
    forall f tau xs e defs Γ,
      well_scoped_exp (union (fundefs_names defs) (add f (union_list Γ xs)))
                      e ->
      well_scoped_fundefs (add f Γ) defs ->
      well_scoped_fundefs Γ (Fcons f tau xs e defs)
| WS_fnil :
    forall Γ,
      well_scoped_fundefs Γ Fnil.

Fixpoint fundefs_ctx_names (cdefs : fundefs_ctx) : FVSet.t :=
  match cdefs with
    | Fcons1_c f _ _ _ defs => add f (fundefs_names defs) 
    | Fcons2_c f _ _ _ cdefs' => add f (fundefs_ctx_names cdefs') 
  end.
    
(** [Γ {[Γ']}|- c  ]: A context is well scoped in an environment Γ, if the
    expression we put in the hole is well scoped in the environment Γ' *)
Inductive well_scoped_exp_ctx : senv -> exp_ctx -> senv -> Prop :=
| WSCtx_hole :
    forall Γ Γ',
      Subset Γ' Γ ->
      well_scoped_exp_ctx Γ Hole_c Γ'
| WSCtx_constr :
    forall x tau t ys c Γ Γ',
      (forall y, List.In y ys -> In y Γ) ->
      well_scoped_exp_ctx (add x Γ) c Γ'->
      well_scoped_exp_ctx Γ (Econstr_c x tau t ys c) Γ'
| WSCtx_proj :
    forall x tau N y c Γ Γ',
      In y Γ ->
      well_scoped_exp_ctx (add x Γ) c Γ' ->
      well_scoped_exp_ctx Γ (Eproj_c x tau N y c) Γ'
| WSCtx_prim :
    forall x tau f ys c Γ Γ',
      (forall y, List.In y ys -> In y Γ) ->
      well_scoped_exp_ctx (add x Γ) c Γ' ->
      well_scoped_exp_ctx Γ (Eprim_c x tau f ys c) Γ'
| WSCtx_fun1 :
    forall defs c Γ Γ',
      well_scoped_fundefs Γ defs ->
      well_scoped_exp_ctx (union Γ (fundefs_names defs)) c Γ' ->
      well_scoped_exp_ctx Γ (Efun1_c defs c) Γ'
| WSCtx_fun2 :
    forall cdefs e Γ Γ',
      well_scoped_fundefs_ctx Γ cdefs Γ' ->
      well_scoped_exp (union Γ (fundefs_ctx_names cdefs)) e ->
      well_scoped_exp_ctx Γ (Efun2_c cdefs e) Γ'
with well_scoped_fundefs_ctx : senv -> fundefs_ctx -> senv -> Prop :=
| WS_fcons1 :
    forall f tau xs c defs Γ Γ',
      well_scoped_exp_ctx (union (fundefs_names defs) (add f (union_list Γ xs)))
                          c Γ' ->
      well_scoped_fundefs (add f Γ) defs ->
      well_scoped_fundefs_ctx Γ (Fcons1_c f tau xs c defs) Γ'
| WS_fcons2 :
    forall f tau xs e cdefs Γ Γ',
      well_scoped_exp (union (fundefs_ctx_names cdefs) (add f (union_list Γ xs))) e ->
      well_scoped_fundefs_ctx (add f Γ) cdefs Γ' ->
      well_scoped_fundefs_ctx Γ (Fcons2_c f tau xs e cdefs) Γ'.

Notation "c '|[' e ']|' " := (app_ctx_f c e)  (at level 28, no associativity)
                             : ctx_scope.
Notation "f '<[' e ']>'" := (app_f_ctx_f f e)  (at level 28, no associativity)
                            : ctx_scope.
Notation "Γ '⊢' e" := (well_scoped_exp Γ e) (at level 30, no associativity)
                      : env_scope.
Notation "Γ '{[' Γ' ']}' '⊢' e " := (well_scoped_exp_ctx Γ e Γ')
                                      (at level 30, no associativity)
                                    : env_scope.
Notation "Γ '⊢*' f" := (well_scoped_fundefs Γ f) (at level 30, no associativity)
                       : env_scope.
Notation "Γ '{[' Γ' ']}' '⊢*' f " := (well_scoped_fundefs_ctx Γ f Γ')
                                       (at level 30, no associativity)
                                     : env_scope.

Open Scope env_scope.
Open Scope ctx_scope.


Scheme ctx_exp_mut := Induction for exp_ctx Sort Prop
                      with ctx_fundefs_mut := Induction for fundefs_ctx Sort Prop.

Lemma exp_fundefs_ctx_mutual_ind :
  forall (P : exp_ctx -> Prop) (P0 : fundefs_ctx -> Prop),
    P Hole_c ->
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp_ctx),
       P e -> P (Econstr_c v t t0 l e)) ->
    (forall (v : var) (t : type) (n : BinNums.N) (v0 : var) (e : exp_ctx),
       P e -> P (Eproj_c v t n v0 e)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp_ctx),
       P e -> P (Eprim_c v t p l e)) ->
    (forall (f3 : fundefs) (e : exp_ctx), P e -> P (Efun1_c f3 e)) ->
    (forall f4 : fundefs_ctx, P0 f4 -> forall e : exp, P (Efun2_c f4 e)) ->
    (forall (v : var) (t : type) (l : list var) (e : exp_ctx),
       P e -> forall f5 : fundefs, P0 (Fcons1_c v t l e f5)) ->
    (forall (v : var) (t : type) (l : list var) 
            (e : exp) (f6 : fundefs_ctx), P0 f6 -> P0 (Fcons2_c v t l e f6)) ->
    (forall e : exp_ctx, P e) /\ (forall f : fundefs_ctx, P0 f).
Proof.
  intros. split.
  apply (ctx_exp_mut P P0); assumption.
  apply (ctx_fundefs_mut P P0); assumption.
Qed.

(** name the induction hypotheses only *)
Ltac exp_fundefs_ctx_induction IH1 IH2 :=
  apply exp_fundefs_ctx_mutual_ind;
  [ | intros ? ? ? ? ? IH1 
    | intros ? ? ? ? ? IH1
    | intros ? ? ? ? ? IH1
    | intros ? ? IH1
    | intros ? IH2 ?
    | intros ? ? ? ? IH1 ?
    | intros ? ? ? ? ? IH2 ].

Lemma Subset_add s s' e :
  Subset s s' ->
  Subset (add e s) (add e s').
Proof.
  intros H e' HIn. eapply add_spec in HIn.
  inv HIn; eapply add_spec; eauto. 
Qed.

Lemma Subset_union_r s s' s'' :
  Subset s s' ->
  Subset (union s s'') (union s' s'').
Proof.
  intros H e' HIn. eapply union_spec in HIn.
  inv HIn; eapply union_spec; eauto. 
Qed.

Lemma Subset_union_l s s' s'' :
  Subset s s' ->
  Subset (union s'' s) (union s'' s').
Proof.
  intros H e' HIn. eapply union_spec in HIn.
  inv HIn; eapply union_spec; eauto. 
Qed.

Lemma Subset_union_list s s' l :
  Subset s s' ->
  Subset (union_list s l) (union_list s' l).
Proof.
  intros H e' HIn. eapply union_list_spec in HIn.
  inv HIn; eapply union_list_spec; eauto. 
Qed.


Lemma well_scoped_exp_fundefs_weakening :
  (forall e Γ Γ',
     Γ ⊢ e -> Subset Γ Γ' -> Γ' ⊢ e) /\
  (forall defs Γ Γ',
     Γ ⊢* defs -> Subset Γ Γ' -> Γ' ⊢* defs).
Proof.
  exp_defs_induction IHc IHfc; intros Γ Γ' Hws Hsub;
  try (now inv Hws; constructor; eauto; eapply IHc;
       eauto using Subset_add, Subset_union_r).
  inv Hws. constructor; eauto.
  eapply IHc; eauto using Subset_add, Subset_union_r,
              Subset_union_l, Subset_union_list.
  eapply IHfc; eauto using Subset_add.
Qed.

Lemma fundefs_names_eq fc e :
  eq (fundefs_ctx_names fc) (fundefs_names (fc <[ e ]>)).
Proof.
  induction fc; simpl; intros x; split; intros HIn; eauto;
  eapply add_spec in HIn; inv HIn; eapply add_spec; eauto;
  right; eapply IHfc; eauto.
Qed.

Lemma well_scoped_ctx_app :
  (forall c e Γ Γ',
     Γ {[ Γ' ]} ⊢ c  -> Γ' ⊢ e -> Γ  ⊢ c |[ e ]| ) /\
  (forall fc e Γ Γ',
     Γ {[ Γ' ]} ⊢* fc  -> Γ' ⊢ e -> Γ  ⊢* fc <[ e ]>).
Proof.
  exp_fundefs_ctx_induction IHc IHfc;
  try (now intros e' Γ Γ' Hws1 Hws2; inv Hws1;
       simpl; constructor; eauto).
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1. simpl.
    eapply well_scoped_exp_fundefs_weakening; eauto.
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1. simpl. constructor; eauto.
    eapply well_scoped_exp_fundefs_weakening; eauto.
    eapply Subset_union_l. intros x HIn. eapply fundefs_names_eq; eauto.
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1. simpl. constructor; eauto.
    eapply well_scoped_exp_fundefs_weakening; eauto.
    eapply Subset_union_r. intros x HIn. eapply fundefs_names_eq; eauto.
Qed.

Close Scope env_scope.
Close Scope ctx_scope.
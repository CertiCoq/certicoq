Require Import cps cps_util set_util.
Require Import List BinNat Relations Coq.MSets.MSetRBT List.
Import ListNotations.

Import PS.

Definition FVSet := PS.t.


(** [f] is a function defined in [fs] *)
Fixpoint name_in_fundefs f (fs : fundefs) :=
  match fs with
    | Fnil => False
    | Fcons f' _ _ _ fs =>
      f' = f \/ name_in_fundefs f fs
  end.

(** [occurs_free x e] iff [x] appears free in [e] *)
Inductive occurs_free : var -> exp -> Prop :=
| Free_Econstr1 :
    forall y x tau t ys e,
      List.In y ys ->
      occurs_free y (Econstr x tau t ys e)
| Free_Econstr2 :
    forall y x tau t ys e,
      ~ x = y ->
      occurs_free y e ->
      occurs_free y (Econstr x tau t ys e)
| Free_Ecase1 :
    forall x ys, 
      occurs_free x (Ecase x ys)
| Free_Ecase2 :  
    forall y x ys,
      List.Exists (fun p => occurs_free y (snd p)) ys ->
      occurs_free y (Ecase x ys)
| Free_Eproj1 :
    forall y x tau n e,
      occurs_free y (Eproj x tau n y e)
| Free_Eproj2 :
    forall y x tau n y' e,
      x <> y ->
      occurs_free y e ->
      occurs_free y (Eproj x tau n y' e)
| Free_Efun1 :
    forall y defs e,
      ~ (name_in_fundefs y defs) -> 
      occurs_free y e ->
      occurs_free y (Efun defs e)
| Free_Efun2 :
    forall y defs e, 
      occurs_free_fundefs y defs ->
      occurs_free y (Efun defs e)
| Free_Eapp1 :
    forall x ys,
      occurs_free x (Eapp x ys)
| Free_Eapp2 :
    forall y x ys,
      List.In y ys ->
      occurs_free y (Eapp x ys)
| Free_Eprim1 :
    forall y x tau p ys e,
      List.In y ys ->
      occurs_free y (Eprim x tau p ys e)
| Free_Eprim2 :
    forall y x tau p ys e,
      x <> y ->
      occurs_free y e ->
      occurs_free y (Eprim x tau p ys e)
with occurs_free_fundefs : var -> fundefs -> Prop :=
| Free_Fcons1 :
    forall x f tau ys e defs,  
      x <> f ->
      ~ (List.In x ys) ->
      ~ (name_in_fundefs x defs) ->
      occurs_free x e ->
      occurs_free_fundefs x (Fcons f tau ys e defs)
| Free_Fcons2 :
    forall x f tau ys e defs,
      occurs_free_fundefs x defs ->
      x <> f ->
      occurs_free_fundefs x (Fcons f tau ys e defs).

(** sanity check : The names of the functions cannot appear 
    free in a fundefs block *)
Lemma fun_names_not_free_in_fundefs f defs :
  name_in_fundefs f defs ->
  ~ occurs_free_fundefs f defs.
Proof.
  intros Hname Hfree.
  induction Hfree; inversion Hname; eauto.
Qed.

Definition closed_exp (e : exp) : Prop :=
  forall x, ~ (occurs_free x e).

Definition closed_fundefs (defs : fundefs) : Prop :=
  forall x, ~ (occurs_free_fundefs x defs).

(** [funs_in_exp B e] iff [B] is a block of functions in [e] *)
Inductive funs_in_exp : fundefs -> exp -> Prop :=
| In_Econstr :
    forall fs e x tau t ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Econstr x tau t ys e)
| In_Eproj :    
    forall fs e x tau N ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Eproj x tau N ys e)
| In_Fun1 :
    forall fs e,
      funs_in_exp fs (Efun fs e)
| In_Fun2 :
    forall fs fs' e,
      funs_in_exp fs e ->
      funs_in_exp fs (Efun fs' e)
| In_Fun3 :
    forall fs fs' e,
      funs_in_fundef fs fs' ->
      funs_in_exp fs (Efun fs' e)
| In_Eprim :
    forall fs e x tau p ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Eprim x tau p ys e)
with funs_in_fundef : fundefs -> fundefs -> Prop :=
| In_Fcons1 :
    forall fs fs' x tau ys e,
      funs_in_exp fs e -> 
      funs_in_fundef fs (Fcons x tau ys e fs')
| In_Fcons2 :
    forall fs fs' x tau ys e,
      funs_in_fundef fs fs' ->
      funs_in_fundef fs (Fcons x tau ys e fs').

(** all functions defined in an expression are closed *)
Definition closed_fundefs_in_exp (e : exp) :=
  forall defs, funs_in_exp defs e -> closed_fundefs defs.

(** bound variables - alternative definition without lists or 
    number of occurences *)
Inductive bound_var : var -> exp -> Prop :=
| Bound_Econstr1 :
    forall x tau t ys e,
      bound_var x (Econstr x tau t ys e)
| Bound_Econstr2 :
    forall y x tau t ys e,
      bound_var y e ->
      bound_var y (Econstr x tau t ys e)
| Bound_Eproj1 :
    forall x y tau n e,
      bound_var x (Eproj x tau n y e)
| Bound_Eproj2 :
    forall y x tau n y' e,
      bound_var y e ->
      bound_var y (Eproj x tau n y' e)
| Bound_Efun1 :
    forall y defs e,
      bound_var_fundefs y defs ->
      bound_var y (Efun defs e)
| Bound_Efun2 :
    forall y defs e,
      bound_var y e ->
      bound_var y (Efun defs e)
| Bound_Eprim1 :
    forall x tau p ys e,
      bound_var x (Eprim x tau p ys e)
| Bound_Eprim2 :
    forall y x tau p ys e,
      bound_var y e ->
      bound_var y (Eprim x tau p ys e)
with bound_var_fundefs : var -> fundefs -> Prop :=
| Bound_Fcons1 :
    forall x f tau ys e defs,  
      x = f \/ List.In x ys ->
      bound_var_fundefs x (Fcons f tau ys e defs)
| Bound_Fcons2 :
    forall x f tau ys e defs,
      bound_var_fundefs x defs ->
      bound_var_fundefs x (Fcons f tau ys e defs)
| Bound_Fcons3 :
    forall x f tau ys e defs,
      bound_var x e ->
      bound_var_fundefs x (Fcons f tau ys e defs).

(** unique bindings - alternative definition without lists *)
Inductive unique_bindings : exp -> Prop :=
| UBound_Econstr :
    forall x tau t ys e,
      (forall x', bound_var x' e -> x <> x') ->
      unique_bindings e ->
      unique_bindings (Econstr x tau t ys e)
| UBound_Eproj :
    forall x tau n y e,
      (forall x', bound_var x' e -> x <> x') ->
      unique_bindings e ->
      unique_bindings (Eproj x tau n y e)
| UBound_Efun :
    forall defs e,
      unique_bindings e ->
      unique_bindings_fundefs defs ->
      (forall x', bound_var x' e -> ~ bound_var_fundefs x' defs) ->
      unique_bindings (Efun defs e)
| UBound_Eprim :
    forall x tau p ys e,
      (forall x', bound_var x' e -> x <> x') ->
      unique_bindings e ->
      unique_bindings (Eprim x tau p ys e)
with unique_bindings_fundefs : fundefs -> Prop :=
| UBound_Fcons :
    forall f tau ys e defs,
      (forall x', bound_var x' e -> f <> x' /\ ~ List.In x' ys) ->
      unique_bindings e ->
      unique_bindings_fundefs defs ->
      unique_bindings_fundefs (Fcons f tau ys e defs)
| UBound_Fnil :
    unique_bindings_fundefs Fnil.

(** The set of names of the functions in the same fix definition *)
Fixpoint fundefs_names (defs : fundefs) : FVSet :=
  match defs with
    | Fcons f _ _ _ defs' => add f (fundefs_names defs') 
    | Fnil => empty
  end.

  
(** The set of free variables of an exp *)
Fixpoint exp_fv (e : exp) : FVSet :=
  match e with
    | Econstr x tau c ys e =>
      let set := remove x (exp_fv e) in
      union_list set ys
    | Ecase x pats =>
      fold_left (fun s p => union (exp_fv (snd p)) s) pats (singleton x)
    | Eproj x tau n y e =>
      let set := remove x (exp_fv e) in
      add y set
    | Efun defs e =>
      let names := fundefs_names defs in
      union (fundefs_fv defs names)
            (diff (exp_fv e) names)
    | Eapp x xs =>
      union_list (singleton x) xs
    | Eprim x tau prim ys e =>
      let set := remove x (exp_fv e) in
      union_list set ys
  end
with fundefs_fv (defs : fundefs) (names : FVSet) : FVSet :=
       match defs with
         | Fcons f t ys e defs' =>
           let fv_e := diff_list (diff (exp_fv e) names) ys in
           union fv_e (fundefs_fv defs' names)
         | Fnil => empty
       end.

(** Equivalence of computational and inductive FV definitions *)

(** fundefs_names correct w.r.t name_in_fundefs *)
Lemma fundefs_names_correct (defs : fundefs) :
  forall f, In f (fundefs_names defs) <-> name_in_fundefs f defs.
Proof.
  induction defs; simpl; intros f; split; intros H; try now inv H.
  - apply add_spec in H. inv H; eauto.
    right. eapply IHdefs; eauto.
  - apply add_spec. inv H; eauto.
    right. eapply IHdefs; eauto.
Qed.

Ltac apply_set_specs_ctx :=
  match goal with
    | [ H : In _ (add _ _) |- _ ] =>
      apply add_spec in H; inv H
    | [ H : In _ (remove _ _) |- _ ] =>
      apply remove_spec in H; inv H
    | [ H : In _  (singleton _ ) |- _ ] =>
      apply singleton_spec in H; subst
    | [ H : In _ (union _ _) |- _ ] =>
      apply union_spec in H; inv H
    | [ H : In _ (diff _ _) |- _ ] =>
      apply diff_spec in H; inv H
    | [ H : In _ (diff_list _ _) |- _ ] =>
      apply diff_list_spec in H; inv H
    | [ H : In _ (union_list _ _) |- _ ] =>
      apply union_list_spec in H; inv H
  end.

Ltac apply_set_specs :=
  match goal with
    | [ |- In _ (add _ _) ] =>
      apply add_spec
    | [ |- In _ (remove _ _) ] =>
      apply remove_spec; split
    | [ |- In _  (singleton _ ) ] =>
      apply singleton_spec
    | [ |- In _ (union _ _) ] =>
      apply union_spec
    | [ |- In _ (diff _ _) ] =>
      apply diff_spec; split
    | [ |- In _ (diff_list _ _) ] =>
      apply diff_list_spec; split
    | [ |- In _ (union_list _ _) ] =>
      apply union_list_spec
  end.

Lemma fundefs_fv_add defs :
  forall s x,
    Equal (fundefs_fv defs (add x s))
          (remove x (fundefs_fv defs s)).
Proof.
  induction defs; intros s x x'; simpl; split; intros HIn.
  - repeat apply_set_specs_ctx.
    + repeat apply_set_specs;
      (try left; repeat apply_set_specs; auto);
      intros Hc; apply H2; apply_set_specs; eauto.
    + repeat apply_set_specs;
      try right; eapply IHdefs in H; repeat apply_set_specs_ctx; auto.
  - repeat apply_set_specs_ctx.
    + repeat apply_set_specs.
      left. repeat apply_set_specs; auto. 
      intros Hc; apply H3. apply_set_specs_ctx; eauto.
      congruence.
    + repeat apply_set_specs. right.
      eapply IHdefs. apply_set_specs; auto.
  - inv HIn.
  - apply_set_specs_ctx; eauto.
Qed.


Lemma In_fold_left_l {A} (f : A -> FVSet) (l : list A)
      (si : FVSet) x:
  In x (fold_left (fun s e => union (f e) s) l si) ->
  In x si \/ List.Exists (fun e => In x (f e)) l.
Proof.
  revert si; induction l; intros si H; simpl in H; eauto.
  eapply IHl in H. inv H.
  - repeat apply_set_specs_ctx.
    + right. constructor; eauto.
    + left; eauto. 
  - right. constructor 2; eauto.
Qed.

Lemma In_fold_left_r {A} (f : A -> FVSet) (l : list A)
      (si : FVSet) x:
  In x si \/ List.Exists (fun e => In x (f e)) l ->
  In x (fold_left (fun s e => union (f e) s) l si).
Proof.
  revert si; induction l; intros si H; simpl in H; eauto.
  - simpl. inv H; eauto. inv H0.
  - inv H; simpl; eapply IHl.
    + left. apply_set_specs; eauto.
    + inv H0; eauto. left.  apply_set_specs; eauto.
Qed.

Lemma In_fold_left_weaken {A} f (l : list A)
      (si si' : FVSet) x:
  Subset si si' ->
  In x (fold_left (fun s e => union (f e) s) l si) ->
  In x (fold_left (fun s e => union (f e) s) l si').
Proof.
  revert si si'; induction l; intros si si' H Hin; simpl in H; eauto.
  simpl in *. eapply IHl; eauto.
  eapply Subset_union_l; eauto.
Qed.

  
(** correctness of exp_fv and fundefs_fv w.r.t occurs_free
    and occurs_free_def *)
Lemma exp_fv_fundefs_fv_correct :
  (forall e x, In x (exp_fv e) <-> occurs_free x e) /\
  (forall defs x,
     In x (fundefs_fv defs (fundefs_names defs)) <->
     occurs_free_fundefs x defs).
Proof.
  exp_defs_induction IHe IHl IHdefs; simpl; intros x; split; intros H.
  - repeat apply_set_specs_ctx.
    + constructor 2; eauto. eapply IHe; eauto.
    + constructor; eauto.
  - inv H; repeat apply_set_specs; eauto.
    left. apply_set_specs; eauto.
    apply IHe; eauto.
  - repeat apply_set_specs_ctx; constructor.
  - inv H; eauto; apply_set_specs; eauto.
    inv H2.
  - repeat apply_set_specs_ctx.
    eapply In_fold_left_l in H.
    inv H.
    + repeat apply_set_specs_ctx.
      * constructor; simpl. constructor; eapply IHe; eauto.
      * constructor.
    + assert (Hsuf : occurs_free x (Ecase v l))
        by (eapply IHl; apply In_fold_left_r; eauto).
      clear H0. inv Hsuf. constructor; eauto.
      constructor. constructor 2. eauto.
  - inv H.
    + eapply In_fold_left_r.
      left. apply_set_specs; right; apply_set_specs; eauto.
    + inv H2; simpl in *.
      * eapply In_fold_left_r.
        left. apply_set_specs; left. apply IHe; eauto.
      * eapply In_fold_left_weaken.
        apply Subset_union_mon_r. apply Subset_refl.
        eapply IHl. constructor; eauto.
  - repeat apply_set_specs_ctx.
    + constructor; eauto.
    + constructor; eauto. eapply IHe; eauto.
  - inv H; repeat apply_set_specs; eauto.
    right. apply_set_specs; eauto. apply IHe; eauto.
  - repeat apply_set_specs_ctx.
    + eapply Free_Efun2. eapply IHdefs; eauto.
    + econstructor. intros Hc; apply H1; apply fundefs_names_correct; eauto.
      eapply IHe; eauto.
  - inv H; repeat apply_set_specs; eauto.
    + right. apply_set_specs; eauto. apply IHe; eauto.
      intros Hc; apply H3; apply fundefs_names_correct; eauto.
    + left. eapply IHdefs; eauto.
  - repeat apply_set_specs_ctx; constructor; eauto.
  - inv H; apply_set_specs; eauto. left. apply_set_specs; eauto.
  - repeat apply_set_specs_ctx.
    + eapply Free_Eprim2; eauto. eapply IHe; eauto.
    + constructor; eauto.
  - inv H; apply_set_specs; eauto. left.
    apply_set_specs; eauto; apply IHe; eauto.
  - repeat apply_set_specs_ctx.
    + constructor; eauto.
      intros Hc; apply H2; apply_set_specs; eauto.
      intros Hc. apply H2. apply_set_specs; eauto;
      right. apply fundefs_names_correct; eauto. 
      apply IHe; eauto.
    + apply fundefs_fv_add in H0. apply_set_specs_ctx.
      constructor 2; eauto. apply IHdefs; eauto.
  - inv H; repeat apply_set_specs.
    + left; repeat apply_set_specs; eauto.
      apply IHe; eauto.
      intros Hc. apply H8. repeat apply_set_specs_ctx.
      congruence. apply fundefs_names_correct; auto.
    + right. apply fundefs_fv_add. repeat apply_set_specs; auto.
      apply IHdefs. eauto.
  - inv H.
  - inv H.
Qed.
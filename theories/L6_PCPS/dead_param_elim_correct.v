Require Import L6.cps L6.identifiers L6.ctx L6.set_util L6.state
        L6.dead_param_elim L6.Ensembles_util L6.tactics L6.map_util
        L6.hoisting.
Require Import compcert.lib.Coqlib Common.compM Common.Pipeline_utils.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega
        maps_util.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.


Import MonadNotation.
Open Scope monad_scope.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Inductive Dead_in_args (S : Ensemble var) : list var -> list bool -> Prop :=
| Live_nil : Dead_in_args S [] []
| ALive_cons_Dead :
    forall (x : var) (xs : list var) (bs: list bool),
      Dead_in_args S xs bs ->
      Dead_in_args S (x :: xs) (false :: bs)
| ALive_cons_Live :
    forall (x : var) (xs : list var) (bs: list bool),
      Dead_in_args S xs bs ->
      ~ x \in S -> 
      Dead_in_args S (x :: xs) (true :: bs).


Fixpoint dead_args (ys : list var) (bs : list bool) : list var := 
  match ys, bs with 
  | [], [] => ys
  | y :: ys', b :: bs' => 
    if b then (dead_args ys' bs')
    else y :: dead_args ys' bs'
| _, _ => ys
end. 

Inductive Dead (S : Ensemble var) (L : live_fun) : exp -> Prop :=
| Live_Constr : 
    forall (x : var) (ys : list var) (ct : ctor_tag) (e : exp), 
      Disjoint _ (FromList ys) S -> 
      Dead S L e ->
      Dead S L (Econstr x ct ys e)
| Live_Prim : 
  forall (x : var) (g : prim) (ys : list var) (e : exp), 
    Disjoint _ (FromList ys) S -> 
    Dead S L e ->
    Dead S L (Eprim x g ys e)
| Live_Proj : 
    forall (x : var) (ct : ctor_tag) (n : N) (y : var) (e : exp), 
      ~ y \in S ->
     Dead S L e ->
     Dead S L (Eproj x ct n y e)
| Live_Case: 
    forall (x : var) (ce : list (ctor_tag * exp)),
      ~ x \in S ->
      Forall (fun p => Dead S L (snd p)) ce -> 
      Dead S L (Ecase x ce)
| Live_Halt : 
    forall (x : var),
      ~ x \in S ->
      Dead S L (Ehalt x)
| Live_App_Unknown :
    forall (f : var) (ys : list var) (ft : fun_tag),
      ~ f \in S ->
      Disjoint _ (FromList ys) S -> 
      L ! f = None -> 
      Dead S L (Eapp f ft ys)
| Live_App_Known :
    forall (f : var) (ys : list var) (ft : fun_tag) (bs : list bool),
      L ! f = Some bs ->
      ~ f \in S ->
      Disjoint _ S (FromList (live_args ys bs)) ->
      Dead S L (Eapp f ft ys)
| Live_LetApp_Unknown :
    forall (x f : var) (ys : list var) (ft : fun_tag) (e : exp),
      ~ f \in S ->
      Disjoint _ (FromList ys) S -> 
      L ! f = None -> 
      Dead S L (Eletapp x f ft ys e)
| Live_LetApp_Known :
    forall (x f : var) (ys : list var) (ft : fun_tag) (e : exp) (bs : list bool),
      L ! f = Some bs ->
      ~ f \in S ->
      Disjoint _ S (FromList (live_args ys bs)) ->      
      Dead S L (Eletapp x f ft ys e). 
  
  
Definition live_map_sound (B : fundefs) (L : live_fun) :=
  forall f ft xs e bs,
    fun_in_fundefs B (f, ft, xs, e) ->
    L ! f = Some bs -> 
    Dead (FromList (dead_args xs bs)) L e. 

Definition live_fun_args (L : live_fun) (f : var) (xs : list var) :=
  exists bs, L ! f = Some bs /\ length xs = length bs. 

Definition live_fun_fundefs (L : live_fun) (B : fundefs) :=
  forall f ft xs e,
    fun_in_fundefs B (f, ft, xs, e) ->
    live_fun_args L f xs.

(* Lemmas about [live] *)

Lemma live_diff B L L' d :
  live B L d = Some (L', false) ->
  d = false.
Proof.
  revert L L' d. induction B; simpl; intros L L' d Hl; eauto.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [ [L'' d''] | ].
    + eapply IHB in Hl. destruct d; eauto. destruct d''; eauto.
    + inv Hl.
  - inv Hl; eauto.
Qed.

Lemma update_live_fun_false L L' f xs S :
  live_fun_args L f xs ->
  update_live_fun L f xs S = Some (L', false) ->
  exists bs,
    get_fun_vars L f = Some bs /\
    L = L' /\ Disjoint _ (FromSet S) (FromList (dead_args xs bs)).
Proof.
  intros Hlive Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf; try congruence.
  eexists.
  split. reflexivity. 
  destruct Hlive. destructAll.
  unfold get_fun_vars in *. subst_exp.
  destruct ((fix update_bs (xs : list PS.elt) (bs : list bool) {struct xs} :
               list bool * bool :=
               match xs with
               | [] => ([], false)
               | x :: xs0 =>
                 match bs with
                 | [] => ([], false)
                 | b :: bs0 =>
                   let (bs', d) := update_bs xs0 bs0 in
                   (PS.mem x S || b :: bs', negb (eqb b (PS.mem x S)) || d)
                 end
               end) xs l) as [bs diff] eqn:Hupd.
  inv Hl.
  destruct diff. congruence. inv H2.
  assert (Hsuff : bs = l /\ Disjoint positive (FromSet S) (FromList (dead_args xs l))).
  { clear H. revert l bs Hupd H0.
    induction xs; intros l bs Hupd Heq.
    - inv Hupd.
      destruct l; inv Heq; eauto.
      split; eauto. simpl. normalize_sets. sets.
    - destruct l. now inv Heq. 
      simpl in *.
      destruct ((fix update_bs (xs : list PS.elt) (bs : list bool) {struct xs} :
                   list bool * bool :=
                   match xs with
                   | [] => ([], false)
                   | x :: xs0 =>
                     match bs with
                   | [] => ([], false)
                   | b :: bs0 =>
                     let (bs', d) := update_bs xs0 bs0 in
                     (PS.mem x S || b :: bs',
                      negb (eqb b (PS.mem x S)) || d)
                     end
                   end) xs l) as [bs' diff] eqn:Hrec.
      inv Hupd.
      eapply orb_false_iff in H1. inv H1. 
      eapply negb_false_iff in H. 
      eapply (eqb_true_iff b) in H. subst.
      inv Heq. specialize (IHxs l bs' Hrec H0). 
      destructAll.
      rewrite orb_diag. split. reflexivity.
      
      destruct (PS.mem a S) eqn:Hmem. eassumption.
      normalize_sets. eapply Union_Disjoint_r; [| eassumption ].  
      eapply Disjoint_Singleton_r. 
      intros Hc. eapply FromSet_sound in Hc; [| reflexivity ].
      eapply PS.mem_spec in Hc. congruence. }
  split. reflexivity.
  inv Hsuff. eassumption.
Qed.


(* Lemma live_expr_monotonic L e Q1 Q2 : *)
(*   FromSet Q1 \subset FromSet Q2 -> *)
(*   FromSet (live_expr L e Q1) \subset FromSet (live_expr L e Q2). *)
(* Proof. *)
(*   revert Q1 Q2. induction e using exp_ind'; intros Q1 Q2 Hsub; simpl; eauto. *)
(*   - eapply IHe. rewrite !FromSet_union_list; sets. *)
(*   - rewrite !FromSet_add; sets. *)
(*   - eapply IHe. rewrite !FromSet_add. sets. *)
(*   - eapply IHe.  *)

(*     simpl in *.  *)

(*     ~eapply IHe. rewrite !FromSet_union_list; sets. *)
(*   - *)
(*     try now (eapply Included_trans; [| eapply IHe ]; rewrite FromSet_union_list; sets). *)
(*   - rewrite FromSet_add; sets. *)
(*   - simpl in *. eapply Included_trans. eapply IHe0. *)
(*     assert (Hsub : FromSet (PS.add v Q) \subset FromSet (live_expr L e (PS.add v Q))). *)
(*     { eapply IHe. } *)
(*     clear IHe. revert Hsub. generalize (PS.add v Q), (live_expr L e (PS.add v Q)). *)
(*     clear IHe0. induction l; intros. *)
(*     + eassumption. *)
(*     + destruct a. eapply IHl; eauto. *)
(*       2:{ reflexivity. } *)

Lemma add_fun_vars_subset L v l Q : 
  FromSet Q \subset FromSet (add_fun_vars L v l Q).
Proof.
  unfold add_fun_vars. 
  destruct (get_fun_vars L v); rewrite FromSet_union_list; sets.
Qed.
        
  
Lemma live_expr_subset L e Q :
  FromSet Q \subset FromSet (live_expr L e Q).
Proof.
  revert Q; induction e using exp_ind'; intros Q; simpl;
    try now (eapply Included_trans; [| eapply IHe ]; rewrite FromSet_union_list; sets).
  - rewrite FromSet_add; sets.
  - simpl in *. rewrite !FromSet_add. setoid_rewrite FromSet_add in IHe0.
    eapply Included_trans; [| eapply IHe0 ].
    eapply IHe.
  - eapply Included_trans; [| eapply IHe ].
    rewrite FromSet_add; sets.
  - eapply Included_trans; [| eapply IHe ].
    eapply Included_trans; [| eapply add_fun_vars_subset ].
    rewrite !FromSet_add; sets.
  - sets. 
  - eapply Included_trans; [| eapply add_fun_vars_subset ].
    rewrite FromSet_add; sets.
  - rewrite FromSet_add; sets.  
Qed.

Lemma fold_left_live_expr_subset L S (P : list (ctor_tag * exp)) :
  FromSet S \subset FromSet (fold_left (fun (S : PS.t) '(_, e') => live_expr L e' S) P S).
Proof.
  revert S. induction P; simpl; intros; sets.
  destruct a. eapply Included_trans; [| eapply IHP ].
  eapply live_expr_subset.
Qed.
  
Lemma live_args_subset ys bs:
  FromList (live_args ys bs) \subset FromList ys.
Proof.
  revert bs; induction ys; intros [ | [|] bs ]; simpl; sets.
  - repeat normalize_sets. sets.
  - repeat normalize_sets. sets.
Qed.  


Lemma live_expr_sound Q L e S :
  no_fun e ->
  Disjoint _ (FromSet (live_expr L e Q)) S ->
  Dead S L e.
Proof.
  revert Q; induction e using exp_ind'; intros Q; simpl; intros Hnf Hdis; inv Hnf.  
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply Included_trans; [| eapply live_expr_subset ].
      rewrite FromSet_union_list. sets.
    + eapply IHe; eauto.
  - rewrite FromSet_add in *.
    econstructor; eauto. intros Hc.
    eapply Hdis. econstructor; eauto.
  - rewrite FromSet_add in *. econstructor.
    + intros Hc. eapply Hdis. econstructor; eauto.
    + econstructor. eapply IHe; eauto.
      * eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_Union_preserv_r.
        eapply fold_left_live_expr_subset.
      * assert (Hsuff : Dead S L (Ecase v l)).
        { eapply IHe0; eauto.
          eapply Disjoint_Included_l; [| eassumption ].
          simpl. rewrite FromSet_add. sets. }
        inv Hsuff. eassumption.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      intros Hc. 
      eapply Hdis; eauto. econstructor; eauto. eapply live_expr_subset.
      rewrite FromSet_add. sets.
    + eapply IHe; eauto.
  - destruct (L ! f) eqn:Heq.
    + eapply Live_LetApp_Known. eassumption. 
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply live_expr_subset.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_trans; [| eapply live_expr_subset ].
        unfold add_fun_vars, get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list.  sets.
    + eapply Live_LetApp_Unknown; eauto.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply live_expr_subset.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_trans; [| eapply live_expr_subset ].
        unfold add_fun_vars. unfold get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list. sets.
  - destruct (L ! v) eqn:Heq.
    + eapply Live_App_Known. eassumption. 
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
        unfold add_fun_vars, get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list.  sets.
    + eapply Live_App_Unknown; eauto.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_l; [| eassumption ].
        unfold add_fun_vars. unfold get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list. sets.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply Included_trans; [| eapply live_expr_subset ].
      rewrite FromSet_union_list. sets.
    + eapply IHe; eauto.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      intros Hc. eapply Hdis. constructor; eauto.
      rewrite FromSet_add. now sets. 
Qed. 
      
Lemma live_correct L L' B :
  no_fun_defs B -> (* no nested functions in B *)
  live_fun_fundefs L B -> (* arity in map is consistent *)
  live B L false = Some (L', false) -> 
  L = L' /\ live_map_sound B L.
Proof.
  revert L L'; induction B; simpl; intros L L' Hnf Hlive Hl.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [[L'' b] | ] eqn:Heq.
    2:{ congruence. }
    
    assert (Hd := live_diff _ _ _ _ Hl). destruct b; inv Hd.
    simpl in *. 
    edestruct update_live_fun_false; try eassumption.
    eapply Hlive.  now left. 
    destructAll.
    eapply IHB in Hl. inv Hl.
    split. reflexivity.
    { intro; intros.  inv H0.
      - inv H4. eapply live_expr_sound. inv Hnf. eassumption.
        unfold get_fun_vars in *. subst_exp.
        eassumption. 
      - eapply H2. eassumption. eassumption. } 
    inv Hnf. eassumption.
    intro; intros. 
    eapply Hlive. now right; eauto. 
  - inv Hl. split; eauto.
    intro; intros. inv H.
Qed. 

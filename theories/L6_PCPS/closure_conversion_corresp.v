(* Correspondence of the computational definition and the declarative spec for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.closure_conversion L6.closure_conversion_util.
From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions logical_relations eval state.
Require Import compcert.lib.Coqlib.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
               Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import Common.compM.
Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.

(** * Correspondence of the relational and the computational definitions of closure conversion *)


(* Sketch of what we want to show: *)

(*
Lemma exp_closure_conv_Closure_conv_sound :
  (forall e Scope Funs c Γ FVs FVmap S
          (* The invariant that relates [FVmap] and [Scope], [Funs], [FV] *)
          (Minv : FVmap_inv FVmap Scope Funs FVs)
          (* [FVmap] contains all the free variables *)
          (Hbin1 : binding_in_map (occurs_free e) FVmap)
          (* [FVmap] does not contain the variables in [S] or [Γ] *)
          (Hbin2 : binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap)
          (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
          (HD1 : Disjoint _ S (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                                     (Union _ (bound_var e)
                                            (Union _ (occurs_free e) (Singleton _ Γ)))))
          (* The current environment argument is fresh *)
          (HD2 : ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ),
      {{ fun s => fresh S (next_var s) }}
        exp_closure_conv clo_tag e FVmap Gmap c Γ
        {{ fun s ef s' =>
             exists C, is_exp_ctx (snd ef) C /\
                       Closure_conversion clo_tag Scope Funs GFuns (subst FVmap) c Γ FVs e (fst ef) C /\
                       fresh S (next_var s')
  }}) /\
  (forall B FVmap Funs FVs S c
          (Minv : FVmap_inv FVmap (Empty_set _) Funs FVs)
          (Hbin1 : binding_in_map (Union _ (occurs_free_fundefs B) (name_in_fundefs B)) FVmap)
          (Hbin2 : binding_not_in_map S FVmap)
          (HD1 : Disjoint _ S (Union _ (image (subst FVmap) Funs)
                                     (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))))
          (Hinc : Included _ (name_in_fundefs B) Funs),
      {{ fun s => fresh S (next_var s) }}
        fundefs_closure_conv clo_tag B FVmap c
        {{ fun s B' s' =>     
             Closure_conversion_fundefs clo_tag Funs (subst FVmap) c FVs B B' /\
             fresh S (next_var s')
  }}).
Proof with now eauto with Ensembles_DB functions_BD.
*)


Section CC_correct.

  Variable (clo_tag : ctor_tag).
  Variable (pr : prims).
  Variable (cenv : ctor_env).

  (** Free variable map invariant *)
  Definition FVmap_inv (FVmap : VarInfoMap) Scope Funs GFuns FVs : Prop :=
    Same_set _ Scope (fun x => M.get x FVmap = Some BoundVar) /\
    Same_set _ (Setminus _ Funs Scope)
             (fun x => exists x', M.get x FVmap = Some (MRFun x')) /\
    forall N x, (nthN FVs N = Some x /\ ~ In _ Scope x /\ ~ In _ Funs x /\ ~ In _ GFuns x) <->
           (M.get x FVmap = Some (FVar N)).

  (** Global function map invariant: gfuns agrees with GFuns *)
  Definition gfuns_inv (gfuns : GFunMap) GFuns : Prop :=
    GFuns <--> (fun x => M.get x gfuns = Some GFun).

  (** Map function name to environment *)
  Definition to_env (FVmap : VarInfoMap) x : var :=
    match M.get x FVmap with
      | Some (MRFun x') => x'
      | _ => x
    end.

  (** A function that corresponds to an evaluation context *)
  Definition is_exp_ctx (f : exp -> exp) C : Prop := 
    forall e, f e = app_ctx_f C e. 

  (** Set of variables not in the map *)
  Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) := 
    forall x : M.elt, In M.elt S x -> M.get x map = None.

  (*
  (** Spec for [get_name_entry] *)
  Lemma get_name_entry_preserves_prop x P :
    {{ fun s => P (next_var s) }} get_name_entry x {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    destruct (Maps.PTree.get x m1);
      eapply return_triple; intros ? H ?; inv H; eauto.
  Qed.

  (** Spec for [set_name_entry] *)
  Lemma set_name_entry_preserves_prop x s P :
    {{ fun s => P (next_var s) }} set_name_entry x s {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    eapply pre_post_mp_l. eapply bind_triple. 
    eapply put_triple. intros.
    eapply return_triple. intros ? ? [H1 H2]. inv H1; eauto.
  Qed.
  
  (** Specs for adding names *)
  Lemma add_name_preserves_prop x y P :
    {{ fun s => P (next_var s) }} add_name x y {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply set_name_entry_preserves_prop.
  Qed.

  Lemma add_name_suff_preserves_prop x y s P :
    {{ fun s => P (next_var s) }} add_name_suff x y s {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply bind_triple. now apply get_name_entry_preserves_prop.
    intros n s1. destruct n; now apply set_name_entry_preserves_prop.
  Qed.

  (** Spec for [get_name] *)
  Lemma get_name_fresh S y str :
    {{ fun s => fresh S (next_var s) }}
      get_name y str
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (next_var s') }}.  
  Proof.
    eapply pre_strenghtening with (P := fun s => fresh S (next_var s) /\ True); intros; eauto.
    eapply bind_triple.
    eapply frame_rule with (Pre := fun _ => True). now eapply get_triple.
    intros [x c i e m] [x' c' i' e' m'].
    eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros H. inv H.
    eapply bind_triple
    with (post' :=  fun _ _ s' => fresh (Setminus var S (Singleton var x')) (next_var s')).
    eapply pre_post_mp_l. eapply post_weakening; [| now eapply put_triple ].
    intros; subst; simpl in *. subst; simpl.
    constructor.
    - eapply Hf. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. zify. omega.
    - intros _ _. eapply bind_triple. 
      now eapply add_name_suff_preserves_prop.
      intros. eapply return_triple. intros; eauto.
  Qed.

  (** Spec for [get_name_no_suff] *)
  Lemma get_name_no_suff_fresh S str :
    {{ fun s => fresh S (next_var s) }}
      get_name_no_suff str
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (next_var s') }}.  
  Proof.
    eapply pre_strenghtening with (P := fun s => fresh S (next_var s) /\ True); intros; eauto.
    eapply bind_triple.
    eapply frame_rule with (Pre := fun _ => True). now eapply get_triple.
    intros [x c i e m] [x' c' i' e' m'].
    eapply pre_curry_l. intros Hf. eapply pre_curry_l. intros H. inv H.
    eapply bind_triple
    with (post' :=  fun _ _ s' => fresh (Setminus var S (Singleton var x')) (next_var s')).
    eapply pre_post_mp_l. eapply post_weakening; [| now eapply put_triple ].
    intros; subst; simpl in *. subst; simpl.
    constructor.
    - eapply Hf. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. zify. omega.
    - intros _ _. eapply bind_triple. 
      now eapply add_name_preserves_prop.
      intros. eapply return_triple. intros; eauto.
  Qed.
   *)

  (* TODO move to state *)
  Lemma get_name_no_suff_fresh 
     : forall (A : Type) (S : Ensemble var) (str : string),
       {{fun (_ : unit) (s : comp_data * A) => fresh S (next_var (fst s))}} get_name_no_suff str
       {{fun (_ : unit) (s : comp_data * A) (x : var) (s' : comp_data * A) =>
         In var S x /\
         In var (Range (next_var (fst s)) (next_var (fst s'))) x /\
         (next_var (fst s) < next_var (fst s'))%positive /\ fresh (S \\ [set x]) (next_var (fst s'))}}.
  Proof.
    intros.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.  
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple. 
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
    split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. omega.
    simpl. split. zify; omega.
    intros z Hin. constructor. eapply H; eauto. simpl. zify. omega.
    intros Hc. inv Hc. zify; omega.
  Qed.

  Lemma FVmap_inv_set_bound FVmap Scope Funs GFuns FVs x :
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (M.set x BoundVar FVmap) (Union _ (Singleton _ x) Scope) Funs GFuns FVs.
  Proof. 
    intros [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (peq y x); subst.
      + unfold In. now rewrite M.gss.
      + inv Hin. inv H; congruence.
        eapply H1 in H. edestruct H as [t' Heq].
        unfold In. rewrite M.gso; now eauto.
    - intros y Hin. destruct (peq y x); subst.
      + eauto.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        right. eapply H1. eauto.
    - intros y Hin. inv Hin. destruct (peq y x); subst.
      + exfalso. eauto.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x' Heq].
        * constructor; eauto.
        * eexists. rewrite M.gso; eauto.
    - eapply H2. destruct H as [x' Heq].
      destruct (peq x x0); subst.
      + rewrite M.gss in Heq. congruence.
      + repeat eexists. rewrite M.gso in Heq; eauto.
    - intros Hc. destruct H as [x' Heq].
      destruct (peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + inv Hc. inv H; congruence.
        eapply H2; eauto. repeat eexists.
        rewrite M.gso in Heq; eauto.
    - intros [Hnth [Hnin1 [Hnin2 Hnin3]]].
      destruct (peq x0 x); subst.
      + exfalso. eauto. 
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto.
        rewrite M.gso in H; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. inv Hc. inv H0; congruence.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [Hc _]]].
        eapply H3 in H0; eauto. contradiction.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ [Hc' _]]]].
        eapply H3 in Hc; eauto. contradiction.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ [_ Hc']]]].
        eapply H3 in Hc; eauto. contradiction.
  Qed.

  Lemma FVmap_inv_set_funs FVmap Scope Funs GFuns FVs x x' :
    ~ In _ Scope x ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (M.set x (MRFun x') FVmap) Scope (Union _ (Singleton _ x) Funs) GFuns FVs.
  Proof. 
    intros Hnin [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (peq y x); subst.
      + contradiction.
      + eapply H1 in Hin. edestruct Hin as [t'' Heq].
        unfold In. rewrite M.gso; eauto.
    - intros y Hin. destruct (peq y x); subst.
      + unfold In in Hin. rewrite M.gss in Hin; congruence.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        now eapply H1.
    - intros y Hin. inv Hin. destruct (peq y x); subst.
      + repeat eexists. rewrite M.gss. reflexivity.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x'' Heq].
        inv H. inv H4; congruence. constructor; eassumption.
        repeat eexists. rewrite M.gso; eassumption.
    - destruct (peq x0 x); subst; eauto. right.
      eapply H2. edestruct H as [x'' Hget].
      rewrite M.gso in Hget; [| now eauto ].
      repeat eexists; eauto. 
    - destruct H as [x'' Hget].
      destruct (peq x0 x); subst; eauto.
      rewrite M.gso in Hget; [| now eauto ].
      intros Hc. apply H1 in Hc. congruence.
    - intros [Hnth [Hnin1 [Hnin2 Hnin3]]].
      destruct (peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto. rewrite M.gso in H; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        eapply H1 in Hc. congruence.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        inv Hc. inv H0; congruence.
        edestruct H2 as [H2' _].  edestruct (H2' x0) as [y Hge'].
        constructor. eauto. intros Hc. eapply H1 in Hc. 
        congruence. congruence.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + rewrite M.gso in H; eauto.
        rewrite <- H3 in H; easy.
  Qed.

  Ltac splits := repeat match goal with |- _ /\ _ => split end.

  (** Spec for [get_var] *)
  Lemma get_var_project_var_sound Scope Funs GFuns gfuns c Γ FVs FVmap S x :
    binding_in_map (Singleton _ x) FVmap ->
    (* binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap -> *)
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      get_var clo_tag x FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S', 
           (let '(x', f) := t in
           project_var clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S x x' C S' /\
           is_exp_ctx f C /\ unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive
    }}.
  Proof.
    intros Hin Minv Hgfuns. destruct Minv as [Minv1 [Minv2 Minv3]]. 
    unfold get_var. edestruct (Hin x) as [inf Hget]; eauto. 
    destruct inf; rewrite Hget. 
    - eapply bind_triple.
      + eapply get_name_fresh.     
      + intros x' s. eapply return_triple. intros _ s' [Hx' [Hrange [Hf Hf']]].
        eexists (Eproj_c x' _ n Γ Hole_c).
        edestruct Minv3 as [H1 [H2 [H3 [H4 H5]]]]. now repeat eexists; eauto.
        eexists; splits. econstructor 4.
        all: auto.
        { unfold is_exp_ctx; reflexivity. }
        { repeat constructor. inversion 1. }
        { intros arb; repeat normalize_bound_var_ctx; normalize_sets.
          intros Harb; inv Harb. unfold In, Range in *; zify; omega. }
        { zify; omega. }
    - eapply bind_triple.
      + eapply get_name_fresh.  
      + intros x' s. eapply return_triple. intros _ s' [Hx' [Hrange [Hf Hf']]].
        edestruct Minv2 as [H1 H2]; eauto. 
        exists (Econstr_c x' clo_tag [x; v] Hole_c). eexists; splits.
        { replace v with (to_env FVmap x) by (unfold to_env; now rewrite Hget).
          specialize (H2 x); unfold In, Setminus in H2; destruct H2 as [HFuns HScope]; [now exists v|].
          econstructor 2; auto. }
        { unfold is_exp_ctx; reflexivity. }
        { repeat constructor; inversion 1. }
        { auto. }
        { intros arb; repeat normalize_bound_var_ctx; normalize_sets.
          intros Harb; inv Harb. unfold In, Range in *; zify; omega. }
        { zify; omega. }
    - eapply return_triple. intros _ [s d] Hin'.      
      exists Hole_c. eexists; splits.
      { constructor; eapply Minv1. eauto. }
      { unfold is_exp_ctx; reflexivity. }
      { constructor. }
      { auto. }
      { intros arb; repeat normalize_bound_var_ctx. intros Harb; inv Harb. }
      { zify; omega. }
  Qed.

  (* TODO: move to compM *)
  Lemma pre_post_mp_l' {R W} {A} (P : @Pre R W) (Q : @Post R W A) e :
    {{ fun r w => P r w }} e {{ fun r w x w' => P r w -> Q r w x w' }} ->
    {{ fun r w => P r w }} e {{ fun r w x w' => Q r w x w' }}.
  Proof.
    intros H.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto. 
  Qed.
  Lemma pre_post_mp_l_inv' {R W} {A} (P P' : @Pre R W) (Q : @Post R W A) e :
    (forall r w, P r w -> P' r w) ->
    {{ fun r w => P r w }} e {{ fun r w x w' => Q r w x w' }} ->
    {{ fun r w => P r w }} e {{ fun r w x w' => P' r w -> Q r w x w' }}.
  Proof.
    intros H Hpre.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto. 
  Qed.

  Lemma bind_triple' {R W A B} (m : compM R W A) (f : A -> compM R W B)
        (P : Pre) (Q : Post B) (Q' : Post A) :
    {{ P }} m {{ Q' }} ->
    (forall (x : A) w, {{ fun r w' => P r w /\ Q' r w x w' }} f x {{ fun r _ x' w' => Q r w x' w' }}) ->
    {{ P }} bind m f {{ Q }}.
  Proof.
    simpl. unfold triple; simpl. 
    intros H1 H2 r w HP.
 
    (* pose (Hm := H1 st s HP). *)
    destruct m as [fm].
    unfold runState in *; simpl in *.
    destruct (fm r w) eqn:Heq_fm, e; auto.
    specialize (H1 r w HP). rewrite Heq_fm in H1. eassumption.
    specialize (H1 r w HP). rewrite Heq_fm in H1.
    eapply H2. split; eassumption.
  Qed.
  
  (* TODO: move to Ensembles_util *)
  Lemma Disjoint_sym {A} S1 S2 : Disjoint A S1 S2 -> Disjoint A S2 S1.
  Proof. eauto with Ensembles_DB. Qed.
  
  Lemma Disjoint_Union {A} S1 S2 S3 :
    Disjoint A S1 (S2 :|: S3) -> Disjoint A S1 S2 /\ Disjoint A S1 S3.
  Proof. eauto with Ensembles_DB. Qed.

  Fixpoint unique_bindings_c_comp C D {struct C} :
    unique_bindings_c C ->
    unique_bindings_c D ->
    Disjoint _ (bound_var_ctx C) (bound_var_ctx D) ->
    unique_bindings_c (ctx.comp_ctx_f C D)
  with unique_bindings_fundefs_c_comp C D {struct C} :
    unique_bindings_fundefs_c C ->
    unique_bindings_c D ->
    Disjoint _ (bound_var_fundefs_ctx C) (bound_var_ctx D) ->
    unique_bindings_fundefs_c (ctx.comp_f_ctx_f C D).
  Proof.
    all: intros HC HD Hdis; destruct C; simpl; inv HC; normalize_bound_var_ctx_in_ctx;
      repeat match goal with
      | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_sym in H
      | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
      end.
    - apply HD.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; try assumption.
      + apply unique_bindings_c_comp; try assumption.
        now apply Disjoint_sym.
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; try assumption.
        normalize_bound_var; apply Union_Disjoint_r; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        apply Union_Disjoint_l; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + apply unique_bindings_fundefs_c_comp; try assumption. now apply Disjoint_sym.
      + rewrite (proj2 bound_var_ctx_comp_ctx).
        apply Union_Disjoint_r; try assumption.
        apply Disjoint_sym; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + rewrite (proj1 bound_var_ctx_comp_ctx). intros Hc; destruct Hc; auto.
        destruct H as [Hdis]; now contradiction (Hdis x).
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + rewrite (proj2 bound_var_ctx_comp_ctx). intros Hc; destruct Hc; auto.
        destruct H as [Hdis]; now contradiction (Hdis x).
      + rewrite (proj2 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + rewrite (proj2 bound_var_ctx_comp_ctx); apply Union_Disjoint_r; try assumption.
        now apply Disjoint_sym.
      + apply unique_bindings_fundefs_c_comp; try assumption. now apply Disjoint_sym.
  Qed.
  
  (** Spec for [get_vars] *)
  Lemma get_vars_project_vars_sound' Scope Funs GFuns gfuns c Γ FVs FVmap S xs S_pre s_pre :
    binding_in_map (FromList xs) FVmap ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) /\ S_pre \subset Range s_pre (next_var (fst s))
               /\ (next_var (fst s) >= s_pre)%positive }}
      get_vars clo_tag xs FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S', 
           (let '(xs', f) := t in
           project_vars clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S xs xs' C S' /\
           is_exp_ctx f C /\
           unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive }}.
  Proof.
    intros Hb Hfv Hgfuns.
    revert S S_pre s_pre Hb Hfv Hgfuns. induction xs; intros S S_pre s_pre Hb Hfv Hgfuns.
    - eapply return_triple. intros _ s [Hf _].
      eexists Hole_c. eexists; splits.
      + constructor.
      + unfold is_exp_ctx; reflexivity. + constructor.
      + auto.
      + intros x; inversion 1.
      + zify; omega.
    - eapply bind_triple.
      + eapply pre_strenghtening; [|eapply get_var_project_var_sound; eauto].
        { simpl; intros ? ? [Hleft ?]; exact Hleft. }
        intros x Hin. eapply Hb. 
        inv Hin. constructor. eauto.
      + intros [x f] s1.
        eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq]].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply (IHxs S'); eauto.
        { intros y Hin. eapply Hb. constructor 2. eassumption. }
        intros [xs' f'] s2. eapply return_triple.  
        intros _ s [C' [S'' [[Hproj' [Hctx' Huniq']] [Hf' [Hran' Hinc']]]]] [Hf [Hran Hinc]].
        exists (comp_ctx_f C C'), S''; splits; auto.
        * econstructor; eauto.
        * unfold is_exp_ctx; intros e.
          now rewrite Hctx, Hctx', app_ctx_f_fuse.
        * apply unique_bindings_c_comp; auto.
          eapply Disjoint_Included_l; [apply Hran|].
          eapply Disjoint_Included_r; [apply Hran'|].
          constructor; intros arb Harb; inv Harb; unfold In, Range in *; zify; omega.
        * normalize_bound_var_ctx.
          apply Union_Included; eapply Included_trans; try eassumption.
          all: intros arb Harb; unfold Range, In in *; zify; omega.
        * zify; omega.
  Qed.

  Corollary get_vars_project_vars_sound Scope Funs GFuns gfuns c Γ FVs FVmap S xs :
    binding_in_map (FromList xs) FVmap ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      get_vars clo_tag xs FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S', 
           (let '(xs', f) := t in
           project_vars clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S xs xs' C S' /\
           is_exp_ctx f C /\
           unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive }}.
  Proof.
    intros Hb Hfv Hgfuns.
    eapply pre_strenghtening.
    2: apply get_vars_project_vars_sound' with (S_pre := Empty_set _) (s_pre := 1%positive); auto.
    intros st s Hfresh; split; auto; split; eauto with Ensembles_DB; zify; omega.
  Qed.
  
  Lemma to_env_BoundVar_f_eq_subdomain FVmap x S :
    f_eq_subdomain S ((to_env FVmap) {x ~> x}) (to_env (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold to_env, extend. rewrite M.gsspec.
    destruct (peq x' x). now eauto. reflexivity. 
  Qed.

  Lemma to_env_BoundVar_f_eq FVmap x :
    f_eq ((to_env FVmap) {x ~> x}) (to_env (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold to_env, extend. rewrite M.gsspec.
    destruct (peq x' x). now eauto. reflexivity. 
  Qed.

  Lemma Disjoint_free_set FVmap Scope Funs GFuns FVs S :
    binding_not_in_map S FVmap ->
    Disjoint _ GFuns S ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    Disjoint _ S (Union var Scope
                        (Union var Funs (FromList FVs))).
  Proof.             
    intros Hb Hdis [Hinv1 [Hinv2 Hinv3]].
    constructor. intros x Hc. inv Hc. 
    assert (Hdec1 : Decidable Scope).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros; congruence. 
      - right. intros; congruence. }
    assert (Hdec2 : Decidable (Setminus _ Funs Scope)).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [y Hc]; congruence. 
      - right. intros [y Hc]; congruence. }
    destruct Hdec1, Hdec2. destruct (Dec x) as [Hin | Hnin]. 
    - eapply Hinv1 in Hin.
      unfold In in Hin. rewrite Hb in Hin; eauto. congruence.
    - destruct (Dec0 x) as [Hin' | Hnin'].
      + eapply Hinv2 in Hin'. destruct Hin' as [y Heq].
        rewrite Hb in Heq; eauto. congruence.
      + unfold binding_not_in_map in Hb.
        inv H0; try contradiction.
        inv H1. now eapply Hnin'; constructor; eauto.
        unfold In, FromList in H0.        
        edestruct In_nthN as [N Hnth]; [ eassumption |].
        destruct (Hinv3 N x) as [Hinv3' _].
        rewrite Hb in Hinv3'; [| eassumption ].
        assert (H3 : ~ Funs x) by (intros Hc; eapply Hnin'; constructor; eauto).
        assert (Hgfuns : ~ GFuns x). {
          intros Hc; destruct Hdis as [Hdis]; specialize (Hdis x).
          apply Hdis; now constructor. }
        specialize (Hinv3' (conj Hnth (conj Hnin (conj H3 Hgfuns)))). congruence.
  Qed.
  
  Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
    Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
  Proof. 
    intros Hin Hb x Hin'. eauto.
  Qed.

  Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
    binding_not_in_map S map ->
    ~ In _ S x ->
    binding_not_in_map S (M.set x v map). 
  Proof. 
    intros HB Hnin x' Hin.
    rewrite M.gsspec. destruct (peq x' x); subst; try contradiction. 
    eauto. 
  Qed.

  Import MonadNotation.

  Transparent bind ret.

  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase {S} m1 (m2 : @compM' S (var * (exp -> exp))) y :
    st_eq
      (ys <- m1 ;; 
       ys' <- ret (y :: ys) ;;
       t1 <- m2 ;;
       let '(x, f) := t1 in
       ret (Ecase x ys', f))
      (fe <- (ys <- m1 ;;
             t1 <- m2 ;;
             let '(x, f1) := t1 in    
             ret (Ecase x ys, f1)) ;;
       match fe with
         | (Ecase x ys, f) =>
           ret (Ecase x (y :: ys), f)
         | _ => ret fe
       end).
  Proof.
    unfold pbind, ret.
    intros r s. simpl. destruct (runState m1 r s).
    destruct e; simpl; auto.
    destruct (runState m2 r p).
    destruct e; simpl; auto.
    destruct p1 as [x f]; simpl; auto.
  Qed.

  Global Opaque bind ret.

  Global Instance FVmap_inv_Scope_Proper :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 S5 S6 Heq6 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq2; eauto. 
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite Heq2.
      intros H. rewrite <- Heq2. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq2; eauto. 
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq2.
      intros H. rewrite Heq2. eapply H3. eassumption. 
  Qed.

  Global Instance FVmap_inv_Funs_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 S5 S6 Heq6 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq3; eauto.
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite Heq3.
      intros H. rewrite <- Heq3. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq3; eauto. 
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq3.
      intros H. rewrite Heq3. eapply H3. eassumption. 
  Qed.

  Lemma FVmapInv_add_params FVmap xs Scope Funs GFuns FVs :
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (add_params xs FVmap) (Union _ Scope (FromList xs)) Funs GFuns FVs. 
  Proof. 
    revert FVmap Scope. induction xs; intros FVmap Scope Hinv.
    - rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - rewrite FromList_cons.
      rewrite Union_assoc, Union_commut with (s2 := Singleton M.elt a), <- Union_assoc. 
      eapply FVmap_inv_set_bound; eauto.
  Qed.

  Lemma binding_in_map_add_params S FVmap xs :
    binding_in_map S FVmap ->
    binding_in_map (Union _ S  (FromList xs)) (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb.
    - intros x. rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - intros x. rewrite FromList_cons.
      rewrite Union_commut with (s2 := FromList xs), Union_assoc.
      simpl. eapply binding_in_map_set; eauto. 
  Qed.

  Lemma binding_not_in_map_add_params S FVmap xs :
    binding_not_in_map S FVmap ->
    Disjoint _ S (FromList xs) ->
    binding_not_in_map S (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb Hd.
    - eauto.
    - rewrite FromList_cons in Hd.
      eapply binding_not_in_map_set_not_In_S; eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
  Qed.
  
  Lemma FVmap_inv_empty GFuns :
    FVmap_inv (Maps.PTree.empty VarInfo) (Empty_set M.elt) (Empty_set M.elt) GFuns [].
  Proof.
    repeat split; (try now intros Hc; inv Hc); (try now intros x Hc; inv Hc). 
    intros x Hx. unfold In in Hx. rewrite M.gempty in Hx. now inv Hx.
    destruct H as [x' Hget]. rewrite M.gempty in Hget. now inv Hget.
    rewrite M.gempty in H. now inv H.
    rewrite M.gempty in H. now inv H.
  Qed.
    
  Lemma FVmap_inv_set_free_var FVmap Scope Funs GFuns FVs x n:
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    N.of_nat (length FVs) = n ->
    ~ In _ Scope x -> ~ In  _ Funs x -> ~ In _ GFuns x -> ~ List.In x FVs ->
    FVmap_inv (Maps.PTree.set x (FVar n) FVmap) Scope Funs GFuns (FVs ++ [x]). 
  Proof.  
    intros [H1 [H2 H3]] Hlen Hnin1 Hnin2 Hnin3.
    split; [| split ]. 
    - split.
      + intros x' Hin. assert (Hin' := Hin). eapply H1 in Hin.
        destruct (peq x' x).
        subst; contradiction.
        unfold In. now rewrite M.gso; eauto.
      + intros x' Hget. eapply H1. 
        unfold In in Hget. rewrite M.gsspec in Hget. destruct (peq x' x).
        subst; congruence. now eauto.
    - split.
      + intros x' Hin. assert (Hin' := Hin). inv Hin'. 
        eapply H2 in Hin. edestruct Hin as [y Heq].
        destruct (peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [y Hget]. eapply H2. 
        rewrite M.gsspec in Hget. destruct (peq x' x).
        subst; congruence.
        now eauto.
    - intros N x'. split.
      + intros [Hnth [Hnin1' [Hnin2' Hnin3']]].
        destruct (nthN_app FVs [x] N) as [Hn | [Hn Hlen']].
        * destruct (peq x' x); subst.
          exfalso. eapply H. eapply nthN_In. rewrite <- Hnth. now eauto.
          edestruct H3 as [Hget _].
          rewrite M.gso; eauto. eapply Hget. repeat split; eauto.
          rewrite <- Hnth. now eauto.
        * subst. rewrite Hnth in Hn. eapply nthN_is_Some_length in Hnth.
          rewrite app_length in Hnth. simpl length in *.
          destruct (N - N.of_nat (length FVs))%N eqn:Heq; simpl in Hn; try congruence.
          inv Hn. rewrite M.gss; eauto.
          repeat f_equal. zify. omega. 
      + subst. intros Hget.
        rewrite M.gsspec in Hget. destruct (peq x' x).
        * subst. inv Hget. repeat split; eauto.
          rewrite nthN_app_geq. rewrite N.sub_diag. reflexivity. 
          zify; omega. 
        * edestruct H3 as [_ [H1' [H2' [H3' H4']]]].
          eassumption.
          repeat split; eauto. apply nthN_is_Some_app. eassumption.
  Qed.

  Lemma make_record_ctor_tag_preserves_prop n P :
    {{ fun _ s => P (next_var (fst s)) }}
      make_record_ctor_tag n
    {{ fun _ _ _ (s : comp_data * unit) => P (next_var (fst s)) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [[x1 c1 f1 e1 m1] []] [[x2 c2 f2 e2 m2] []].
    apply pre_post_mp_l. eapply bind_triple. now apply put_triple.
    intros [] s. eapply return_triple. intros _ s'. intros <-. intros [H1 H2]; subst. inv H1.
    intros.
    eassumption.
  Qed.

  Lemma make_env_spec fv FVmap_o c Γ_n Γ_o Scope Funs GFuns gfuns FVs S :
    binding_in_map (FromList fv) FVmap_o ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ_o)) FVmap_o ->
    FVmap_inv FVmap_o Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    Disjoint _ GFuns (FromList fv) ->
    NoDup fv ->
    ~ Γ_n \in S ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      make_env clo_tag fv (Maps.PTree.empty VarInfo) FVmap_o c Γ_n Γ_o gfuns
    {{ fun _ s t  s' =>
         let '(c', FVmap_n, f) := t in
         exists C S' FVs',
           (project_vars clo_tag Scope Funs GFuns c (to_env FVmap_o) Γ_o FVs S fv FVs' C S' /\
           is_exp_ctx f (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c)) /\
           unique_bindings_c (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c))) /\
           fresh S' (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive /\
           binding_in_map (FromList fv) FVmap_n /\
           binding_not_in_map (Complement _ (FromList fv)) FVmap_n /\
           FVmap_inv FVmap_n (Empty_set _) (Empty_set _) GFuns fv
     }}.
  Proof. 
    intros Hb1 Hb2 Minv Hgfuns Hdis Hdup Hnin. unfold make_env.
    destruct ((fix
                 add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
                 {struct l} : Maps.PTree.t VarInfo * N :=
                 match l with
                   | [] => (map, n)
                   | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                 end)
                fv 0%N (Maps.PTree.empty VarInfo)) as [map_new n] eqn:Heq.
    apply pre_post_mp_l'. eapply bind_triple.
    - eapply get_vars_project_vars_sound; eauto.
    - intros [xs f] s1.
      eapply pre_existential. intros C1. eapply pre_existential. intros S'.
      eapply pre_curry_l. intros [Hvars [Hctx Huniq]].
      eapply bind_triple.
      apply make_record_ctor_tag_preserves_prop with (n := n)
        (P := fun x => fresh S' x /\
          bound_var_ctx C1 \subset Range (next_var (fst s1)) x /\
          (x >= next_var (fst s1))%positive).
      intros tau s2. eapply return_triple.
      intros _ s3 [Hf [Hran Hinc]] Hfresh.
      do 3 eexists. split; [splits|split; [|split]]; try eassumption.
      + intros e. rewrite Hctx. rewrite <- app_ctx_f_fuse. now f_equal.
      + apply unique_bindings_c_comp; auto.
        { repeat constructor; inversion 1. }
        repeat normalize_bound_var_ctx; normalize_sets.
        constructor; intros arb Harb; inv Harb. inv H0.
        contradiction Hnin.
        apply Hran in H.
        apply Hfresh.
        unfold In, Range in *; zify; omega.
      + replace map_new with
        (fst ((fix
                add_fvs (l : list M.elt) (n : N)
                (map : Maps.PTree.t VarInfo) {struct l} :
                Maps.PTree.t VarInfo * N :=
                match l with
                  | [] => (map, n)
                  | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                end) fv 0%N (Maps.PTree.empty VarInfo)))
          by (rewrite Heq; eauto).
        clear - Hdis Hdup.
        assert (He : FVmap_inv (Maps.PTree.empty VarInfo)
                               (Empty_set M.elt) (Empty_set M.elt) GFuns [])
          by apply FVmap_inv_empty.
        assert (Hb : binding_in_map (FromList (@nil PS.elt)) (Maps.PTree.empty VarInfo))
          by (intros x H; inv H).
        assert (Hb' : binding_not_in_map (Complement _ (FromList ((@nil PS.elt))))
                                         (Maps.PTree.empty VarInfo))
          by (intros x H; rewrite Maps.PTree.gempty; reflexivity).
        assert (Hlen : N.of_nat (@length PS.elt []) = 0%N) by eauto.
        assert (Hnin : forall x, List.In x fv -> ~ List.In x [])
          by (intros x H1 H2; inv H2).
        replace fv with ([] ++ fv) at 1 3 6 by reflexivity.
        revert Hlen He Hb Hb' Hnin Hdis Hdup. generalize (Maps.PTree.empty VarInfo) as FVmap_i.
        unfold PS.elt, map_util.M.elt in *.
        generalize (@nil positive). generalize 0%N. 
        induction fv as [|v fv IHfv]; intros n vars FVmap_i Hlen Hinv Hb Hb' Hnin Hdis Hdup.
        * simpl. rewrite app_nil_r. eauto.
        * simpl. replace (vars ++ v :: fv) with ((vars ++ [v]) ++ fv). simpl.
          eapply IHfv. rewrite app_length. simpl. zify. omega.
          eapply FVmap_inv_set_free_var. now eauto. eassumption. 
          now intros Hc; inv Hc. now intros Hc; inv Hc. 
          { normalize_sets. apply Disjoint_sym, Disjoint_Union_l in Hdis.
            intros Hc; destruct Hdis as [Hdis]; now contradiction (Hdis v). }
          { eapply Hnin. constructor. reflexivity. }
          { intros x H. eapply binding_in_map_set. eassumption.
            rewrite FromList_app, FromList_cons, FromList_nil, Union_Empty_set_neut_r in H.
            eassumption. }
          { eapply binding_not_in_map_set_not_In_S.
            eapply binding_not_in_map_antimon; [| eassumption ].  
            eapply Complement_antimon. rewrite FromList_app. now apply Included_Union_l.
            intros Hc. eapply Hc.
            rewrite FromList_app, FromList_cons, FromList_nil. now eauto. }
          { intros x Hin Hc. eapply Hnin.
            - now constructor 2; eauto.
            - inv Hdup. apply Coqlib.in_app in Hc. inv Hc; eauto. inv H. 
              exfalso. eapply H1. eauto. now inv H0. }
          { normalize_sets.
            now apply Disjoint_sym, Disjoint_Union_r, Disjoint_sym in Hdis. }
          { now inv Hdup. }
          { now rewrite <- app_assoc. }
  Qed.

  Lemma to_env_MRFun_f_eq (FVmap : VarInfoMap) (x x' : var) :
    f_eq ((to_env FVmap) {x ~> x'}) (to_env (M.set x (MRFun x') FVmap)).
  Proof.
    unfold to_env. intros y. unfold extend.
    rewrite M.gsspec. destruct (peq y x); eauto.
  Qed.

  (*
  Lemma make_full_closure_spec B FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2' :
    binding_in_map S1 FVmap_o -> 
    binding_in_map S2 FVmap_n ->
    binding_not_in_map S1' FVmap_o -> 
    binding_not_in_map S2' FVmap_n ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    FVmap_inv FVmap_n (Empty_set _) (Empty_set _) FVs' ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B FVmap_n FVmap_o Γ
    {{ fun s t s' =>
         let '(FVmap_n', FVmap_o', f) := t in
         exists C S',
           fresh S' (next_var s') /\
           make_closures clo_tag B S Γ C (subst FVmap_n') S' /\
           is_exp_ctx f C /\
           f_eq_subdomain (Setminus _ Funs (Union _ Scope (name_in_fundefs B)))
                          (subst FVmap_o) (subst FVmap_o') /\
           binding_in_map (Union _ S1 (name_in_fundefs B)) FVmap_o' /\
           binding_in_map (Union _ S2 (name_in_fundefs B)) FVmap_n' /\
           binding_not_in_map (Setminus _ S1' (name_in_fundefs B)) FVmap_o' /\
           binding_not_in_map (Setminus _ S2' (name_in_fundefs B)) FVmap_n' /\
           FVmap_inv FVmap_o' (Union _ (name_in_fundefs B) Scope) Funs FVs /\
           FVmap_inv FVmap_n' (Empty_set _) (name_in_fundefs B) FVs'
     }}.
  Proof with now eauto with Ensembles_DB.
    revert FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2'.
    induction B;
      intros FVmap_n FVmap_o Γ Scope Funs FVs FVs' S
             S1 S2 S1' S2' Hb1 Hb2 Hb1' Hb2'  Minv_o Minv_n. 
    - eapply bind_triple; [ now apply get_name_fresh |].
      intros x s1. eapply pre_curry_l. intros Hx.
      eapply bind_triple; [ eapply IHB; eassumption |].
      intros [[FVmap_n' FVmap_o'] f'] _.
      eapply pre_existential. intros C. eapply pre_existential. intros S'.
      eapply pre_curry_r.
      intros [Hclo [Hctx [Hfeq [Hbn [Hbo [Hbn' [Hbo' [Minv_o' Minv_n']]]]]]]].
      apply return_triple. 
      intros s3 Hf. do 2 eexists. split. eassumption. 
      split. econstructor. eassumption. eapply Hx. zify; omega.
      rewrite <- subst_MRFun_f_eq. reflexivity.
      split. intros e'. simpl. rewrite Hctx. reflexivity.
      split. rewrite <- subst_BoundVar_f_eq.
      apply f_eq_subdomain_extend_not_In_S_r.
      intros Hc. inv Hc. eapply H0. right. left. now eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
      split.
      eapply binding_in_map_antimon;[| eapply binding_in_map_set; eassumption ]...
      split. simpl.
      eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ]...
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ]...
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ]...
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. simpl. rewrite <- Union_assoc. eapply FVmap_inv_set_bound.
      eassumption.
      simpl. apply FVmap_inv_set_funs. now apply not_In_Empty_set.
      eassumption. 
    - eapply return_triple. intros s Hs. do 2 eexists.
      split. eassumption. split. now constructor.
      split. intros e. reflexivity.
      split. intros x H. reflexivity.
      split. intros x H. eapply Hb1. now rewrite Union_Empty_set_neut_r in H.
      split. intros x H. eapply Hb2. now rewrite Union_Empty_set_neut_r in H.
      split. eapply binding_not_in_map_antimon; [| eassumption ]...
      split. eapply binding_not_in_map_antimon; [| eassumption ]...
      split. rewrite Union_Empty_set_neut_l. eassumption.
      eassumption. 
  Qed.
  *)

  Global Instance extend_fundefs'_Proper S :
    Proper (f_eq_subdomain S ==> eq ==> eq ==> f_eq_subdomain S) extend_fundefs'.
  Proof. 
    intros σ σ' Hσ B B' HB Γ Γ' HΓ; unfold extend_fundefs'; intros g Hg; subst;
      destruct (Dec g) as [Hin|Hnin]; auto.
  Qed.

  Lemma extend_fundefs'_eq_subdomain S σ σ' B Γ :
    f_eq_subdomain S σ σ' ->
    f_eq_subdomain (name_in_fundefs B :|: S) (extend_fundefs' σ B Γ) (extend_fundefs' σ' B Γ).
  Proof. 
    unfold extend_fundefs'; intros Hσ g Hg.
    destruct (Dec g) as [Hin|Hnin]; auto.
    rewrite Hσ; auto.
    now destruct Hg.
  Qed.

  Lemma add_closures_spec B FVmap Γ :
    f_eq_subdomain (fun _ => True) (to_env (add_closures B FVmap Γ)) (extend_fundefs' (to_env FVmap) B Γ).
  Proof.
    induction B as [f ft xs e B IHB|].
    - intros x _; simpl. unfold to_env at 1.
      destruct (Pos.eq_dec f x) as [Heq|Hne]; subst; [rewrite M.gss|rewrite M.gso by auto].
      + unfold extend_fundefs'. destruct (@Dec _ (name_in_fundefs _) _ x) as [Hin|Hnin]; auto.
        contradiction Hnin; now left.
      + unfold f_eq_subdomain, to_env at 1 in IHB. rewrite IHB by auto. unfold extend_fundefs'.
        destruct (@Dec _ (name_in_fundefs B) _ x) as [HinB|HninB];
        destruct (@Dec _ (name_in_fundefs _) _ x) as [HinC|HninC]; auto.
        * contradiction HninC; now right.
        * contradiction Hne; inv HinC; [now inv H|easy].
    - intros x _; simpl; unfold extend_fundefs'.
      destruct (@Dec _ (name_in_fundefs Fnil) _ x) as [Hin|]; [inv Hin|]; auto.
  Qed.

  Lemma add_closures_gfuns_open B gfuns :
    add_closures_gfuns B gfuns false = gfuns.
  Proof. induction B as [f ft xs e B IHB|]; simpl in *; congruence. Qed.

  Lemma add_closures_gfuns_closed B gfuns Funs GFuns
        (HFuns : Funs <--> name_in_fundefs B)
        (HGFuns : gfuns_inv gfuns GFuns) :
    gfuns_inv (add_closures_gfuns B gfuns true) (Funs :|: GFuns).
  Proof.
    generalize dependent Funs; induction B as [f ft xs e B IHB|]; intros Funs HFuns.
    - simpl in *; unfold gfuns_inv in *.
      specialize IHB with (Funs := name_in_fundefs B).
      rewrite HFuns, <- Union_assoc, IHB by eauto with Ensembles_DB.
      split; intros x Hx.
      + inv Hx; unfold In in *; [inv H; now rewrite M.gss|].
        destruct (Pos.eq_dec f x); subst; [rewrite M.gss|rewrite M.gso by auto]; auto.
      + unfold In in *; destruct (Pos.eq_dec f x); subst;
          [rewrite M.gss in Hx|rewrite M.gso in Hx by auto]; [now left|now right].
    - unfold gfuns_inv. rewrite HFuns; simpl; normalize_sets; apply HGFuns.
  Qed.

  Inductive squash A : Prop := mk_squash : A -> squash A.
  Lemma add_closures_gfuns_spec B gfuns is_closed Funs FVs GFuns :
    reflect (FVs <--> Empty_set _) is_closed ->
    Funs <--> name_in_fundefs B ->
    Disjoint _ Funs GFuns ->
    gfuns_inv gfuns GFuns -> exists GFuns',
    gfuns_inv (add_closures_gfuns B gfuns is_closed) GFuns' /\
    squash (add_global_funs GFuns Funs FVs GFuns').
  Proof.
    destruct is_closed.
    - intros Hclos HFuns Hdis Hgfuns.
      exists (Funs :|: GFuns); split.
      + now apply add_closures_gfuns_closed.
      + constructor; constructor. now inv Hclos.
    - intros Hclos HFuns Hdis Hgfuns; inv Hclos; exists (GFuns \\ Funs); split.
      + rewrite add_closures_gfuns_open.
        apply Disjoint_sym, Setminus_Disjoint in Hdis.
        unfold gfuns_inv. rewrite Hdis. apply Hgfuns.
      + constructor. now constructor.
  Qed.

  (* Rewrite does not exactly works for these two, but they are still useful as lemmas *)
  Global Instance project_var_Proper Scope Funs GFuns c :
    Proper
      (f_eq_subdomain (Funs \\ Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_var clo_tag Scope Funs GFuns c).
  Proof. 
    constructor; subst; intros Hproj; inv Hproj; try (now constructor; eauto).
    - rewrite H; now econstructor; eauto.
    - rewrite <- H; now econstructor; eauto.
  Qed.
  
  Global Instance project_vars_Proper Scope Funs GFuns c :
    Proper
      (f_eq_subdomain (Funs \\ Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_vars clo_tag Scope Funs GFuns c).
  Proof. 
      constructor; subst; intros Hproj; induction Hproj; try (now constructor; eauto).
      - econstructor. eapply project_var_Proper; eauto.
        now symmetry. now eauto.
      - econstructor. now eapply project_var_Proper; eauto. now eauto.
  Qed.

  Lemma Closure_conversion_f_eq_subdomain_mut :
    (forall e Scope Funs GFuns σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c σ Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs GFuns c σ' Γ FVs e e' C) /\
    (forall B Funs GFuns c FVs B'
       (Hinc : Included _ (name_in_fundefs B) (name_in_fundefs Funs))
       (Hcc : Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'),
       Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B').
  Proof with now eauto with Ensembles_DB. 
    eapply exp_def_mutual_ind; intros; inv Hcc.
    - econstructor; try reflexivity.
      rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      inv H12; constructor.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      inv H14. inv H4. simpl in H1; subst. destruct H2 as [C' [e' [Heq Hcc]]].
      constructor. now split; eauto.
      assert (Hcc' : Closure_conversion clo_tag Scope Funs GFuns c0 σ' Γ FVs
                                        (Ecase v l)  (Ecase x' l') C).
      { eapply H0. econstructor; eauto. eassumption. }
      now inv Hcc'.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - rewrite image_f_eq_subdomain in H5 by eassumption.
      econstructor; try reflexivity. { eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { eassumption. } { eassumption. } { eassumption. }
      eapply H; eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity; try eassumption.
      { rewrite <- image_f_eq_subdomain; eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { rewrite <- image_f_eq_subdomain by eassumption. eassumption. }
      { rewrite <- image_f_eq_subdomain by eassumption. eassumption. }
      { eapply H0; [eassumption|].
        eapply f_eq_subdomain_antimon; [|apply extend_fundefs'_eq_subdomain; eassumption].
        rewrite Union_commut.
        rewrite <- Union_Setminus_Setminus_Union; [|auto with Decidable_DB].
        eauto with Ensembles_DB. }
    - econstructor; try reflexivity.
      { rewrite <- image_f_eq_subdomain; eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { assumption. } { assumption. } { assumption. }
    - econstructor. rewrite <- image_f_eq_subdomain; eassumption.
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      eapply H; [eassumption|].
      eapply f_eq_subdomain_antimon; [|eassumption]...
    - econstructor. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
    - econstructor; try eassumption.
    - constructor. 
  Qed.

  Corollary Closure_conversion_f_eq_subdomain :
    forall e Scope Funs GFuns σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c σ Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs GFuns c σ' Γ FVs e e' C.
  Proof.
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

  Corollary Closure_conversion_fundefs_f_eq_subdomain :
    forall B Funs GFuns c FVs B'
       (Hinc : Included _ (name_in_fundefs B) (name_in_fundefs Funs))
       (Hcc : Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'),
       Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'.
  Proof. 
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

(*
  Lemma subst_add_params_f_eq_subdomain S l FVmap :
    Disjoint _ (FromList l) S ->
    f_eq_subdomain S
     (subst (add_params l FVmap)) (subst FVmap).
  Proof.
    intros Hd. induction l.
    - simpl. reflexivity.
    - simpl. rewrite <- subst_BoundVar_f_eq_subdomain.
      eapply f_eq_subdomain_extend_not_In_S_l.
      intros H. eapply Hd. constructor. rewrite FromList_cons.
      now left. eassumption.
      eapply IHl. eapply Disjoint_Included_l; [| eassumption ].
      rewrite FromList_cons. now apply Included_Union_r.
  Qed.
    
  Hint Resolve image_Setminus_extend : functions_BD.
 *)

  Ltac solve_Union_Inc :=
    repeat match goal with |- _ :|: _ \subset _ => apply Union_Included end; eauto with Ensembles_DB.
  Ltac decomp_Disjoint :=
    repeat match goal with
    | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
    | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_sym in H
    end.
  Ltac splits_Disjoint :=
    repeat match goal with
    | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r
    | |- Disjoint _ (_ :|: _) _ => apply Union_Disjoint_l
    end.

  (* TODO: move to compM *)
  Lemma pre_curry_rr {R W A} (P1 P2 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P2 st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_curry_rl {R W A} (P1 P2 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P' /\ P2 st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_and_swap {R W A} (P1 P2 : @Pre R W) (Q : Post A) e :
    {{ fun st s => P2 st s /\ P1 st s }} e {{ Q }} ->
    {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_existential_r {R W A B} (P1 : @Pre R W) (P2 : B -> @Pre R W) (Q : Post A) e :
    (forall b, {{ fun st s => P1 st s /\ P2 b st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ exists b, P2 b st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. destruct HP; eapply Hyp; eauto.
  Qed.

  (* move to proper file *)
  Lemma fresh_inc S x y : (y >= x)%positive -> fresh S x -> fresh S y.
  Proof. unfold fresh, In; intros Hyx Hx; intros; apply Hx; zify; omega. Qed.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs GFuns gfuns c Γ FVs FVmap S
       (* The invariant that relates [FVmap] and [Scope], [Funs], [GFuns], [FV] *)
       (Minv : FVmap_inv FVmap Scope Funs GFuns FVs)
       (* [FVmap] contains all the free variables *)
       (Hbin1 : binding_in_map (occurs_free e) FVmap)
       (* [FVmap] does not contain the variables in [S] or [Γ] *)
       (Hbin2 : binding_not_in_map (S :|: [set Γ]) FVmap)
       (* [gfuns] relates to [GFuns] *)
       (Hgfuns : gfuns_inv gfuns GFuns)
       (Huniq : unique_bindings e)
       (Hdis1 : Disjoint _ Funs Scope)
       (Hdis2 : Disjoint _ (Funs :|: GFuns) (bound_var e))
       (* [S] is disjoint with the free and bound variables of [e] and [Γ] and ran(to_env FVmap) *)
       (HD1 : Disjoint _ S ((Funs \\ Scope) :|: GFuns :|: used_vars e :|: [set Γ]
                                            :|: image (to_env FVmap) (Funs \\ Scope)))
       (* The current environment argument is fresh *)
       (HD2 : ~ In _ (used_vars e) Γ),
       {{ fun _ s => fresh S (next_var (fst s)) }}
         exp_closure_conv clo_tag e FVmap gfuns c Γ
       {{ fun _ s ef s' =>
            fresh S (next_var (fst s')) /\
            exists C, is_exp_ctx (snd ef) C /\
              Closure_conversion clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs e (fst ef) C /\
              bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
              (next_var (fst s') >= next_var (fst s))%positive /\
              bound_var (fst ef) \subset bound_var e :|: Range (next_var (fst s)) (next_var (fst s')) /\
              unique_bindings (C |[ fst ef ]|)
       }}) /\
    (forall B Bg Bl FVmap Funs GFuns gfuns FVs S c
       (HB : Bg = fundefs_append Bl B)
       (HFuns : Funs <--> name_in_fundefs Bg)
       (HGFuns : gfuns_inv gfuns GFuns)
       (Minv : FVmap_inv FVmap (Empty_set _) (Empty_set _) GFuns FVs)
       (Hbin1 : binding_in_map (occurs_free_fundefs Bg :|: name_in_fundefs Bg) FVmap)
       (Hbin2 : binding_not_in_map S FVmap)
       (Huniq : unique_bindings_fundefs B)
       (HD1 : Disjoint _ S (used_vars_fundefs Bg :|: image (to_env FVmap) Funs :|: GFuns))
       (HD2 : Disjoint _ GFuns (bound_var_fundefs Bg \\ name_in_fundefs Bg)),
       {{ fun _ s => fresh S (next_var (fst s)) }}
         fundefs_closure_conv clo_tag Bg B FVmap gfuns c
       {{ fun _ s B' s' =>     
          fresh S (next_var (fst s')) /\
          Closure_conversion_fundefs clo_tag Bg GFuns c FVs B B' /\
          bound_var_fundefs B' \subset bound_var_fundefs B :|: Range (next_var (fst s)) (next_var (fst s')) /\
          (next_var (fst s') >= next_var (fst s))%positive /\
          unique_bindings_fundefs B'
       }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    eapply exp_def_mutual_ind; intros; simpl. Opaque exp_closure_conv.
    - apply pre_post_mp_l'; eapply bind_triple.
      + eapply get_vars_project_vars_sound; try eassumption.
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply pre_strenghtening.
        { intros ? ? [Hleft ?]; exact Hleft. }
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Econstr_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { unfold used_vars in HD1. eapply HD1; constructor; [eassumption|].
            left; left; right; left; eauto. }
          { inv H0; eapply HD2; unfold used_vars; eauto. }
        * assumption.
        * now inv Huniq.
        * normalize_bound_var_in_ctx. decomp_Disjoint. eauto with Ensembles_DB.
        * normalize_bound_var_in_ctx.
          decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        * eapply Disjoint_Included_l.
          eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          -- apply Included_Union_compat; [|now apply Included_refl].
             normalize_used_vars; rewrite Union_assoc.
             apply Included_Union_compat; [|now apply Included_refl].
             eauto with Ensembles_DB.
          -- admit. (* should be easy *)
        * intros Hc. inv Hc; eapply HD2; eauto; normalize_used_vars.
          right; now left.
          right; now right.
        * intros e' s'.
          eapply return_triple.
          intros _ s'' [Hfresh [C' [Hctx' [Hcc [Hran'' [Hinc'' [Hbv'' Huniq'']]]]]]] [Hf' [Hran' Hinc']] Hf; eauto.
          split; [|exists C; splits]; auto.
          -- eapply fresh_inc; [|eassumption]; zify; omega.
          -- rewrite Hctx'; simpl. econstructor; [|eassumption|].
             ++ decomp_Disjoint; splits_Disjoint; auto.
                ** (* Scope # S because Scope ⊆ dom(FVmap) and dom(FVmap) # S *) admit.
                ** (* Sufficient to show Disjoint S (FVs\Funs\GFuns\Scope).
                        x ∈ FVs\Funs\GFuns\Scope ==> x ∈ dom(FVmap) ==> x ∉ S
                      Disjoint_free_set could be useful, but currently precondition too strong.
                        Requires something about GFuns. Try weaken this *)
                     admit.
             ++ eapply Closure_conversion_f_eq_subdomain; [eassumption|].
                rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
                intros Hc. inv Hc. now eauto. reflexivity. 
          -- eapply Included_trans; try eassumption.
             intros arb Harb; unfold Range, In in *; zify; omega.
          -- zify; omega.
          -- simpl. rewrite Hctx'. repeat normalize_bound_var.
             rewrite bound_var_app_ctx.
             apply Union_Included; auto with Ensembles_DB. apply Union_Included.
             ++ (* BV(C') ⊆ [s', s'') by Hran'' and [s', s'') ⊆ [s, s'') by Hinc' *)
                admit.
             ++ (* BV(C') ⊆ BV(e) ∪ {v} ∪ [s', s'') by Hbv'' and [s', s'') ⊆ [s, s'') by Hinc' *)
                admit.
          -- simpl. rewrite Hctx'.
             (* UB(C[Econstr v t xs (C'[e'])])
                  <=> UB(C) /\ UB(C') /\ UB(e') /\ (BV(C) # {v} # BV(C') # BV(e'))
                Have UB(C) by Huniq', UB(C') /\ UB(e') by Huniq'', leaving
                  BV(C) # {v} # BV(C') # BV(e')
                Have v ∉ BV(C) because BV(C) ⊆ [s, s') ⊆ S (by Hran', Hf) and v ∉ S (by HD1)
                Have v ∉ BV(C') because BV(C') ⊆ [s', s'') ⊆ S (by Hran'', Hinc', Hf) and v ∉ S
                Have v ∉ BV(e') because BV(e') ⊆ BV(e) ∪ [s', s'') (by Hbv'') and
                  v ∉ BV(e) by Huniq
                  v ∉ [s', s'') because [s', s'') ⊆ S
                This leaves
                  BV(C) # BV(C') # BV(e')
                Have BV(C) # BV(C') because BV(C) ⊆ [s, s') by Hran' and BV(C') ⊆ [s', s'') by Hran''
                Have BV(C) # BV(e') because BV(e') ⊆ BV(e) ∪ [s', s'') by Hbv'' and
                  BV(C) ⊆ [s, s') by Hran' and [s, s') # [s', s'')
                  BV(C) ⊆ [s, s') ⊆ S # BV(e) by Hran', Hf, HD1
                Similarly BV(C') # BV(e') *)
             admit.
    - setoid_rewrite left_id.
      eapply bind_triple'.
      + apply get_var_project_var_sound; eauto.
        intros x Hx. eapply Hbin1. rewrite occurs_free_Ecase_nil. eassumption.
      + intros [x f] s. eapply return_triple.
        intros _ s' [Hfresh [C [S' [[Hproj [Hctx Huniq']] [Hf' [Hran Hinc]]]]]].
        split; [eapply fresh_inc; [|eassumption]; zify; omega|]; exists C; splits; auto.
        { econstructor; [| eassumption | constructor].
          decomp_Disjoint; splits_Disjoint; auto.
          - (* x ∈ Scope ==> x ∈ dom(FVmap) ==> x ∉ S *) admit.
          - (* Sufficient to show Disjoint S (FVs\Funs\GFuns\Scope).
                x ∈ FVs\Funs\GFuns\Scope ==> x ∈ dom(FVmap) ==> x ∉ S *)
            admit. }
        { simpl; normalize_bound_var; eauto with Ensembles_DB. }
        { simpl. admit. (* should follow from Huniq', but may need lemma *) }
    - setoid_rewrite assoc. eapply bind_triple'.
      + eapply H; try eassumption.
        * eapply binding_in_map_antimon; [| eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * now inv Huniq.
        * admit. (* Follows from Hdis2 *)
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. 2: now apply Included_refl.
          normalize_used_vars.
          eauto with Ensembles_DB.
        * (* Follows from HD2 *) admit.
      + intros [e' f'] s'. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential_r. intros C. apply pre_curry_rl; intros Hctx.
        apply pre_curry_rl; intros Hcc. eapply bind_triple'.
        eapply pre_strenghtening.
        2: eapply H0 with (FVmap := FVmap) (Γ := Γ) (c := c0); try eassumption.
        { simpl. intros _ s Hconj; decompose [and] Hconj. intros arb Harb.
          apply Hfresh. zify; omega. }
        * eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Ecase_cons...
        * now inv Huniq.
        * (* Follows from Hdis2 *) admit.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_used_vars.
          solve_Union_Inc.
        * (* Follows from HD2 *) admit.
        * intros [e'' f] s''.   
          edestruct e''; eapply return_triple;
            intros _ s''' [Hpre [Hfresh_s''' [C2 [Hctx2 [Hcc2' Hf2]]]]]; inv Hcc2'.
          destruct Hf2 as [HbvC2 [Hinc'' [Hbv_case Huniq'']]], Hpre as [HbvC [Hinc' [Hbv_e Huniq_e]]].
          split; [eapply fresh_inc; [|eassumption]; zify; omega|]; eexists; splits.
          { eassumption. }
          { econstructor; try eassumption.
            constructor; auto; splits; auto; simpl.
            rewrite Hctx; repeat eexists; eauto. }
          { (* Follows from HbvC2, Hinc' *) admit. }
          { zify; omega. }
          { simpl; repeat normalize_bound_var. rewrite Hctx.
            rewrite bound_var_app_ctx. (* Follows from HbvC, Hinc'', Hbv_e, Hbv_case *) admit. }
          { simpl. unfold is_exp_ctx in Hctx. rewrite Hctx. (* Should be provable *) admit. }
    - eapply bind_triple'.
      + eapply get_var_project_var_sound; try eassumption.
        intros x Hx. inv Hx. eapply Hbin1. eauto.
      + intros [x f] s.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply pre_strenghtening.
        2: eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        { clear; tauto. }
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eproj_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { eapply HD1; eauto.
            constructor; try eassumption.
            normalize_used_vars. left; left; right; now left. }
          { inv H0; eapply HD2; normalize_used_vars. now left. }
        * assumption.
        * now inv Huniq.
        * normalize_bound_var_in_ctx; decomp_Disjoint; eauto with Ensembles_DB.
        * normalize_bound_var_in_ctx; decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        * eapply Disjoint_Included_l. eapply project_var_free_set_Included; now eauto.
          rewrite <- to_env_BoundVar_f_eq.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. 
          2: rewrite (Union_commut (Singleton _ _)), <- Setminus_Union.
          2: now eapply image_Setminus_extend.
          apply Included_Union_compat; [| now apply Included_refl ].
          normalize_used_vars; solve_Union_Inc.
        * (* Follows from HD2 *) admit.
        * intros e' s'. eapply return_triple.
          intros _ s'' [Hfresh' [C' [Hctx' [Hcc [HbvC' [Hinc' [Hbv' Huniq'']]]]]]] [Hfresh'' [HbvC Hinc]].
          split; [eapply fresh_inc; [|eassumption]; zify; omega|].
          eexists; splits. { eassumption. }
          { simpl. rewrite Hctx'. econstructor; try eassumption.
            - eapply Disjoint_free_set in Minv.
              + decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
              + eapply binding_not_in_map_antimon; [| eassumption ].
                now apply Included_Union_l.
              + (* Follows from HD1 *) admit.
            - eapply Closure_conversion_f_eq_subdomain. eassumption.
              rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
              + intros Hc. inv Hc. now eauto.
              + reflexivity. }
          { admit. (* Follows from HbvC, Hinc' *) }
          { zify; omega. }
          { simpl; repeat normalize_bound_var. rewrite Hctx'.
            rewrite bound_var_app_ctx.
            admit. (* follows from HbvC' and friends *) }
          { simpl; rewrite Hctx'.
            admit. (* Folows by same argument as in Econstr case *) }
    - eapply bind_triple'; [apply get_var_project_var_sound; try eassumption|].
      1: eapply binding_in_map_antimon; [|eassumption]; normalize_occurs_free...
      intros [f' Cf] s.
      apply pre_curry_l; intros Hfresh.
      apply pre_existential; intros C_f.
      apply pre_existential; intros S_f.
      apply pre_curry_l; intros [Hproj [Hctx Huniq']].
      eapply bind_triple'.
      eapply pre_strenghtening; [|apply get_vars_project_vars_sound; try eassumption].
      1: simpl; intros ? ? [Hres ?]; exact Hres.
      1: eapply binding_in_map_antimon; [|eassumption]; normalize_occurs_free...
      intros [ys' Cys] s'.
      apply pre_curry_l; intros [Hfresh_f [HbvC_f Hinc_f]].
      apply pre_existential; intros C_ys; apply pre_existential; intros S_ys.
      apply pre_curry_l; intros [Hprojs [Hctx_ys Huniq_ys]].
      eapply bind_triple'; [eapply pre_strenghtening; [|apply get_name_fresh] |].
      { intros ? ? [Hres ?]; exact Hres. }
      intros ptr s_ptr; apply pre_curry_l; intros [Hfresh_ys [HbvC_ys Hinc_ys]].
      eapply bind_triple'; [eapply pre_strenghtening; [|apply get_name_fresh] |].
      { intros ? ? [? [? [? Hres]]]; exact Hres. }
      intros Γ' s_Γ'; apply pre_curry_l; intros [HS_ptr [Hptr_ran [Hs_ptr Hfresh_ptr]]].
      apply pre_curry_l; intros HS_Γ'.
      eapply bind_triple'; [eapply pre_strenghtening|].
      { simpl; intros ? ? [? [? Hres]]; exact Hres. }
      { eapply H with (Scope := x |: Scope)
                      (FVmap := Maps.PTree.set x BoundVar FVmap); try eassumption.
        - eapply FVmap_inv_set_bound. eassumption. 
        - eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          normalize_occurs_free.
          assert (occurs_free e \subset (occurs_free e \\ [set x]) :|: [set x]). {
            apply Included_Union_Setminus. eauto with Decidable_DB. }
          eapply Included_trans; [eassumption|]...
        - eapply binding_not_in_map_antimon with (S := S :|: [set Γ]).
          + assert (Hsub_ys : S_ys \subset S_f). { eapply project_vars_free_set_Included; eauto. }
            assert (Hsub_f : S_f \subset S). { eapply project_var_free_set_Included; eauto. }
            apply Included_Union_compat; [|apply Included_refl].
            do 2 apply Setminus_Included_Included_Union.
            eapply Included_trans; [eassumption|].
            eapply Included_trans; [eassumption|]...
          + eapply binding_not_in_map_set_not_In_S.
            { eapply binding_not_in_map_antimon; [|eassumption]... }
            intros Hc; inv Hc.
            { eapply HD1; constructor; [eassumption|]. normalize_used_vars... }
            { inv H0. apply HD2. normalize_used_vars... }
        - now inv Huniq.
        - normalize_bound_var_in_ctx; decomp_Disjoint...
        - normalize_bound_var_in_ctx; decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        - (* Can ignore Γ'.
             S_ys\{ptr}\{Γ'} ⊆ S_ys ⊆ S_f ⊆ S.
             S # Funs\({x}∪Scope) by HD1.
             FVmap[x↦BVar](Funs\({x}∪Scope)) ⊆ FVmap(Funs\Scope) # S by HD1.
             GFuns, used_vars e # S by HD1. *)
          admit.
        - intros Hc; apply HD2; normalize_used_vars... }
      intros e' s_e'; apply pre_curry_l; intros [HΓ' [Hinc_Γ' Hfresh_Γ']].
      apply pre_existential_r; intros C_e'; apply pre_curry_rl; intros Hctx_e'.
      apply pre_curry_rl; intros Hcc_e'.
      apply return_triple.
      intros _ s_final [Hfresh_final [HbvC_e' [Hinc_e' [Hbv_e' Huniq_e']]]].
      split; [eapply fresh_inc; [|eassumption]; zify; omega|]; exists (comp_ctx_f C_f C_ys); splits.
      { unfold is_exp_ctx; simpl; intros ?. now rewrite Hctx, Hctx_ys, app_ctx_f_fuse. }
      { simpl. unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        eapply CC_Eletapp with (S := S).
        - (* S # Funs\Scope, S # GFuns, S # FVmap(Funs\Scope), S # {Γ} by HD1
             S # Scope by Minv, Hbin2 
             Finally, sufficient to show S # FVs\Scope\Funs\GFuns, which follows from Minv, Hbin2 *)
          admit.
        - econstructor; eassumption.
        - auto.
        - now inv HS_Γ'.
        - admit. (* ptr ∈ [s_ptr, s_Γ') while Γ' ∈ [s_Γ', s_e') *)
        - eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          + intros Hc. inv Hc. now eauto.
          + reflexivity. }
        { admit. (* Follows from HbvC, Hinc' *) }
        { zify; omega. }
        { simpl; repeat normalize_bound_var. rewrite Hctx_e'.
          rewrite bound_var_app_ctx.
          admit. (* follows from HbvC' and friends *) }
        { simpl; rewrite Hctx_e'.
          admit. (* Follows by similar argument as in EConstr case *) }
    - remember (filter _ _) as FVs_pre eqn:HFVs_pre.
      remember (match FVs_pre with [] => true | _ :: _ => false end) as is_closed eqn:Hclos.
      eapply bind_triple'; [ eapply get_name_no_suff_fresh |].
      intros Γ' s_Γ'. eapply pre_curry_l. intros HS_Γ'.
      eapply bind_triple'.
      { eapply pre_strenghtening; [|eapply make_env_spec].
        { intros ? ? [? [? [? Hres]]]; exact Hres. }
        - eapply binding_in_map_antimon; [| eassumption ].
          admit. (* filter _ (FV(f2)) ⊆ FV(f2) ⊆ FV(Efun f2 e) *)
        - eapply binding_not_in_map_antimon; [| eassumption ]...
        - eassumption.
        - eassumption.
        - (* GFuns # (filter (member gfuns) _) because dom(gfuns) = GFuns *)
          admit.
        - (* NoDup (filter _ (PS.elements xs)) 
               <== NoDup (PS.elements xs) 
               <== NoDupA eq (PS.elements xs) (by NoDupA_NoDup)
               qed (by PS.elements_spec2w) *)
          admit.
        - intros Hc; inv Hc; auto. }
      intros [[c' FVmap'] f] s_env.
      remember (add_closures f2 FVmap Γ') as FVmap_n eqn:HFVmap_n.
      remember (add_closures_gfuns f2 gfuns is_closed) as gfuns' eqn:Hgfuns'.
      apply pre_curry_l; intros [HΓ' [Hran_Γ' [Hinc_Γ' Hfresh_Γ']]].
      eapply pre_existential; intros C_env.
      eapply pre_existential; intros S_env.
      eapply pre_existential; intros FVs'.
      eapply pre_curry_l. intros [Hproj_env [Hctx_env Huniq_env]].
      destruct (add_closures_gfuns_spec f2 gfuns is_closed (name_in_fundefs f2) (FromList FVs_pre) GFuns)
        as [GFuns' [HGFuns' [Hsquash]]]; eauto with Ensembles_DB.
      { destruct is_closed, FVs_pre; inv Hclos; constructor; normalize_sets; eauto with Ensembles_DB.
        intros [Hc _]. specialize (Hc p); destruct Hc; now left. }
      { clear - Hdis2. normalize_bound_var_in_ctx. decomp_Disjoint.
        eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|]; auto. }
      eapply bind_triple'.
      apply pre_curry_rr; intros [Hbin1' [Hbin2' Minv']].
      eapply pre_strenghtening; [|eapply H with (Bl := Fnil) (FVs := FVs_pre)].
      { intros ? ? [Hres ?]; exact Hres. }
      { reflexivity. }
      { reflexivity. }
      { subst gfuns'; apply HGFuns'. }
      { (* GFuns' = if is_closed then GFuns ∪ names(f2) else GFuns.
           If not is_closed then follows from Hinv'.
           Else follows from names(f2) # dom(FVmap'). *) admit. }
      { eapply binding_in_map_antimon; [simpl|eassumption].
        (* FV(f2)\GFuns' ⊆ FV(f2)\GFuns = FVs_pre *)
        admit. }
      { eapply binding_not_in_map_antimon; [|eassumption].
        (* ∀ S T, S ⊆ ¬T <==> S ∩ T ⊆ ∅ <==> S # T
           S_env ⊆ S\{Γ'} ⊆ S # FV(Efun f2 e) ⊇ FV(f2) ⊇ filter _ (FV(f2)) = FVs_pre *)
        admit. }
      { now inv Huniq. }
      { simpl.
        (* S_env ⊆ S # vars(f2) by HD1.
           FVmap'(names(f2)) = names(f2) because dom(FVmap') = FVs_pre.
           So S # vars(f2) ⊇ names(f2). *)
        admit. }
      { simpl.
        (* GFuns' = if is_closed then GFuns ∪ names(f2) else GFuns.
           If not is_closed then follows from Hdis2.
           Else need to show GFuns ∪ names(f2) # BV(f2)\names(f2)
             GFuns # BV(f2)\names(f2) by Hdis2
             names(f2) # BV(f2)\names(f2) by some lemma about Setminus *)
        admit. }
      intros B' s_B'.
      apply pre_curry_l. intros [Hfresh_B' [Hinc_B' [Hbin1' [Hbin2' Minv']]]].
      apply pre_curry_rl. intros Hcc_B; simpl in Hcc_B.
      eapply bind_triple'; [eapply pre_strenghtening;
        [|apply H0 with (Funs := name_in_fundefs f2 :|: Funs) (GFuns := GFuns')
            (Scope := Scope \\ name_in_fundefs f2)] |].
      { intros ? ? [Hres ?]; exact Hres. }
      { admit. (* TODO: lemma about FVmap_inv and add_closures *) }
      { admit. (* dom(FVmap_n) = dom(FVmap) ∪ names(f2) ⊇ FV(e) *) }
      { admit. (* S_env ∪ {Γ} ⊆ S ∪ {Γ} # dom(FVmap) by Hbin2
                  S ∪ {Γ} # names(f2) by HD1, HD2 *) }
      { subst gfuns'; apply HGFuns'. }
      { now inv Huniq. }
      { admit. }
      { admit. }
      { admit. }
      { admit. (* HD2 *) }
      intros e' s_e'; apply return_triple.
      intros _ s_final [[Hfresh_e' [HbvB' [Hinc_e' Huniq_B']]]
                       [Hfresh_final [C_e' [Hctx_e' [Hcc_e' [HbvC_e' [Hinc_final [Hbv_e' Huniq_e']]]]]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; omega|].
      exists (comp_ctx_f C_env (Econstr_c Γ' c' FVs' Hole_c)); splits.
      + simpl; unfold is_exp_ctx; intros expr. now rewrite Hctx_env.
      + simpl. unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        eapply CC_Efun with (GFuns' := GFuns') (FVs' := FVs_pre) (S1 := S \\ [set Γ']) (S1' := S_env)
                            (S3 := [set Γ'])
                            (S2 := Empty_set _).
        * (* HFVs_pre *) admit.
        * (* PS.elements produces (NoDupA eq) lists *) admit.
        * (* Funs\Scope # S, GFuns # S, FVmap(Funs\Scope) # S, {Γ} # S by HD1
             Scope # S by Minv, Hbin2
             Sufficient to show FVs\Scope\Funs\GFuns # S, which follows from Hbin2 and Minv *) admit.
        * assumption.
        * (* Γ' ∈ S
             S # BV(Efun f2 e) ∪ GFuns ∪ FVmap(Funs\Scope) ∪ {Γ} by HD1
             S # Scope ∪ FVs by similar argument as 2 cases above *) admit.
        * constructor.
        * eauto with Ensembles_DB.
        * assumption.
        * assumption.
        * assert (Hmap_eq : f_eq_subdomain ((name_in_fundefs f2 :|: Funs) \\ (Scope \\ name_in_fundefs f2))
              (to_env FVmap_n) (extend_fundefs' (to_env FVmap) f2 Γ')). {
            subst FVmap_n. eapply f_eq_subdomain_antimon; [|apply add_closures_spec].
            intros x Hx; unfold In; auto. }
          eapply Closure_conversion_f_eq_subdomain; [|eassumption].
          eassumption.
      + repeat normalize_bound_var_ctx; normalize_sets.
        (* BV(C_env) ⊆ [s_Γ', s_final) needs lemma which says BV(C_env) ⊆ [s_env, s_B') 
           {Γ'} ⊆ [s_Γ', s_env) ⊆ [s_Γ', s_final) by Hran_Γ' and Hinc* *)
        admit.
      + zify; omega.
      + simpl; unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'; repeat normalize_bound_var.
        rewrite bound_var_app_ctx.
        (* Should follow from Hbv* *)
        admit.
      + simpl; unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        rewrite <- app_ctx_f_fuse; simpl.
        (* Should follow from ranges and Huniq* *)
        admit.
    - eapply bind_triple'.
      + eapply get_var_project_var_sound; try eassumption.
        eapply binding_in_map_antimon; [| eassumption ].
        rewrite occurs_free_Eapp...
      + intros [x f] s1.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hvar [Hctx1 Huniq1]].
        eapply bind_triple'.
        * eapply pre_strenghtening; [|eapply get_vars_project_vars_sound].
          { intros ? ? [Hres ?]; exact Hres. }
          all: try eassumption.
          eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Eapp...
        * intros [xs f'] s2.
          eapply pre_curry_l. intros Hfresh'.
          eapply pre_existential. intros C2.
          eapply pre_existential. intros S''.
          eapply pre_curry_l. intros [Hvars [Hctx2 Huniq2]].
          eapply bind_triple'.
          eapply pre_strenghtening; [|eapply get_name_fresh].
          { intros ? ? [Hres ?]; exact Hres. }
          intros x' i. eapply pre_curry_l. intros [Hfresh'' Hf1].
          eapply bind_triple'; [eapply pre_strenghtening; [|eapply get_name_fresh] |].
          { intros ? ? [? [? [? Hres]]]; exact Hres. }
          intros x'' s3. eapply pre_curry_l. intros Hf2. 
          eapply return_triple.
          intros _ s5 Hf5. simpl.
          split; [eapply fresh_inc; [|eassumption]; zify; omega|].
          exists (comp_ctx_f C1 C2); splits.
          { intros e. rewrite <- app_ctx_f_fuse. congruence. }
          { eapply CC_Eapp with (S := S).
            - admit. (* Similar argument to prev cases *)
            - econstructor; eassumption.
            - intuition.
            - admit. (* Hf5 *)
            - admit. (* Ranges in Hf2, Hf5 *) }
          { admit. (* Ranges and Hf1, HF5 *) }
          { zify; omega. }
          { repeat normalize_bound_var; repeat normalize_sets.
            (* Ranges in Hf2, Hf5 *) admit. }
          { rewrite <- app_ctx_f_fuse. (* Should be provable *) admit. }
    - eapply bind_triple'.
      + eapply get_vars_project_vars_sound; try eassumption.
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s.
        eapply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        eapply bind_triple'; [eapply pre_strenghtening|].
        { intros ? ? [Hres ?]; exact Hres. }
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eprim_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { eapply HD1; eauto. constructor; eauto.
            normalize_used_vars; left; left; right; left; now left. }
          { inv H0; contradiction HD2; normalize_used_vars; now do 2 left. }
        * assumption.
        * now inv Huniq.
        * admit. (* Follows from Hdis1, Hdis2 *)
        * admit. (* Follows from Hdis2 *)
        * eapply Disjoint_Included_l. eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          -- normalize_used_vars. solve_Union_Inc.
          -- rewrite <- to_env_BoundVar_f_eq, Union_commut, <- Setminus_Union.
             now eapply image_Setminus_extend.
        * (* Follows from HD2 *) admit.
        * intros e' s'. eapply return_triple.
          intros _ s'' [[Hfresh' [HbvC Hinc]] [Hfresh'' [C' [Hctx' [Hcc Hf'']]]]]; eauto.
          split; [eapply fresh_inc; [|eassumption]; zify; omega|].
          eexists; splits.
          { now eapply Hctx. }
          { simpl. unfold is_exp_ctx in Hctx'. rewrite Hctx'. econstructor; [| eassumption |].
            - admit. (* provable *)
            - eapply Closure_conversion_f_eq_subdomain. eassumption.
              rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
              intros Hc. inv Hc. now eauto. reflexivity. }
          { admit. (* HbvC and s'' > s' *) }
          { zify; omega. }
          { simpl; normalize_bound_var. unfold is_exp_ctx in Hctx'; rewrite Hctx'.
            rewrite bound_var_app_ctx. (* ranges and HbvC, Hf'' *) admit. }
          { simpl. rewrite Hctx'. (* provable *) admit. }
    - eapply bind_triple'. eapply get_var_project_var_sound; eauto.
      { eapply binding_in_map_antimon; [| eassumption ].
        rewrite occurs_free_Ehalt... }
      intros [x f] s1. apply return_triple.
      intros _ s2 [Hfresh [C [S' [[Hproj [Hctx Huniq']] Hf]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; omega|].
      eexists; splits.
      + eassumption.
      + simpl. econstructor; try eassumption.
        admit. (* provable *)
      + intuition.
      + zify; omega.
      + simpl; normalize_bound_var; eauto with Ensembles_DB.
      + simpl. rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
        * constructor.
        * normalize_bound_var; eauto with Ensembles_DB.
    - eapply bind_triple'; [apply get_name_no_suff_fresh|].
      intros Γ s_Γ. apply pre_curry_l; intros Hfresh_Γ.
      apply pre_curry_l; intros HS_Γ.
      eapply bind_triple'; [eapply pre_strenghtening;
        [|eapply H with (FVs := FVs) (Funs := name_in_fundefs Bg) (Scope := FromList l)] |].
      { intros ? ? [? [? Hres]]; exact Hres. }
      { rewrite <- (FVmap_inv_Scope_Proper _ _ eq_refl _ _ (Union_Empty_set_neut_l _ _)
                                          _ _ eq_refl _ _ eq_refl _ _ eq_refl).
        apply FVmapInv_add_params. admit. (* should follow from add_closures_spec *) }
      { admit. (* Follows from Hbin1. useful lemma: occurs_free_in_fun *) }
      { (* S\{Γ} ∪ {Γ} ⊆ S ∪ {Γ} ⊆ S by HS_Γ
           S # l ∪ names(Bg) ∪ dom(FVmap) ⊇ dom(add_params l (add_closures f5 FVmap)) by HD1 *)
        admit. }
      { eassumption. }
      { now inv Huniq. }
      { admit. (* Huniq *) }
      { admit. (* HD2, Huniq *) }
      { (* S # names(Bg), S # GFuns, S # vars(e) by HD1
           S\{Γ] # {Γ} by some setminus lemma
           Finally (add_params l (add_closures f5 FVmap Γ))(names(Bg)) ⊆ {Γ} ∪ names(f5)
             S\{Γ} # {Γ} as above
             S # names(f5) by HD1 *)
        admit. }
      { admit. (* HS_Γ, HD1 *) }
      intros e' s_e'.
      apply pre_curry_l. intros [HΓ_ran [Hinc_e' Hfresh_e']].
      apply pre_existential_r; intros C_e.
      apply pre_curry_rl; intros Hctx_e.
      apply pre_curry_rl; intros Hcc_e.
      eapply bind_triple'; [eapply pre_strenghtening;
        [|eapply H0 with (FVs := FVs) (Bg := Bg) (Bl := fundefs_append Bl (Fcons v t l e Fnil))] |].
      { intros ? ? [Hres ?]; exact Hres. }
      { rewrite <- fundefs_append_assoc; simpl. now subst Bg. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eapply binding_not_in_map_antimon; [|eassumption]. eauto with Ensembles_DB. }
      { now inv Huniq. }
      { eapply Disjoint_Included_l; eauto... }
      { assumption. }
      intros B' s_B'; apply return_triple.
      intros _ s_final [[Hfresh_B' [HbvC_e [Hinc_B' [Hbv_e' Huniq_e']]]]
                          [Hfresh_final [Hcc_B' [Hbv_B' [Hinc_final' Huniq_B']]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; omega|].
      unfold is_exp_ctx in Hctx_e; rewrite Hctx_e.
      splits.
      + eapply CC_Fcons with (FVs := FVs); auto.
        * (* HS_Γ, HD1 *) admit.
        * assert (Hfeq : f_eq_subdomain (name_in_fundefs Bg \\ FromList l)
                                        (to_env (add_params l (add_closures Bg FVmap Γ)))
                                        (extend_fundefs' id Bg Γ)). {
            (* We can get rid of (add_params l) because domain excludes l *) admit. }
          eapply Closure_conversion_f_eq_subdomain; [|apply Hfeq]; auto.
      + repeat normalize_bound_var; normalize_sets; rewrite bound_var_app_ctx.
        decomp_Disjoint; solve_Union_Inc.
        * (* HΓ_ran *) admit.
        * (* HbvC_e + ranges *) admit.
        * (* Hbv_e' + ranges *) admit.
        * (* Hbv_B' + ranges *) admit.
      + zify; omega.
      + (* should be provable *) admit.
    - eapply return_triple. intros _ s Hf.
      splits; auto.
      + constructor.
      + eauto with Ensembles_DB.
      + zify; omega.
  Admitted.

  Transparent exp_closure_conv.

  (** Correctness of [exp_closure_conv] *)
  Corollary exp_closure_conv_correct k rho rho' S e c Γ FVmap Scope Funs FVs :
    (* [Scope], [Funs] and [FVs] are uniquely identified by [FVmap] *)
    FVmap_inv FVmap Scope Funs FVs ->
    (* [Γ] (the current environment parameter) is fresh in e *)
    ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* [FVmap] contains all the free variables *)
    binding_in_map (occurs_free e) FVmap ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e ->
    (* [FVmap] does not contain the variables in [S] or [Γ] *)
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [Fun] invariant *)
    Fun_inv pr cenv clo_tag k rho rho' Scope Funs (subst FVmap) c Γ ->
    (* Free variables invariant *)
    FV_inv pr cenv clo_tag k rho rho' Scope Funs c Γ FVs ->
    (* The function name substitution is injective *)
    injective_subdomain Funs (subst FVmap) ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image (subst FVmap) (Setminus _ Funs Scope)) (bound_var e) ->
    (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
    Disjoint _ S (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                        (Union _ (bound_var e)
                               (Union _ (occurs_free e) (Singleton _ Γ)))) ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         let '(e', f) := ef in 
         cc_approx_exp pr cenv clo_tag k (boundL k e rho) boundG (e, rho) (f e', rho')    
    }}.
  Proof.
    intros IFVmap HGamma Hin_map_rho Hin_map_FVmap Hun
           Hnot_in_map Hcc IFun IFVs Hinj HD1 HD2.
    eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; eassumption ].
    intros s [e' f] s' Hf [C [Hctx [Hclo _]]]. simpl in Hctx, Hclo.
    replace (f e') with (C |[ e' ]|); [| now eauto].
    eapply Closure_conversion_correct; try eassumption.
    intros Hc. eapply HGamma; eauto.
  Qed.

  Lemma get_var_is_exp_ctx  x FVmap c Γ :
    {{ fun s => True }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Eproj_c x' c n Γ Hole_c).
        intros e. reflexivity.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Econstr_c x' clo_tag [v; Γ] Hole_c).
        intros e'. reflexivity.
      + apply return_triple.
        intros _ _. exists Hole_c. intros ?; reflexivity.
    - apply return_triple.
      intros _ _. exists Hole_c. intros ?; reflexivity.
  Qed.

  Lemma get_vars_is_exp_ctx  xs FVmap c Γ :
    {{ fun s => True }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    induction xs.
    - apply return_triple. intros _ _.
      exists Hole_c; intros ?; reflexivity. 
    - eapply bind_triple.
      + apply get_var_is_exp_ctx.
      + intros [x f] i. apply pre_post_mp_l.
        eapply bind_triple.
        * apply IHxs.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [C2 Hctx] [C1 Hctx'].
          exists (comp_ctx_f C1 C2). intros e.
          rewrite <- app_ctx_f_fuse. congruence.
  Qed.

  Lemma make_env_is_exp_ctx FVset FVmap FVmap' c Γ Γ' :
    {{ fun s => True }}
      make_env clo_tag FVset FVmap FVmap' c Γ Γ'
    {{ fun s t s' =>
         let '(_, _, f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold make_env.
    destruct
      ((fix add_fvs (l : list M.elt)
            (n : N)
            (map : Maps.PTree.t VarInfo)
            {struct l} :
          Maps.PTree.t VarInfo * N :=
          match l with
            | [] => (map, n)
            | x :: xs =>
              add_fvs xs 
                      (n + 1)%N
                      (Maps.PTree.set x 
                                      (FVar n) map)
          end) (PS.elements FVset) 0%N
               (Maps.PTree.empty VarInfo)).
    eapply bind_triple.
    + apply get_vars_is_exp_ctx.
    + intros [xs f] i. apply pre_post_mp_l.
      eapply bind_triple. apply post_trivial.
      intros. eapply return_triple. intros _ _ [C Hctx]. 
      eexists (comp_ctx_f C (Econstr_c Γ x xs Hole_c)).
      intros e. rewrite <- app_ctx_f_fuse, Hctx.
      reflexivity.
  Qed.

  Lemma exp_closure_conv_is_exp_ctx e c Γ FVmap :
    {{ fun s => True }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         exists C, is_exp_ctx (snd ef) C
     }}.
  Proof.
    destruct e. 
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros.
      now eapply return_triple.
    - unfold exp_closure_conv.
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.            
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply make_env_is_exp_ctx.
      intros [[? ?] ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      destruct x0 as [[? ?] ?]. 
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple. now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply return_triple. intros _ _ [C1 H1] [C2 H2]. 
      simpl. eexists (comp_ctx_f C2 C1). intros e'.
      rewrite <- app_ctx_f_fuse. congruence. 
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros.
      eapply return_triple. now eauto.
  Qed.

  Lemma get_var_bound_var_Included  x FVmap c Γ S S':
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            (Included _ (bound_var e) (Union _ S' ((Setminus _ S (Singleton _ x')))) ->
             Included _ (bound_var (f e)) (Union _ S' S))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin. rewrite bound_var_Eproj.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; omega.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin'. rewrite bound_var_Econstr.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; omega.
      + apply return_triple.
        intros i' Hf. split.
        * intros e Hin'. eapply Included_trans; [ eassumption |]...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e Hin'. eapply Included_trans; [ eassumption |]...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included xs FVmap c Γ S S':
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Included _ (bound_var (f e)) (Union _ S' S)) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e Hin'. eapply Hx. eapply Hxs.
          rewrite FromList_cons in Hin'. rewrite Setminus_Union. eassumption.
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma make_full_closure_bound_var_Included B m1 m2 Γ S :
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Same_set _ (bound_var (f e)) (Union _ (bound_var  e) (name_in_fundefs B))) /\
         Included _ (image (subst m1') (name_in_fundefs B)) S /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S. 
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. apply pre_curry_l. intros Hf1.
      eapply bind_triple. now eapply IHB.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [Hinc [Him Hf]]. split; [| split ].
      + intros e'. rewrite bound_var_Econstr; simpl.
        rewrite Hinc...
      + rewrite <- subst_MRFun_f_eq. rewrite image_extend_In_S.
        simpl. apply Union_Included.
        eapply Included_trans.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set,
        Union_Empty_set_neut_l.
        apply image_monotonic. now apply Setminus_Included.
        eapply Included_trans. eassumption. now apply Setminus_Included.
        apply Singleton_Included. eapply Hf1. zify; omega.
        now left; eauto.
      + eapply fresh_monotonic; [| eassumption ].
        now apply Setminus_Included.
    - apply return_triple. intros s Hf.
      simpl. split; [ |  split; [| now eauto] ].
      intros e. now rewrite Union_Empty_set_neut_r.
      rewrite image_Empty_set. now apply Included_Empty_set.
  Qed.

  Lemma exp_closure_conv_bound_var_Included_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e))),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            Included _ (bound_var ((snd ef) (fst ef)))
                     (Union _ (bound_var e) S) /\
            fresh S (next_var s')
        }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
            Included _ (bound_var_fundefs B')
                     (Union _ (bound_var_fundefs B)
                            (Union _ S (image (subst FVmap) (name_in_fundefs B)))) /\
            fresh S (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Econstr...
      + intros [xs f] i. apply pre_curry_l; intros Hf.
        eapply bind_triple. eapply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Econstr_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split.
        simpl in *. eapply Hf. rewrite !bound_var_Econstr.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc. 
        apply Included_Union_compat; [ eassumption | now apply Included_refl].
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple. apply get_var_bound_var_Included.
      intros Hc. eapply HD. now constructor; eauto.
      intros [x f] _. apply return_triple. intros i'.
      intros [He Hf]. split. simpl.
      eapply He. rewrite !bound_var_Ecase_nil.
      now apply Included_Empty_set.
      eapply fresh_monotonic; [| eassumption ]...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      eapply bind_triple.
      + eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_l; intros He'.
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included.
          - eapply pre_strenghtening;
            [ | now eapply exp_closure_conv_is_exp_ctx
                with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
            intros. simpl; eauto. }
        intros [e'' f''] s''.
        destruct e''; apply return_triple;
        try (intros s''' [[Hin Hf] _]; split; eauto;
             eapply Included_trans; [ eassumption |]; normalize_bound_var;
             now eauto with Ensembles_DB).
        intros s''' [[Hin Hf] [C Hctx]]; split; eauto. simpl in *.
        rewrite Hctx. rewrite bound_var_ctx_app_Ecase_cons, bound_var_Ecase_cons.
        apply Union_Included.
        * eapply Included_trans. eassumption. eauto with Ensembles_DB.
        * rewrite <- Hctx. eapply Included_trans. eassumption.
          eauto with Ensembles_DB.
    - eapply bind_triple.
      + eapply get_var_bound_var_Included. intros Hc. eapply HD; eauto.
      + intros [xs f] i. apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eproj_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split. 
        simpl in *. eapply Hf. rewrite !bound_var_Eproj.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc... 
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple. now apply get_name_no_suff_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple with
      (post' :=
         fun _ t s' =>
           let '(_, f) := t in
           (forall e0 : exp,
              Included var (bound_var e0)
                       (Union var (bound_var (Efun f2 e)) S) ->
              Included var (bound_var (f e0))
                       (Union var (bound_var (Efun f2 e)) S)) /\
           fresh (Setminus var S (Singleton var Γ')) (next_var s')).
      + unfold make_env.
        destruct
          ((fix
              add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
              {struct l} : Maps.PTree.t VarInfo * N :=
              match l with
                | [] => (map, n)
                | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
              end) _ _ _ ) as [m1' n].
        eapply bind_triple.
        apply get_vars_bound_var_Included with (S' := Union _ (bound_var (Efun f2 e)) S).
        assert (Heq : (@FromList var (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
        rewrite Heq, <- fundefs_fv_correct.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        apply Included_Union_preserv_r. normalize_occurs_free...
        intros [xs f] s2. apply pre_curry_l. intros He. 
        eapply bind_triple. apply make_record_ctor_tag_preserves_prop.
        intros c' s3. apply return_triple. intros s4 Hf. split.
        intros e' He'.
        rewrite <- Union_Same_set with (s6 := S),
                Union_commut with (s6 := S), Union_assoc.
        eapply He. rewrite bound_var_Econstr. 
        apply Union_Included.
        eapply Included_trans; [ eassumption |]...
        apply Included_Union_preserv_l. apply Included_Union_preserv_r.
        apply Singleton_Included. apply Hf1. zify; omega.
        now apply Setminus_Included.
        eapply fresh_monotonic; [| eassumption ]...
      + intros [[c' map'] f] _. apply pre_curry_l.
        intros He. eapply bind_triple.
        now apply make_full_closure_bound_var_Included.
        intros [[map_n map_o] f'] _. apply pre_curry_l.
        intros He'. eapply pre_curry_l. intros Him.
        eapply bind_triple. eapply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Efun_Included.
        intros [e' f''] s. apply pre_curry_l. intros He''.
        eapply bind_triple. apply IHB.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_fundefs_Efun_Included.
        intros B' s2. apply return_triple. intros s3 [HB Hf].
        simpl in *. split. 
        eapply He. rewrite !bound_var_Efun.
        apply Union_Included.
        eapply Included_trans. eassumption.
        apply Union_Included. eauto with Ensembles_DB.
        apply Union_Included. eauto with Ensembles_DB.
        eapply Included_trans. eassumption. eauto with Ensembles_DB.
        rewrite <- Union_Same_set with (s5 := (Union _ (Union _ _ _) _)),
                                      Union_commut.
        rewrite He'. apply Union_Included.
        eapply Included_trans. eassumption. apply Union_Included.
        now eauto with Ensembles_DB. now eauto with Ensembles_DB.
        do 3 apply Included_Union_preserv_l.
        now apply name_in_fundefs_bound_var_fundefs.
        eauto with Ensembles_DB.
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      eapply get_var_bound_var_Included.
      intros Hc. now eapply HD; eauto.
      intros [g f] s1. apply pre_curry_l. intros He.
      eapply bind_triple.
      eapply get_vars_bound_var_Included.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      rewrite occurs_free_Eapp...
      intros [xs f'] s2. apply pre_curry_l. intros He'.
      eapply bind_triple. now apply get_name_fresh.
      intros ptr s3. apply pre_curry_l. intros Hf.
      eapply bind_triple. now apply get_name_fresh.
      intros env s4. apply pre_curry_l. intros Hf'.
      apply return_triple. intros s5. intros Hf''.
      simpl in *. split.
      eapply He. eapply He'.
      rewrite !bound_var_Eproj, !bound_var_Eapp, !Union_Empty_set_neut_l.
      apply Union_Included. eapply Singleton_Included.
      eapply Hf'. zify; omega.
      eapply Singleton_Included. eapply Hf. zify; omega.
      eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Eprim...
      + intros [xs f] i.
        apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eprim_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split. 
        simpl in *. eapply Hf. rewrite !bound_var_Eprim.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc... 
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      apply get_var_bound_var_Included. intros Hc.
      eapply HD. now constructor; eauto.
      intros [x f] _. apply return_triple. intros s [Hin Hf].
      split.
      eapply Included_trans. now eapply Hin. reflexivity.
      eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      now apply get_name_fresh.
      intros env s1. apply pre_curry_l; intros Hf.
      eapply bind_triple. eapply IHe.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_Fcons_Included.
      intros [e' f] s2. apply pre_curry_l. intros He.
      eapply bind_triple. eapply IHB.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_fundefs_Fcons_Included.
      intros B s3. eapply return_triple.
      intros s4 [Hin Hf']. split. simpl.
      rewrite !bound_var_fundefs_Fcons.
      apply Union_Included.
      destruct (Maps.PTree.get v FVmap) as [v' | ] eqn:Heq;
        try destruct v'; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r.
      rewrite image_Union, image_Singleton. apply Included_Union_preserv_l.
      unfold subst. rewrite Heq. now eauto.
      apply Union_Included. rewrite FromList_cons.
      apply Union_Included. apply Included_Union_preserv_r.
      apply Included_Union_preserv_l. apply Singleton_Included.
      eapply Hf. zify; omega. now eauto with Ensembles_DB.
      apply Union_Included. eapply Included_trans; [ eassumption |]...
      eauto with Ensembles_DB.
      eapply Included_trans; [ eassumption |].
      apply Union_Included. now eauto with Ensembles_DB.
      apply Union_Included. now eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r. 
      apply image_monotonic. now apply Included_Union_r.
      eapply fresh_monotonic; [|  eassumption ]...
    - apply return_triple. intros. split; eauto.
      now apply Included_Union_l.
  Qed.

  Lemma get_var_bound_var_Included' x FVmap c Γ S :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (Singleton _ x'))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Eproj...
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Econstr...
      + apply return_triple.
        intros i' Hf. split.
        * intros e...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included' xs FVmap c Γ S:
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (FromList xs'))) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction xs; intros S Hd.
    - apply return_triple. intros i Hf.
      split.
      intros ?; rewrite !FromList_nil...
      intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included'.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e. eapply Included_trans. eapply Hx.
          eapply Included_trans. eapply Included_Union_compat. eapply Hxs.
          now apply Included_refl. rewrite FromList_cons...
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma get_var_occurs_free_Included' x FVmap c Γ S Scope Funs FVs :
    FVmap_inv FVmap Scope Funs FVs ->
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (occurs_free (f e))
                     (Union _ (occurs_free e)
                            (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                                   (Singleton _ Γ)))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hinv Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. normalize_occurs_free...
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. normalize_occurs_free. rewrite FromList_cons, FromList_singleton.
        apply Union_Included.
        apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        apply Singleton_Included. exists x.
        split. eapply Hinv. now eexists; eauto.
        unfold subst. now rewrite Heq.
        now eauto with Ensembles_DB.
        now eauto with Ensembles_DB. 
      + apply return_triple.
        intros i' Hf. split.
        * intros e...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

   Lemma get_var_occurs_free_Included x FVmap c Γ S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (occurs_free (f e)) (occurs_free e)) /\
            x = x' /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
    }}.
  Proof with now eauto with Ensembles_DB.
    intros Hinv Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf'].
        eapply Hinv in Heq. inv Heq. inv H.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf'].
        assert (Hc : In _ (Setminus _ (Empty_set var) Scope) x)
          by (eapply Hinv; eexists; eauto).
        inv Hc. inv H.
      + apply return_triple.
        intros i' Hf. split; [| split ].
        * intros e...
        * reflexivity.
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split; [| split ].
      + intros e...
      + reflexivity.
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.
  
  Lemma get_vars_occurs_free_Included xs FVmap c Γ S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (occurs_free (f e)) (occurs_free e)) /\
         xs = xs' /\
         fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof.
    revert S; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split. now eauto with Ensembles_DB.
      now rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included.
        eassumption.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        apply pre_curry_l. intros Heq; subst.
        eapply bind_triple.
        * apply IHxs. eassumption. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs [Heq Hf']]. subst. split.
          intros e. now eapply Included_trans; eauto.
          split. reflexivity.
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.
  
  Lemma make_full_closure_occurs_free_Included B m1 m2 Γ S :
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Included _ (occurs_free (f e))
                     (Union _ (Singleton _ Γ)
                            (Union _ (image (subst m1') (name_in_fundefs B))
                                   (Setminus _ (occurs_free e) (name_in_fundefs B))))) /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S Hun. 
    - inv Hun. eapply bind_triple. now apply get_name_fresh.
      intros x s1. apply pre_curry_l. intros Hf1.
      eapply bind_triple. now eapply IHB.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [Hinc Hf]. split.
      + intros e'. normalize_occurs_free.
        rewrite FromList_cons, FromList_singleton.
        simpl. rewrite <- subst_MRFun_f_eq.
        apply Union_Included.
        apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        rewrite image_Union, image_Singleton, extend_gss...    
        now eauto with Ensembles_DB.
        eapply Included_trans.
        eapply Included_Setminus_compat. now eapply Hinc.
        reflexivity.
        rewrite !Setminus_Union_distr.
        apply Union_Included. now eauto with Ensembles_DB. 
        simpl. apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        eapply Included_trans. now apply Setminus_Included.
        eapply Included_image_extend. eassumption.
        rewrite Setminus_Union...
      + eapply fresh_monotonic; [| eassumption ].
        now apply Setminus_Included.
    - apply return_triple. intros s Hf.
      simpl. split.
      intros e... eassumption.
  Qed.

  Lemma make_env_occurs_free_Included FVs m1 m2 c Γ' Γ S Scope :
    FVmap_inv m2 Scope (Empty_set var) [] ->
    Disjoint var S (FromList (PS.elements FVs)) ->
    {{ fun s => fresh S (next_var s) }}
      make_env clo_tag FVs m1 m2 c Γ' Γ
    {{ fun _ t s' =>
         let '(xs, f) := t in
         (forall e : exp,
            Included var (occurs_free (f e))
                     (Union _ (FromList (PS.elements FVs))
                            (Setminus _ (occurs_free e) (Singleton _ Γ')))) /\
         fresh S (next_var s') }}.
  Proof with now eauto with Ensembles_DB.
    intros Hi HD. unfold make_env.
    destruct
      ((fix
          add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
          {struct l} : Maps.PTree.t VarInfo * N :=
          match l with
            | [] => (map, n)
            | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
          end) _ _ _ ) as [m1' n].
    eapply bind_triple.
    eapply get_vars_occurs_free_Included.
    eassumption. eassumption.
    intros [xs f] s2. apply pre_curry_l. intros He.
    apply pre_curry_l. intros Heq. subst.
    eapply bind_triple. apply make_record_ctor_tag_preserves_prop.
    intros c' s3. apply return_triple. intros s4 Hf. split.
    intros e'.
    eapply Included_trans; [ now apply He |].
    repeat normalize_occurs_free. reflexivity.
    eapply fresh_monotonic; [| eassumption ]...
  Qed.

  Corollary exp_closure_conv_closed_fundefs  e c Γ FVmap S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    binding_in_map (occurs_free e) FVmap ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ)) FVmap ->
    Disjoint M.elt S
             (Union var (bound_var e)
                    (Union var (occurs_free e) (Singleton M.elt Γ))) ->
    ~ In var (Union var (bound_var e) (occurs_free e)) Γ ->
    fundefs_names_unique e ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         closed_fundefs_in_exp ((snd ef) (fst ef))
    }}.
  Proof.
    intros Hinv HD1 Hin Hnin HD2 Hnin' Hun.
    eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; try eassumption ]. 
    intros s [e' f] s' _ [C [Hctx [Hcc _]]]. 
    simpl. rewrite Hctx. eapply Closure_conversion_closed_fundefs_mut.
    eassumption. eassumption.
    rewrite Setminus_Empty_set_abs_r, image_Empty_set, Union_Empty_set_neut_l.
    eauto with Ensembles_DB.
  Qed.

  Lemma funs_in_exp_ctx_app_mut :
    (forall C e B, funs_in_exp B e -> funs_in_exp B (C |[ e ]|)) /\
    (forall fC e B, funs_in_exp B e -> funs_in_fundef B (fC <[ e ]>)).
  Proof.
    exp_fundefs_ctx_induction IHe IHB;
    try now (intros e' B' Hfin; eauto; constructor; eauto).
    intros P e' B Hfin. simpl. econstructor.
    eapply IHe. eassumption.
    eapply in_or_app. right. now constructor. 
  Qed.

  Corollary funs_in_exp_ctx_app C e B :
    funs_in_exp B e -> funs_in_exp B (C |[ e ]|).
  Proof.
    now apply funs_in_exp_ctx_app_mut.
  Qed.

  Corollary funs_in_fundefs_ctx_app fC e B :
    funs_in_exp B e -> funs_in_fundef B (fC <[ e ]>).
  Proof.
    now apply funs_in_exp_ctx_app_mut.
  Qed.

  Lemma fundefs_closure_conv_in_image_subst_map B map c :
    {{ fun _ => True }}
      fundefs_closure_conv clo_tag B map c
    {{ fun _ B' _ =>
         Same_set _ (name_in_fundefs B') (image (subst map) (name_in_fundefs B)) }}.
  Proof with now eauto with Ensembles_DB.
    induction B.
    - eapply bind_triple. now apply post_trivial.
      intros x s1. eapply bind_triple. now apply post_trivial.
      intros e' s2. eapply bind_triple. now apply IHB.
      intros B' s3. apply return_triple. intros _ Hseq.
      simpl. rewrite image_Union, image_Singleton...
    - apply return_triple. simpl. intros. 
      rewrite image_Empty_set...
  Qed.
  
  Lemma exp_closure_conv_occurs_free_Included  e c Γ FVmap S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    binding_in_map (occurs_free e) FVmap ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ)) FVmap ->
    Disjoint M.elt S
             (Union var (bound_var e)
                    (Union var (occurs_free e) (Singleton M.elt Γ))) ->
    ~ In var (Union var (bound_var e) (occurs_free e)) Γ ->
    fundefs_names_unique e ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         Included _ (occurs_free ((snd ef) (fst ef))) (occurs_free e) /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S Scope FVmap; induction e using exp_ind';
    intros S Scope FVmap Hinv HD1 Hin Hnin HD2 Hnin' Hun; simpl.
    Opaque exp_closure_conv fundefs_closure_conv. 
    - eapply bind_triple.
      + eapply get_vars_occurs_free_Included.
        eassumption. eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Econstr...
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe. 
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Econstr_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances. 
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc. 
        eapply HD1. constructor; [| now eauto ]. now eapply Setminus_Included; eauto.
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Econstr_Included.
        reflexivity.
        intros Hc.  eapply Hnin'. now eapply bound_var_occurs_free_Econstr_Included.
        now intros B Hfe; eapply Hun; eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. simpl. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple. eapply get_var_occurs_free_Included.
      eassumption.
      intros Hc. eapply HD1. now constructor; eauto.
      intros [x f] _. apply return_triple. intros i'.
      intros [He [Heq Hf]]. subst. split. simpl.
      eapply Included_trans. eapply He.
      repeat normalize_occurs_free...
      eapply fresh_monotonic; [| eassumption ]...
    - setoid_rewrite assoc. eapply bind_triple.
      + eapply IHe. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
        eapply binding_in_map_antimon; [| eassumption ].
        normalize_occurs_free...
        eapply binding_not_in_map_antimon; [| eassumption ]...
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. eapply Included_Union_compat.
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
        reflexivity.
        intros Hc. eapply Hnin'. eapply bound_var_occurs_free_Ecase_Included.
        constructor. reflexivity. eassumption.
        intros B Hfe. eapply Hun. econstructor. now eauto. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_l; intros He'.
        eapply bind_triple. eapply post_conj.
        * eapply IHe0 with (FVmap := FVmap).
          eassumption. 
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Union_assoc. apply Included_Union_preserv_l.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
          eapply binding_not_in_map_antimon; [| eassumption ]...
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc. eapply Included_Union_compat.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          reflexivity.
          intros Hc. eapply Hnin'.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          intros B Hfe. eapply Hun. inv Hfe. econstructor. now eauto.
          constructor 2. now eauto.
        * assert (Ht := exp_closure_conv_is_exp_ctx (Ecase v l) c Γ FVmap).
          eapply pre_strenghtening; [| now apply Ht ].
          intros; simpl; now eauto.
        * intros [e'' f''] s''; destruct e'';
          try (apply return_triple; intros s''' [[Hin1 Hf1] _];
               simpl in *; split;
               [ eapply Included_trans;
                 [ eassumption | normalize_occurs_free; now eauto with Ensembles_DB ]
               | eassumption ]).
          apply return_triple; intros s''' [[Hin1 Hf1] [C Hctx]].
          simpl in *; split; [| eassumption ].
          rewrite Hctx. eapply Included_trans.
          apply occurs_free_Ecase_ctx_app'. rewrite <- Hctx.
          repeat normalize_occurs_free...
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included.
        eassumption.
        intros Hc. eapply HD1. constructor; eauto.
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe. 
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Eproj_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances. 
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc. 
        eapply HD1.
        constructor; [ eapply Setminus_Included; eassumption | now eauto ].
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Eproj_Included.
        reflexivity.
        intros Hc. eapply Hnin'. now eapply bound_var_occurs_free_Eproj_Included.
        intros B Hfe. eapply Hun. now eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply post_mp. 
      eapply exp_closure_conv_closed_fundefs with (e := Efun f2 e); eassumption.
      eapply bind_triple. now eapply get_name_no_suff_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple.
      + eapply post_conj.
        * eapply make_env_spec.
          eapply binding_in_map_antimon; [| eassumption ].
          intros x Hfv. eapply occurs_free_Efun. left.
          eapply fundefs_fv_correct. eassumption. 
          eapply binding_not_in_map_antimon; [| eassumption ]...
          eassumption.
        * eapply make_env_occurs_free_Included. eassumption.
          assert (Heq : (FromList (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
          rewrite Heq, <- fundefs_fv_correct.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_occurs_free...
      + intros [[c' FVmap'] f] _. eapply pre_strenghtening.
        intros s [H H'].
        match type of H with
          | @ex ?t1 (fun C => (@ex ?t2 (fun S' => @ex ?t3 (fun l => ?H1 /\ ?H2)))) =>
            assert (H6 : @ex t1 (fun C => (@ex t2 (fun S' => @ex t3 (fun l => H2)))))
              by (edestruct H as [C1 [S1 [l1 [_ H4']]]]; eauto)
        end.
        exact (conj H6 H').
        apply pre_curry_l. intros [C [S1 [l1 [Hproj [Hctx [Hbin [Hbnin Hinv']]]]]]].
        eapply pre_curry_l. intros He.
        eapply bind_triple.
        * eapply post_conj. 
          eapply make_full_closure_spec; eassumption.
          eapply make_full_closure_occurs_free_Included.
          eapply Hun. now eauto.
        * intros [[FVmap_n FVmap_o] f'] _. eapply pre_strenghtening.
          intros s [H H'].
          match type of H with
            | @ex ?t1 (fun C => (@ex ?t2 (fun S' => ?H1 /\ ?H2))) =>
              assert (H6 : @ex t1 (fun C => (@ex t2 (fun S' => H2))))
                by (edestruct H as [C1 [S1' [_ H4']]]; eauto)
          end.
          exact (conj H6 H').
          apply pre_curry_l. intros [C' [S2 [Hproj' [Hctx' [Hfeq [Hbin1' [Hbin2' [Hbnin1' [Hbnin2' [Hinv1' Hinv2']]]]]]]]]].
          eapply pre_curry_l. intros He'.
          eapply bind_triple.
          eapply IHe. eassumption.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc. apply Included_Union_preserv_l.
          now apply bound_var_occurs_free_Efun_Included.
          eapply binding_in_map_antimon; [| eassumption ].
          now apply occurs_free_Efun_Included.
          eapply binding_not_in_map_antimon; [| eassumption ].
          rewrite <- (Included_Setminus_Disjoint _ (name_in_fundefs f2)).
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. do 2 apply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Singleton_l. intros Hc. eapply Hnin'.
          left. constructor. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc.
          eapply Included_Union_compat; [| now apply Included_refl ]. 
          now apply bound_var_occurs_free_Efun_Included.
          intros Hc. eapply Hnin'. 
          now apply bound_var_occurs_free_Efun_Included.
          intros B Hfe. eapply Hun. now eauto.
          intros [e' f''] s2. eapply pre_curry_l. intros He''.
          eapply bind_triple.
          eapply post_conj. 
          eapply pre_strenghtening;
            [| now eapply fundefs_closure_conv_in_image_subst_map ].
          now simpl; eauto.
          (* a silly way to obtain [fresh S (next_var s4)] but. Too bored
           * to prove it independently now *)
          eapply exp_closure_conv_bound_var_Included_mut.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Union_assoc. apply Included_Union_preserv_l.
          now apply bound_var_occurs_free_fundefs_Efun_Included.
          intros B' s3. eapply return_triple. simpl in *.
          intros s4 [Hseq [_ Hf4]] Hclo. split. 
          eapply Included_trans. eapply He.
          assert (Heq : (FromList (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
          rewrite Heq, <- fundefs_fv_correct.
          normalize_occurs_free.
          rewrite Hctx, <- app_ctx_f_fuse in Hclo. simpl in Hclo.
          assert (Hclo' : Same_set _ (occurs_free_fundefs B') (Empty_set _))
            by (eapply Hclo; apply funs_in_exp_ctx_app; eauto).
          rewrite Hclo', Union_Empty_set_neut_l. 
          repeat normalize_occurs_free. apply Union_Included.
          now eauto with Ensembles_DB.
          do 2 eapply Setminus_Included_Included_Union.
          eapply Included_trans. eapply He'.
          apply Union_Included. now eauto with Ensembles_DB.
          apply Union_Included. rewrite <- Hseq...
          eapply Setminus_Included_Included_Union.
          eapply Included_trans. eassumption.
          rewrite Union_commut, (Union_commut (occurs_free_fundefs f2)), !Union_assoc.
          do 3 apply Included_Union_preserv_l.
          rewrite Union_Setminus_Included; now eauto with Ensembles_DB typeclass_instances.
          eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included. eassumption.
        intros Hc.  eapply HD1. now constructor; eauto.
      + intros [x f] s1.
        apply pre_curry_l. intros He. apply pre_curry_l; intros Heq; subst.
        eapply bind_triple.
        eapply get_vars_occurs_free_Included. eassumption.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        repeat normalize_occurs_free_in_ctx...
        intros [xs f'] s2. 
        apply pre_curry_l. intros He'. apply pre_curry_l; intros Heq; subst.
        eapply bind_triple. now apply get_name_fresh.
        intros y s3. apply pre_curry_l. intros Hfy.
        eapply bind_triple. now apply get_name_fresh.
        intros z s4. apply pre_curry_l. intros Hfz.
        apply return_triple. intros s5 Hf.
        split.
        simpl. eapply Included_trans. apply He.
        eapply Included_trans. apply He'.
        repeat normalize_occurs_free. rewrite FromList_cons.
        now eauto 20 with Ensembles_DB. (* takes some time... *)
        eapply fresh_monotonic; [| eassumption ]...
    -  eapply bind_triple.
      + eapply get_vars_occurs_free_Included.
        eassumption. eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Eprim...
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe. 
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Eprim_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances. 
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc. 
        eapply HD1. constructor; [| now eauto ]. now eapply Setminus_Included; eauto.
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Eprim_Included.
        reflexivity.
        intros Hc.  eapply Hnin'. now eapply bound_var_occurs_free_Eprim_Included.
        now intros B Hfe; eapply Hun; eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. simpl. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      eapply get_var_occurs_free_Included. eassumption.
      intros Hc. eapply HD1. now constructor; eauto.
      intros [x f] _. apply return_triple.
      intros s1 [He [Heq Hf]]. subst. split.
      now apply He.
      eapply fresh_monotonic; [| eassumption ]...
  Qed.

  Transparent exp_closure_conv fundefs_closure_conv.
  
  Lemma get_var_unique_bindings x FVmap c Γ S S' :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (Singleton _ x'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin. unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto. 
        eapply Hf. zify; omega. inv H. exfalso; eauto.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto. 
        eapply Hf. zify; omega. inv H. exfalso; eauto.
      + apply return_triple.
        intros i' Hf. split.
        intros e Hin Hd Hun. eassumption. 
        intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      intros e Hin Hd Hun. eassumption.
      intros x' Hleq. constructor. now eauto.
      intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_unique_bindings xs FVmap c Γ S S' :
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_unique_bindings;
        intros Hin'; eapply Hd; constructor; eauto;
        rewrite FromList_cons; left; eauto.
      + intros [x f] i.
        apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * rewrite FromList_cons in Hd.
          eapply post_conj;
          [apply get_vars_bound_var_Included | apply IHxs ]...
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [[Hxs1 _] [Hxs2 Hf']]. split.
          intros e Hin' Hd' Hun. eapply Hx.
          eapply Hxs1. eapply Included_trans. eassumption.
          rewrite FromList_cons. apply Included_Union_compat. now apply Included_refl.
          eauto with Ensembles_DB.
          eassumption.
          eapply Hxs2. eapply Included_trans. eassumption.
          apply Included_Union_compat. now apply Included_refl.
          rewrite FromList_cons... eauto with Ensembles_DB.
          eassumption. rewrite FromList_cons, <- Setminus_Union...
  Qed.
  
  Lemma make_full_closure_unique_bindings B m1 m2 Γ S :
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Disjoint _ (bound_var e) (bound_var_fundefs B) ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (image (subst m1') (name_in_fundefs B)))
               (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S Hun. 
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. apply pre_curry_l. intros Hf1. inv Hun.
      eapply bind_triple. eapply post_conj. now eapply IHB.
      now apply make_full_closure_bound_var_Included.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [[Hun Hf] [Heq [Hinc _]]]. split.
      + intros e' Hun1 Hin1. constructor.
        intros Hb. eapply Hun1.
        constructor. apply Heq in Hb. inv Hb; eauto.
        exfalso. now eauto. rewrite bound_var_fundefs_Fcons...
        eapply Hun; eauto.
        rewrite bound_var_fundefs_Fcons in Hun1. 
        eauto with Ensembles_DB.
      + eapply fresh_monotonic; [| eassumption ].
        rewrite <- subst_MRFun_f_eq. simpl.
        rewrite image_extend_In_S.  rewrite Setminus_Union.
        apply Included_Setminus_compat. reflexivity.
        rewrite Union_commut. eapply Included_Union_compat.
        reflexivity. apply image_monotonic...
        now eauto.
    - apply return_triple. intros s Hf.
      simpl. split. now eauto.
      rewrite image_Empty_set, Setminus_Empty_set_neut_r. eassumption.
  Qed.

  Lemma make_full_closure_injective S B m1 m2 Γ :
    Disjoint var S (name_in_fundefs B) ->
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }} 
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s p s' =>
         let '(m1', m2', f) := p in
         injective_subdomain (name_in_fundefs B) (subst m1') /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S. induction B; intros S HD Hun.
    - eapply bind_triple. now apply get_name_fresh.
      intros v' s1. apply pre_curry_l. intros Hfv'.
      eapply bind_triple.
      + eapply post_conj.
        * eapply IHB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          now eauto with Ensembles_DB. inv Hun. eassumption.
        * eapply make_full_closure_bound_var_Included.
      + intros [[m1' m2'] f'] _.
        apply return_triple. intros s2 [[HInj Hf] [_ [Hinc _]]].
        split.
        * simpl. apply injective_subdomain_Union.
          now apply injective_subdomain_Singleton.
          rewrite <- subst_MRFun_f_eq. eapply injective_subdomain_extend'.
          eapply injective_subdomain_antimon; [ eassumption |]...
          intros Hc. eapply Hinc. eapply image_monotonic; [| eassumption ].
          now eapply Setminus_Included. now eauto.
          rewrite image_Singleton. 
          unfold subst at 1. rewrite M.gss, <- subst_MRFun_f_eq.
          rewrite image_extend_not_In_S. 
          eapply Disjoint_Included_r. eassumption.
          eapply Disjoint_Setminus_r. reflexivity.
          inv Hun. eassumption.
        * eapply fresh_monotonic; [| eassumption ].
          now apply Setminus_Included.
    - eapply return_triple. intros s1 Hf. split; [| eassumption ].
      now apply injective_subdomain_Empty_set.
  Qed.


  Lemma exp_closure_conv_unique_bindings_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e)))
       (Hun : unique_bindings e),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            unique_bindings ((snd ef) (fst ef)) /\
            fresh (Setminus _ S (bound_var ((snd ef) (fst ef)))) (next_var s')
        }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B)))
       (HD' : Disjoint _  (image (subst FVmap) (name_in_fundefs B))
                       (Union _ (bound_var_fundefs B) S))
       (Hun : unique_bindings_fundefs B)
       (Hinj : injective_subdomain (name_in_fundefs B) (subst FVmap)),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
            unique_bindings_fundefs B' /\
            Disjoint _ (name_in_fundefs B) (bound_var_fundefs B') /\
            fresh (Setminus _ S (bound_var_fundefs B')) (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite occurs_free_Econstr...
      + intros [xs f] i.
        eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]]. 
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin'].
        eapply bind_triple. inv Hun.
        eapply post_conj;
          [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Econstr_Included | eassumption ]]).
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
        simpl in *. inv Hun. eapply Hun'. rewrite bound_var_Econstr.
        apply Union_Included;
          [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx. now eauto with Ensembles_DB.
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Econstr...
        eapply Setminus_Disjoint_preserv_l... 
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple.
       eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; now constructor; eauto.
       intros [x f] _. apply return_triple. intros i' [[He _] [Hin Hf]].
       split; eauto. simpl. eapply He; try now constructor.
       rewrite bound_var_Ecase_nil... eauto with Ensembles_DB.
       eapply fresh_monotonic; [| eassumption ]. simpl.
       eapply Included_Setminus_compat. reflexivity.
       eapply Included_trans. eapply Hin. rewrite bound_var_Ecase_nil...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      inv Hun. eapply bind_triple.
      + eapply post_conj.
        * eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
          eassumption.
        * eapply exp_closure_conv_bound_var_Included_mut.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        eapply pre_strenghtening. intros i [[Hun' Hf] [Hin _]]. 
        exact (conj (conj Hun' Hin) Hf).
        eapply pre_curry_l; intros [He' Hin]. 
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_l. now apply Setminus_Included.
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included. 
            eassumption.
          - eapply post_conj.
            + eapply pre_strenghtening;
              [ | now eapply exp_closure_conv_is_exp_ctx
                  with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
              intros. simpl; eauto.
            + eapply exp_closure_conv_bound_var_Included_mut
              with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap).
              eapply Disjoint_Included_l. now apply Setminus_Included.
              eapply Disjoint_Included_r; [| eassumption ].
              now eapply bound_var_occurs_free_Ecase_cons_Included. }
        intros [e'' f''] s''. 
        destruct e''; apply return_triple;
        try now (intros ? [[? Hf] [? [? ?]]]; split;
                 [ now eauto | eapply fresh_monotonic; [| now apply Hf ];
                               eauto with Ensembles_DB ]).
        intros s''' [[Hin' Hf'] [[C Hctx] [Hin'' Hf'']]]; split; eauto. simpl in *.
        rewrite Hctx. apply unique_bindings_ctx_app_Ecase_cons.
        eassumption. now rewrite <- Hctx.
        rewrite <- Hctx. eapply Disjoint_Included_r. eassumption.
        eapply Union_Disjoint_r. eapply Disjoint_Included_l. eassumption.
        repeat normalize_bound_var_in_ctx...
        now eauto with Ensembles_DB. 
        simpl in *. rewrite Hctx in *. rewrite bound_var_ctx_app_Ecase_cons.
        rewrite <- Setminus_Union. eassumption.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; eauto.
      + intros [xs f] i. eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]].
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin']. inv Hun.
        eapply bind_triple.
        * eapply post_conj.
          eapply IHe. eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
          eassumption.
          eapply exp_closure_conv_bound_var_Included_mut.
          eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
        * intros [e' f'] s'. simpl. apply return_triple.
          intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
          simpl in *. eapply Hun'. rewrite bound_var_Eproj.
          apply Union_Included;
            [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx...
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Eproj...
        eapply Setminus_Disjoint_preserv_l... 
    - eapply bind_triple. now apply get_name_no_suff_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1. unfold make_env.
      assert (Heqel : (@FromList var (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
      destruct
        ((fix
            add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
            {struct l} : Maps.PTree.t VarInfo * N :=
            match l with
              | [] => (map, n)
              | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
            end) _ _ _ ) as [m1' n].
      setoid_rewrite assoc.
      eapply bind_triple.
      eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        eapply Setminus_Disjoint_preserv_l;
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite Heqel, <- fundefs_fv_correct; rewrite occurs_free_Efun...
      intros [xs f1] s2. eapply pre_strenghtening. intros ? [[Hun1 _] [Hin Hf]].
      exact (conj (conj Hun1 Hin) Hf).
      apply pre_curry_l; intros [Hun1 Hin1]. inv Hun.
      setoid_rewrite assoc.
      eapply bind_triple. now apply make_record_ctor_tag_preserves_prop.
      intros c1 s3.  eapply bind_triple.
      now eapply return_triple with
      (Post := fun s r s' =>
                 fresh (Setminus var (Setminus var S (Singleton var Γ')) (FromList xs))
                       (next_var s') /\
                 r = (c1, m1', fun e0 : exp => f1 (Econstr Γ' c1 xs e0))).
      intros [[c' m] f] s4. eapply pre_curry_r; intros Heq; inv Heq.
      eapply bind_triple.
      eapply post_conj;
        [ eapply make_full_closure_unique_bindings |
          eapply post_conj;
            [ eapply make_full_closure_bound_var_Included
            | eapply make_full_closure_injective ]].
      now apply unique_bindings_fundefs_unique_functions.
      eapply Disjoint_Included_l; [ now apply Setminus_Included | ].         
      eapply Disjoint_Included_l; [ now apply Setminus_Included | ].         
      eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
      repeat normalize_bound_var_in_ctx...
      now eapply unique_bindings_fundefs_unique_functions.
      intros [[m m'] f'] s5. eapply pre_strenghtening.
      intros ? [[Hun2 Hf] [[Hseq [Hin2 _]] [Hinj _]]].
      exact (conj (conj Hun2 (conj Hin2 (conj Hseq Hinj))) Hf).
      apply pre_curry_l; intros [Hun2 [Hin2 [Hseq Hinj]]].
      eapply bind_triple.
      + eapply post_conj.
         eapply IHe. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].         
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included. eassumption. 
         eapply exp_closure_conv_bound_var_Included_mut. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included.
      + intros [e' f''] s6. eapply pre_strenghtening. intros ? [[Hun3 Hf] [Hin3 _]]. 
        exact (conj (conj Hun3 Hin3) Hf). eapply pre_curry_l. intros [Hun3 Hin3]. simpl in *.
        eapply bind_triple.
        * eapply post_conj.
          eapply IHB. rewrite !Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          normalize_bound_var_in_ctx...
          apply Setminus_Disjoint_preserv_r. now apply Disjoint_Setminus_r.
          eassumption. eassumption.
          eapply post_conj.
          eapply exp_closure_conv_bound_var_Included_mut. rewrite !Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included.
          eapply pre_strenghtening; [| eapply fundefs_closure_conv_in_image_subst_map ].
          now intros; simpl; eauto. 
        * intros B' s7. apply return_triple.
          intros s8 [[Hun4 [Hd Hf']] [[Hinc4 _] Hin5]]. simpl in *.
          split. eapply Hun1. repeat normalize_bound_var.
          rewrite Hseq. repeat apply Union_Included.
          eapply Included_trans. eassumption.
          repeat apply Union_Included. eapply Included_Union_preserv_l.
          now eapply (Included_Union_l _ (Union _ (bound_var e) (Singleton _ Γ'))).
          eapply Included_Union_preserv_r... rewrite <- Hin5.
          eapply Included_trans. now eapply name_in_fundefs_bound_var_fundefs.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          do 2 eapply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB.
          rewrite Union_assoc. eapply Union_Disjoint_l.
          repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. now apply Setminus_Included.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Setminus_r...
          constructor. intros Hc. eapply bound_var_Efun in Hc. 
          inv Hc. eapply Hinc4 in H. inv H.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          now eauto.
          inv H0. inv H. inv H0. inv H. inv H0. now eauto.
          eapply Hin2 in H. inv H. inv H0. now eauto.
          rewrite Hseq in H. inv H. eapply Hin3 in H0.
          inv H0. eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          now repeat normalize_bound_var; eauto. inv H.
          inv H0. inv H. now eauto.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          left. rewrite bound_var_Efun. left. now eapply name_in_fundefs_bound_var_fundefs.
          constructor. eapply Hun2. eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. eassumption.
          eapply (Disjoint_Included_l _ _ S). now eauto with Ensembles_DB.
          repeat normalize_bound_var_in_ctx...
          eassumption. eassumption.
          rewrite Hseq. apply Union_Disjoint_l; [| eassumption ].
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.         
          eapply Union_Disjoint_l. eassumption.
          do 3 eapply Setminus_Disjoint_preserv_l.
          repeat normalize_bound_var_in_ctx...
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_Included_r. eassumption.
          do 2 eapply Setminus_Disjoint_preserv_r.
          repeat normalize_bound_var_in_ctx...
          now eauto with Ensembles_DB.
          eapply fresh_monotonic; [| eassumption ].
          rewrite !Setminus_Union.
          eapply Included_trans;
            [| eapply Included_Setminus_compat;
               [ now apply Included_refl | now eapply Hin1 ] ].
          repeat normalize_bound_var. rewrite Hseq.  
          rewrite <- !Union_assoc, (Union_commut (name_in_fundefs f2) _), <- !Setminus_Union.
          rewrite <- (Included_Setminus_Disjoint _ (name_in_fundefs f2)).
          rewrite !Setminus_Union.
          eapply Included_Setminus_compat;
            [ now apply Included_refl  | now eauto 10 with Ensembles_DB ].
          do 4 eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          repeat normalize_bound_var_in_ctx...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings |
          eapply post_conj;
            [ eapply get_var_bound_var_Included with (S' := Empty_set _) |
              eapply get_var_bound_var_Included' ]];
        intros Hc; eapply HD; eauto. 
      + intros [x f] s1. eapply pre_strenghtening.
        intros ? [[Hun1 _] [[Hin Hf] [Hin' _]]].
        exact (conj (conj Hun1 (conj Hin Hin')) Hf).
        eapply pre_curry_l; intros [Hun1 [Hin1 Hin1']]. eapply bind_triple.
        eapply post_conj;
          [ eapply get_vars_unique_bindings |
            eapply post_conj;
              [ eapply get_vars_bound_var_Included |
                eapply get_vars_bound_var_Included' ]];
        normalize_bound_var_in_ctx; normalize_occurs_free_in_ctx...
        intros [xs f'] s2. eapply pre_strenghtening.
        intros ? [[Hun2 _] [[Hin2 Hf2] [Hin2' _]]].
        exact (conj (conj Hun2 (conj Hin2 Hin2')) Hf2).
        eapply pre_curry_l; intros [Hun2 [Hin2 Hin2']].
        eapply bind_triple. now apply get_name_fresh.
        intros g' s3. eapply pre_curry_l. intros Hg'.
        eapply bind_triple. now apply get_name_fresh.
        intros Γ' s4. eapply pre_curry_l. intros HΓ'.
        apply return_triple. intros s5. intros Hfs5. simpl. split.
        eapply Hun1.
        eapply Included_trans. eapply Hin2.
        repeat normalize_bound_var. rewrite Union_Empty_set_neut_l.
        apply Union_Included.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply HΓ'. zify; omega.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply Hg'. zify; omega.
        now apply Included_refl. apply Disjoint_sym. eassumption.
        eapply Hun2. repeat normalize_bound_var. rewrite Union_Empty_set_neut_l.
        apply Union_Included.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply HΓ'. zify; omega.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply Hg'. zify; omega.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ]...
        constructor.
        intros Hc. inv Hc. eapply HΓ' with (y := g'). zify; omega.
        now eauto. now inv H5. 
        constructor. intros Hc. now inv Hc. 
        now constructor.
        eapply fresh_monotonic; [| eassumption ]. rewrite !Setminus_Union.
        apply Included_Setminus_compat. reflexivity.
        eapply Included_trans. now apply Hin1'.
        apply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Included_trans. now apply Hin2'.
        apply Union_Included; [| now eauto with Ensembles_DB ].
        repeat normalize_bound_var...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite occurs_free_Eprim...
      + intros [xs f] i.
        eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]]. 
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin'].
        eapply bind_triple. inv Hun.
        eapply post_conj;
          [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Eprim_Included | eassumption ]]).
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
        simpl in *. inv Hun. eapply Hun'. rewrite bound_var_Eprim.
        apply Union_Included;
          [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx. now eauto with Ensembles_DB.
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Eprim...
        eapply Setminus_Disjoint_preserv_l...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings |
          eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; eauto. 
      + intros [x f] s1. apply return_triple.
        intros s2 [[Hun' Hf] [Hin' Hf']].
        split. simpl. eapply Hun'. rewrite bound_var_Ehalt.
        now apply Included_Union_l. now eauto with Ensembles_DB.
        now constructor.
        simpl. eapply fresh_monotonic; [| eassumption ].
        eapply Included_Setminus_compat. reflexivity.
        eapply Included_trans. now apply Hin'.
        normalize_bound_var...
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. eapply pre_curry_l. intros Hfx. inv Hun. eapply bind_triple.
      + eapply post_conj;
        [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Fcons_Included  | eassumption ]]).
      + intros [e' f] s2.
        eapply pre_strenghtening. intros ? [[Hun Hf] [Hin _]]. 
        exact (conj (conj Hun Hin) Hf).
        apply pre_curry_l; intros [Hun Hin].
        eapply bind_triple.
        eapply post_conj.
        eapply IHB.
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].        
        eapply Disjoint_Included_r; [| eassumption ].
        now eapply bound_var_occurs_free_fundefs_Fcons_Included.
        simpl in *.
        eapply Disjoint_Included; [| | now apply HD' ].
        normalize_bound_var... apply image_monotonic...
        eassumption.
        eapply injective_subdomain_antimon. eassumption.
        now eauto with Ensembles_DB.
        eapply post_conj.
        eapply exp_closure_conv_bound_var_Included_mut.
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_r; [| eassumption ].
        now eapply bound_var_occurs_free_fundefs_Fcons_Included.
        eapply pre_strenghtening; [| eapply fundefs_closure_conv_in_image_subst_map ].
        now intros; simpl; eauto.
        intros B' s3. eapply return_triple. intros s4 [[Hun' [HD'' Hf4]] [[Hin' _] Hseq]].
        simpl in *. split.
        * constructor; eauto. intros Hb. eapply Hin in Hb.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hb; [ now eauto |]; inv H; eapply HD;
               constructor; [ eassumption |
                              normalize_bound_var; now eauto with Ensembles_DB ]).
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. normalize_bound_var. inv Hb.
          now eauto. right. now eapply H.
          intros Hb. eapply Hin' in Hb.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hb; [ now eauto |
                         inv H; [ inv H0; inv H; eapply HD; constructor;
                                  [ eassumption
                                  | normalize_bound_var; now eauto with Ensembles_DB ]
                                |  eapply HD'; constructor;
                                   [ eapply image_monotonic; [| eassumption ];
                                     eauto with Ensembles_DB
                                   | normalize_bound_var; now eauto with Ensembles_DB ]
                                ]]).
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. normalize_bound_var. inv Hb.
          now eauto. inv H. right. now eapply H0.
          exfalso. destruct H0 as [v' [Hv' Heq']].
          assert (Heq'': v = v').
          { eapply Hinj; eauto. rewrite Heq'. unfold subst. now rewrite Heq. }
          subst. eapply H5. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. rewrite FromList_cons.
          eapply Union_Disjoint_r; [| eassumption ].
          eapply Disjoint_Singleton_r. intros H. eapply HD with (x := x).
          constructor. eapply Hfx. zify. omega.
          normalize_bound_var...
          rewrite FromList_cons. eapply Union_Disjoint_r.
          eapply Disjoint_Setminus_l...
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          rewrite FromList_cons. 
          eapply Disjoint_Included_l. eassumption.
          apply Union_Disjoint_l.
          apply Union_Disjoint_r; [| eassumption ].
          eapply Disjoint_Included_r with (s6 := S).
          apply Singleton_Included. eapply Hfx. zify; omega.
          eapply Disjoint_Included_l_sym; [| eassumption ]. 
          normalize_bound_var...
          apply Union_Disjoint_l. apply Union_Disjoint_r.
          rewrite Setminus_Union. eapply Disjoint_Setminus_l...
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          apply Union_Disjoint_r.
          eapply Disjoint_Included; [| | now apply HD' ].
          apply Included_Union_preserv_r. apply Singleton_Included.
          apply Hfx. zify; omega.
          apply image_monotonic...          
          eapply Disjoint_Included; [| | now apply HD' ].
          apply Included_Union_preserv_l.
          normalize_bound_var...
          apply image_monotonic...          
          eapply Disjoint_Included_r; [ eassumption  |  ].
          apply Union_Disjoint_r.
          eapply Disjoint_Included_l; [ eassumption  |  ].
          apply Union_Disjoint_l. eassumption.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          apply Union_Disjoint_r.
          apply Disjoint_Setminus_r...
          eapply Disjoint_Included_l; [ eassumption  |  ].
          apply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD' ].
          normalize_bound_var...
          apply image_monotonic...          
          intros Hc. apply FromList_cons in Hc.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hc; [ inv H; eapply HD with (x := v);
                         constructor; [ eapply Hfx; zify; omega | now eauto ]
                       | now eauto ]).
          inv Hc.
          inv H. eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. right. eapply Hfx. zify; omega.
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. now left; eauto.
          constructor; eauto. intros Hinl.
          eapply HD with (x := x). constructor. eapply Hfx. zify; omega.
          left. normalize_bound_var...
        * split. normalize_bound_var.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r.
          intros Hc. 
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (eapply HD'; constructor;
               [ now eexists; eauto | now unfold subst; rewrite Heq; eauto ]).
          inv Hc. inv H. eapply HD'. constructor. now eexists; eauto.
          unfold subst; rewrite Heq; eauto. 
          eapply HD' with (x := v0). constructor. eexists; eauto. split.
          now left; eauto. unfold subst; rewrite Heq; now eauto.
          normalize_bound_var. left. do 3 right. now apply name_in_fundefs_bound_var_fundefs.
          apply Union_Disjoint_r. rewrite FromList_cons. apply Union_Disjoint_l.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r. intros Hc; inv Hc.
          eapply HD. constructor; [| now eauto ]. eapply Hfx; zify; omega.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r. intros Hc. 
          eapply HD. constructor; [| now eauto ]. apply Hfx; zify; omega.
          eassumption.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_r. eassumption.
          apply Union_Disjoint_r. apply Union_Disjoint_l.
          now apply Disjoint_Singleton_l.
          eapply Disjoint_Included_l_sym. now apply name_in_fundefs_bound_var_fundefs.
          eassumption.
          apply Union_Disjoint_l. apply Disjoint_Singleton_l.
          intros Hc. eapply HD. constructor; [| now eauto ].
          eapply Setminus_Included. eassumption.
          eapply Disjoint_Included_l_sym. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          repeat normalize_bound_var_in_ctx...
          apply Union_Disjoint_l; [| eassumption ].
          eapply Disjoint_Included_r. eassumption.
          apply Union_Disjoint_r. now apply Disjoint_Singleton_l.
          apply Union_Disjoint_r. do 2 apply Setminus_Disjoint_preserv_r.
          repeat normalize_bound_var_in_ctx...
          eapply Disjoint_Included_r. apply image_monotonic.
          apply Included_Union_r.
          repeat normalize_bound_var_in_ctx...
          eapply fresh_monotonic; [| eassumption ].
          normalize_bound_var. rewrite !Setminus_Union, FromList_cons.
          rewrite (Union_commut _ (FromList _)), <- !Union_assoc.
          rewrite (Union_assoc (Singleton _ _) (FromList _)), (Union_commut (Union _ (Singleton _ _) (FromList _))).
          rewrite <- (Setminus_Union _ _ (Union _ (Singleton _ _) (FromList _))).
          rewrite <- (Included_Setminus_Disjoint _ (Union _ (Singleton _ _) (FromList _))).
          reflexivity.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          apply Union_Disjoint_r.
          apply Disjoint_Singleton_r. intros Hc. 
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          now (eapply HD'; constructor;
               [ now eexists; eauto | now unfold subst; rewrite Heq; eauto ]).
          repeat normalize_bound_var_in_ctx...
    - apply return_triple. intros s2 Hf. split. now constructor.
      split. now eauto with Ensembles_DB. normalize_bound_var.
      rewrite Setminus_Empty_set_neut_r. eassumption.
  Qed.

  (** Correctness of [exp_closure_conv] and invariant preservation *)
  Corollary exp_closure_conv_correct_inv k rho rho' S e c Γ FVmap Scope :
    (* [Scope], [Funs] and [FVs] are uniquely identified by [FVmap] *)
    FVmap_inv FVmap Scope (Empty_set _) [] ->
    (* [Γ] (the current environment parameter) is fresh in e *)
    ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* [FVmap] contains all the free variables *)
    binding_in_map (occurs_free e) FVmap ->
    (* [e] has unique bindings *)
    unique_bindings e ->
    (* [FVmap] does not contain the variables in [S] or [Γ] *)
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
    Disjoint _ S  (Union _ (bound_var e)
                         (Union _ (occurs_free e) (Singleton _ Γ))) ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         cc_approx_exp pr cenv clo_tag k (boundL k e rho) boundG (e, rho) ((snd ef) (fst ef), rho') /\
         Included _ (occurs_free ((snd ef) (fst ef))) (occurs_free e) /\
         unique_bindings ((snd ef) (fst ef)) /\
         closed_fundefs_in_exp ((snd ef) (fst ef)) /\
         Included _ (bound_var ((snd ef) (fst ef)))
                  (Union _ (bound_var e) S)
    }}.
  Proof with now eauto with Ensembles_DB.
    intros IFVmap HGamma Hin_map_rho Hin_map_FVmap Hun
           Hnot_in_map Hcc HD. 
    eapply post_conj; [| eapply post_conj; [| eapply post_conj; [| eapply post_conj ]]].
    - eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; try eassumption ].
      intros s [e' f] s' Hf [C [Hctx [Hclo _]]]. simpl in Hctx, Hclo.
      simpl. replace (f e') with (C |[ e' ]|); [| now eauto].
      eapply Closure_conversion_correct; try eassumption.
      intros Hc. eapply HGamma; eauto.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
      now apply injective_subdomain_Empty_set.
      rewrite Setminus_Empty_set_abs_r, image_Empty_set...
      intros f' v Hnin Hin. now inv Hin.
      intros x N v Hnin Hin Hnth. eapply nthN_In in Hnth. now inv Hnth.
      rewrite Setminus_Empty_set_abs_r, image_Empty_set, Union_Empty_set_neut_l.
      now eauto with Ensembles_DB.
    - eapply post_weakening; [| eapply exp_closure_conv_occurs_free_Included; try eassumption ].
      now simpl; intros s [x f] s' _ [Hin _]; eauto.
      now eauto with Ensembles_DB.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
    - eapply post_weakening; [| eapply exp_closure_conv_unique_bindings_mut; try eassumption ].
      now simpl; intros s [x f] s' _ [Hin _]; eauto.
      now eauto with Ensembles_DB.
    - eapply post_weakening; [| eapply exp_closure_conv_closed_fundefs; try eassumption ].
      now simpl; eauto.
      now eauto with Ensembles_DB.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
    - eapply post_weakening; [| eapply exp_closure_conv_bound_var_Included_mut; try eassumption ].
      now simpl; eauto.
      now eauto with Ensembles_DB.
  Qed.

  Lemma populate_map_FVmap_inv l map Scope Funs FVs:
    FVmap_inv map Scope Funs FVs ->
    FVmap_inv (populate_map l map) (Union _ (FromList (List.map fst l)) Scope) Funs FVs.
  Proof.
    unfold populate_map. revert Scope map. induction l as [| [x v] l IHl ]; intros Scope map Hinv.
    - simpl. rewrite FromList_nil, Union_Empty_set_neut_l. eassumption.
    - simpl in *. rewrite FromList_cons, (Union_commut (Singleton _ _) _), <- Union_assoc.
      eapply IHl. apply FVmap_inv_set_bound. eassumption.
  Qed.
  
  Lemma populate_map_binding_in_map S l map :
    binding_in_map S map ->
    binding_in_map (Union _ (FromList (List.map fst l)) S) (populate_map l map).
  Proof.
    revert S map. induction l; intros S map Hin. 
    - simpl. intros x Hc.
      rewrite FromList_nil, Union_Empty_set_neut_l in Hc.
      now eauto.
    - simpl. intros x Hc.
      rewrite FromList_cons, (Union_commut (Singleton _ _) _), <- Union_assoc in Hc.
      eapply IHl; [| eassumption ].
      intros x' Hc'. eapply binding_in_map_set. eassumption.
      inv Hc'; eauto.
  Qed.

  Lemma populate_map_binding_not_in_map S l map :
    binding_not_in_map S map ->
    Disjoint _ S (FromList (List.map fst l)) ->
    binding_not_in_map S (populate_map l map).
  Proof.
    revert S map. induction l; intros S map Hnin HD. 
    - simpl. intros x Hc. eapply Hnin. eassumption.
    - simpl in *. intros x Hc.
      eapply IHl. eapply binding_not_in_map_set_not_In_S. eassumption.
      intros Hc'. eapply HD. constructor. eassumption.
      rewrite FromList_cons. now eauto.
      rewrite FromList_cons in HD. now eauto with Ensembles_DB.
      eassumption.
  Qed.
    
End CC_correct.

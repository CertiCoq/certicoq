From Coq Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon Common.compM.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import L4.expression L4.fuel_sem.

Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        tactics L4_to_L6 L4_to_L6_util L6.tactics identifiers
        cps_util rename state. 

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Corresp.

  Context (prim_map : M.t (kername * string * nat))
          (func_tag kon_tag default_tag : positive). 


  Definition cps_cvt_exp_corresp :=
    forall e S vn k ctrs (Hwf : exp_wf (N.of_nat (List.length vn)) e),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt prim_map func_tag kon_tag default_tag e vn k ctrs 
      {{ fun _ s e' s' =>
           exists S',
             cps_cvt_rel func_tag kon_tag default_tag S e vn k ctrs S' e' /\
             fresh S' (next_var (fst s'))
             (* Needed to compose with λANF proofs -- ignore for now *) 
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var e' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings e' /\ *)
             (* Disjoint _ (occurs_free e') (bound_var e') *)
      }} .

  Definition cps_cvt_exps_corresp := 
    forall es S vn xs k ctrs (Hwf : exps_wf (N.of_nat (List.length vn)) es)
           (Hlen : List.length xs = N.to_nat (exps_length es)),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_exps prim_map func_tag kon_tag default_tag es vn k xs ctrs 
      {{ fun _ s e' s' =>
           exists S',
             cps_cvt_rel_exps func_tag kon_tag default_tag S es vn k xs ctrs S' e' /\
             fresh S' (next_var (fst s')) 
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var e' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings e' /\ *)
             (* Disjoint _ (occurs_free e') (bound_var e') *)
      }}.

  Definition cps_cvt_efnlst_corresp :=
    forall efns S vn xs ctrs (Hwf : efnlst_wf (N.of_nat (List.length vn)) efns)
           (Hlen : List.length xs = efnlength efns),
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_efnlst prim_map func_tag kon_tag default_tag efns vn xs ctrs 
      {{ fun _ s B' s' =>
           exists S',
             cps_cvt_rel_efnlst func_tag kon_tag default_tag S efns vn xs ctrs S' B' /\
             fresh S' (next_var (fst s'))
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var_fundefs B' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings_fundefs B' /\ *)
             (* Disjoint _ (occurs_free_fundefs B') (bound_var_fundefs B') *)
      }} .
    
  Definition cps_cvt_branches_corresp :=
    forall bs S vn k r ctrs (Hwf : branches_wf (N.of_nat (List.length vn)) bs),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_branches prim_map func_tag kon_tag default_tag bs vn k r ctrs 
      {{ fun _ s P s' =>
           exists S',
             cps_cvt_rel_branches func_tag kon_tag default_tag S bs vn k r ctrs S' P /\
             fresh S' (next_var (fst s'))
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var (Ecase r P) \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings (Ecase r P) /\            *)
             (* Disjoint _ (occurs_free (Ecase r P)) (bound_var (Ecase r P)) *)
      }} .

  Require Import closure_conversion_corresp.

  (* TODO move to state *)
  Lemma get_named_spec : 
    forall (A : Type) (S : Ensemble var) (n : name),
      {{fun (_ : unit) (s : comp_data * A) => fresh S (next_var (fst s))}} get_named n
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
    split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. lia.
    simpl. split. zify; lia.
    intros z Hin. constructor. eapply H; eauto. simpl. zify. lia.
    intros Hc. inv Hc. zify; lia.
  Qed.

  Lemma get_named_str_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_str_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.  
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_str_fresh.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  Lemma get_named_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.  
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_spec.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  Ltac inv_setminus :=
    match goal with
    | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
    end.

  Section IP.

    Context (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop). 

    Context
      (H1 : forall n : N, P (Var_e n))
      (H2 : forall (n : name) (e : expression.exp), P e -> P (Lam_e n e))
      (H3: forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0))
      (H4 : forall (d : dcon) (e : exps), P0 e -> P (Con_e d e))
      (H5 : forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b))
      (H6 : forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0))
      (H7 : forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n))
      (H9 : P Prf_e)
      (H10 : forall p : positive, P (Prim_e p))
      (H11 : P0 enil)
      (H12 : forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0))
      (H13 : P1 eflnil)
      (H14 : forall (n : name) (e : expression.exp),
          (forall n' e', e = Lam_e n' e' ->  P e' -> forall e0 : efnlst, P1 e0 -> P1 (eflcons n e e0)) /\          
          (~ isLambda e -> P e -> forall e0 : efnlst, P1 e0 -> P1 (eflcons n e e0)))
      (H15 : P2 brnil_e)
      (H16 : forall (d : dcon) (p : N * list name) (e : expression.exp), P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)).

    Lemma exp_ind_alt2 : forall e, P e
    with exps_ind_alt2 : forall es, P0 es
    with efnlst_ind_alt2 : forall fns, P1 fns
    with branches_ind_alt2 : forall brs, P2 brs. 
    Proof.
      - intros. destruct e.
        + eapply H1.
        + eapply H2. eapply exp_ind_alt2.
        + eapply H3; eapply exp_ind_alt2.
        + eapply H4. eapply exps_ind_alt2.
        + eapply H5. eapply exp_ind_alt2. eapply branches_ind_alt2.
        + eapply H6; eapply exp_ind_alt2.
        + eapply H7. eapply efnlst_ind_alt2.
        + eapply H9.
        + eapply H10.
      - intros. destruct es.
        + eapply H11.
        + eapply H12. eapply exp_ind_alt2.
          eapply exps_ind_alt2.
      - intros. destruct fns.
        + eapply H13.
        + assert (Hdec : isLambda e \/ ~ isLambda e).
          { destruct e; eauto. now left. }      
          destruct Hdec.
          * destruct e; try contradiction.
            edestruct H14.
            eapply H0. reflexivity. 
            eapply exp_ind_alt2; eauto.
            eapply efnlst_ind_alt2.
          * edestruct H14.
            eapply H8. eassumption.
            eapply exp_ind_alt2; eauto.
            eapply efnlst_ind_alt2.
      - intros brs. destruct brs.
        + eapply H15.
        + eapply H16.
          eapply exp_ind_alt2.
          eapply branches_ind_alt2.
    Qed. 


    Lemma exp_ind_alt_2 :
      (forall e : expression.exp, P e) /\
      (forall e : exps, P0 e) /\
      (forall e : efnlst, P1 e) /\
      (forall b : branches_e, P2 b).
    Proof.
      repeat split.
      eapply exp_ind_alt2.
      eapply exps_ind_alt2.
      eapply efnlst_ind_alt2.
      eapply branches_ind_alt2.
    Qed.
    
  End IP.

  
  Lemma cps_cvt_sound :
    cps_cvt_exp_corresp /\
    cps_cvt_exps_corresp /\
    cps_cvt_efnlst_corresp /\
    cps_cvt_branches_corresp.
  Proof.
    eapply exp_ind_alt_2; intros; try inv Hwf.
    - (* Var_e *)
      unfold cps_cvt.
      destruct (nth_error vn (N.to_nat n)) eqn:Hnth.
      + eapply return_triple. intros _ w Hf.
        eexists. split.
        * econstructor. eassumption.
        * eassumption.
        (* * lia. *)
        (* * normalize_bound_var. sets. *)
        (* * constructor. *)
        (* * normalize_bound_var. sets. *)
      + eapply nth_error_Some in Hnth. now exfalso; eauto. lia.
    - (* Lam_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
 
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.

      intros f w2. simpl.
      eapply pre_curry_l; intros Hr'.
      eapply pre_curry_l; intros Hlt'.
      eapply pre_curry_l; intros Hf.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule. 
      eapply get_named_str_fresh.
      
      intros k1 w1. simpl.
      eapply pre_curry_l; intros Hr.
      eapply pre_curry_l; intros Hlt.
      eapply pre_curry_l; intros Hk1.


      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply H.
      
      simpl List.length.
      replace (N.of_nat (Datatypes.S (Datatypes.length vn))) with (1 + N.of_nat (Datatypes.length vn)) by lia.
      eassumption.
      
      intros e' w3. simpl. eapply return_triple.
      intros. destructAll.
      
      eexists. split.
      + inv_setminus. econstructor; eauto.
        now constructor; eauto.
        constructor; eauto. intros Hc; inv Hc; eauto; inv H14; now eauto.
      + eassumption. 
      (* + lia. *)
      (* + repeat normalize_bound_var. repeat normalize_sets.  *)
      (*   eapply Union_Included; [ | eapply Union_Included; [ eapply Union_Included | ] ]. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Included_trans. eassumption. eapply Range_Subset; lia. *)
      (* + constructor. now constructor. *)
      (*   constructor; eauto. *)
      (*   * intros Hc. eapply H6 in Hc. unfold In, Range in *. lia. *)
      (*   * intros Hc. inv Hc. *)
      (*   * repeat normalize_sets. *)
      (*     eapply Union_Disjoint_r. *)
      (*     eapply Disjoint_Singleton_r. *)
      (*     intros Hc. eapply H6 in Hc. unfold In, Range in *. lia. *)
      (*     eapply Disjoint_Singleton_r. *)
      (*     intros Hc. eapply H6 in Hc. unfold In, Range in *. lia. *)
      (*   * repeat normalize_bound_var. sets. *)
      (*   * repeat normalize_bound_var. sets. *)
      (*   * inv_setminus. intros Hc. inv Hc; eauto. inv H14; eauto. *)
      (*   * inv_setminus. constructor. *)
      (*     intros Hc; inv Hc; now eauto. *)
      (*     constructor; eauto. constructor. *)
      (*   * constructor.  *)
      (*   * repeat normalize_bound_var. sets. *)
      (* + inv_setminus. repeat normalize_bound_var. repeat normalize_occurs_free. simpl. *)
      (*   rewrite !FromList_cons, !FromList_nil at 1. *)
      (*   rewrite Setminus_Empty_set_abs_r. rewrite !Union_Empty_set_neut_r at 1. *)
      (*   eapply Union_Disjoint_r. now sets. *)
      (*   eapply Union_Disjoint_r. *)
      (*   eapply Union_Disjoint_l. now sets. *)
      (*   rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set. normalize_sets.  *)
      (*   eapply Union_Disjoint_r. *)
      (*   eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H14; eapply Hdis; eauto. *)
      (*   eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H14; eapply Hdis; eauto. *)
      (*   eapply Union_Disjoint_l; sets. *)
      (*   rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set. normalize_sets.  *)
      (*   eapply Disjoint_Included_r. eassumption. *)

      (*   assert (Hleq : (k < next_var (fst w))%positive). *)
      (*   { eapply POrderedType.Positive_as_DT.lt_nle. intros Hc. eapply Hfresh in Hc. *)
      (*     eapply Hdis; eauto. } *)
      (*   eapply Disjoint_Included_l. eapply Setminus_Included. *)
      (*   eapply Disjoint_Singleton_l. intros Hc. unfold In, Range in *. lia. *)

    - (* App_e *)
      unfold cps_cvt. 
      
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.
      
      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.
      
      eapply bind_triple.

      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.
      
      intros k2 w4. simpl.
      eapply pre_curry_l; intros Hr3.
      eapply pre_curry_l; intros Hlt3.
      eapply pre_curry_l; intros Hk2.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.
            
      intros x2 w5. simpl.
      eapply pre_curry_l; intros Hr4.
      eapply pre_curry_l; intros Hlt4.
      eapply pre_curry_l; intros Hk4.
      
      eapply bind_triple.

      
      eapply frame_rule. eapply frame_rule. eapply H. eassumption. 

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.      
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1. 
      eapply pre_curry_l; intros Hrel1.

      (* eapply pre_strenghtening. *)
      (* intros st s Hyp. destructAll. exact (conj (conj H6 H7) (conj H2 (conj H3 H1))). *)
      
      (* eapply pre_curry_l. intros [Hun Hdis']. *)
      
      eapply bind_triple.      
      
      (* eapply frame_rule. eapply frame_rule.  *)
      eapply H0 with (S := S1). eassumption.
      (* eapply Disjoint_Included_l. eapply cps_cvt_exp_subset. eassumption.  now sets. *)
      
      intros e2 w6. simpl. eapply return_triple.
      intros. destructAll.
      
      eexists. split.
      + econstructor; eauto.
      + eassumption.
      (* + lia. *)
      (* + rewrite !bound_var_Efun, !bound_var_fundefs_Fcons. *)
      (*   rewrite !bound_var_Efun, !bound_var_fundefs_Fcons, !bound_var_Eapp, !bound_var_fundefs_Fnil at 1. *)
      (*   repeat normalize_sets.  *)
      (*   eapply Union_Included. *)
      (*   eapply Union_Included; [ | eapply Union_Included; [ | eapply Union_Included; [ eapply Union_Included |  ] ] ]. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Singleton_Included. unfold In, Range in *. lia. *)
      (*   * eapply Included_trans. eassumption. eapply Range_Subset; lia. *)
      (*   * eapply Included_trans. eassumption. eapply Range_Subset; lia. *)
      (* + constructor; eauto. *)
      (*   constructor; eauto. *)
      (*   * intros Hc. eapply bound_var_Efun in Hc. *)
      (*     repeat normalize_bound_var_in_ctx. repeat normalize_sets. inv_setminus. *)
      (*     inv Hc; eauto. inv H20; eauto. inv H21; eauto. inv H21; eauto. *)
      (*     eapply H8 in H20. unfold In, Range in *. lia. *)
      (*   * intros Hc. inv Hc. *)
      (*   * repeat normalize_bound_var. repeat normalize_sets. inv_setminus. *)
      (*     eapply Union_Disjoint_l. eapply Union_Disjoint_l.           *)
      (*     eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto. *)
      (*     eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto. *)
      (*     eapply Disjoint_Singleton_r. *)
      (*     intros Hc. eapply H8 in Hc. unfold In, Range in *. lia. *)
      (*   * repeat normalize_bound_var. sets. *)
      (*   * rewrite bound_var_fundefs_Fnil. sets. *)
      (*   * inv_setminus. intros Hc. inv Hc; eauto. *)
      (*   * inv_setminus. constructor. *)
      (*     intros Hc; inv Hc; now eauto. *)
      (*     constructor; eauto. *)
      (*   * constructor; eauto. *)
      (*     constructor; eauto. *)
      (*     now intros Hc; inv Hc.  *)
      (*     now intros Hc; inv Hc.  *)
      (*     normalize_bound_var. now sets. *)
      (*     normalize_bound_var. now sets. *)
      (*     normalize_bound_var. now sets. *)
      (*     intros Hc. inv_setminus. inv Hc; eauto. *)
      (*     constructor. intros Hc. now inv Hc.  *)
      (*     now constructor. *)
      (*     now constructor. now constructor. *)
      (*     repeat normalize_bound_var. repeat normalize_sets. *)
      (*     eapply Disjoint_Included_l. eassumption. *)
      (*     eapply Union_Disjoint_r. eapply Disjoint_Singleton_r. *)
      (*     intros Hc. unfold In, Range in *. lia. *)
      (*     eapply Disjoint_Singleton_r. *)
      (*     intros Hc. unfold In, Range in *. lia. *)
      (*   * constructor. *)
      (*   * do 4 normalize_bound_var. rewrite !bound_var_fundefs_Fnil at 1. *)
      (*     repeat normalize_sets. *)
      (*     rewrite !Union_assoc. *)
      (*     eapply Union_Disjoint_r. *)
      (*     -- eapply Disjoint_Included_l. eassumption. *)
      (*        repeat eapply Union_Disjoint_r. *)
      (*        eapply Disjoint_Singleton_r. intros Hc; unfold In, Range in *. lia. *)
      (*        eapply Disjoint_Singleton_r. intros Hc; unfold In, Range in *. lia. *)
      (*        eapply Disjoint_Singleton_r. intros Hc; unfold In, Range in *. lia. *)
      (*        eapply Disjoint_Singleton_r. intros Hc; unfold In, Range in *. lia. *)
      (*     -- eapply Disjoint_Included. eassumption. eassumption. *)
      (*        eapply Disjoint_Range. lia. *)

      (* + do 5 normalize_bound_var. rewrite !bound_var_fundefs_Fnil at 1. *)
      (*   do 5 normalize_occurs_free. rewrite !occurs_free_fundefs_Fnil at 1. *)
      (*   simpl. *)
      (*   rewrite !FromList_cons, !FromList_nil, !Union_Empty_set_neut_r at 1. *)
      (*   repeat normalize_sets.  *)

      (*   eapply Union_Disjoint_r. *)
      (*   eapply Union_Disjoint_r. now sets. *)
      (*   eapply Union_Disjoint_r. *)
      (*   eapply Union_Disjoint_l. now sets. *)
      (*   admit. *)
      (*   eapply Union_Disjoint_r. *)
      (*   eapply Union_Disjoint_r. *)
      (*   eapply Union_Disjoint_l. now sets. *)
      (*   admit. *)
    - (* Con_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.

      intros k1 w1. simpl.
      eapply pre_curry_l; intros Hinx.
      eapply pre_curry_l; intros Hr.
      eapply pre_curry_l; intros Hk.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule.
      eapply get_named_str_lst_spec.

      intros xs w2. simpl.
      eapply pre_curry_l; intros Hink.
      eapply pre_curry_l; intros Hlt'.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.
      

      eapply bind_triple.
      eapply frame_rule. eapply frame_rule.

      eapply get_named_str_lst_spec.

      intros xs' w3. simpl.
      eapply pre_curry_l; intros Hsub'.
      eapply pre_curry_l; intros Hlt''.
      eapply pre_curry_l; intros Hnd'.
      eapply pre_curry_l; intros Hlen'.
      eapply pre_curry_l; intros Hsub''.

      eapply bind_triple.
      eapply frame_rule. eapply frame_rule.
      
      eapply H. eassumption.

      rewrite map_length in *. rewrite Hlen'. 
      { clear. induction e; simpl. congruence.
        rewrite IHe.  
        destruct (exps_length e0). lia.
        destruct p; lia. }
      
      
      intros e' w4. simpl. 

      eapply return_triple. intros. destructAll.
      
      eexists. split; eauto. econstructor; eauto.
      
      rewrite Hlen. rewrite map_length.

      clear. induction e; eauto. simpl. destruct (exps_length e0); simpl; try lia. 
      destruct p; lia.

    - (* Match_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.

      intros k1 w1. simpl.
      eapply pre_curry_l; intros Hinx.
      eapply pre_curry_l; intros Hr.
      eapply pre_curry_l; intros Hk.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply H. eassumption.

      intros e' w2. simpl.

      eapply pre_curry_l; intros Hink.
      eapply pre_curry_l; intros Hlt'.

      eapply pre_existential. intros S1.      
      eapply pre_curry_l; intros Hrel.

      eapply bind_triple.

      eapply H0. eassumption.

      intros Ps w3. simpl. 

      eapply return_triple. intros. destructAll.

      eexists. split; eauto. econstructor; eauto.

    - (* Let_e *)
      unfold cps_cvt. 
      
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.
      
      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.
      
      eapply bind_triple.

      eapply frame_rule. eapply frame_rule. 
      eapply H0. 

      replace (N.of_nat (Datatypes.length (x :: vn))) with (1 + N.of_nat (Datatypes.length vn)).
      2:{ simpl Datatypes.length. lia. } 
      eassumption.     

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.      
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1. 
      eapply pre_curry_l; intros Hrel1.
      
      eapply bind_triple.      
      
      eapply H with (S := S1). eassumption.
      intros e2 w6. simpl. eapply return_triple.
      intros. destructAll.
      
      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* Fix_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_lst_spec.  
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.

      assert (Hlen' : N.of_nat (Datatypes.length (efnlst_as_list e)) = efnlst_length e).
      { clear. induction e. simpl. lia.
        simpl Datatypes.length; simpl efnlst_length. 
        simpl. destruct (efnlst_length e0); simpl; try lia. destruct p; lia. }

      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 

      eapply H. rewrite app_length, rev_length. unfold fnames in Hlen.
      rewrite map_length in Hlen. rewrite Hlen. 
      
      rewrite Nnat.Nat2N.inj_add. rewrite Hlen'. eassumption.
      rewrite Hlen. unfold fnames. rewrite map_length.
      rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).
      rewrite <- Nnat.Nat2N.id with (n := efnlength e).
      rewrite Hlen', efnlength_efnlst_length. reflexivity.

      intros B w1. simpl.
      
      destruct (nth_error x (N.to_nat n)) eqn:Hnth.
      + eapply return_triple. intros _ w3 Hf. destructAll. 
        eexists. split.
        * econstructor; eauto. rewrite Hlen. unfold fnames. rewrite map_length.
          rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).
          rewrite <- Nnat.Nat2N.id with (n := efnlength e).
          rewrite Hlen'. rewrite efnlength_efnlst_length. reflexivity.

        * eassumption.

      + eapply nth_error_Some in Hnth. now exfalso; eauto.
        rewrite Hlen. unfold fnames. rewrite map_length. 
        rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).          
        rewrite Hlen'. lia.

    - (* Prf_e *)
      unfold cps_cvt. 
      
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply return_triple.
      intros. destructAll.
      
      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* enil *)

      eapply return_triple. intros. eexists. split; [ | eassumption ].
      destruct xs; simpl in *; try congruence. constructor. 

    - (* econs *)
      destruct xs.
      { inv Hlen. destruct (exps_length e0). lia. destruct p; lia. } 
      
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply H. eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.      
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1. 
      eapply pre_curry_l; intros Hrel1.
      
      eapply bind_triple.
      eapply H0. eassumption.

      simpl in Hlen. destruct (exps_length e0). lia. destruct p; lia.

      intros e2 w4. eapply return_triple. intros. destructAll. 
      
      eexists. split.
      + econstructor; eauto.
      + eassumption.
      
    - (* efnil *) 
      eapply return_triple. intros. destruct xs; [ | simpl in *; congruence ].
      eexists. split. now constructor. eassumption.
      
    - (* efcons *) split; intros.
      2:{ inv Hwf. exfalso; eauto. }
      inv Hwf. 

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh. 
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply get_named_spec.
      
      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.
      
      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 
      eapply H0.
      inv H6.

      replace (N.of_nat (Datatypes.length (x :: vn))) with (1 + N.of_nat (Datatypes.length vn)).
      2:{ simpl Datatypes.length. lia. }
      eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.      
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1. 
      eapply pre_curry_l; intros Hrel1.

      destruct xs. simpl in Hlen. congruence.
      eapply bind_triple.
      eapply H1. eassumption.
      
      simpl in *. congruence.

      intros B w4. eapply return_triple. intros. destructAll. 
      
      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* brnil_e *)
      
      eapply return_triple. intros. eexists. split.
      now constructor. eassumption.

    - (* brcons_e *)
      destruct p. eapply bind_triple. eapply pre_post_copy.

      eapply H0. eassumption.

      intros e1 w1. simpl.
      eapply pre_curry_l; intros Hr2.      
      eapply pre_existential. intros S1. 
      eapply pre_curry_l; intros Hrel1.
      
      eapply bind_triple.
      
      eapply get_named_lst_spec.  
      intros xs w2. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.

      eapply bind_triple.
      
      eapply frame_rule. eapply frame_rule. 

      eapply H. simpl in *.
      rewrite app_length. rewrite Hnd, names_lst_length.
      rewrite Nnat.Nat2N.inj_add. rewrite Nnat.N2Nat.id. eassumption.

      intros e2 w3. eapply return_triple. intros. destructAll.  
      
      eexists. split.
      + econstructor; [ | | | | | eassumption | eassumption ]; eauto.
        rewrite Hnd. rewrite names_lst_length. reflexivity.
        rewrite Hnd. rewrite names_lst_length. reflexivity.
      + eassumption.
  Qed. 

  Lemma set_lists_Forall2 {A} xs (vs : list A) rho rho' :
    set_lists xs vs rho = Some rho' ->
    NoDup xs ->
    Forall2 (fun x v => M.get x rho' = Some v) xs vs.
  Proof.
    revert vs rho rho'; induction xs; intros ys rho rho' Hset Hnd;
      destruct ys; simpl in *; try congruence.
    - constructor.
    - destruct (set_lists xs ys rho) eqn:Hset'; try congruence.
      inv Hset.
      constructor.
      rewrite M.gss. reflexivity.
      eapply Forall2_monotonic_strong.
      2:{ eapply IHxs; eauto. inv Hnd. eassumption. }

      intros. rewrite M.gso. eassumption.
      intros Heq; subst.
      inv Hnd; eauto.
  Qed.
      


  Fixpoint pos_seq (start : var) (n : nat) : list positive :=
    match n with
    | 0%nat => []
    | S n =>
      start :: (pos_seq (start + 1)%positive n)
    end.

  Lemma pos_seq_len start n :
    List.length (pos_seq start n) = n.
  Proof.
    revert start. induction n; intros start.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  (* Lemma pos_seq_In start n : *)
  (*   Disjoint _ (FromList (pos_seq start n)) (fun x => (start + Pos.of_nat n <= x)%positive). *)
  (* Proof. *)
  (*   revert start. induction n; intros start. *)
  (*   - simpl. normalize_sets. sets. *)
  (*   - simpl. normalize_sets. *)
  (*     eapply Union_Disjoint_l. *)
  (*     + eapply Disjoint_Singleton_l. *)
  (*       intros Hc. unfold In in *. *)
  (*       destruct n; lia. *)
  (*     + eapply Disjoint_Included_r; [ | eapply IHn ]. *)
  (*       intros y. unfold In. simpl. *)
  (*       destruct n. lia.  *)
        
  (*   intros start Hin. *)
  (*   - inv Hin. *)
  (*   - inv Hin. *)
  (*     + lia. *)
  (*     + eapply IHn in H. *)
  (*       split. lia. *)
  (*       simpl in *. destruct n; try lia. *)
  (*       simpl lia.  *)
  (*     reflexivity. *)
  (*   - simpl. rewrite IHn. reflexivity. *)
  (* Qed. *)


  Lemma pos_seq_In start n x :
    List.In x (pos_seq start n) ->
    (start <= x <= Pos.of_nat (Pos.to_nat start + n)%nat)%positive.
  Proof.
    revert start. induction n; intros start Hin.
    - inv Hin.
    - inv Hin.
      + lia.
      + eapply IHn in H.
        split. lia. lia.
  Qed.

  Lemma pos_seq_NoDup start n :
    NoDup (pos_seq start n).
  Proof.
    revert start; induction n; intros start.
    - now constructor.
    - simpl. constructor; eauto.
      intros Hc. eapply pos_seq_In in Hc. lia.
  Qed.
    

  Lemma cps_fix_rel_exists m efns ctrs fnames names fnames' : 
    efnlst_wf (N.of_nat (List.length (fnames ++ names))) efns ->
    Disjoint _ (fun x => (m <= x)%positive) (FromList fnames :|: FromList names) ->
    List.length fnames' = N.to_nat (efnlst_length efns) ->
    exists B S3,
      cps_fix_rel ctrs func_tag kon_tag default_tag fnames names (fun x => (m <= x)%positive) fnames' efns B S3. 
  Proof.
    revert m ctrs fnames names fnames'.
    induction efns; intros m ctrs fnames names fnames'; intros Hwf Hdis Hlen.

    - do 2 eexists.
      destruct fnames'; simpl in *; try congruence.
      econstructor.

    - destruct fnames'. simpl in Hlen. destruct (efnlst_length efns); lia.

      assert (Heq : N.to_nat (efnlst_length (eflcons n e efns)) = (1 + N.to_nat (efnlst_length efns))%nat).
      { simpl. destruct (efnlst_length efns). lia. destruct p; lia. }

      rewrite Heq in *. clear Heq. simpl in *. inv Hlen.
      inv Hwf.

      set (k := (1 + m)%positive).
      set (y := (1 + k)%positive).      
      set (next_id := (1 + y)%positive).

      
      set (comp_d := pack_data next_id
                               1%positive 1%positive 1%positive
                               (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

      set (S := fun x => (next_id <= x)%positive).

      assert (Hf : fresh S next_id).
      { unfold S, next_id, fresh, In. lia. }

      destruct e; inv H5. 

      destruct cps_cvt_sound as (Hexp & _).
      
      edestruct (runState (cps_cvt prim_map func_tag kon_tag default_tag e (y :: (rev fnames ++ names)) k ctrs) tt (comp_d, tt)) eqn:Hcvt.

      inv H4.
      assert (Hwf : exp_wf (N.of_nat (Datatypes.length (y :: (rev fnames ++ names)))) e).
      { simpl. rewrite app_length in *. rewrite rev_length.
        replace (N.pos (Pos.of_succ_nat (Datatypes.length fnames + Datatypes.length names)))
          with (1 + N.of_nat (Datatypes.length fnames + Datatypes.length names)) by lia.
        eassumption. }

      unfold cps_cvt_efnlst_corresp, triple in Hexp.
      specialize (Hexp e S (y :: (rev fnames ++ names)) k ctrs Hwf tt (comp_d, tt) Hf).
      rewrite Hcvt in Hexp.
      destruct e0; try contradiction. destructAll.

      edestruct IHefns with (m := (next_var (fst p))). eassumption.
      eapply Disjoint_Included_l; [ | eassumption ].
      intros z. unfold In.
      intros Hc. eapply H1 in Hc. unfold In in *.
      eapply cps_cvt_exp_subset in Hc; [ | eassumption ].
      unfold S, In, next_id in *. lia.
      eassumption. destructAll.
      
      
      do 2 eexists. econstructor; [ | | | | | eassumption | eassumption  ].
      + eassumption.
      + unfold In, y. lia.
      + constructor.
        unfold In, x2. lia.
        intros Hc. inv Hc. lia.
      + unfold S. intros z. unfold In. intros Hleq.
        constructor. constructor. 
        unfold In. lia.
        intros Hc. inv Hc. lia.
        intros Hc. inv Hc. lia.
      + intros z Hc. eapply H1 in Hc. eassumption.
  Qed.      
    
    
  
  Lemma cps_val_rel_exists v ctrs :
    well_formed_val v ->
    exists v', cps_val_rel ctrs func_tag kon_tag default_tag v v'. 
  Proof.
    induction v using value_ind'; intros Hwf; inv Hwf.
    
    - (* Con_v *)
      induction vs. 
      + eexists. constructor. constructor. reflexivity.
      + inv H. inv H1.
        edestruct IHvs; eauto. edestruct H3; eauto.
        inv H.
        eexists. constructor. econstructor. eassumption. eassumption. reflexivity.
        
    - (* Prf_v *)
      eexists. constructor; eauto.
      
    - (* Clos_v *)

      set (k := 1%positive).
      set (f := 2%positive).
      set (x := 3%positive).
      set (names := pos_seq 4%positive (List.length vs)).
      
      assert (Hvs : exists vs', Forall2 (cps_val_rel ctrs func_tag kon_tag default_tag) vs vs').
      { revert H H2. clear. intros. induction vs.
        + eexists. constructor.
        + inv H2. inv H.
          edestruct IHvs; eauto. edestruct H2; eauto. }

      destruct Hvs as [vs' Hvs].
      
      edestruct (@set_lists_length3 val) with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.

      assert (Henv: cps_env_rel' (cps_val_rel ctrs func_tag kon_tag default_tag) names vs rho). 
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. } 
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 4%positive (Datatypes.length vs)) as ns.
        revert vs' rho. 
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.        
        now eauto. 
        eapply IHvs; eauto. }

      destruct cps_cvt_sound as (Hexp & _).

      specialize (H4 Prf_v). 

      assert (Hwf : exp_wf (N.of_nat (Datatypes.length (x :: names))) e).
      { unfold well_formed_in_env in *. simpl in *.
        unfold names. rewrite pos_seq_len. eassumption. }

      set (next_id := (Pos.of_nat (Pos.to_nat 4%positive + (List.length vs))%nat + 1)%positive).
      
      set (comp_d := pack_data next_id
                               1%positive 1%positive 1%positive
                               (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

      set (S := fun x => (next_id <= x)%positive).

      assert (Hf : fresh S next_id).
      { unfold S, next_id, fresh, In. lia. }
      
      edestruct (runState (cps_cvt prim_map func_tag kon_tag default_tag e (x :: names) k ctrs) tt (comp_d, tt)) eqn:Hcvt.

      unfold cps_cvt_exp_corresp, triple in Hexp.
      specialize (Hexp e S (x :: names) k ctrs Hwf tt (comp_d, tt) Hf).
      rewrite Hcvt in Hexp.
      destruct e0; try contradiction. destructAll.
      
      eexists. eapply rel_Clos with (f := f); [ eassumption | | | | | | eassumption ].
      + eapply pos_seq_NoDup.
      + unfold S, next_id. constructor. intros z Hc.
        inv Hc. unfold In in *.
        inv H5. inv H7. lia.
        inv H7. inv H5. lia.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        inv Hx. inv H5. inv H6. inv H6.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        inv Hx. inv H5.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        eapply pos_seq_In in Hx. lia.
        
    - (* ClosFix_v *)

      set (names := pos_seq 1%positive (List.length vs)).
      set (fnames := pos_seq (Pos.of_nat (List.length vs + 2)) (N.to_nat (efnlst_length fnl))).
      set (next_id := (Pos.of_nat (N.to_nat (efnlst_length fnl) + (List.length vs) + 3)%nat)%positive).
      
      assert (Hvs : exists vs', Forall2 (cps_val_rel ctrs func_tag kon_tag default_tag) vs vs').
      { revert H H3. clear. intros. induction vs.
        + eexists. constructor.
        + inv H3. inv H.
          edestruct IHvs; eauto. edestruct H3; eauto. }
      
      destruct Hvs as [vs' Hvs].
      
      edestruct (@set_lists_length3 val) with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.
      
      assert (Henv: cps_env_rel' (cps_val_rel ctrs func_tag kon_tag default_tag) names vs rho). 
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. } 
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 1%positive (Datatypes.length vs)) as ns.
        revert vs' rho. 
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.        
        now eauto. 
        eapply IHvs; eauto. }


      assert (Hlen : efnlst_length fnl = N.of_nat (List.length fnames)).
      { unfold fnames. rewrite pos_seq_len. lia. }
      
      assert (Hwf : efnlst_wf (N.of_nat (Datatypes.length (fnames ++ names))) fnl).
      { revert H5. rewrite app_length, Nnat.Nat2N.inj_add, Hlen.
        unfold names. rewrite pos_seq_len. generalize (N.of_nat (Datatypes.length fnames) + N.of_nat (Datatypes.length vs)).
        clear. induction fnl; intros m Hall.
        - constructor.
        - inv Hall. destructAll. constructor; eauto. } 


      edestruct cps_fix_rel_exists with (fnames' := fnames) (m := next_id).

      eassumption. 

      { eapply Union_Disjoint_r. 
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. inv H2. lia.
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. lia. }

      unfold fnames. rewrite pos_seq_len. reflexivity.

      destructAll.


      edestruct (nth_error fnames (N.to_nat n)) eqn:Hnth.
      2:{ eapply nth_error_Some in Hnth. contradiction.
          unfold fnames. rewrite pos_seq_len. lia. }
      
      eexists. econstructor; [ eassumption  | | | | | | eassumption ].

      + eapply pos_seq_NoDup.

      + eapply pos_seq_NoDup.

      + unfold next_id. constructor. intros z Hc.
        inv Hc. unfold In in *. inv H2.
        eapply pos_seq_In in H7. lia.
        eapply pos_seq_In in H7. lia.

      + constructor. intros z Hc.
        inv Hc.  eapply pos_seq_In in H2.
        eapply pos_seq_In in H6. lia.

      + eassumption.

  Qed. 


End Corresp. 

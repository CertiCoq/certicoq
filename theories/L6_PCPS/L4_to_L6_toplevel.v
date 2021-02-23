From Coq Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import L4.expression L4.fuel_sem.

Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        tactics L4_to_L6 L4_to_L6_util L4_to_L6_corresp L4_to_L6_correct
        L6.tactics identifiers bounds cps_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


Section Refinement.

  Context (cnstrs : conId_map)
          (dtag : positive) (* default tag *)
          (cenv : ctor_env).

  Fixpoint value_ref' (v1 : value) (v2 : val) : Prop:=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          value_ref' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2_aux vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.


  Definition value_ref (v1 : value) (v2 : val) : Prop:=
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2 value_ref' vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.

  Lemma value_ref_eq v1 v2 :
    value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    induction v1; try easy.

    destruct v2; simpl; try easy.

    
    revert l0. induction l; intros l'.

    - split; intros [H1 H2]. split; eauto; destruct l'; eauto.
      inv H2. split; eauto.

    - split; intros [H1 H2].
      
      + split; eauto; destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.

      + split; eauto. destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.
  Qed.

  Definition diverge (v : list value) (e : expression.exp) :=
    forall (c1 : nat), eval_env_fuel v e fuel_sem.OOT c1.
  
  
  Program Definition refines (e1 : expression.exp) (e2 : cps.exp) := 
    (* Termination *)
    (forall (v1 : value) (c1 : nat),
        eval_env_fuel [] e1 (Val v1) c1 ->
        exists (v2 : val) (c2 : nat),
          bstep_fuel cenv (M.empty _) e2 c2 (Res v2) tt /\
          value_ref v1 v2) /\
    (* Divergence *)    
    (diverge [] e1 -> eval.diverge cenv (M.empty _) e2).

  Context (prim_map : M.t (kername * string (* C definition *) * nat (* arity *))). 
  Context (func_tag kon_tag default_itag : positive)
          (next_id : positive).
  Context (dcon_to_tag_inj :
             forall (tgm : conId_map) (dc dc' : dcon),
               dcon_to_tag dtag dc tgm = dcon_to_tag dtag dc' tgm -> dc = dc'). 
  
  Definition cps_rel_top (e : expression.exp) (xs : list var)
             (k : var) (e' : cps.exp) :=
    let S := fun x => (max_list xs k + 1 <= x)%positive in
    exists S', cps_cvt_rel func_tag kon_tag dtag S e xs k cnstrs S' e'.


  Lemma cps_val_comp k v1 v2 v3 : 
    cps_val_rel func_tag kon_tag dtag cnstrs v1 v2 ->
    preord_val cenv eq_fuel k v2 v3 ->
    value_ref v1 v3. 
  Proof.
    revert v2 v3.
    induction v1 using value_ind'; intros v2 v3 Hval Hll; inv Hval.
    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction. inv Hll.
      simpl. split. reflexivity.

      revert l vs' H2 H1.
      induction H.

      + intros. inv H2. inv H1. constructor.

      + intros. inv H2. inv H1. constructor; eauto.
        eapply value_ref_eq. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.
  Qed. 


  Theorem cps_corrrect_top e k x (Hneq : x <> k):
    exp_wf 0%N e ->
    exists e',
      cps_rel_top e [] k e' /\
      refines e (Efun (Fcons k kon_tag [x] (Ehalt x) Fnil) e').
  Proof.
    intros Hwf.
    edestruct cps_rel_exists with (xs := @nil var).
    eassumption.
    eassumption.

    destructAll.
    eexists. split.
    eexists. eassumption.
    

    split.

    - intro; intros.
      edestruct cps_cvt_correct
        with (rho := M.set k
                           (Vfun (M.empty _) (Fcons k kon_tag [x] (Ehalt x) Fnil) k)
                           (M.empty _)) (x := x); try eassumption.
      + now constructor.
      + simpl. eassumption.
      + repeat normalize_sets.
        eapply Disjoint_Singleton_l. simpl.
        intros Hin. unfold In in *. lia.
      + repeat normalize_sets. intros Hc. inv Hc.
        eauto.
      + intros Hc. inv Hc. 
      + constructor.
      + rewrite M.gss. reflexivity.
      + clear H2.

        edestruct cps_val_rel_exists as [v2 Hval]. eassumption.
        eapply eval_env_step_preserves_wf. eassumption. reflexivity. constructor.
        eassumption.
        
        specialize (H1 v1 v2 eq_refl Hval).

        edestruct H1. reflexivity.

        econstructor 2. econstructor.
        rewrite M.gso. rewrite M.gss. reflexivity.
        now eauto.
        simpl. rewrite M.gss. reflexivity.
        simpl. rewrite Coqlib.peq_true. reflexivity.
        simpl. reflexivity.
        
        econstructor 2. econstructor. rewrite M.gss. reflexivity.
        
        destructAll. destruct x2. contradiction.
        
        destruct x4.

        do 2 eexists. split.

        replace tt with (tt <+> tt) by reflexivity.
        econstructor 2. 
        econstructor. simpl. eassumption.

        simpl in *. eapply cps_val_comp. eassumption. eassumption.

    - 

        ines .eassumption. 
      exact (M.empty _).
      
    edestruct 

    
    . 
    cps_exp_rel_exists
    edestruct (cps_fix_rel_exists (max_list xs k + 1) 
    
well_formed_env vs ->
exp_wf (N.of_nat (Datatypes.length vnames))
  e ->
Disjoint var (k |: FromList vnames) S ->
~ In var (k |: FromList vnames) x ->
~ In var (FromList vnames) k ->
cps_env_rel func_tag kon_tag default_tag
  cnstrs vnames vs rho ->
rho ! k = Some vk ->
cps_cvt_rel func_tag kon_tag default_tag S
  e vnames k cnstrs S' e' ->
(forall (v : value) (v' : val),
 r = Val v ->
 cps_val_rel func_tag kon_tag default_tag
   cnstrs v v' ->
 preord_exp cenv (cps_bound f) eq_fuel i
   (Eapp k kon_tag [x],
   M.set x v' (M.set k vk (M.empty val)))
   (e', rho)) /\
(r = fuel_sem.OOT ->

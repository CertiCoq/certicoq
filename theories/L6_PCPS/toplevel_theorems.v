
Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.

Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx L6.set_util
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.relations L6.rel_comp
        L6.uncurry L6.bounds
        L6.closure_conversion L6.closure_conversion_util L6.hoisting.
Require Export L6.logical_relations L6.logical_relations_cc L6.alpha_conv L6.inline_letapp L6.inline L6.inline_correct.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.


(* TODO use John's definition once merged *)

Definition well_scoped e :=
  unique_bindings e /\ Disjoint _ (bound_var e) (occurs_free e).

Definition wf_pres e1 e2 :=
  (well_scoped e1 -> well_scoped e2) /\
  occurs_free e2 \subset occurs_free e1.

Definition PostT := @PostT nat (nat * nat).
Definition PostGT := @PostGT nat (nat * nat).

  
Context (cenv : ctor_env) (ctag : ctor_tag).

Definition post_prop P1 PG :=
  Post_properties cenv P1 P1 PG /\
  post_upper_bound P1.  

Section Inline.

 Lemma inline_correct St IH e d st c :
   well_scoped e ->
   max_var e 1 < state.next_var c ->
   exists (e' : exp) (c' : state.comp_data),
     beta_contract_top St IH e d st c true = (compM.Ret e', c') /\
     wf_pres e e' /\
     max_var e' 1 < state.next_var c' /\
     (forall (k : nat) (rho1 rho2 : env),
         preord_env_P cenv (inline_bound d d) (occurs_free e) k rho1 rho2 ->
         preord_exp cenv (inline_bound_top d) (inline_bound d d) k (e, rho1) (e', rho2)).
 Proof.
   intros.
   edestruct inline_correct_top with (P1 := fun L => inline_bound L d)
                                     (PG := inline_bound d d).
   
   - intros. eapply inline_bound_compat. eassumption.
   - intros. eapply inline_bound_post_Eapp_l.
   - intros. eapply inline_bound_remove_steps_letapp.
   - intros. rewrite plus_comm. eapply inline_bound_remove_steps_letapp_OOT. 
   - reflexivity.
   - eapply inline_bound_top_impl.
   - eapply H.
   - eapply H.
   - eassumption.
   - destructAll. do 2 eexists. split. eassumption.
     split.
     split. intros. split. eassumption. eassumption. eassumption.
     split. eassumption. eassumption.
 Qed.

End Inline.

Section CCHoist.

  Context (clo_tag : ctor_tag).
  
  Lemma closure_conversion_hoist_correct e c :
   well_scoped e ->
   max_var e 1 < state.next_var c ->
   exists (e' : exp) (c' : state.comp_data),
     closure_conversion_hoist clo_tag e c = (compM.Ret e', c') /\
     R_n_exp cenv clo_tag wf_pres post_prop (simple_bound 0) (simple_bound 0) 0%nat 1%nat e e' /\
     max_var e' 1 < state.next_var c'.
  Proof.
    intros Hws Hmvar.
    edestruct closure_conversion_correct.exp_closure_conv_correct
      with (boundL := simple_bound) (boundG := simple_bound 0).
    (* CC bounds *)
    - eapply simple_bound_compat.
    - eapply Hpost_locals_r.
    - eapply Hpost_locals_l.
    - eapply Hpost_locals_l0.
    - eapply HOOT.
    - eapply HPost_letapp_cc.
    - eapply HPost_letapp_OOT_cc.
    - eapply bounds.HPost_app.
    - eapply Hbase.
    (* scoping *)
    - eapply Hws.
    - eapply Hws.
    - eassumption.
    - destructAll.

      edestruct (exp_hoist x) as [e' m] eqn:Hhoist. 
      
      edestruct exp_hoist_correct_top with
          (e := x)
          (P1 := fun n =>  hoisting_bound n m)
          (P2 := hoisting_bound_top m)
          (PG := hoisting_bound m m).

      (* Hoisting bounds *)
      + intros. eapply hoisting_bound_compat. eassumption.
      + intros. eapply hoisting_bound_mon. eassumption.
      + intros. eapply hoisting_bound_post_Efun_l.
      + intros. eapply hoisting_bound_post_Efun_r. eassumption.
      + admit. (* easy *)
      + intros. eapply hoisting_boound_top_incl. easy.
      + reflexivity.
      (* scoping *)
      + easy.
      + eapply Disjoint_sym. eassumption. 
      + eassumption.
      + eassumption.
      + destructAll. do 2 eexists. split; [| split ].
        * unfold closure_conversion_hoist. rewrite H. rewrite Hhoist. simpl. reflexivity.
        * eexists. split.
          

          admit.
        * eapply Pos.lt_trans; [| eassumption ]. 

        e
  forall n G : nat,
  (n <= G)%nat -> inclusion
    

(* Section Uncurry. *)

(*   boun *)
  
(*   Lemma uncurry_fuel_correct cps n e c :  *)
(*     uncurry_fuel cps n e st =  -> *)
(*     forall rho rho1, *)
(*       preord_env_P cenv PostG (occurs_free e) k rho rho1 -> *)
(*       preord_exp cenv Post PostG k (e, rho) (e1, rho1). *)

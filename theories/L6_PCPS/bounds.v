Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles Coq.micromega.Lia.

Require Import L6.cps L6.eval L6.Ensembles_util L6.List_util L6.tactics L6.set_util
        L6.logical_relations L6.logical_relations_cc L6.algebra L6.inline_letapp.
Require Import micromega.Lia.

Import ListNotations.

Open Scope alg_scope. 


Section Bounds.
  

  (* ***** Fuel ***** *)
  
  Program Instance fuel_res_pre : @resource fin nat :=
    { zero := 0;
      one_i fin := 1;
      plus x y  := x + y; }.
  Solve Obligations with (simpl; lia).


  Program Instance fuel_res_ordered : @ordered fin nat fuel_res_pre :=
    { lt := Peano.lt }.
  Solve Obligations with (intro; intros; simpl; lia).
  Solve Obligations with (simpl; lia).
  Next Obligation.
    destruct (lt_dec x y); auto. right. eexists (x - y). lia.
  Qed.
  
  Program Instance fuel_res_ones : @resource_ones fin nat fuel_res_pre. 

  Program Instance fuel_res_hom : @nat_hom fin nat fuel_res_pre :=
    { to_nat y := y }.

  Program Instance fuel_res_exp : @exp_resource nat :=
    { HRes := fuel_res_pre }.
  
  Instance fuel_res : @fuel_resource nat.
  Proof.
    econstructor.
    eapply fuel_res_ordered.
    eapply fuel_res_ones.
    eapply fuel_res_hom.
  Defined.


  (* ***** Trace ***** *)

  
  Program Instance trace_res_pre : @resource fin (nat * nat) :=
    { zero := (0, 0);
      one_i fin :=
        match fin with
        | Four => (0, 1)
        | Six => (0, 1)
        | _ => (1, 0)
        end;
      plus x y := (fst x + fst y, snd x + snd y) }.
  Solve Obligations with (simpl; lia).
  Solve Obligations with (split; congruence).
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.  

  Program Instance trace_res_exp : @exp_resource (nat * nat) :=
    { HRes := trace_res_pre }.
  
  Instance trace_res : @trace_resource (nat * nat).
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.


  Section Inline_bound. 

    (* bound for inlining *)
    Definition inline_bound (L G : nat) : PostT := 
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + 2 * G * tapp1 + 2 * L /\
        tapp1 <= tapp2 + 2 * G * tapp2 + L /\
        t2 + tapp2 = c2. 

    Context (cenv : ctor_env).

    Ltac unfold_all :=
      try unfold zero in *;
      try unfold one_ctx in *;
      try unfold one in *;
      try unfold one_i in *;
      try unfold HRes in *;
      try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
      try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

    Instance inline_bound_compat L G (Hi : L <= G) (Hg : G > 0):
      Post_properties cenv (inline_bound L G) (inline_bound L G) (inline_bound G G). 
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold inline_bound in *; unfold_all; simpl; split; [| split ]; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold inline_bound in *; unfold_all; simpl. destructAll. split. lia. split; lia.

      - intro; intros. intro; intros. 
        unfold inline_bound in *; unfold_all; simpl.
        assert (c = 0). eapply Nat.lt_1_r. eassumption. subst. lia.
      - intro; intros. unfold post_base'. 
        unfold inline_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold inline_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. split; [| split ]; lia.
    Qed. 
    
    Lemma inline_bound_post_Eapp_l i G v t l rho1 x rho2 :
      post_Eapp_l (inline_bound i G) (inline_bound (S i) G) v t l rho1 x rho2.
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *. destructAll. 
      split; [| split ]; try lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp_OOT i j G : 
      remove_steps_letapp_OOT cenv (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *.
      split; [| split ]; lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp i j G : 
      remove_steps_letapp cenv (inline_bound i G) (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all; simpl in *.
      destruct cout1; destruct cout2. destruct cout1'; destruct cout2'. simpl in *. lia. 
    Qed.    


    (* This allows us to prove divergence preservation *)  
    Lemma inline_bound_post_upper_bound L G :
      post_upper_bound (inline_bound L G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all.
      eexists (fun x => (1 + 2 * G + 2 * G * 2 * G) * x + 2 * L * 2 * G + 2 * L).
      intros. 
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].

      destruct H. destruct H0.
      assert (Hleq : tapp1 <= cin2 + 2 * G * cin2 + L) by lia. clear H0 H1.
      
      assert (Hleq' : (1 + 2 * G + 2 * G * 2 * G) * cin1 + 2 * L * 2 * G + 2 * L <=
                      (1 + 2 * G + 2 * G * 2 * G) * cin2 + 2 * L * 2 * G + 2 * L).
      { eapply le_trans. eassumption. eapply le_trans.
        eapply plus_le_compat_r. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
        lia. } 
      
      assert (Hleq'' : cin1 <= cin2).
      { eapply Nat.add_le_mono_r in Hleq'. eapply Nat.add_le_mono_r in Hleq'.
        eapply NPeano.Nat.mul_le_mono_pos_l in Hleq'. eassumption. lia. }

      eexists (cin2 - cin1). simpl. lia.
    Qed.

    (* bound for inlining, toplevel *)
    Definition inline_bound_top (L G : nat) : @PostT nat (nat * nat) := 
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= G * c2 + L.

    Lemma inline_bound_top_impl (G L : nat) :
      inclusion _ (inline_bound L G)
                (inline_bound_top (2 * L * 2 * G + 2 * L) (1 + 2 * G + 2 * G * 2 * G)).
    Proof.
      intros [[[? ?] ?] [? ?]] [[[? ?] ?] [? ?]]. unfold inline_bound, inline_bound_top in *. unfold_all.
      intros. destructAll.
      rewrite !NPeano.Nat.mul_add_distr_l in *. 
      rewrite !NPeano.Nat.mul_add_distr_r in *. 
      eapply le_trans. eassumption.
      eapply le_trans. eapply plus_le_compat_r. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      lia.
    Qed.
    
    (* Lemma inline_bound_post_inline G : *)
    (*   post_inline cenv (inline_bound_top G) (inline_bound_top G) (inline_bound_top (3 * G)). *)
    (* Proof. *)
    (*   intro; intros. unfold inline_bound in *. unfold_all; simpl in *. *)
    (*   destruct cout1; destruct cout2. destruct cout3; destruct cout4. *)
    (*   destruct cout1'; destruct cout3'. *)
    (*   simpl in *. *)
    (*   inv H3; inv H4; destructAll; inv H8; inv H4; *)
    (*     try (simpl in *; lia). *)
    (* Qed. *)

    (* Lemma inline_bound_post_inline_OOT G : *)
    (*   post_inline_OOT (inline_bound_top G) (inline_bound_top G). *)
    (* Proof. *)
    (*   intro; intros. unfold inline_bound in *. unfold_all; simpl in *. *)
    (*   destruct cout1; destruct cout3; destruct cout3'. *)
    (*   inv H1; destructAll; inv H3; lia. *)
    (* Qed. *)

  
End Bounds.

  

Require Import Coq.Strings.String Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.Prototype.
Require Import L6.proto_util.
Require Import L6.cps L6.ctx L6.cps_proto L6.identifiers.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import L6.Ensembles_util L6.List_util L6.cps_util L6.state L6.uncurry_proto L6.uncurry_rel.

Lemma uncurry_fundefs_step_app pre f1 s1 m1 f2 s2 m2 :
  uncurry_fundefs_step f1 s1 m1 f2 s2 m2 ->
  uncurry_fundefs_step (fundefs_append pre f1) s1 m1 (fundefs_append pre f2) s2 m2.
Proof. induction pre; auto; intros Hstep; simpl; now constructor. Qed.

Lemma uncurry_proto_corresp_step e1 s1 e2 :
  s1 <--> used_vars e1 ->
  uncurry_proto.uncurry_step e1 e2 -> exists m1 s2 m2,
  uncurry_rel.uncurry_step e1 s1 m1 e2 s2 m2.
Proof.
  intros Hused Hstep; destruct Hstep.
  - (* CPS uncurrying *)
    destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    unfold Rec; decompose [and] H; clear H; subst.
    exists (M.empty _); do 2 eexists. apply app_ctx_uncurry_step; [destruct Hused; auto|].
    simpl; constructor.
    unfold fresh_copies, proto_util.fresh_copies in *.
    rewrite <- !Hused in *.
    apply uncurry_fundefs_step_app, uncurry_fundefs_curried; auto.
    + now rewrite M.gempty.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + reflexivity.
  - (* ANF uncurrying *)
    destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    unfold Rec; decompose [and] H; clear H; subst.
    exists (M.empty _); do 2 eexists. apply app_ctx_uncurry_step; [destruct Hused; auto|].
    simpl; constructor.
    unfold fresh_copies, proto_util.fresh_copies in *.
    rewrite <- !Hused in *.
    apply uncurry_fundefs_step_app, uncurry_fundefs_curried_anf; auto.
    + now rewrite M.gempty.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + reflexivity.
Qed.

Corollary uncurry_proto_corresp e1 s1 e2 :
  s1 <--> used_vars e1 ->
  uncurry_proto.uncurry_step e1 e2 -> exists m1 s2 m2,
  uncurry_rel 1 e1 s1 m1 e2 s2 m2.
Proof.
  intros; edestruct uncurry_proto_corresp_step as [? [? [? ?]]]; eauto.
  do 3 eexists; econstructor; [|constructor]; eauto.
Qed.

(* TODO after uncurry_rel is fixed, uncurry_rel_correct gives
     ∀ e1 e2, uncurry_step e1 e2 -> ∀ k, e1 ≈_k e2 
   ==>
     ∀ e1 e2, clos_refl_trans _ uncurry_step e1 e2 -> ∀ k, e1 ≈_k e2
*)

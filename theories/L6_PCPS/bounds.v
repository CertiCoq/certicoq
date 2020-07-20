Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.

Require Import L6.cps L6.eval L6.Ensembles_util L6.List_util L6.tactics L6.set_util
        L6.logical_relations L6.logical_relations_cc.

Import ListNotations.


Section Bounds. 

  Context (K : nat -> env -> exp -> nat) (* in essence, the number of inlined applications *)
          (M : nat -> env -> exp -> nat). (* The total overhead of all L6 transformations, generally different for each program *)
          
  (* TODO: maybe remove step-index k if not needed in bounds *)

  Definition upper_boundG (k : nat) : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c2 <= (M k rho1 e1) * (c1 + 1).

  Definition lower_boundG (k : nat) : relation (exp * env * nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c1 <= (K k rho1 e1) * (c2 + 1).

  (* + 1 is needed in the lower bound ecause sourvce might time out 
   * in say M steps but that may be 0 steps in target *)

  (* + 1 is not technically needed in the upper bound but it makes 
    things easier *)

  Definition boundG (k : nat) : relation (exp * env *  nat) :=
    relation_conjunction (lower_boundG k) (upper_boundG k).
 
  Definition upper_boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat := 
    fun c1 c2 => c2 + local <= M k rho e * (c1 + 1).

  Definition lower_boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat := 
    fun c1 c2 => c1 <= K k rho e * (c2 + 1 + local).

  Definition boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat :=
    relation_conjunction (lower_boundL local k rho e) (upper_boundL local k rho e).
  
  (* bound properties *)
  
  Lemma boundL_0_implies_boundG k e1 e2 rho1 rho2 c1 c2 : 
    boundL 0 k rho1 e1 c1 c2 -> boundG k (e1, rho1, c1) (e2, rho2, c2).
  Proof.
    unfold boundL, boundG, lower_boundL, lower_boundG, upper_boundL, upper_boundG. 
    intros [H1 H2]. split; eauto.
    eapply le_trans. eassumption. 
    eapply Nat_as_OT.mul_le_mono_l. omega. 
    rewrite Nat_as_DT.add_0_r in H2. 
    eapply le_trans. eassumption. 
    eapply Nat_as_OT.mul_le_mono_l. omega.       
  Qed.
(*
  (* Divergence preservation *)
  Lemma cc_approx_exp_divergence pr cenv ct l e1 rho1 e2 rho2 :  
    (forall k, cc_approx_exp pr cenv ct k (boundL l) boundG (e1, rho1) (e2, rho2)) ->
    diverge pr cenv rho1 e1 -> 
    diverge pr cenv rho2 e2.
  Proof.
    intros Hexp H1 c2. assert (Hd := H1). specialize (H1 (K*(c2 + 1 + l))).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. reflexivity. eassumption.
    destruct v2; try contradiction.
    assert (Hleq : c2 <= c2').
    { destruct Hp as [Hp1 Hp2]. unfold lower_boundL in Hp1.  
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp1; eauto. omega. }
    eapply bstep_fuel_OOT_monotonic; eassumption. 
  Qed.
*)

End Bounds.

  

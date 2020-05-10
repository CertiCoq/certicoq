Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.

Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.set_util
        L6.logical_relations L6.logical_relations_cc.

Import ListNotations.


Section Bounds. 

  Context (K : nat) (* in essence, the number of inlined applications *)
          (M : nat) (* The total overhead of all L6 transformations, generally different for each program *)
          (Kpos : K > 0) (Mpos : M > 0).
  (* TODO: maybe remove step-index k if not needed in bounds *)

  Definition upper_boundG : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c2 <= M * c1.

  Definition lower_boundG : relation (exp * env * nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c1 <= K * c2.

  Definition boundG : relation (exp * env *  nat) :=
    relation_conjunction lower_boundG upper_boundG.
 
  Definition upper_boundL (local : nat) : relation nat := 
    fun c1 c2 => c2 + local <= M * c1.

  Definition lower_boundL (local : nat) : relation nat := 
    fun c1 c2 => c1 <= K * (c2 + local).

  Definition boundL (local : nat) : relation nat :=
    relation_conjunction (lower_boundL local) (upper_boundL local).
  
  (* Divergence preservation *)
  Lemma cc_approx_exp_divergence pr cenv ct l e1 rho1 e2 rho2 :  
    (forall k, cc_approx_exp pr cenv ct k (boundL l) boundG (e1, rho1) (e2, rho2)) ->
    diverge pr cenv rho1 e1 -> 
    diverge pr cenv rho2 e2.
  Proof.
    intros Hexp H1 c2. assert (Hd := H1). specialize (H1 (K*(c2 + l))).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. reflexivity. eassumption.
    destruct v2; try contradiction.
    assert (Hleq : c2 <= c2').
    { destruct Hp as [Hp1 Hp2]. unfold lower_boundL in Hp1.  
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp1; eauto. omega. }
    

End Bounds.

  
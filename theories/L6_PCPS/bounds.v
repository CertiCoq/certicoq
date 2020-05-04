Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.

Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.set_util
        L6.logical_relations.

Import ListNotations.


Section Bounds. 

  Context (K : nat) (* basically the number of inlined applications *)
          (M : nat). (* The total overhead of all L6 transformations *)

  (* TODO: maybe remove step-index k if not needed in bounds *)

  Definition upper_boundG (k : nat) : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c2 <= M * c1.

  Definition lower_boundG (k : nat) : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c1 <= K * c2.

  Definition boundG (k : nat) : relation (exp * env *  nat) :=
    relation_conjunction (lower_boundG k) (upper_boundG k).
 
  Definition upper_boundL (local : nat) : relation nat := 
    fun c1 c2 => c2 + local <= M * c1.

  Definition lower_boundL (local : nat) : relation nat := 
    fun c1 c2 => c1 <= K * (c2 + local).

  Definition boundL (local : nat) : relation nat :=
    relation_conjunction (lower_boundL local) (upper_boundL local).
  
End Bounds.

  
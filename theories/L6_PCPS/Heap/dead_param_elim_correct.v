From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel dead_param_elim_rel GC log_rel_defs log_rel_post_cc.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module DeadParamCorrect (H : Heap).

  Module LR := LogRelPostCC H.
  
  Import H LR LR.LRDefs LR.LRDefs.Sem.GC LR.LRDefs.Sem.GC.Equiv
         LR.LRDefs.Sem.GC.Equiv.Defs LR.LRDefs.Sem.


  Definition Pre : IInv :=
    fun c1 c2 => 
      let '(H1, rho1, e1) := c1 in
      let '(H2, rho2, e2) := c2 in
      size_heap H2 <= size_heap H1. 

  Definition Post : Inv :=
    fun c p1 p2 =>
      let '(c1, m1) := p1 in
      let '(c2, m2) := p1 in
      c2 <= c1 /\ m2 <= m1. 

  Definition PreG : GIInv :=
    fun _ _ _ _ c1 c2 => 
      let '(H1, rho1, e1) := c1 in
      let '(H2, rho2, e2) := c2 in
      size_heap H2 <= size_heap H1. 

  Definition PostG : GInv :=
    fun _ _ c p1 p2 =>
      let '(c1, m1) := p1 in
      let '(c2, m2) := p1 in
      c2 <= c1 /\ m2 <= m1. 


  Definition drop_invariant (drop : var -> option (list bool)) rho1 rho2 :=
    forall f bs, drop f = Some bs ->
            exists B1 f1 B2 f2 ft1 xs1 e1 ft2 xs2 e2 S,
              M.get f rho1 = Some (FunPtr B1 f1) /\
              M.get f rho2 = Some (FunPtr B1 f2) /\
              find_def f1 B1 = Some (ft1, xs1, e1) /\
              find_def f2 B2 = Some (ft2, xs2, e2) /\
              Drop_params xs1 bs xs2 S /\
              Drop_body drop S e1 e2.
  
  Lemma dead_param_elim_correct
        k j (* step and heap indices *)
        H1 rho1 e1 H2 rho2 e2 (* source and target conf *)
        b (* location renaming *)
        drop (* dropper function *)
        S (* dropped variables *) :

    (forall j, (H1, rho1) ⋞ ^ (occurs_free e1 \\ S (* \\ dropped_funs drop *) ; k ; j; PreG ; PostG ; b) (H2, rho2)) ->

    (* invariant about dropped function names *)
    drop_invariant drop rho1 rho2 -> 
    
    (* Assumptions about variable names *)
    unique_bindings e1 -> 
    Disjoint _ (occurs_free e1) (bound_var e1) -> 
    
    (* e2 is the dropping of e1 *)
    Drop_body drop S e1 e2 ->
    (* The source and target are related *)
    (H1, rho1, e1) ⪯ ^ ( k ; j ; Pre ; PreG ; Post ; PostG ) (H2, rho2, e2).
  Proof.
  Abort. 

End DeadParamCorrect.
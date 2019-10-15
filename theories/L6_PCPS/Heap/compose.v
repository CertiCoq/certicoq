(* Generic definitions for step-indexed logical relations for L6 language transformations
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2019
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                 List_util Heap.heap Heap.heap_defs Heap.space_sem Heap.GC tactics map_util Heap.log_rel_defs.
From compcert Require Import lib.Coqlib.


Module LogRelCompose (H : Heap).

  Module LRD :=  LogRelDefs H.

  Import H LRD LRD.Sem.GC.Equiv.Defs.

  Class CompPass :=
    { eval_src : heap block -> env -> exp -> ans -> nat -> nat -> Prop;
      eval_trg : heap block -> env -> exp -> ans -> nat -> nat -> Prop;
      fun_rel  : GIInv -> GInv -> Inj -> value -> heap block -> value -> heap block ->
                 fun_body_rel -> Prop; 
      clos_val : GIInv -> GInv -> Inj -> block -> heap block -> block -> heap block ->
                 fun_body_rel -> val_rel -> Prop
    }.

  
  Section PassDefs.
    
    Context (Pass : CompPass)
            (GP : GIInv) (LP : IInv)
            (GQ : GInv) (LQ : Inv).

    Lemma val_rel_refl k j IP P b r :
      val_log_rel' GP LP GQ LQ k j IP P b r r. 
(* Generic definitions for step-indexed logical relations for L6 language transformations
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2019
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                                List_util tactics map_util.
From CertiCoq.L6.Heap Require Import heap heap_defs space_sem GC log_rel_defs.
From compcert Require Import lib.Coqlib.



Module LogRelPostCC (H : Heap).

  Module LRDefs := LogRelDefs H.

  Import H LRDefs LRDefs.Sem.GC LRDefs.Sem.GC.Equiv
         LRDefs.Sem.GC.Equiv.Defs LRDefs.Sem.
  
  Definition fun_ptr_rel (GP : GIInv) (GQ : GInv) (b : Inj)
             (v1 : value) (H1 : heap block) (v2 : value) (H2 : heap block)
             (fR : fun_body_rel) : Prop :=
    match v1, v2 with
    | FunPtr B1 f1, FunPtr B2 f2 =>
      forall H1' H1'' rho1 H2' b1 b2 ft1 xs1 e1 vs1 vs2,
         Union_list (map val_loc vs1) |- H1 ≃_(id, b1) H1' ->
         injective_subdomain (reach' H1' (Union_list (map val_loc vs1))) b1 ->

         Union_list (map val_loc vs2) |- H2 ≃_(b2, id) H2' ->
         injective_subdomain (reach' H2' (Union_list (map val_loc vs2))) b2 ->
                                       
         find_def f1 B1 = Some (ft1, xs1, e1) ->
         setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho1 ->
         live' (env_locs rho1 (occurs_free e1)) H1' H1'' b1 ->

         length vs1 = length vs2 ->
         
         exists ft2 xs2 e2 rho2 H2'',
           find_def f1 B1 = Some (ft2, xs2, e2) /\
           setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho2 /\
           live' (env_locs rho2 (occurs_free e2)) H2' H2'' b2 /\
           fR GP GQ (b2 ∘ b ∘ b2) vs1 H1' vs2 H2' (H1'', rho1, e1) (H2'', rho2, e2)           
    | _, _ => False
    end. 
      
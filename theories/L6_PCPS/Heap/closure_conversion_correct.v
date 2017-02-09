From L6 Require Import cps size_cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions closure_conversion.

From L6.Heap Require Import heap heap_defs space_sem cc_log_rel.

From Libraries Require Import Coqlib.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

  (* Module Sem := SpaceSem H. *)
  Module LogRel := CC_log_rel H.

  Import H LogRel.Sem LogRel.Sem.Defs LogRel.
  
  Variable clo_tag : cTag.

  Variable (IG : GInv).
  Variable (IL1 IL2 IL : GInv).
  

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) (FVs : list var)
        (σ : var -> var) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (H1, rho1) ⋞ ^ (Scope; k; IG) (H2, rho2) ->
    (* [Fun] invariant *)
    Fun_inv k IG rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    (* Free variables invariant *)
    FV_inv k IG rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
    
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e1) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain Funs σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Setminus _ Funs Scope)) (bound_var e1) ->

    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs σ c Γ FVs e1 e2 C ->
    (e1, rho1, H1) ⪯ ^ (k; IL; IG) (C |[ e2 ]|, rho2, H2).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ c Γ
           Henv Hnin HFVs Hun Hinj Hd Hfun Hfv Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.
      admit.
    - (* case Ecase nil *)
      inv Hcc.
      admit.
    - (* case Ecase cons *)
      inv Hcc. (* TODO change compat *) 
      admit.
    - (* case Eproj *)
      inv Hcc.
      admit.
    - (* case Efun *)
      inv Hcc.
      admit.
    - (* case Eapp *)
      inv Hcc.
      admit.
    - (* case Eprim *)
      intros ? ? ? ? ? ? ? ? Hstep. inv Hstep.
    - (* case Ehalt *)
      inv Hcc.
      admit.
  Abort.
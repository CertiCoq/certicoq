(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From CertiCoq.L6 Require Import cps ctx cps_util eval List_util Ensembles_util functions
                 identifiers Heap.heap Heap.heap_defs Heap.heap_equiv Heap.GC tactics.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Module SpaceSem (H : Heap).
  
  Module GC := GC H.
  
  Parameter (cloTag : cTag).

  Import H GC.Equiv.Defs GC.Equiv.Defs.HL GC.Equiv GC.

  (* The cost of evaluating the head constructor before CC *)
  Definition cost (e : exp) : nat :=
    match e with
      | Econstr x t ys e => 1 + length ys
      | Ecase y cl => 1 
      | Eproj x t n y e => 1
      | Efun B e => 1
      | Eapp f t ys => 1 + length ys
      | Eprim x p ys e => 0
      | Ehalt x => 1
    end.
    
  
  (** Deterministic semantics with garbage collection upon function entry.
    * We will show that it takes asymptotically the same amount of space as perfect
    * garbage collection. *)
  Inductive big_step_GC :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* Upper bound for the number of the evaluation steps  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_oot_gc :
      forall (H : heap block) (rho : env) (e : exp) (c m : nat)
        (Hcost : c < cost e) 
        (Hsize : size_heap H = m),
        (big_step_GC H rho e OOT c m)
  | Eval_constr_gc :
      forall (H H' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys : list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
                
        (Hbs : big_step_GC H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),

        big_step_GC H rho (Econstr x t ys e) r c m
  | Eval_proj_gc : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)
        
        (Hbs : big_step_GC H (M.set x v rho) e r (c - cost (Eproj x t n y e)) m),
        
        big_step_GC H rho (Eproj x t n y e) r c m
  | Eval_case_gc :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)
        
        (Hbs : big_step_GC H rho e r (c - cost (Ecase y cl)) m),
        
        big_step_GC H rho (Ecase y cl) r c m
  | Eval_fun_gc :
      forall (H H' H'' : heap block) (rho rho_clo rho' : env) lenv (B : fundefs)
        (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (fundefs_fv B) rho = rho_clo)
        (Ha : alloc (Env rho_clo) H = (lenv, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' (Loc lenv) = (H'', rho'))
        
        (Hbs : big_step_GC H'' rho' e r (c - cost (Efun B e)) m),

        big_step_GC H rho (Efun B e) r c m
    
  | Eval_app_gc :
      forall (H H' H'' : heap block) lenv (rho_clo rho rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l : loc) b
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Eapp f t ys))
        (Hgetf : M.get f rho = Some (Loc l))
        (* Look up the closure *)
        (Hgetl : get l H = Some (Clos (FunPtr B f') (Loc lenv)))
        (* Find the code *)
        (Hfind : find_def f' B = Some (t, xs, e))
        (Hgetenv : get lenv H = Some (Env rho_clo))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (* Allocate mutually defined closures *)
        (Hredef : def_closures B B rho_clo H (Loc lenv) = (H', rho_clo1))
        (Hset : setlist xs vs rho_clo1 = Some rho_clo2)
        
        (* collect H' *)
        (Hgc : live' ((env_locs rho_clo2) (occurs_free e)) H' H'' b)
        (Hsize : size_heap H' = m')
        
        (Hbs : big_step_GC H'' (subst_env b rho_clo2)
                           e r (c - cost (Eapp f t ys)) m),
        big_step_GC H rho (Eapp f t ys) r c (max m m')
  | Eval_halt_gc :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC H rho (Ehalt x) (Res (l, H)) c m.


  (** Deterministic semantics with perfect garbage collection, for closure converted code
   * The execution time cost model does not account for the cost of GC  *)
  Inductive big_step_GC_cc :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* Upper bound for the number of the evaluation steps  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_oot_per_cc :
      forall (H : heap block) (rho : env) (e : exp) (c m : nat)
        (Hcost : c < cost e) 
        (Hsize : size_heap H = m),
        (big_step_GC_cc H rho e OOT c m)
  | Eval_constr_per_cc :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
              
        (Hbs : big_step_GC_cc H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),

        big_step_GC_cc H rho (Econstr x t ys e) r c m
  | Eval_proj_per_cc : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)

        (Hbs : big_step_GC_cc H (M.set x v rho) e r (c - cost (Eproj x t n y e)) m),
        
        big_step_GC_cc H rho (Eproj x t n y e) r c m
  | Eval_case_per_cc :
      forall (H H' : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)


        (Hbs : big_step_GC_cc H' rho e r (c - cost (Ecase y cl)) m),
        
        big_step_GC_cc H rho (Ecase y cl) r c m
  | Eval_fun_per_cc :
      forall (H : heap block) (rho rho' : env) (B : fundefs)
        (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Efun B e))
        (* add the functions in the environment *)
        (Hfuns : def_funs B B rho = rho')
        
        (Hbs : big_step_GC_cc H rho' e r (c - cost (Efun B e)) m),
        
        big_step_GC_cc H rho (Efun B e) r c m
  | Eval_app_per_cc :
      forall (H H' : heap block) (rho rho_clo : env) (B : fundefs)
        (f f' : var) (ct : cTag) (xs : list var) (e : exp) b
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Eapp f ct ys))
        (Hgetf : M.get f rho = Some (FunPtr B f'))
        (* Find the code *)
        (Hfind : find_def f' B = Some (ct, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (Hset : setlist xs vs (def_funs B B (M.empty _)) = Some rho_clo)
        
        (* collect H' *)
        (Hgc : live' ((env_locs rho_clo) (occurs_free e)) H H' b)
        (Hsize : size_heap H = m')
        
        (Hbs : big_step_GC_cc H' (subst_env b rho_clo) e r (c - cost (Eapp f ct ys)) m),
        big_step_GC_cc H rho (Eapp f ct ys) r c (max m m')
  | Eval_halt_per_cc :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC_cc H rho (Ehalt x) (Res (l, H)) c m.

  Definition is_res (r : ans) : Prop :=
    match r with
      | Res _ =>  True
      | _ => False
    end.

  Lemma big_step_gc_heap_env_equiv_l H1 H2 β rho1 rho2 e (r : ans) c m :
    big_step_GC H1 rho1 e r c m ->
    (occurs_free e) |- (H1, rho1) ⩪_(β, id) (H2, rho2) ->
    injective_subdomain (reach' H1 (env_locs rho1 (occurs_free e))) β -> 
    (exists r' m' β', big_step_GC H2 rho2 e r' c m' /\
                 injective_subdomain (reach_ans r') β' /\
                 ans_equiv β' r id r').
  Admitted.
  
  Lemma big_step_gc_heap_env_equiv_r H1 H2 β1 β2 rho1 rho2 e (r : ans) c m :
    big_step_GC H1 rho1 e r c m ->
    (occurs_free e) |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    injective_subdomain (reach' H1 (env_locs rho1 (occurs_free e))) β1 ->
    injective_subdomain (reach' H2 (env_locs rho2 (occurs_free e))) β2 -> 
    (exists r' m' β1' β2', big_step_GC H2 rho2 e r' c m' /\
                      injective_subdomain (reach_ans r) β1' /\
                      injective_subdomain (reach_ans r') β2' /\
                      ans_equiv β1' r β2' r').
  Admitted.
  

  (** * Interpretation of a context as a heap and an environment *)

  Fixpoint cost_ctx_full (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + cost_ctx_full c
      | Eproj_c x t n y c => 1 + cost_ctx_full c
      | Efun1_c B c => 1 + cost_ctx_full c
      | Eprim_c x p ys c => 1 + length ys + cost_ctx_full c
      | Hole_c => 0
      | Efun2_c B _ => cost_ctx_full_f B
      | Ecase_c _ _ _ c _ => cost_ctx_full c
    end
  with cost_ctx_full_f (f : fundefs_ctx) : nat :=
    match f with
      | Fcons1_c _ _ _ c _ => cost_ctx_full c
      | Fcons2_c _ _ _ _ f => cost_ctx_full_f f
    end.

  
  Fixpoint cost_ctx (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys
      | Eproj_c x t n y c => 1 
      | Efun1_c B c => 1
      | Eprim_c x p ys c => 1 + length ys
      | Hole_c => 0
      | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
      | Ecase_c _ _ _ _ _ => 0
    end.
  
  Inductive ctx_to_heap_env : exp_ctx -> heap block -> env -> heap block -> env -> nat -> Prop :=
  | Hole_c_to_heap_env :
      forall H rho,
        ctx_to_heap_env Hole_c H rho H rho 0
  | Econstr_c_to_rho :
      forall H H' H'' rho rho' x t ys C vs l c,
        getlist ys rho = Some vs ->
        alloc (Constr t vs) H = (l, H') ->
        
        ctx_to_heap_env C H' (M.set x (Loc l) rho)  H'' rho'  c -> 
        
        ctx_to_heap_env (Econstr_c x t ys C) H rho H'' rho' (c + cost_ctx (Econstr_c x t ys C))

  | Eproj_c_to_rho :
      forall H H' rho rho' x N t y C vs v t' l c,
        
        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t' vs) ->
        nthN vs N = Some v ->
        
        ctx_to_heap_env C H (M.set x v rho)  H' rho'  c -> 
        
        ctx_to_heap_env (Eproj_c x t N y C) H rho H' rho' (c + cost_ctx (Eproj_c x t N y C))
  | Efun_c_to_rho :
      forall H H' H'' H''' rho rho' rho'' rho_clo lenv B C c,
        restrict_env (fundefs_fv B) rho = rho_clo ->
        alloc (Env rho_clo) H = (lenv, H') ->
        def_closures B B rho H' (Loc lenv) = (H'', rho') ->
        ctx_to_heap_env C H'' rho' H''' rho'' c -> 
        ctx_to_heap_env (Efun1_c B C) H rho H''' rho'' (c + cost_ctx (Efun1_c B C)).
  
  Inductive ctx_to_heap_env_CC : exp_ctx -> heap block -> env -> heap block -> env -> nat -> Prop :=
  | Hole_c_to_heap_env_CC :
      forall H rho,
        ctx_to_heap_env_CC Hole_c H rho H rho 0
  | Econstr_c_to_rho_CC :
      forall H H' H'' rho rho' x t ys C vs l c,
        getlist ys rho = Some vs ->
        alloc (Constr t vs) H = (l, H') ->
        
        ctx_to_heap_env_CC C H' (M.set x (Loc l) rho)  H'' rho'  c -> 
        
        ctx_to_heap_env_CC (Econstr_c x t ys C) H rho H'' rho' (c + cost_ctx (Econstr_c x t ys C))

  | Eproj_c_to_rho_CC :
      forall H H' rho rho' x N t y C vs v t' l c,
        
        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t' vs) ->
        nthN vs N = Some v ->
        
        ctx_to_heap_env_CC C H (M.set x v rho)  H' rho'  c -> 
        
        ctx_to_heap_env_CC (Eproj_c x t N y C) H rho H' rho' (c + cost_ctx (Eproj_c x t N y C))
  | Efun_c_to_rho_CC :
      forall H H' rho rho' B C c,
        ctx_to_heap_env_CC C H (def_funs B B rho) H' rho' c -> 
        ctx_to_heap_env_CC (Efun1_c B C) H rho H' rho' (c + cost_ctx (Efun1_c B C)).
  

  (** Number of function definitions *)
  Fixpoint numOf_fundefs (B : fundefs) : nat := 
    match B with
      | Fcons _ _ xs e B =>
        1 + numOf_fundefs B
      | Fnil => 0
    end.

  (** Allocation cost of an evaluation context *)
  Fixpoint cost_alloc_ctx (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + cost_alloc_ctx c
      | Eproj_c x t n y c => cost_alloc_ctx c
      | Efun1_c B c => 1 + (numOf_fundefs B) + cost_alloc_ctx c
      (* not relevant *)
      | Eprim_c x p ys c => cost_alloc_ctx c
      | Hole_c => 0
      | Efun2_c f _ => cost_alloc_f_ctx f
      | Ecase_c _ _ _ c _ => cost_alloc_ctx c
    end
  with
  cost_alloc_f_ctx (f : fundefs_ctx) : nat :=
    match f with
      | Fcons1_c _ _ _ c _ => cost_alloc_ctx c
      | Fcons2_c _ _ _ _ f => cost_alloc_f_ctx f
    end.
 
  (** Allocation cost of an evaluation context *)
  Fixpoint cost_alloc_ctx_CC (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + cost_alloc_ctx_CC c
      | Eproj_c x t n y c => cost_alloc_ctx_CC c
      | Efun1_c B c =>  cost_alloc_ctx_CC c
      (* not relevant *)
      | Eprim_c x p ys c => cost_alloc_ctx_CC c
      | Hole_c => 0
      | Efun2_c f _ => cost_alloc_f_ctx_CC f
      | Ecase_c _ _ _ c _ => cost_alloc_ctx_CC c
    end
  with
  cost_alloc_f_ctx_CC (f : fundefs_ctx) : nat :=
    match f with
      | Fcons1_c _ _ _ c _ => cost_alloc_ctx_CC c
      | Fcons2_c _ _ _ _ f => cost_alloc_f_ctx_CC f
    end.
  
  Lemma cost_alloc_ctx_comp_ctx_f C C' :
    cost_alloc_ctx (comp_ctx_f C C') =
    cost_alloc_ctx C + cost_alloc_ctx C'
  with cost_alloc_comp_f_ctx_f f C' :
         cost_alloc_f_ctx (comp_f_ctx_f f C') =
         cost_alloc_f_ctx f + cost_alloc_ctx C'.
  Proof.
    - destruct C; simpl; try reflexivity;
      try (rewrite cost_alloc_ctx_comp_ctx_f; omega).
      rewrite cost_alloc_comp_f_ctx_f. omega.
    - destruct f; simpl; try reflexivity.
      rewrite cost_alloc_ctx_comp_ctx_f; omega.
      rewrite cost_alloc_comp_f_ctx_f. omega.
  Qed.

  Lemma cost_alloc_ctx_CC_comp_ctx_f C C' :
    cost_alloc_ctx_CC (comp_ctx_f C C') =
    cost_alloc_ctx_CC C + cost_alloc_ctx_CC C'
  with cost_alloc_comp_CC_f_ctx_f f C' :
         cost_alloc_f_ctx_CC (comp_f_ctx_f f C') =
         cost_alloc_f_ctx_CC f + cost_alloc_ctx_CC C'.
  Proof.
    - destruct C; simpl; try reflexivity;
      try (rewrite cost_alloc_ctx_CC_comp_ctx_f; omega).
      rewrite cost_alloc_comp_CC_f_ctx_f. omega.
    - destruct f; simpl; try reflexivity.
      rewrite cost_alloc_ctx_CC_comp_ctx_f; omega.
      rewrite cost_alloc_comp_CC_f_ctx_f. omega.
  Qed.

  Lemma cost_ctx_full_ctx_comp_ctx_f (C : exp_ctx) :
    (forall C', cost_ctx_full (comp_ctx_f C C') =
           cost_ctx_full C + cost_ctx_full C')
  with cost_ctx_full_f_comp_ctx_f f :
         (forall C', cost_ctx_full_f (comp_f_ctx_f f C') =
                cost_ctx_full_f f + cost_ctx_full C').
  Proof.
    - destruct C; intros C'; simpl; eauto.
      + rewrite (cost_ctx_full_ctx_comp_ctx_f C C'). omega.
      + rewrite (cost_ctx_full_ctx_comp_ctx_f C C'). omega.
    - destruct f; intros C'; simpl.
      + rewrite cost_ctx_full_ctx_comp_ctx_f. omega.
      + rewrite cost_ctx_full_f_comp_ctx_f. omega.
  Qed.

  Lemma def_closures_size B1 B2 rho H envc H' rho' :
    def_closures B1 B2 rho H envc = (H', rho') ->
    size_heap H' = size_heap H + numOf_fundefs B1.
  Proof. 
    revert rho H H' rho'. induction B1; intros rho H H' rho' Hdefs; simpl; eauto.
    - simpl in Hdefs.
      destruct (def_closures B1 B2 rho H envc) as [H'' rho''] eqn:Hdefs'.
      destruct (alloc (Clos (FunPtr B2 v) envc)) as [l' H'''] eqn:Hal. inv Hdefs.
      unfold size_heap.
      erewrite (HL.size_with_measure_alloc _ _ _ H'' H'); eauto.
      erewrite IHB1; eauto. simpl. unfold size_heap. omega.
    - inv Hdefs. omega.
  Qed.
    
    (** * Lemmas about [ctx_to_heap_env] *)
  
  Lemma ctx_to_heap_env_comp_ctx_f_r C1 C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 :
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m1 ->
    ctx_to_heap_env C2 H2 rho2 H3 rho3 m2 ->
    ctx_to_heap_env (comp_ctx_f C1 C2) H1 rho1 H3 rho3 (m1 + m2).
  Proof.
    revert C2 rho1 H1 m1 rho2 H2 m2 rho3 H3.
    induction C1; intros C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - replace (c0 + cost_ctx (Econstr_c v c l C1) + m2) with (c0 + m2 + cost_ctx (Econstr_c v c l C1)) by omega.
      simpl. econstructor; eauto. 
    - replace (c0 + cost_ctx (Eproj_c v c n v0 C1) + m2) with (c0 + m2 + cost_ctx (Eproj_c v c n v0 C1)) by omega.
      simpl. econstructor; eauto.
    - replace (c + cost_ctx (Efun1_c f C1) + m2) with (c + m2 + cost_ctx (Efun1_c f C1)) by omega.
      simpl. econstructor; eauto.
  Qed.

  Lemma ctx_to_heap_env_CC_comp_ctx_f_r C1 C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 :
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m1 ->
    ctx_to_heap_env_CC C2 H2 rho2 H3 rho3 m2 ->
    ctx_to_heap_env_CC (comp_ctx_f C1 C2) H1 rho1 H3 rho3 (m1 + m2).
  Proof.
    revert C2 rho1 H1 m1 rho2 H2 m2 rho3 H3.
    induction C1; intros C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - replace (c0 + cost_ctx (Econstr_c v c l C1) + m2) with (c0 + m2 + cost_ctx (Econstr_c v c l C1)) by omega.
      simpl. econstructor; eauto. 
    - replace (c0 + cost_ctx (Eproj_c v c n v0 C1) + m2) with (c0 + m2 + cost_ctx (Eproj_c v c n v0 C1)) by omega.
      simpl. econstructor; eauto.
    - replace (c + cost_ctx (Efun1_c f C1) + m2) with (c + m2 + cost_ctx (Efun1_c f C1)) by omega.
      simpl. econstructor; eauto.
  Qed.
  
  Lemma ctx_to_heap_env_comp_ctx_l C C1 C2 H rho H' rho' m :
    ctx_to_heap_env C H rho H' rho' m ->
    comp_ctx C1 C2 C ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. repeat eexists; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists. split; [ | split ].  econstructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists. split; [ | split ]. econstructor; eauto.
        eassumption. simpl. omega.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists; split; [| split ]. constructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists; split; [| split ]. econstructor; eauto.
        eassumption. simpl. omega.
    - inv Hcomp.
      + edestruct IHHctx as [rho''' [H'''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists; split; [| split ]. constructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho''' [H'''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists; split; [| split ]. econstructor; eauto.
        eassumption. simpl. omega.
  Qed.

  Lemma ctx_to_heap_env_CC_comp_ctx_l C C1 C2 H rho H' rho' m :
    ctx_to_heap_env_CC C H rho H' rho' m ->
    comp_ctx C1 C2 C ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env_CC C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env_CC C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. repeat eexists; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists. split; [ | split ].  econstructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists. split; [ | split ]. econstructor; eauto.
        eassumption. simpl. omega.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists; split; [| split ]. constructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists; split; [| split ]. econstructor; eauto.
        eassumption. simpl. omega.
    - inv Hcomp.
      + edestruct IHHctx as [rho''' [H'''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv Hc1.
        do 4 eexists; split; [| split ]. constructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho''' [H'''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists; split; [| split ]. econstructor; eauto.
        eassumption. simpl. omega.
  Qed.
  
  Lemma ctx_to_heap_env_comp_ctx_f_l C1 C2 H rho H' rho' m :
    ctx_to_heap_env (comp_ctx_f C1 C2) H rho H' rho' m ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros. eapply ctx_to_heap_env_comp_ctx_l. eassumption.
    eapply comp_ctx_f_correct. reflexivity.
  Qed.

  Lemma ctx_to_heap_env_CC_comp_ctx_f_l C1 C2 H rho H' rho' m :
    ctx_to_heap_env_CC (comp_ctx_f C1 C2) H rho H' rho' m ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env_CC C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env_CC C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros. eapply ctx_to_heap_env_CC_comp_ctx_l. eassumption.
    eapply comp_ctx_f_correct. reflexivity.
  Qed.
  
  Lemma ctx_to_heap_env_size_heap C rho1 rho2 H1 H2 c :
    ctx_to_heap_env C H1 rho1 H2 rho2 c ->
    size_heap H2 = size_heap H1 + cost_alloc_ctx C. 
  Proof.
    intros Hctx; induction Hctx; eauto.
    simpl. rewrite IHHctx.
    unfold size_heap.
    erewrite (HL.size_with_measure_alloc _ _ _ H H');
      [| reflexivity | eassumption ].
    erewrite getlist_length_eq; [| eassumption ]. 
    simpl. omega.
    simpl.
    rewrite IHHctx. 
    erewrite def_closures_size; eauto. unfold size_heap. 
    erewrite size_with_measure_alloc; [| reflexivity | eassumption ]. simpl. omega.
  Qed.

  Lemma ctx_to_heap_env_CC_size_heap C rho1 rho2 H1 H2 c :
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 c ->
    size_heap H2 = size_heap H1 + cost_alloc_ctx_CC C. 
  Proof.
    intros Hctx; induction Hctx; eauto.
    simpl. rewrite IHHctx.
    unfold size_heap.
    erewrite (HL.size_with_measure_alloc _ _ _ H H');
      [| reflexivity | eassumption ].
    erewrite getlist_length_eq; [| eassumption ]. 
    simpl. omega.
  Qed.

  Lemma ctx_to_heap_env_subheap C H rho H' rho' m :
    ctx_to_heap_env C H rho H' rho' m ->
    H ⊑ H'.
  Proof.
    intros Hc; induction Hc.
    - eapply HL.subheap_refl.
    - eapply HL.subheap_trans.
      eapply HL.alloc_subheap. eassumption. eassumption.
    - eassumption.
    - eapply HL.subheap_trans. eapply alloc_subheap. eassumption. 
      eapply HL.subheap_trans.
      eapply def_funs_subheap. now eauto. eassumption.
  Qed.

  Lemma ctx_to_heap_env_CC_subheap C H rho H' rho' m :
    ctx_to_heap_env_CC C H rho H' rho' m ->
    H ⊑ H'.
  Proof.
    intros Hc; induction Hc.
    - eapply HL.subheap_refl.
    - eapply HL.subheap_trans.
      eapply HL.alloc_subheap. eassumption. eassumption.
    - eassumption.
    - eassumption.
  Qed. 

  Lemma ctx_to_heap_env_big_step_compose H1 rho1 H2 rho2 C e r c1 c m :
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 c ->
    big_step_GC_cc H2 rho2 e r c1 m ->
    big_step_GC_cc H1 rho1 (C |[ e ]|) r (c1 + c) m.
  Proof.
    intros Hctx. revert e c1. induction Hctx; intros e c1 Hbstep; simpl; eauto.
    - rewrite <- plus_n_O. eassumption.
    - econstructor; eauto. simpl. omega.
      simpl.
      assert (Heq : c1 + (c + S (length ys)) - S (length ys) = (c1 + c)) by omega.
      specialize (IHHctx e c1). rewrite <- Heq in IHHctx.
      eapply IHHctx. eassumption.
    - econstructor; eauto. simpl. omega.
      simpl.
      replace (c1 + (c + 1) - 1) with (c1 + c) by omega.  eauto.
    - econstructor; eauto. simpl. omega.
      simpl.
      replace (c1 + (c + 1) - 1) with (c1 + c) by omega.  eauto.
  Qed.

  Lemma ctx_to_heap_env_determistic C H1 rho1 H2 rho2 H1' rho1' e c b :
    well_formed (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) H1 ->
    (env_locs rho1 (occurs_free (C |[ e ]|))) \subset dom H1 ->

    ctx_to_heap_env_CC C H1 rho1 H2 rho2 c ->
    occurs_free (C |[ e ]|) |- (H1, rho1) ⩪_(b, id) (H1', rho1') ->
    injective_subdomain (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) b ->
    exists H2' rho2' b',
      occurs_free e |- (H2, rho2) ⩪_(b', id) (H2', rho2') /\
      injective_subdomain (reach' H2 (env_locs rho2 (occurs_free e))) b' /\
      ctx_to_heap_env_CC C H1' rho1' H2' rho2' c.
  Proof with (now eauto with Ensembles_DB).
    intros Hwf Hlocs Hctx. revert b H1' rho1' e Hwf Hlocs. induction Hctx; intros b H1' rho1' e Hwf Hlocs Heq Hinj.
    - do 3 eexists. repeat (split; eauto). now constructor.
    - edestruct heap_env_equiv_env_getlist as [vs' [Hlst Hall]]; try eassumption.
      simpl. normalize_occurs_free...
      destruct (alloc (Constr t vs') H1') as [l2 H1''] eqn:Halloc.
      specialize (IHHctx (b {l ~> l2}) H1'' (M.set x (Loc l2) rho1')).
      edestruct IHHctx as [H2' [rho2' [b' [Heq' [Hinj' Hres]]]]].
      + eapply well_formed_antimon with
        (S2 := reach' H' (env_locs (M.set x (Loc l) rho) (FromList ys :|: occurs_free (C |[ e ]|)))).
        eapply reach'_set_monotonic. eapply env_locs_monotonic...
        eapply well_formed_reach_alloc'; try eassumption.
        eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic.
        eapply env_locs_monotonic. 
        simpl. normalize_occurs_free... 
        eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic. 
        simpl. normalize_occurs_free...
        eapply Included_trans; [| now eapply reach'_extensive ].
        rewrite env_locs_Union. 
        eapply Included_Union_preserv_l. rewrite env_locs_FromList.
        simpl. reflexivity. eassumption.
      + eapply Included_trans.
        eapply env_locs_set_Inlcuded'.
        rewrite HL.alloc_dom; try eassumption.
        eapply Included_Union_compat. reflexivity.
        eapply Included_trans; [| eassumption ].
        simpl. normalize_occurs_free...
      + eapply heap_env_equiv_alloc with (b1 :=  (Constr t vs));
        [ | | | | | | | | now apply Halloc | | ].
        * eapply reach'_closed; try eassumption.
        * eapply reach'_closed.
          eapply well_formed_respects_heap_env_equiv; eassumption.
          eapply env_locs_in_dom; eassumption.
        * eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
        * eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
        * simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
        * simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
        * eapply heap_env_equiv_antimon.
          eapply heap_env_equiv_rename_ext. eassumption.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply reachable_in_dom in Hc.
          destruct Hc as [vc Hgetc].
          erewrite alloc_fresh in Hgetc; eauto. congruence.
          eassumption. eassumption. reflexivity.
          reflexivity.
          simpl. normalize_occurs_free...
        * eassumption.
        * rewrite extend_gss. reflexivity.
        * split. reflexivity.
          eapply Forall2_monotonic_strong; try eassumption.
          intros x1 x2 Hin1 Hin2 Heq'.
          assert (Hr := well_formed (reach' H (val_loc x1)) H).
          { eapply res_equiv_rename_ext. now apply Heq'. 
            eapply f_eq_subdomain_extend_not_In_S_r.
            intros Hc. eapply reachable_in_dom in Hc.
            destruct Hc as [vc Hgetc].
            erewrite alloc_fresh in Hgetc; eauto. congruence.
            eapply well_formed_antimon; [| eassumption ].
            eapply reach'_set_monotonic. simpl. normalize_occurs_free.
            rewrite env_locs_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_FromList.
            eapply In_Union_list. eapply in_map. eassumption.
            eassumption. eapply Included_trans; [| eassumption ].
            simpl. normalize_occurs_free.
            rewrite env_locs_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_FromList.
            eapply In_Union_list. eapply in_map. eassumption.
            eassumption. reflexivity. reflexivity. }
      + eapply injective_subdomain_antimon.
        eapply injective_subdomain_extend. eassumption.

        intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].
        eapply heap_env_equiv_image_reach in Hc; try (symmetry; eassumption).
        eapply (image_id
                  (reach' H1' (env_locs rho1' (occurs_free (Econstr_c x t ys C |[ e ]|)))))
          in Hc.
        eapply reachable_in_dom in Hc; try eassumption. destruct Hc as [v1' Hgetv1'].
        erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.
        
        eapply well_formed_respects_heap_env_equiv. eassumption. eassumption.
        
        eapply Included_trans; [| eapply env_locs_in_dom; eassumption ].
        reflexivity.

        eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply occurs_free_Econstr_Included.
        eapply reach'_alloc_set; [| eassumption ]. 
        eapply Included_trans; [| eapply reach'_extensive ].
        simpl. normalize_occurs_free. rewrite env_locs_Union.
        eapply Included_Union_preserv_l. 
        rewrite env_locs_FromList. reflexivity.
        eassumption.
      + do 3 eexists. split; eauto. split; eauto.
        econstructor; eauto.
    - assert (Hget := H0). eapply Heq in H0; [| now constructor ].
      destruct H0 as [l' [Hget' Heql]].
      rewrite res_equiv_eq in Heql. destruct l' as [l' |]; try contradiction.
      destruct Heql as [Hbeq Heql]. 
      simpl in Heql. rewrite H1 in Heql.
      destruct (get l' H1') eqn:Hgetl'; try contradiction.
      destruct b0 as [c' vs'| | ]; try contradiction.
      destruct Heql as [Heqt Hall]; subst.
      edestruct (Forall2_nthN _ vs vs' _ _ Hall H2) as [v' [Hnth' Hv]].
      specialize (IHHctx b H1' (M.set x v' rho1') e).
      edestruct IHHctx as [H1'' [rho1'' [b' [Heq' [Hinj' Hres]]]]].
      + eapply well_formed_antimon with
        (S2 := reach' H (env_locs (M.set x v rho) ([set y] :|: occurs_free (C |[ e ]|)))).
        eapply reach'_set_monotonic. eapply env_locs_monotonic...
        eapply well_formed_reach_set'.
        eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic.
        eapply env_locs_monotonic. 
        simpl. normalize_occurs_free...
        rewrite env_locs_Union, reach'_Union.
        eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
        eapply Included_trans; [| eapply Included_post_reach' ].
        simpl. rewrite post_Singleton; eauto. simpl.
        eapply In_Union_list. eapply in_map.
        eapply nthN_In; eassumption.
      + eapply Included_trans.
        eapply env_locs_set_Inlcuded'.
        eapply Union_Included.
        eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
        simpl. normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
        eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
        eapply Included_trans; [| eapply Included_post_reach' ].
        simpl. rewrite post_Singleton; eauto. simpl.
        eapply In_Union_list. eapply in_map.
        eapply nthN_In; eassumption.
        eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic. simpl. normalize_occurs_free...
      + eapply heap_env_equiv_set; try eassumption.
        eapply heap_env_equiv_antimon. eassumption.
        simpl. normalize_occurs_free...
      + eapply injective_subdomain_antimon. eassumption.
        simpl. normalize_occurs_free.
        rewrite env_locs_Union, reach'_Union.
        eapply Included_trans.
        eapply reach'_set_monotonic. eapply env_locs_set_Inlcuded'.
        rewrite reach'_Union.
        eapply Included_Union_compat; [| reflexivity ].
        rewrite (reach_unfold H (env_locs rho [set y])).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic.
        rewrite env_locs_Singleton; try eassumption.
        simpl. rewrite post_Singleton; try eassumption.
        simpl.
        eapply In_Union_list. eapply in_map.
        eapply nthN_In; eassumption.
      + do 3 eexists. split; eauto. split; eauto.
        econstructor; eauto.
    - specialize (IHHctx b H1' (def_funs B B rho1') e).
      edestruct IHHctx as [H1'' [rho1'' [b' [Heq' [Hinj' Hres]]]]].
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply Included_trans.
        eapply def_funs_env_loc. simpl. 
        normalize_occurs_free...
      + eapply Included_trans; [| eassumption ].
        eapply Included_trans.
        eapply def_funs_env_loc. simpl. 
        normalize_occurs_free...
      + eapply heap_env_equiv_def_funs'. 
        eapply heap_env_equiv_antimon. eassumption.
        simpl. normalize_occurs_free...
      + eapply injective_subdomain_antimon.
        eassumption.
        eapply reach'_set_monotonic. eapply Included_trans.
        eapply def_funs_env_loc. simpl. 
        normalize_occurs_free...
      + do 3 eexists. split; eauto. split; eauto.
        econstructor; eauto.
  Qed. 

  Lemma ctx_to_heap_env_cost C H1 rho1 H2 rho2 c :
    ctx_to_heap_env C H1 rho1 H2 rho2 c ->
    c = cost_ctx_full C.
  Proof.
    intros Hctx. induction Hctx; simpl; eauto; omega.
  Qed.
  
  Lemma ctx_to_heap_env_CC_cost C H1 rho1 H2 rho2 c :
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 c ->
    c = cost_ctx_full C.
  Proof.
    intros Hctx. induction Hctx; simpl; eauto; omega.
  Qed.

  
End SpaceSem.
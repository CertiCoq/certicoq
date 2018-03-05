(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps ctx cps_util eval List_util Ensembles_util functions
        identifiers Heap.heap Heap.heap_defs Heap.heap_equiv tactics.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Module SpaceSem (H : Heap).
  
  Module Equiv := HeapEquiv H.
  
  Context (cloTag : cTag).

  Import H Equiv.Defs Equiv.Defs.HL Equiv.

  Fixpoint def_funs (B B0 : fundefs) rho :=
    match B with
      | Fcons f _ _ _ B =>
        M.set f (FunPtr B0 f) (def_funs B B0 rho)
      | Fnil => rho
    end.

  (* The cost of evaluating the head constructor before CC *)
  Definition cost (H : heap block) (rho : env) (e : exp) : nat :=
    match e with
      | Econstr x t ys e => 1 + length ys
      | Ecase y cl => 1 
      | Eproj x t n y e => 1
      | Efun B e => 1
      | Eapp f t ys => 1 + length ys
        (* match M.get f rho with *)
        (*   | Some (Loc l1) => *)
        (*     match get l1 H with *)
        (*       | Some (Clos (FunPtr B g) (Loc env_loc)) => *)
        (*         match get env_loc H, find_def g B, getlist ys rho with *)
        (*           | Some (Env rho_clo), Some (t, xs, e), Some vs => *)
        (*             let '(H', rho_clo1) := def_closures B B rho_clo H env_loc in  *)
        (*             match setlist xs vs rho_clo1 with *)
        (*               | Some rho_clo2 =>  *)
        (*                 1 + length ys + size_reachable (env_locs rho_clo2 (occurs_free e)) H *)
        (*               | _ => 0 *)
        (*             end *)
        (*           | _,_ , _  => 0 *)
        (*         end *)
        (*       | _ => 0 *)
        (*     end *)
        (*   | Some (FunPtr B g) => *)
        (*     match find_def g B,  getlist ys rho with *)
        (*       | Some (ct, xs, e), Some vs => *)
        (*         match setlist xs vs (def_funs B B (M.empty _)) with *)
        (*           | Some rho_clo =>  *)
        (*             1 + length ys + size_reachable (env_locs rho_clo (occurs_free e)) H *)
        (*           | None => 0 *)
        (*         end *)
        (*       | _, _ => 0 *)
        (*     end *)
        (*   | None => 0 *)
        (* end *)
      | Eprim x p ys e => 1 + length ys
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
        (Hcost : c < cost H rho e) 
        (Hsize : size_heap H = m),
        (big_step_GC H rho e OOT c m)
  | Eval_constr_gc :
      forall (H H' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys : list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost H rho (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
                
        (Hbs : big_step_GC H' (M.set x (Loc l) rho) e r (c - cost H rho (Econstr x t ys e)) m),

        big_step_GC H rho (Econstr x t ys e) r c m
  | Eval_proj_gc : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost H rho (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)
        
        (Hbs : big_step_GC H (M.set x v rho) e r (c - cost H rho (Eproj x t n y e)) m),
        
        big_step_GC H rho (Eproj x t n y e) r c m
  | Eval_case_gc :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost H rho (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)
        
        (Hbs : big_step_GC H rho e r (c - cost H rho (Ecase y cl)) m),
        
        big_step_GC H rho (Ecase y cl) r c m
  | Eval_fun_gc :
      forall (H H' H'' : heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost H rho (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (fundefs_fv B) rho = rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' env_loc = (H'', rho'))
        
        (Hbs : big_step_GC H'' rho' e r (c - cost H rho (Efun B e)) m),

        big_step_GC H rho (Efun B e) r c m
    
  | Eval_app_gc :
      forall (H H' H'' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost H rho (Eapp f t ys))
        (Hgetf : M.get f rho = Some (Loc l))
        (* Look up the closure *)
        (Hgetl : get l H = Some (Clos (FunPtr B f') (Loc env_loc)))
        (* Look up the closure environment *)
        (Hget_env : get env_loc H = Some (Env rho_clo))
        (* Find the code *)
        (Hfind : find_def f' B = Some (t, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (* Allocate mutually defined closures *)
        (Hredef : def_closures B B rho_clo H env_loc = (H', rho_clo1))
        (Hset : setlist xs vs rho_clo1 = Some rho_clo2)
        
        (* collect H' *)
        (Hgc : live ((env_locs rho_clo2) (occurs_free e)) H' H'')
        (Hsize : size_heap H' = m')
        
        (Hbs : big_step_GC H'' rho_clo2 e r (c - cost H rho (Eapp f t ys)) m),
        big_step_GC H rho (Eapp f t ys) r c (max m m')
  | Eval_halt_gc :
      forall H rho x l c m
        (Hcost : c >= cost H rho (Ehalt x))
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
        (Hcost : c < cost H rho e) 
        (Hsize : size_heap H = m),
        (big_step_GC_cc H rho e OOT c m)
  | Eval_constr_per_cc :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost H rho (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
              
        (Hbs : big_step_GC_cc H' (M.set x (Loc l) rho) e r (c - cost H rho (Econstr x t ys e)) m),

        big_step_GC_cc H rho (Econstr x t ys e) r c m
  | Eval_proj_per_cc : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost H rho (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)

        (Hbs : big_step_GC_cc H (M.set x v rho) e r (c - cost H rho (Eproj x t n y e)) m),
        
        big_step_GC_cc H rho (Eproj x t n y e) r c m
  | Eval_case_per_cc :
      forall (H H' : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost H rho (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)


        (Hbs : big_step_GC_cc H' rho e r (c - cost H rho (Ecase y cl)) m),
        
        big_step_GC_cc H rho (Ecase y cl) r c m
  | Eval_fun_per_cc :
      forall (H : heap block) (rho rho' : env) (B : fundefs)
        (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost H rho (Efun B e))
        (* add the functions in the environment *)
        (Hfuns : def_funs B B rho = rho')
        
        (Hbs : big_step_GC_cc H rho' e r (c - cost H rho (Efun B e)) m),
        
        big_step_GC_cc H rho (Efun B e) r c m
  | Eval_app_per_cc :
      forall (H H' : heap block) (rho rho_clo : env) (B : fundefs)
        (f f' : var) (ct : cTag) (xs : list var) (e : exp)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost H rho (Eapp f ct ys))
        (Hgetf : M.get f rho = Some (FunPtr B f'))
        (* Find the code *)
        (Hfind : find_def f' B = Some (ct, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (Hset : setlist xs vs (def_funs B B (M.empty _)) = Some rho_clo)
        
        (* collect H' *)
        (Hgc : live' ((env_locs rho_clo) (occurs_free e)) H H')
        (Hsize : size_heap H = m')
        
        (Hbs : big_step_GC_cc H' rho_clo e r (c - cost H rho (Eapp f ct ys)) m),
        big_step_GC_cc H rho (Eapp f ct ys) r c (max m m')
  | Eval_halt_per_cc :
      forall H rho x l c m
        (Hcost : c >= cost H rho (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC_cc H rho (Ehalt x) (Res (l, H)) c m.
  

  Definition is_res (r : ans) : Prop :=
    match r with
      | Res _ =>  True
      | _ => False
    end.
  
  (* TODO move *)
  Definition reach_ans (a : ans) : Ensemble loc :=
    match a with
      | Res r => reach_res r
      | OOT => Empty_set _
      | OOM => Empty_set _
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

  Fixpoint costCC_ctx_full (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + costCC_ctx_full c
      | Eproj_c x t n y c => 1 + costCC_ctx_full c
      | Efun1_c B c => 1 + costCC_ctx_full c
      | Eprim_c x p ys c => 1 + length ys + costCC_ctx_full c
      | Hole_c => 0
      | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
      | Ecase_c _ _ _ _ _ => 0
    end.
  
  Fixpoint costCC_ctx (c : exp_ctx) : nat :=
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
        
        ctx_to_heap_env (Econstr_c x t ys C) H rho H'' rho' (c + costCC_ctx (Econstr_c x t ys C))

  | Eproj_c_to_rho :
      forall H H' rho rho' x N t y C vs v t' l c,
        
        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t' vs) ->
        nthN vs N = Some v ->
        
        ctx_to_heap_env C H (M.set x v rho)  H' rho'  c -> 
        
        ctx_to_heap_env (Eproj_c x t N y C) H rho H' rho' (c + costCC_ctx (Eproj_c x t N y C)).
  

  (** Allocation cost of an evaluation context *)
  Fixpoint cost_alloc_ctx (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + cost_alloc_ctx c
      | Eproj_c x t n y c => cost_alloc_ctx c
      (* not relevant *)
      | Efun1_c B c => cost_alloc_ctx c
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

    (** * Lemmas about [ctx_to_heap_env] *)

  Lemma ctx_to_heap_env_comp_ctx_f_r C1 C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 :
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m1 ->
    ctx_to_heap_env C2 H2 rho2 H3 rho3 m2 ->
    ctx_to_heap_env (comp_ctx_f C1 C2) H1 rho1 H3 rho3 (m1 + m2).
  Proof.
    revert C2 rho1 H1 m1 rho2 H2 m2 rho3 H3.
    induction C1; intros C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - replace (c0 + costCC_ctx (Econstr_c v c l C1) + m2) with (c0 + m2 + costCC_ctx (Econstr_c v c l C1)) by omega.
      simpl. econstructor; eauto. 
    - replace (c0 + costCC_ctx (Eproj_c v c n v0 C1) + m2) with (c0 + m2 + costCC_ctx (Eproj_c v c n v0 C1)) by omega.
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
  Qed.  
  

End SpaceSem.
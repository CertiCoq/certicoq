(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
     MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
     Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From CertiCoq.L6 Require Import cps ctx cps_util eval List_util Ensembles_util functions
     identifiers Heap.heap Heap.heap_defs Heap.heap_equiv Heap.GC tactics set_util map_util.
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
    | Efun B e => 1 + PS.cardinal (fundefs_fv B)
    | Eapp f t ys => 1 + length ys
    | Eprim x p ys e => 0
    | Ehalt x => 1
    end.

  (* The cost of evaluating the head constructor after CC *)
  Definition cost_cc (e : exp) : nat :=
    match e with
    | Econstr x t ys e => 1 + length ys
    | Ecase y cl => 1 
    | Eproj x t n y e => 1
    | Efun B e => 1
    | Eapp f t ys => 1 + length ys
    | Eprim x p ys e => 0
    | Ehalt x => 1
    end.

  
  (** Deterministic semantics with garbage collection upon function entry. *)
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
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag)
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


  Definition reach_size (H : heap block) (rho : env) (e : exp) :=
    size_reachable (env_locs rho (occurs_free e)) H. 

  (** Deterministic semantics with reachable space profiling *)
  Inductive big_step :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* Upper bound for the number of the evaluation steps  *)
    nat -> (* The maximum amount of reachable space during execution *)
    Prop :=
  | Eval_oot :
      forall (H : heap block) (rho : env) (e : exp) (c m : nat)
        (Hcost : c < cost e), 
        big_step H rho e OOT c (reach_size H rho e)
  | Eval_constr :
      forall (H H' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys : list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
        
        (Hbs : big_step H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),
        
        big_step H rho (Econstr x t ys e) r c (max (reach_size H rho (Econstr x t ys e)) m)
  | Eval_proj : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)
        
        (Hbs : big_step H (M.set x v rho) e r (c - cost (Eproj x t n y e)) m),
        
        big_step H rho (Eproj x t n y e) r c (max (reach_size H rho (Eproj x t n y e)) m)
  | Eval_case :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)
        
        (Hbs : big_step H rho e r (c - cost (Ecase y cl)) m),
        
        big_step H rho (Ecase y cl) r c (max (reach_size H rho (Ecase y cl)) m)
  | Eval_fun :
      forall (H H' H'' : heap block) (rho rho_clo rho' : env) lenv (B : fundefs)
        (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (fundefs_fv B) rho = rho_clo)
        (Ha : alloc (Env rho_clo) H = (lenv, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' (Loc lenv) = (H'', rho'))
        
        (Hbs : big_step H'' rho' e r (c - cost (Efun B e)) m),

        big_step H rho (Efun B e) r c (max (reach_size H rho (Efun B e)) m)
  | Eval_app :
      forall (H H' : heap block) lenv (rho_clo rho rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l : loc)
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
        
        (Hbs : big_step H' rho_clo2
                        e r (c - cost (Eapp f t ys)) m),
        big_step H rho (Eapp f t ys) r c (max (reach_size H rho (Eapp f t ys)) m)
  | Eval_halt :
      forall H rho x l c
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l),
        big_step H rho (Ehalt x) (Res (l, H)) c (reach_size H rho (Ehalt x)).


  (** Deterministic semantics with garbage collection, for closure converted code
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
        (Hcost : c < cost_cc e) 
        (Hsize : size_heap H = m),
        (big_step_GC_cc H rho e OOT c m)
  | Eval_constr_per_cc :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost_cc (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
        
        (Hbs : big_step_GC_cc H' (M.set x (Loc l) rho) e r (c - cost_cc (Econstr x t ys e)) m),

        big_step_GC_cc H rho (Econstr x t ys e) r c m
  | Eval_proj_per_cc : (* XXX Tag annotation in projections is redundant in this semantics *)
      forall (H : heap block) (rho : env) (x : var) (t t' : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost_cc (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t' vs))
        (Hnth : nthN vs n = Some v)

        (Hbs : big_step_GC_cc H (M.set x v rho) e r (c - cost_cc (Eproj x t n y e)) m),
        
        big_step_GC_cc H rho (Eproj x t n y e) r c m
  | Eval_case_per_cc :
      forall (H H' : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost_cc (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)


        (Hbs : big_step_GC_cc H' rho e r (c - cost_cc (Ecase y cl)) m),
        
        big_step_GC_cc H rho (Ecase y cl) r c m
  | Eval_fun_per_cc :
      forall (H : heap block) (rho rho' : env) (B : fundefs)
        (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost_cc (Efun B e))
        (* add the functions in the environment *)
        (Hfuns : def_funs B B rho = rho')
        
        (Hbs : big_step_GC_cc H rho' e r (c - cost_cc (Efun B e)) m),
        
        big_step_GC_cc H rho (Efun B e) r c m
  | Eval_app_per_cc :
      forall (H H' : heap block) (rho rho_clo : env) (B : fundefs)
        (f f' : var) (ct : cTag) (xs : list var) (e : exp) b
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost_cc (Eapp f ct ys))
        (Hgetf : M.get f rho = Some (FunPtr B f'))
        (* Find the code *)
        (Hfind : find_def f' B = Some (ct, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (Hset : setlist xs vs (def_funs B B (M.empty _)) = Some rho_clo)
        
        (* collect H' *)
        (Hgc : live' ((env_locs rho_clo) (occurs_free e)) H H' b)
        (Hsize : size_heap H = m')
        
        (Hbs : big_step_GC_cc H' (subst_env b rho_clo) e r (c - cost_cc (Eapp f ct ys)) m),
        big_step_GC_cc H rho (Eapp f ct ys) r c (max m m')
  | Eval_halt_per_cc :
      forall H rho x l c m
        (Hcost : c >= cost_cc (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC_cc H rho (Ehalt x) (Res (l, H)) c m.

  Definition is_res (r : ans) : Prop :=
    match r with
    | Res _ =>  True
    | _ => False
    end.

  (* not used *) 
  Lemma big_step_gc_heap_env_equiv_l H1 H2 β rho1 rho2 e (r : ans) c m :
    big_step_GC H1 rho1 e r c m ->
    (occurs_free e) |- (H1, rho1) ⩪_(β, id) (H2, rho2) ->
    injective_subdomain (reach' H1 (env_locs rho1 (occurs_free e))) β -> 
    (exists r' m' β', big_step_GC H2 rho2 e r' c m' /\
                 injective_subdomain (reach_ans r') β' /\
                 ans_equiv β' r id r').
  Abort.

  Lemma heap_env_equiv_preserves_closed S H1 H2 rho1 rho2 b1 b2 :
    S |- (H1, rho1) ⩪_(b1, b2) (H2, rho2) ->
        closed (reach' H1 (env_locs rho1 S)) H1 ->
        closed (reach' H2 (env_locs rho2 S)) H2. 
  Proof.
    intros Heq Hclo.
    eapply reach'_closed. 
    - eapply well_formed_respects_heap_env_equiv. 
      eapply well_formed'_closed. eassumption.
      eassumption. 
    - eapply env_locs_in_dom. eassumption.
      eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
      eassumption. 
  Qed.

  (* TODO move *) 
  Lemma heap_env_approx_inverse_subdomain_l
        (S : Ensemble var) (b1 b2 b2' : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H2 (env_locs rho2 S)) b2 b2' -> 
    heap_env_approx S (b1, (H1, rho1)) (b2, (H2, rho2)) ->
    heap_env_approx S (b2' ∘ b1, (H1, rho1)) (id, (H2, rho2)). 
  Proof.
    intros Hinv Heq x v Hin Hget. 
    edestruct Heq as [l' [Hget2 Heq2]]. eassumption. eassumption.
    eexists. split. eassumption.
    symmetry in Heq2. 
    eapply res_equiv_inverse_subdomain in Heq2. 
    symmetry in Heq2. eassumption. 
    eapply inverse_subdomain_antimon. 
    eassumption. eapply reach'_set_monotonic.
    eapply get_In_env_locs; eassumption.
  Qed.
  
  Lemma heap_env_approx_inverse_subdomain_r
        (S : Ensemble var) (b1 b1' b2 : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H1 (env_locs rho1 S)) b1 b1' -> 
    heap_env_approx S (b1, (H1, rho1)) (b2, (H2, rho2)) ->
    heap_env_approx S (id, (H1, rho1)) (b1' ∘ b2, (H2, rho2)). 
  Proof.
    intros Hinv Heq x v Hin Hget. 
    edestruct Heq as [l' [Hget2 Heq2]]. eassumption. eassumption.
    eexists. split. eassumption.
    eapply res_equiv_inverse_subdomain in Heq2. 
    eassumption. 
    eapply inverse_subdomain_antimon. 
    eassumption. eapply reach'_set_monotonic.
    eapply get_In_env_locs; eassumption.
  Qed.
  
  Lemma heap_env_equiv_inverse_subdomain
        (S : Ensemble var) (b1 b2 b2' : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H2 (env_locs rho2 S)) b2 b2' -> 
    S |- (H1, rho1) ⩪_(b1, b2) (H2, rho2) ->
        S |- (H1, rho1) ⩪_(b2' ∘ b1, id) (H2, rho2). 
  Proof.
    intros Hinv [Heq1 Heq2]. split.
    eapply heap_env_approx_inverse_subdomain_l; eassumption.
    eapply heap_env_approx_inverse_subdomain_r; eassumption. 
  Qed.

  Lemma inverse_subdomain_symm A B S (f1 : A -> B) (f2 : B -> A) :
    inverse_subdomain S f1 f2 ->
    inverse_subdomain (image f1 S) f2 f1. 
  Proof.
    intros [Hin1 Hin2]. split. 
    rewrite <- image_compose.
    rewrite image_f_eq_subdomain; [| eassumption ].
    rewrite image_id. eassumption. eassumption.
  Qed.

  Lemma heap_env_equiv_def_funs_strong_left S {Hs : ToMSet S} b1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    well_formed (reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) H1 ->
    env_locs rho1 (S \\ (name_in_fundefs B)) \subset dom H1 ->
    
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->

    env_locs clo_rho1 (Full_set _) \subset (reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) ->
    env_locs clo_rho2 (Full_set _) \subset (reach' H2 (env_locs rho2 (S \\ (name_in_fundefs B)))) ->

    (occurs_free_fundefs B0) \subset (S \\ (name_in_fundefs B)) ->

    (Loc l1, H1) ≈_(b1, id) (Loc l2, H2) ->

    injective_subdomain (l1 |: reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) b1 ->

    S \\ (name_in_fundefs B) |- (H1, rho1) ⩪_(b1, id) (H2, rho2) ->

    (exists b1', S |- (def_closures B B0 rho1 H1 (Loc l1)) ⩪_(b1', id) (def_closures B B0 rho2 H2 (Loc l2)) /\
            (* f_eq_subdomain (dom H1) b1 b1' /\ *)
            let '(H1', rho1') := (def_closures B B0 rho1 H1 (Loc l1)) in
            let '(H2', rho2') := (def_closures B B0 rho2 H2 (Loc l2)) in
            well_formed (reach' H1' (env_locs rho1' S)) H1' /\
            well_formed (reach' H2' (env_locs rho2' S)) H2' /\
            env_locs rho1' S \subset dom H1' /\
            env_locs rho2' S \subset dom H2' /\
            injective_subdomain (l1 |: reach' H1' (env_locs rho1' S)) b1').
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Hl1 Hg1 Hg2 Hr1 Hr2 Hsub Heq Hinj Heqenv. 
    edestruct inverse_exists with (b := b1) as [d [Hinji Hinvi]]; [| eassumption |]. 
    now tci.
    
    edestruct heap_env_equiv_def_funs_strong as (b1' & Hequiv' & Hfeq1' & Hlet ). 
    - eassumption.
    - eapply well_formed_respects_heap_env_equiv. eassumption.
      eassumption.
    - eassumption.
    - eapply env_locs_in_dom. eassumption. eassumption.
    - eassumption.
    - eassumption.
    - eassumption.
    - eassumption.
    - eassumption. 
    - eapply res_equiv_inverse_subdomain; [| eassumption ].
      eapply inverse_subdomain_antimon. eassumption.
      simpl. rewrite (reach_unfold H1 [set l1]).
      simpl. rewrite post_Singleton; eauto. eapply Included_Union_compat.
      reflexivity.
      simpl. rewrite (reach'_idempotent H1 (env_locs rho1 _)). eapply reach'_set_monotonic. 
      eassumption.
    - rewrite compose_id_neut_r.
      eapply injective_subdomain_antimon. eassumption.
      rewrite image_Union, image_Singleton. eapply Included_Union_compat.

      rewrite res_equiv_eq in Heq. destruct Heq as [Heq _].
      unfold id in *. subst. reflexivity. 

      rewrite heap_env_equiv_image_reach; [| eassumption ]. 
      rewrite image_id. reflexivity. 

    - rewrite compose_id_neut_r.
      symmetry in Heqenv.
      eapply heap_env_equiv_inverse_subdomain in Heqenv; [| eapply inverse_subdomain_antimon; try eassumption ].
      symmetry in Heqenv. eassumption. now eauto with Ensembles_DB.
    - destruct (def_closures B B0 rho1 H1 (Loc l1)) as [H1' rho1'] eqn:Hdefs1.
      destruct (def_closures B B0 rho2 H2 (Loc l2)) as [H2' rho2'] eqn:Hdefs2.
      destruct Hlet as (Hwf1' & Hwf2' & Hl1' & Hl2' & Hinjd).
      
      edestruct inverse_exists with (b := b1') as [d' [Hinji' Hinvi']]; [| eassumption |]. 
      now tci.

      eexists d'. split; [| split; [| split; [| split; [| split ]]]]. 
      
      + eapply heap_env_equiv_inverse_subdomain in Hequiv'. 
        rewrite compose_id_neut_r in Hequiv'. eassumption. 
        eapply inverse_subdomain_antimon; [ eassumption |]... 

      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eapply injective_subdomain_antimon. eassumption.
        rewrite image_Union, image_Singleton. eapply Included_Union_compat.
        
        rewrite res_equiv_eq in Heq. destruct Heq as [Heq _].
        unfold id in *. subst. eapply Singleton_Included.
        destruct Hinvi as [Hfeq1 Hfeq2]. rewrite <- Hfeq1'.
        unfold compose; simpl.
        replace (d (b1 l1)) with ((d ∘ b1) l1). 
        rewrite Hfeq2. reflexivity. now left.
        reflexivity. 
        now eexists; eauto. 
        rewrite <- heap_env_equiv_image_reach; [| eassumption ]. 
        rewrite image_id. reflexivity. 
  Qed.


  Lemma heap_env_equiv_def_funs_strong_left_alt S {Hs : ToMSet S} b1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    well_formed (reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) H1 ->
    env_locs rho1 (S \\ (name_in_fundefs B)) \subset dom H1 ->
    
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->

    env_locs clo_rho1 (Full_set _) \subset dom H1 ->
    env_locs clo_rho2 (Full_set _) \subset dom H2 ->

    (occurs_free_fundefs B0) \subset (S \\ (name_in_fundefs B)) ->

    (Loc l1, H1) ≈_(b1, id) (Loc l2, H2) ->

    injective_subdomain (l1 |: reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) b1 ->

    S \\ (name_in_fundefs B) |- (H1, rho1) ⩪_(b1, id) (H2, rho2) ->

   (exists b1', S |- (def_closures B B0 rho1 H1 (Loc l1)) ⩪_(b1', id) (def_closures B B0 rho2 H2 (Loc l2)) /\
           let '(H1', rho1') := (def_closures B B0 rho1 H1 (Loc l1)) in
           let '(H2', rho2') := (def_closures B B0 rho2 H2 (Loc l2)) in
           f_eq_subdomain (dom H1) b1 b1' /\
           well_formed (reach' H1' (env_locs rho1' S)) H1' /\
           well_formed (reach' H2' (env_locs rho2' S)) H2' /\
           env_locs rho1' S \subset dom H1' /\
           env_locs rho2' S \subset dom H2' /\
           injective_subdomain (l1 |: reach' H1' (env_locs rho1' S)) b1').
  Proof with (now eauto with Ensembles_DB).
  Admitted.
  
  
  Lemma big_step_gc_heap_env_equiv_r H1 H2 b1 rho1 rho2 e (r : ans) c m :
    closed (reach' H1 (env_locs rho1 (occurs_free e))) H1 ->
    big_step_GC H1 rho1 e r c m ->
    (occurs_free e) |- (H1, rho1) ⩪_(b1, id) (H2, rho2) ->
                      injective_subdomain (reach' H1 (env_locs rho1 (occurs_free e))) b1 ->
                      (exists r' m' b1' b2', big_step_GC H2 rho2 e r' c m' /\
                                        injective_subdomain (reach_ans r) b1' /\
                                        injective_subdomain (reach_ans r') b2' /\
                                        ans_equiv b1' r b2' r').
  Proof with (now eauto with Ensembles_DB).
    revert H1 H2 b1 rho1 rho2 e r m.
    induction c as [k IHk] using lt_wf_rec1.  
    intros H1 H2 b1 rho1 rho2 e r m Hclo Hbs Heq Hinj1.
    destruct Hbs; subst.
    - (* case OOT *)
      eexists OOT. eexists. eexists id, id.
      repeat split; eauto. 
      econstructor. eassumption. reflexivity.
      now eapply injective_subdomain_Empty_set. 
      now eapply injective_subdomain_Empty_set. 
      
    - (* case EConstr *)
      edestruct heap_env_equiv_env_getlist as [vs' [Hlst Hall]]; try eassumption.
      simpl. normalize_occurs_free...
      destruct (alloc (Constr t vs') H2) as [l2 H2'] eqn:Halloc'.
      assert (Hlt : c - cost (Econstr x t ys e) < c) by (simpl in *; omega). 
      specialize (IHk (c - cost (Econstr x t ys e)) Hlt
                      H' H2' (b1 {l ~> l2}) (M.set x (Loc l) rho)
                      (M.set x (Loc l2) rho2)).
      edestruct IHk as (r2 & m' & b1' & b2' & Hstep' & Hinj1' & Hinj2' & Hres).
      + eapply closed_set_alloc; [ | eassumption ].
        rewrite occurs_free_Econstr in Hclo. simpl.  
        rewrite env_locs_Union in Hclo.
        rewrite <- env_locs_FromList; [| eassumption ]. 
        eassumption.
      + eassumption. 
      + eapply heap_env_equiv_alloc with (b1 :=  (Constr t vs));
          [ | | | | | | | | now apply Halloc' | | ].
        * eassumption.
        * eapply heap_env_equiv_preserves_closed; eassumption.
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

          eapply well_formed'_closed. eassumption. 
          eapply Included_trans. eapply reach'_extensive.
          eapply env_locs_closed. eassumption. 
          reflexivity. reflexivity. normalize_occurs_free...
        * eassumption.
        * rewrite extend_gss. reflexivity.
        * split. reflexivity. 
          eapply Forall2_monotonic_strong; try eassumption.
          intros x1 x2 Hin1 Hin2 Heq'.
          eapply res_equiv_rename_ext. eapply Heq'.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply reachable_in_dom in Hc.
          destruct Hc as [vc Hgetc].
          erewrite alloc_fresh in Hgetc; eauto. congruence.

          eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ]. 
          eapply reach'_set_monotonic.
          normalize_occurs_free. rewrite env_locs_Union. eapply Included_Union_preserv_l.
          rewrite env_locs_FromList.
          eapply In_Union_list. eapply in_map. eassumption.
          eassumption.

          eapply Included_trans; [| eapply env_locs_closed; eassumption ]. 
          eapply Included_trans; [| eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union. eapply Included_Union_preserv_l.
          rewrite env_locs_FromList.
          eapply In_Union_list. eapply in_map. eassumption.
          eassumption.

          reflexivity. reflexivity.
      + eapply injective_subdomain_antimon.
        eapply injective_subdomain_extend. eassumption.
        
        intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].
        eapply heap_env_equiv_image_reach in Hc; try (symmetry; eassumption).
        destruct Hc as [l2' [Hin Heq2]].
        unfold id in *; subst.
        
        eapply reachable_in_dom in Hin; try eassumption. destruct Hin as [v1' Hgetv1'].
        erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.
        eapply well_formed_respects_heap_env_equiv.
        eapply well_formed'_closed. eassumption.
        eassumption.
        
        eapply env_locs_in_dom. eassumption.
        eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply reach'_extensive. 
        
        eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply occurs_free_Econstr_Included.
        eapply reach'_alloc_set; [| eassumption ]. 
        eapply Included_trans; [| eapply reach'_extensive ].
        simpl. normalize_occurs_free. rewrite env_locs_Union.
        eapply Included_Union_preserv_l. 
        rewrite env_locs_FromList. reflexivity.
        eassumption.
      + do 4 eexists. split; eauto.
        eapply Eval_constr_gc; [| | | eassumption ]; eassumption.

        
    - (* case Eproj  *)
      assert (Hgety' := Hgety). eapply Heq in Hgety; [| now constructor ].
      destruct Hgety as [l' [Hget' Heql]].
      rewrite res_equiv_eq in Heql. destruct l' as [l' |]; try contradiction.
      destruct Heql as [Hbeq Heql]. 
      simpl in Heql. unfold id in *; subst. rewrite Hgetl in Heql.
      destruct (get (b1 l) H2) eqn:Hgetl'; try contradiction.
      destruct b as [c' vs'| | ]; try contradiction.
      destruct Heql as [Heqt Hall]; subst.
      edestruct (Forall2_nthN _ vs vs' _ _ Hall Hnth) as [v' [Hnth' Hv]].

      assert (Hlt : c - cost (Eproj x t n y e)  < c) by (simpl in *; omega). 
      specialize (IHk (c - cost (Eproj x t n y e)) Hlt
                      H H2 b1  (M.set x v rho)
                      (M.set x v' rho2) e).
      edestruct IHk as (r2 & m' & b1' & b2' & Hstep' & Hinj1' & Hinj2' & Hres).
      + eapply reach'_closed.
        
        eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        rewrite (reach'_idempotent H (env_locs rho _)). eapply reach'_set_monotonic.
        eapply Included_trans. eapply env_locs_set_Inlcuded'. 
        normalize_occurs_free. rewrite env_locs_Union, reach'_Union. eapply Included_Union_compat.
        rewrite env_locs_Singleton; [| eassumption ]. simpl.
        rewrite reach_unfold. rewrite post_Singleton; [| eassumption ].
        eapply Included_Union_preserv_r. eapply Included_trans; [| eapply reach'_extensive ].
        eapply In_Union_list. eapply in_map.
        eapply nthN_In; eassumption.
        now eapply reach'_extensive. 

        eapply Included_trans; [| eapply env_locs_closed; eassumption ]. 
        eapply Included_trans. eapply env_locs_set_Inlcuded'. 
        normalize_occurs_free. rewrite env_locs_Union, reach'_Union. eapply Included_Union_compat.
        rewrite env_locs_Singleton; [| eassumption ]. simpl.
        rewrite reach_unfold. rewrite post_Singleton; [| eassumption ].
        eapply Included_Union_preserv_r. eapply Included_trans; [| eapply reach'_extensive ].
        eapply In_Union_list. eapply in_map.
        eapply nthN_In; eassumption.
        now eapply reach'_extensive.
      + eassumption. 
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
      + do 4 eexists. split; eauto.
        econstructor; eauto.

    - (* case Ecase  *)
      admit.

    - (* case Efun  *)
      destruct (alloc (Env (restrict_env (fundefs_fv B) rho2)) H2) as [lenv2 H2'] eqn:Ha'.
      destruct (def_closures B B rho2 H2' (Loc lenv2)) as [H2'' rho2'] eqn:Hdef.  

      assert (Hlocs : locs (Env (restrict_env (fundefs_fv B) rho)) \subset reach' H (env_locs rho (occurs_free (Efun B e)))).
      { simpl. eapply Included_trans. eapply restrict_env_env_locs.
        eapply restrict_env_correct. reflexivity.
        
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply env_locs_monotonic. normalize_occurs_free. eapply Included_Union_preserv_l. 
        rewrite fundefs_fv_correct. reflexivity. }
      
      
      assert (Hca : closed (reach' H' (env_locs rho (occurs_free (Efun B e)))) H').
      { rewrite reach'_alloc; [| eassumption | eassumption ].
        eapply closed_alloc'; eassumption. }
      
      assert (Heqa : (occurs_free (Efun B e)) |- (H', rho) ⩪_(b1 {lenv ~> lenv2}, id) (H2', rho2)). 
      { eapply heap_env_equiv_weaking'. now eapply Hclo. 
        eapply heap_env_equiv_preserves_closed. eassumption. eassumption.
        now eapply reach'_extensive.
        now eapply reach'_extensive. 
        eapply heap_env_equiv_rename_ext. eassumption.

        eapply f_eq_subdomain_extend_not_In_S_r. 
        intros Hc. eapply reachable_in_dom in Hc.
        destruct Hc as [vc Hgetc].
        erewrite alloc_fresh in Hgetc; eauto. congruence.
        eapply well_formed'_closed. eassumption. 
        eapply Included_trans. eapply reach'_extensive.
        eapply env_locs_closed. eassumption.  
        reflexivity. reflexivity.

        eapply HL.alloc_subheap. eassumption.
        eapply HL.alloc_subheap. eassumption. } 

      
      edestruct (heap_env_equiv_def_funs_strong_left (name_in_fundefs B :|: occurs_free (Efun B e))
                                                     (b1 {lenv ~> lenv2}) H' H2')
        as [d1 [Hequiv Hlet]]. 
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ]. 
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        now eauto with Ensembles_DB.
      + eapply Included_trans; [| eapply dom_subheap; eapply HL.alloc_subheap; eassumption ].
        eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. eapply env_locs_monotonic.
        now eauto with Ensembles_DB.
      + erewrite gas. reflexivity. eassumption. 
      + erewrite gas. reflexivity. eassumption. 
      + eapply Included_trans. eapply restrict_env_env_locs.
        eapply restrict_env_correct. reflexivity.
        
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply env_locs_monotonic. normalize_occurs_free. rewrite !Setminus_Union_distr.
        eapply Included_Union_preserv_r. eapply Included_Union_preserv_l. rewrite <- Included_Setminus_Disjoint. 
        rewrite fundefs_fv_correct. reflexivity.
        eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
      + eapply Included_trans. eapply restrict_env_env_locs.
        eapply restrict_env_correct. reflexivity.
        
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply env_locs_monotonic. normalize_occurs_free. rewrite !Setminus_Union_distr.
        eapply Included_Union_preserv_r. eapply Included_Union_preserv_l. rewrite <- Included_Setminus_Disjoint. 
        rewrite fundefs_fv_correct. reflexivity.
        eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
      + normalize_occurs_free. rewrite !Setminus_Union_distr.
        eapply Included_Union_preserv_r. eapply Included_Union_preserv_l. rewrite <- Included_Setminus_Disjoint. 
        reflexivity.
        eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
      + rewrite res_equiv_eq. split.
        rewrite extend_gss. reflexivity.
        do 2 (erewrite gas; eauto). simpl.  
        
        eapply heap_env_equiv_restrict_env.
        eassumption. normalize_occurs_free. eapply Included_Union_preserv_l. 
        now eapply fundefs_fv_correct. 
        eapply restrict_env_correct. reflexivity.
        eapply restrict_env_correct. reflexivity.
      + rewrite reach'_alloc; [| eassumption |].

        eapply injective_subdomain_extend.
        eapply injective_subdomain_antimon. eassumption. 
        eapply reach'_set_monotonic. eapply env_locs_monotonic...

        intros Hc.
        eapply image_monotonic in Hc. eapply heap_env_equiv_image_reach in Hc; try (symmetry; eassumption).
        rewrite image_id in Hc. eapply reachable_in_dom in Hc.
        destruct Hc as [vc Hgetc].
        erewrite alloc_fresh in Hgetc; eauto. congruence.

        eapply well_formed'_closed.
        eapply heap_env_equiv_preserves_closed; eassumption.

        eapply Included_trans. eapply reach'_extensive.
        eapply env_locs_closed.
        eapply heap_env_equiv_preserves_closed; eassumption.
        
        eapply Setminus_Included_preserv. eapply reach'_set_monotonic. 
        eapply env_locs_monotonic...

        simpl. 
        eapply Included_trans. eapply restrict_env_env_locs.
        eapply restrict_env_correct. reflexivity.
        
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply env_locs_monotonic. normalize_occurs_free. rewrite !Setminus_Union_distr.
        eapply Included_Union_preserv_r. eapply Included_Union_preserv_l. rewrite <- Included_Setminus_Disjoint. 
        rewrite fundefs_fv_correct. reflexivity.
        eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
      + eapply heap_env_equiv_antimon...
      + rewrite Hfuns, Hdef in Hlet.
        destruct Hlet as (Hwf1 & Hwf2 & Hl1 & Hl2 & Hinj).
        
        assert (Hlt : c - cost (Efun B e) < c) by (simpl in *; omega). 
        specialize (IHk (c - cost (Efun B e)) Hlt
                        H'' H2'' d1 rho' rho2' e). 
        edestruct IHk as (r2 & m' & b1' & b2' & Hstep' & Hinj1' & Hinj2' & Hres).
        * eapply reach'_closed.
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          normalize_occurs_free. rewrite  !Union_assoc.
          now rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances. 

          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic.
          normalize_occurs_free. rewrite !Union_assoc.
          now rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances. 
        * eassumption.  
        * rewrite Hdef, Hfuns in Hequiv.
          eapply heap_env_equiv_antimon. eassumption.
          normalize_occurs_free. rewrite !Union_assoc.
          now rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances. 
        * eapply injective_subdomain_antimon. eassumption. normalize_occurs_free. 
          eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
          eapply env_locs_monotonic.
          rewrite !Union_assoc.
          now rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances. 
        * do 4 eexists. repeat split; eauto. econstructor; eauto.

    - (* case Eapp *)
      edestruct heap_env_equiv_env_getlist as [vs' [Hlst Hall]]; try eassumption.
      simpl. normalize_occurs_free... 
      
      edestruct heap_env_equiv_env_get as [lf [Hgetf' Heqf]]. eassumption.
      eassumption. normalize_occurs_free...
      
      destruct lf as [l' |]; [| rewrite res_equiv_eq in Heqf; contradiction ].

      assert (Hlt : c - cost (Eapp f t ys) < c) by (simpl in *; omega).
      
      assert (Heqf' := Heqf). 
      rewrite res_equiv_eq in Heqf. destruct Heqf as [Hbeq Hres].
      rewrite Hgetl in Hres.
      destruct (get l' H2) as [b2 |] eqn:Hgetl'; try contradiction.
      simpl in Hres. destruct b2 as [| v1' v2' |]; try contradiction.
      destruct Hres as [Hres1 Hres2]. 
      rewrite res_equiv_eq in Hres1. destruct v1'; try contradiction. simpl in Hres1.
      destruct Hres1; subst. 
      
      rewrite res_equiv_eq in Hres2. destruct v2'; try contradiction. simpl in Hres2.
      destruct Hres2 as [Heq2 Hres2]; unfold id in *; subst.
      rewrite Hgetenv in Hres2.
      destruct (get (b1 lenv) H2) as [b2 |] eqn:Hgetenv'; try contradiction.
      destruct b2 as [| | rho_clo' ]; try contradiction. 
      
      assert (Hincl1 : env_locs rho_clo (Full_set _) \subset
                                reach' H (env_locs rho (occurs_free (Eapp f t ys)))). 
      { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
        rewrite env_locs_Singleton; eauto. simpl. eapply Included_Union_preserv_r.
        rewrite reach_unfold. eapply Included_Union_preserv_r.
        rewrite post_Singleton; eauto. simpl. rewrite Union_Empty_set_neut_l.
        rewrite reach_unfold. eapply Included_Union_preserv_r.
        rewrite post_Singleton; eauto. simpl. 
        now eapply reach'_extensive. }
      
      assert (Hincl1' : env_locs rho_clo (FromList ys :|: occurs_free_fundefs f0 \\ name_in_fundefs f0) \subset
                                 reach' H (env_locs rho (occurs_free (Eapp f t ys)))).
      { eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic... }
      
      assert (Hincl2 : env_locs rho_clo' (Full_set _) \subset
                                reach' H2 (env_locs rho2 (occurs_free (Eapp f t ys)))). 
      { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
        rewrite env_locs_Singleton; eauto. simpl. eapply Included_Union_preserv_r.
        rewrite reach_unfold. eapply Included_Union_preserv_r.
        rewrite post_Singleton; eauto. simpl. rewrite Union_Empty_set_neut_l.
        rewrite reach_unfold. eapply Included_Union_preserv_r.
        rewrite post_Singleton; eauto. simpl. 
        now eapply reach'_extensive. }
      
      edestruct (heap_env_equiv_def_funs_strong_left_alt (name_in_fundefs f0 :|: (FromList ys :|: occurs_free_fundefs f0))
                                                         b1 H H2 rho_clo rho_clo')
        as [d1 [Hequiv Hlet]]. 
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ]. 
        rewrite (reach'_idempotent H (env_locs rho _)). eapply reach'_set_monotonic.
        rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. rewrite Union_Empty_set_neut_l.
        eassumption.
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. rewrite Union_Empty_set_neut_l.        
        eassumption. 
      + eassumption.
      + eassumption.
      + eapply Included_trans; [| eapply in_dom_closed; eassumption ].
        eassumption.
      + eapply Included_trans; [| eapply in_dom_closed;
                                  eapply heap_env_equiv_preserves_closed; [| now apply Hclo ] ];
        eassumption.
      + rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. rewrite Union_Empty_set_neut_l.
        eapply Included_Union_preserv_r. rewrite <- Included_Setminus_Disjoint. reflexivity. 
        eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
      + rewrite res_equiv_eq. split.
        reflexivity. rewrite Hgetenv, Hgetenv'. simpl. eassumption.
      + eapply injective_subdomain_antimon. eassumption.
        eapply Union_Included. 
        * eapply Singleton_Included. eexists 1. split.
          now constructor.
          simpl. eexists. eexists. split.
          eapply get_In_env_locs. normalize_occurs_free. now right. 
          eassumption. reflexivity.
          split; eauto. now right.
        * rewrite (reach'_idempotent H (env_locs rho _)). eapply reach'_set_monotonic.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. rewrite Union_Empty_set_neut_l.
          eassumption.
      + eapply heap_env_equiv_antimon; [ eassumption |]...
      + rewrite Hredef in Hlet.

        destruct (def_closures f0 f0 rho_clo' H2 (Loc (b1 lenv))) as [H2' rho2'] eqn:Hredef'.
        destruct (setlist_length3 rho2' xs vs') as [rho2'' Hset'']. 
        erewrite setlist_length_eq; try eassumption. 
        eapply Forall2_length. eassumption.
        
        edestruct (live_exists' (env_locs rho2'' (occurs_free e)) H2') as [H2'' [d Hl2]]. now tci.
        destruct Hgc as [Hdom1 [Heq1 Hin1]].
        destruct Hl2 as [Hdom2 [Heq2 Hin2]]. 
        
        
        destruct Hlet as (Hfeq & Hwf1 & Hwf2 & Hl1 & Hl2 & Hinj).                  
        rewrite Hredef in Hequiv.
        
        
        assert (Hequiv' := Hequiv).
        symmetry in Hequiv. eapply heap_env_approx_heap_equiv in Hequiv.
        eapply heap_equiv_symm in Hequiv.

        assert (Himeq := heap_env_equiv_image_post_n _ _ _ _ _ _ _ 0 Hequiv').
        rewrite image_id in Himeq. simpl in Himeq.
        assert (Heqset : occurs_free e |- (H', rho_clo2) ⩪_(d1, id) (H2', rho2'')).
        { eapply heap_env_equiv_setlist; try eassumption. 
          - eapply heap_env_equiv_antimon. eassumption.
            eapply Setminus_Included_Included_Union. eapply Included_trans. 
            eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
            now eauto with Ensembles_DB.
          - eapply Forall2_monotonic_strong; [| eassumption ]. simpl.
            intros x1 x2 Hinx1 Hinx2 Hreseq. eapply res_equiv_weakening.
            now eapply Hclo. eapply heap_env_equiv_preserves_closed; [| now eapply Hclo ].
            eassumption.  
            eapply res_equiv_rename_ext. eassumption.
            eapply f_eq_subdomain_antimon; [| eassumption ].
            eapply Included_trans; [| eapply env_locs_closed; eassumption ].
            eapply reach'_set_monotonic. normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. rewrite env_locs_FromList; [| eassumption ].
            eapply In_Union_list. eapply in_map. eassumption.
            reflexivity. 

            eapply def_funs_subheap. now eauto.
            eapply def_funs_subheap. now eauto. 

            normalize_occurs_free. rewrite env_locs_Union, reach'_Union. eapply Included_Union_preserv_l. 
            rewrite env_locs_FromList; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            eapply In_Union_list. eapply in_map. eassumption. 

            normalize_occurs_free. rewrite env_locs_Union, reach'_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_FromList; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            eapply In_Union_list. eapply in_map. eassumption. }
        
        edestruct inverse_exists with (b := b) as [b' [Hdinv Hdinj]]; [| eassumption |].
        now tci.
        
        assert (Hheq : image b (env_locs rho_clo2 (occurs_free e)) |- H'' ≃_(d ∘ d1 ∘ b', id) H2'').
        { eapply heap_equiv_symm. eapply heap_equiv_compose_r with (H2 := H').
          - rewrite <- image_compose. destruct Hdinj as [Hdinj1 Hdinj2].
            rewrite image_f_eq_subdomain; [| eapply f_eq_subdomain_antimon; try eassumption; eapply reach'_extensive ].
            rewrite image_id. 
            eapply heap_equiv_compose_r. eapply heap_equiv_symm.
            eapply heap_equiv_antimon. eassumption.
            eapply heap_env_equiv_image_post_n with (n := 0) in Heqset.
            rewrite Heqset. simpl. rewrite image_id. reflexivity.
            eapply heap_equiv_symm. eapply heap_env_approx_heap_equiv_r. eassumption.
          - eapply heap_equiv_symm. eapply heap_equiv_inverse_subdomain in Heq1; [| eassumption ].
            eapply heap_equiv_symm. eassumption.  }             

        assert (Hseq := Heqset). eapply heap_env_equiv_image_post_n with (n := 0) in Hseq. 
        simpl in Hseq. rewrite image_id in Hseq. 
        assert (Hheq' := Hheq). 
        
        rewrite <- subst_env_image in Hheq'. eapply heap_env_equiv_heap_equiv_l in Hheq'.
        symmetry in Hheq'. eapply heap_env_equiv_respects_compose in Hheq'. symmetry in Hheq'. 
        specialize (IHk (c - cost (Eapp f t ys)) Hlt
                        H'' H2'' (d ∘ d1 ∘ b') (subst_env b rho_clo2) (subst_env d rho2'') e).
        
        edestruct IHk as (r2 & m' & b1' & b2' & Hstep' & Hinj1' & Hinj2' & Hres).
        * eapply heap_equiv_preserves_closed in Heq1.
          rewrite <- subst_env_image in Heq1. eassumption. 
          
          assert (Hsub : reach' H (Union_list (map val_loc vs)) \subset reach' H (env_locs rho (occurs_free (Eapp f t ys)))). 
          { eapply reach'_set_monotonic. normalize_occurs_free. rewrite <- env_locs_FromList; [| eassumption ].
            eapply env_locs_monotonic... }
          
          { eapply reach'_closed. 
            - eapply well_formed_antimon. 
              eapply Included_trans. eapply reach'_set_monotonic. 
              eapply env_locs_monotonic. 
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
              reflexivity. 
              rewrite Union_commut. eapply well_formed_reach_setlist; try eassumption.

              + eapply well_formed_antimon; [| eassumption ]. eapply reach'_set_monotonic.
                eapply env_locs_monotonic...
              + eapply well_formed_subheap.
                rewrite <- well_formed_reach_subheap_same.  
                eapply well_formed_antimon; [| eapply well_formed'_closed; now eapply Hclo ].
                eassumption. 
                eapply well_formed_antimon; [| eapply well_formed'_closed; now eapply Hclo ].
                eassumption. 

                eapply Included_trans; [| eapply env_locs_closed; now eapply Hclo ].
                eapply Included_trans; [| eassumption ]. eapply reach'_extensive.

                eapply def_funs_subheap. now eauto.

                rewrite <- well_formed_reach_subheap_same.
                eapply Included_trans; [| eapply env_locs_closed; now eapply Hclo ].
                eassumption.
                eapply well_formed_antimon; [| eapply well_formed'_closed; now eapply Hclo ]. 
                eassumption.
                eapply Included_trans; [| eapply env_locs_closed; now eapply Hclo ].
                eapply Included_trans; [| eassumption ]. eapply reach'_extensive.
                eapply def_funs_subheap. now eauto. 
                eapply def_funs_subheap. now eauto. 
            - eapply Included_trans. eapply env_locs_monotonic. 
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
              eapply Included_trans.
              rewrite Union_commut. eapply env_locs_setlist_Included. 
              eassumption.
              eapply Union_Included.
              + eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
              + eapply Included_trans; [| eapply dom_subheap; eapply def_funs_subheap; now eauto ].
                eapply Included_trans; [| eapply env_locs_closed; now eapply Hclo ].
                eapply Included_trans; [| eassumption ]. eapply reach'_extensive. }
        * eassumption. 
        * rewrite <- subst_env_image in Hheq. eapply heap_env_equiv_heap_equiv_l in Hheq.
          (* heap_env_equiv up to env_eq *)
          admit.
        * admit. 
        (* eapply injective_subdomain_compose. *)

        (* eapply heap_equiv_reach_eq in Heq1. rewrite subst_env_image. *)
        (* rewrite <- Heq1. eassumption. *)

        (* eapply injective_subdomain_compose. *)
          
        (* eapply heap_equiv_inverse_subdomain in Heq1; [| eassumption ]. *)
        (* eapply heap_equiv_symm in Heq1. *)
        (* eapply heap_equiv_reach_eq in Heq1. rewrite subst_env_image. *)
        (* rewrite Heq1.    *)
          
        (* rewrite <- image_compose. *)
        (* destruct Hdinj as [Hd1 Hd2].  *)
        (* rewrite image_f_eq_subdomain; *)
        (*   [| eapply f_eq_subdomain_antimon; try eassumption; now eapply reach'_extensive ]. *)
        (* rewrite image_id. *)
          
        (* eapply injective_subdomain_antimon; *)
        (* [| eapply reach'_set_monotonic; eapply env_locs_monotonic; *)
        (*    eapply occurs_free_in_fun; eapply find_def_correct; eassumption ]. *)
          
        (* eapply injective_subdomain_antimon; *)
        (*   [| eapply reach'_set_monotonic; rewrite Union_commut; *)
        (*      eapply env_locs_setlist_Included; eassumption ]. *)
          
        (* rewrite reach'_Union. *)
        (* rewrite Union_Included_Union_Setminus; [| | reflexivity ]; tci. *)
          

        (*   eapply injective_subdomain_Union.  *)
        (*   rewrite <- image_compose. *)
        (*   destruct Hdinj as [Hd1 Hd2].  *)
        (*   rewrite image_f_eq_subdomain; *)
        (*     [| eapply f_eq_subdomain_antimon; try eassumption; now eapply reach'_extensive ]. *)
        (*   rewrite image_id.  *)
        (*   eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic. *)
        (*   eapply occurs_free_in_fun. eapply find_def_correct. eassumption. *)
        (*   eapply Included_Union_preserv_r.  *)
          
        (*   eapply Included_trans. *)
        (*   eapply reach'_set_monotonic. rewrite Union_commut. eapply env_locs_setlist_Included. *)
        (*   eassumption.  *)
        (*   rewrite !env_locs_Union, !reach'_Union.  *)
        (*   eapply Union_Included; [ now eauto with Ensembles_DB |].  *)

        (*   eapply Union_Included; eauto with Ensembles_DB.  *)
          
        (*   rewrite (Union_commut (FromList ys) _), Union_assoc. *)
        (*   rewrite (env_locs_Union _ _ (FromList ys)). rewrite <- env_locs_FromList; [| eassumption ]. *)
        (*   eapply Included_Union_preserv_r. rewrite <- env_locs_Union. eapply Included_Union.  *)
        (*   rewrite env_locs_Union. *)
        (*   eapply Included_Union_compat. eapply env_locs_setlist_In. eassumption.  *)
        (*   reflexivity.  *)
        (*   | eassumption ].  *)
        (*   (* apply inverse lemma in Heq1, get eq  *) *)
        (*   admit. *)

        (*   eapply injective_subdomain_antimon. eassumption. *)
          
        (*   Injective_subdomain_extend. *)

        (*   admit. *)
        * do 4 eexists. split.
          eapply Eval_app_gc; try now eapply Hstep'.  eassumption. eassumption. eassumption. eassumption.
          eassumption. eassumption. eassumption. eassumption.  split; eauto. reflexivity.
          split. eassumption. split. eassumption. eassumption.
    - (* EHalt *)
      admit.
  Admitted. 

  (** * Interpretation of a context as a heap and an environment *)

  Fixpoint cost_ctx_full (c : exp_ctx) : nat :=
    match c with
    | Econstr_c x t ys c => 1 + length ys + cost_ctx_full c
    | Eproj_c x t n y c => 1 + cost_ctx_full c
    | Efun1_c B c => 1 + (PS.cardinal (fundefs_fv B)) + cost_ctx_full c
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

  Fixpoint cost_ctx_full_cc (c : exp_ctx) : nat :=
    match c with
    | Econstr_c x t ys c => 1 + length ys + cost_ctx_full_cc c
    | Eproj_c x t n y c => 1 + cost_ctx_full_cc c
    | Efun1_c B c => 1 + cost_ctx_full_cc c
    | Eprim_c x p ys c => 1 + length ys + cost_ctx_full_cc c
    | Hole_c => 0
    | Efun2_c B _ => cost_ctx_full_f_cc B
    | Ecase_c _ _ _ c _ => cost_ctx_full_cc c
    end
  with cost_ctx_full_f_cc (f : fundefs_ctx) : nat :=
         match f with
         | Fcons1_c _ _ _ c _ => cost_ctx_full_cc c
         | Fcons2_c _ _ _ _ f => cost_ctx_full_f_cc f
         end.

  Fixpoint cost_ctx (c : exp_ctx) : nat :=
    match c with
    | Econstr_c x t ys c => 1 + length ys
    | Eproj_c x t n y c => 1 
    | Efun1_c B c => 1 + PS.cardinal (fundefs_fv B)
    | Eprim_c x p ys c => 1 + length ys
    | Hole_c => 0
    | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
    | Ecase_c _ _ _ _ _ => 0
    end.

  Fixpoint cost_ctx_cc (c : exp_ctx) : nat :=
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
        
        ctx_to_heap_env_CC (Econstr_c x t ys C) H rho H'' rho' (c + cost_ctx_cc (Econstr_c x t ys C))

  | Eproj_c_to_rho_CC :
      forall H H' rho rho' x N t y C vs v t' l c,
        
        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t' vs) ->
        nthN vs N = Some v ->
        
        ctx_to_heap_env_CC C H (M.set x v rho)  H' rho'  c -> 
        
        ctx_to_heap_env_CC (Eproj_c x t N y C) H rho H' rho' (c + cost_ctx_cc (Eproj_c x t N y C))
  | Efun_c_to_rho_CC :
      forall H H' rho rho' B C c,
        ctx_to_heap_env_CC C H (def_funs B B rho) H' rho' c -> 
        ctx_to_heap_env_CC (Efun1_c B C) H rho H' rho' (c + cost_ctx_cc (Efun1_c B C)).
  

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
    | Efun1_c B c => 1 + PS.cardinal (fundefs_fv B) + 3 * (numOf_fundefs B) + cost_alloc_ctx c
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
      + rewrite (cost_ctx_full_ctx_comp_ctx_f C C'). omega.
    - destruct f; intros C'; simpl.
      + rewrite cost_ctx_full_ctx_comp_ctx_f. omega.
      + rewrite cost_ctx_full_f_comp_ctx_f. omega.
  Qed.

  Lemma def_closures_size B1 B2 rho H envc H' rho' :
    def_closures B1 B2 rho H envc = (H', rho') ->
    size_heap H' = size_heap H + 3 * numOf_fundefs B1.
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
    - replace (c0 + cost_ctx_cc (Econstr_c v c l C1) + m2) with (c0 + m2 + cost_ctx_cc (Econstr_c v c l C1)) by omega.
      simpl. econstructor; eauto. 
    - replace (c0 + cost_ctx_cc (Eproj_c v c n v0 C1) + m2) with (c0 + m2 + cost_ctx_cc (Eproj_c v c n v0 C1)) by omega.
      simpl. econstructor; eauto.
    - replace (c + cost_ctx_cc (Efun1_c f C1) + m2) with (c + m2 + cost_ctx_cc (Efun1_c f C1)) by omega.
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

  (* TODO move *)
  Lemma binding_in_map_def_closures (S : Ensemble M.elt) (rho1 rho1' : env) H1 H1' B1 B1' v :
    binding_in_map S rho1 ->
    def_closures B1 B1' rho1 H1 v = (H1', rho1') ->
    binding_in_map (name_in_fundefs B1 :|: S) rho1'.
  Proof. 
    revert H1' rho1'. induction B1; intros H2 rho2 Hbin Hclo.
    - simpl in *.
      destruct (def_closures B1 B1' rho1 H1 v) as [H' rho'] eqn:Hd.
      destruct (alloc (Clos (FunPtr B1' v0) v) H')as [l' H''] eqn:Ha. 
      inv Hclo.
      eapply binding_in_map_antimon; [|  eapply binding_in_map_set; eapply IHB1 ].
      now eauto with Ensembles_DB. 
      eassumption. reflexivity.
    - inv Hclo. simpl. eapply binding_in_map_antimon; [| eassumption ].
      eauto with Ensembles_DB.
  Qed.


  Lemma ctx_to_heap_env_size_heap C rho1 rho2 H1 H2 c :
    binding_in_map (occurs_free_ctx C) rho1 -> 
    ctx_to_heap_env C H1 rho1 H2 rho2 c ->
    size_heap H2 = size_heap H1 + cost_alloc_ctx C. 
  Proof with (now eauto with Ensembles_DB). 
    intros Hin Hctx; induction Hctx; eauto; simpl.
    - rewrite IHHctx.
      unfold size_heap. 
      erewrite (HL.size_with_measure_alloc _ _ _ H H');
        [| reflexivity | eassumption ]. 
      erewrite getlist_length_eq; [| eassumption ].   
      simpl. omega.
      eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      normalize_occurs_free_ctx.
      rewrite <- Union_assoc, <- Union_Setminus; tci...
    - rewrite IHHctx. reflexivity. 
      eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      normalize_occurs_free_ctx. 
      rewrite <- Union_assoc, <- Union_Setminus; tci...
    - rewrite IHHctx.
      
      erewrite def_closures_size; eauto. unfold size_heap.
      erewrite size_with_measure_alloc; [| reflexivity | eassumption ]. simpl.
      rewrite <- !plus_assoc. 
      f_equal. simpl. f_equal.
      f_equal.

      unfold size_env. 
      rewrite !PS.cardinal_spec. f_equal. eapply elements_eq.
      eapply Same_set_From_set. rewrite <- mset_eq.
      subst. rewrite key_set_binding_in_map_alt. reflexivity.

      eapply binding_in_map_antimon; [| eassumption ].
      rewrite <- fundefs_fv_correct. normalize_occurs_free_ctx...
      
      eapply binding_in_map_antimon;
        [| eapply binding_in_map_def_closures; eassumption ].
      
      normalize_occurs_free_ctx.
      rewrite (Union_commut _ (_ \\ _)), Union_assoc, (Union_commut _ (_ \\ _)).
      rewrite <- Union_Setminus; tci...
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
    c = cost_ctx_full_cc C.
  Proof.
    intros Hctx. induction Hctx; simpl; eauto; omega.
  Qed.

  
End SpaceSem.
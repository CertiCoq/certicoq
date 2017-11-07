(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps cps_util eval List_util Ensembles_util functions
        identifiers Heap.heap Heap.heap_defs tactics.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Module SpaceSem (H : Heap).
  
  Module Defs := HeapDefs H.

  Context (cloTag : cTag).

  Import H Defs.

  (* TODO: Collect right now assumes that the objects are not moved. Provide a different definition
     that doesn't make this assumption *)

  (* The cost of evaluating the head *)
  (* TODO make semantics parametric in the cost model *)
  Definition cost (e : exp) : nat :=
    match e with
      | Econstr x t ys e => 1 + length ys
      | Ecase y cl => 1 
      | Eproj x t n y e => 1
      | Efun B e => fundefs_num_fv B + 1 (* XXX maybe revisit *)
      | Eapp f t ys => 1 + length ys
      | Eprim x p ys e => 1 + length ys
      | Ehalt x => 1
    end.

  (* TODO move *)
  (* M utils *)
  Definition key_set {A : Type} (map : M.t A) :=
    [ set x : positive | match M.get x map with
                           | Some x => True
                           | None => False
                         end ].

  Definition sub_map {A : Type} (map1 map2 : M.t A) :=
    forall x v, M.get x map1 = Some v ->
           M.get x map2 = Some v.
  
  (** [rho'] is the restriction of [rho] in [S] *)
  Definition restrict_env (S : Ensemble var) (rho rho' : env) : Prop :=
    (forall x, x \in S -> M.get x rho = M.get x rho') /\
    sub_map rho' rho /\ key_set rho' \subset S.

   
  (** Non-deterministic semantics with garbage collection *)
  Inductive big_step :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The result of evaluation *)
    nat -> (* Upper bound for the number of the evaluation steps *)
    nat -> (* Maximum space required for the evaluation *)
    Type := (* XXX This will bite us. Change it. *)
  | Eval_oot : (* Out of time *)
      forall (H : heap block) (rho : env) (e : exp) (c m : nat)
        (Hsize : size_heap H = m)
        (Hcost : c < cost e),
        big_step H rho e OOT 0 m
  | Eval_constr :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag) (ys : list var)
        (e : exp) (vs : list value) (l : loc) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Econstr x t ys e)) 
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
        (Hbs : big_step H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),
        big_step H rho (Econstr x t ys e) r c m
  | Eval_proj :
      forall (H : heap block) (rho : env) (x : var) (t : cTag) (n : N) (y : var)
        (e : exp) (l : loc) (v : value) (vs : list value) (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs)) 
        (Hargs : nthN vs n = Some v)
        (Hbs : big_step H (M.set x v rho) e r (c - cost (Eproj x t n y e)) m),
        big_step H rho (Eproj x t n y e) r c m
  | Eval_case :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Hfind : findtag cl t = Some e)
        (Hbs : big_step H rho e r (c - cost (Ecase y cl)) m),
        big_step H rho (Ecase y cl) r c m
  | Eval_fun :
      forall (H H' H'': heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (occurs_free_fundefs B) rho rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' cloTag env_loc = (H'', rho'))
        (Hbs : big_step H'' rho' e r (c - cost (Efun B e)) m),
        big_step H rho (Efun B e) r c m
  | Eval_app :
      forall (H H' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Eapp f t ys))
        (Hgetf : M.get f rho = Some (Loc l))
        (* Look up the closure *)
        (Hgetl : get l H = Some (Constr cloTag [FunPtr B f'; Loc env_loc]))
        (* Look up the closure environment *)
        (Hget_env : get env_loc H = Some (Env rho_clo))
        (* Find the code *)
        (Hfind : find_def f' B = Some (t, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (* Allocate mutually defined closures *)
        (Hredef : def_closures B B rho_clo H cloTag env_loc = (H', rho_clo1))
        (Hset : setlist xs vs rho_clo1 = Some rho_clo2)
        (Hbs : big_step H' rho_clo2 e r (c - cost (Eapp f t ys)) m),
        big_step H rho (Eapp f t ys) r c m
  | Eval_halt :
      forall (H : heap block) (rho : env) (x : var) (v : value) (c m : nat)
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some v)
        (Heq : size_heap H = m),
        big_step H rho (Ehalt x) (Res (v, H)) c m
  | Eval_GC :
      forall (H H' : heap block) (rho : env) (e : exp) (r : ans) (c : nat) (m m' : nat)
        (* Garbage collect H *)
        (Hgc : collect (env_locs rho (occurs_free e)) H H')
        (* XXX cost model? *)
        (Hsize : H.size H' = m' -> c >= m')
        (Hbs : big_step H' rho e r (c - m') m),
        big_step H rho e r c (max m m').
  
  (** Deterministic semantics with perfect garbage collection
   * The execution time cost model does not account for the cost of GC  *)
  Inductive big_step_perfect_GC :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* Upper bound for the number of the evaluation steps  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_oot_per :
      forall (H : heap block) (rho : env) (e : exp) (c m : nat)
        (Hcost : c < cost e) 
        (Hsize : size_heap H = m),
        (big_step_perfect_GC H rho e OOT c m)
  | Eval_constr_per :
      forall (H H' H'' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m m' : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
        
        (* collect H' *)
        (Hgc : live (env_locs (M.set x (Loc l) rho) (occurs_free e)) H' H'')
        (Hsize : size_heap H' = m')
        
        (Hbs : big_step_perfect_GC H'' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),

        big_step_perfect_GC H rho (Econstr x t ys e) r c (max m m')
  | Eval_proj_per :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m m' : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Hnth : nthN vs n = Some v)

        (* collect H *)
        (Hgc : live (env_locs (M.set x v rho) (occurs_free e)) H H')
        (Hsize : size_heap H = m')

        (Hbs : big_step_perfect_GC H' (M.set x v rho) e r (c - 1) m),
        
        big_step_perfect_GC H rho (Eproj x t n y e) r c (max m m')
  | Eval_case_per :
      forall (H H' : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m m' : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)

        (* collect H *)
        (Hgc : live ((env_locs rho) (occurs_free e)) H H')
        (Hsize : size_heap H = m')

        (Hbs : big_step_perfect_GC H' rho e r (c - cost (Ecase y cl)) m),
        
        big_step_perfect_GC H rho (Ecase y cl) r c (max m m')
  | Eval_fun_per :
      forall (H H' H'' H''': heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (e : exp) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (occurs_free_fundefs B) rho rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' cloTag env_loc = (H'', rho'))

        (* collect H'' *)
        (Hgc : live (env_locs rho' (occurs_free e)) H'' H''')
        (Hsize : size_heap H'' = m')

        (Hbs : big_step_perfect_GC H''' rho' e r (c - cost (Efun B e)) m),
        big_step_perfect_GC H rho (Efun B e) r c (max m m')
    
  | Eval_app_per :
      forall (H H' H'' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Eapp f t ys))
        (Hgetf : M.get f rho = Some (Loc l))
        (* Look up the closure *)
        (Hgetl : get l H = Some (Constr cloTag [FunPtr B f'; Loc env_loc]))
        (* Look up the closure environment *)
        (Hget_env : get env_loc H = Some (Env rho_clo))
        (* Find the code *)
        (Hfind : find_def f' B = Some (t, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (* Allocate mutually defined closures *)
        (Hredef : def_closures B B rho_clo H cloTag env_loc = (H', rho_clo1))
        (Hset : setlist xs vs rho_clo1 = Some rho_clo2)
        
        (* collect H' *)
        (Hgc : live ((env_locs rho_clo2) (occurs_free e)) H' H'')
        (Hsize : size_heap H' = m')
        
        (Hbs : big_step_perfect_GC H'' rho_clo2 e r (c - cost (Eapp f t ys)) m),
        big_step_perfect_GC H rho (Eapp f t ys) r c (max m m')
  | Eval_halt_per :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_perfect_GC H rho (Ehalt x) (Res (l, H)) c m.


  Fixpoint def_funs (B B0 : fundefs) rho :=
    match B with
      | Fcons f _ _ _ B =>
        M.set f (FunPtr B0 f) (def_funs B B0 rho)
      | Fnil => rho
    end.

  (** Deterministic semantics with perfect garbage collection, for closure converted code
   * The execution time cost model does not account for the cost of GC  *)
  Inductive big_step_perfect_GC_cc :
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
        (big_step_perfect_GC_cc H rho e OOT c m)
  | Eval_constr_per_cc :
      forall (H H' H'' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m m' : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
        
        (* collect H' *)
        (Hgc : live (env_locs (M.set x (Loc l) rho) (occurs_free e)) H' H'')
        (Hsize : size_heap H' = m')
        
        (Hbs : big_step_perfect_GC_cc H'' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),

        big_step_perfect_GC_cc H rho (Econstr x t ys e) r c (max m m')
  | Eval_proj_per_cc :
      forall (H H' : heap block) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m m' : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Hnth : nthN vs n = Some v)

        (* collect H *)
        (Hgc : live (env_locs (M.set x v rho) (occurs_free e)) H H')
        (Hsize : size_heap H = m')

        (Hbs : big_step_perfect_GC_cc H' (M.set x v rho) e r (c - 1) m),
        
        big_step_perfect_GC_cc H rho (Eproj x t n y e) r c (max m m')
  | Eval_case_per_cc :
      forall (H H' : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m m' : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)

        (* collect H *)
        (Hgc : live ((env_locs rho) (occurs_free e)) H H')
        (Hsize : size_heap H = m')

        (Hbs : big_step_perfect_GC_cc H' rho e r (c - cost (Ecase y cl)) m),
        
        big_step_perfect_GC_cc H rho (Ecase y cl) r c (max m m')
  | Eval_fun_per_cc :
      forall (H H' H'' H''': heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (ct : cTag) (e : exp) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Efun B e))
        (* add the functions in the environment *)
        (Hfuns : def_funs B B rho = rho')

        (* collect H'' *)
        (Hgc : live (env_locs rho' (occurs_free e)) H H')
        (Hsize : size_heap H = m')

        (Hbs : big_step_perfect_GC_cc H' rho' e r (c - cost (Efun B e)) m),
        big_step_perfect_GC_cc H rho (Efun B e) r c (max m m')
  | Eval_app_per_cc :
      forall (H H' H'' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (ct : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Eapp f ct ys))
        (Hgetf : M.get f rho = Some (FunPtr B f'))
        (* Find the code *)
        (Hfind : find_def f' B = Some (ct, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (Hset : setlist xs vs (def_funs B B (M.empty _)) = Some rho_clo)
        
        (* collect H' *)
        (Hgc : live ((env_locs rho_clo) (occurs_free e)) H H')
        (Hsize : size_heap H = m')
        
        (Hbs : big_step_perfect_GC_cc H' rho_clo e r (c - cost (Eapp f ct ys)) m),
        big_step_perfect_GC_cc H rho (Eapp f ct ys) r c (max m m')
  | Eval_halt_per_cc :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_perfect_GC_cc H rho (Ehalt x) (Res (l, H)) c m.
  
  (** Deterministic semantics with garbage collection when needed.
   * The execution time cost model accounts for the cost of GC  *)
  Context (Hmax : nat).
  
  Inductive big_step_GC_when_needed :
    heap block -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    ans -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* Upper bound for the number of the evaluation steps  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_constr_need :
      forall (H H' : heap block) (rho rho' : env) (x : var) (t : cTag) (ys :list var)
        (e : exp) (vs : list value) (l : loc) (r : ans) (c m : nat),
        c >= cost (Econstr x t ys e) ->
        (* No GC is needed *)
        size_heap H < Hmax ->
        
        getlist ys rho = Some vs ->
        alloc (Constr t vs) H = (l, H') ->
        big_step_GC_when_needed H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m ->
        big_step_GC_when_needed H rho (Econstr x t ys e) r c m
  | Eval_proj_need :
      forall (H : heap block) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat),
        c >= cost (Eproj x t n y e) ->
        (* No GC is needed *)
        size_heap H < Hmax ->
        
        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t vs) -> 
        nthN vs n = Some v ->
        big_step_GC_when_needed H (M.set x v rho) e r (c - cost (Eproj x t n y e)) m ->
        big_step_GC_when_needed H rho (Eproj x t n y e) r c m
  | Eval_case_need :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value)
        (e : exp) (r : ans) (size c m : nat),
        c >= cost (Ecase y cl) ->
        (* No GC is needed *)
        size_heap H < Hmax ->

        M.get y rho = Some (Loc l) ->
        get l H = Some (Constr t vs) ->
        findtag cl t = Some e ->
        big_step_GC_when_needed H rho e r (c - cost (Ecase y cl)) m ->
        big_step_GC_when_needed H rho (Ecase y cl) r c m
  | Eval_fun_need :
      forall (H H' H'' : heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (cloTag : cTag) (e : exp) (r : ans) (size c m : nat)
        (Hcost: c >= cost (Efun B e))
        (* No GC is needed *)
        (Hheap : size_heap H < Hmax)
        (* find the closure environment *)
        (Hres : restrict_env (occurs_free_fundefs B) rho rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' cloTag env_loc = (H'', rho'))
        (Hbs : big_step_GC_when_needed H'' rho' e r (c - cost (Efun B e)) m),
        big_step_GC_when_needed H rho (Efun B e) r c m
  | Eval_app_need :
      forall (H H' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Eapp f t ys))
        (* No GC is needed *)
        (Hheap : size_heap H < Hmax)
        (Hgetf : M.get f rho = Some (Loc l))
        (* Look up the closure *)
        (Hgetl : get l H = Some (Constr cloTag [FunPtr B f'; Loc env_loc]))
        (* Look up the closure environment *)
        (Hget_env : get env_loc H = Some (Env rho_clo))
        (* Find the code *)
        (Hfind : find_def f' B = Some (t, xs, e))
        (* Look up the actual parameters *)
        (Hargs : getlist ys rho = Some vs)
        (* Allocate mutually defined closures *)
        (Hredef : def_closures B B rho_clo H cloTag env_loc = (H', rho_clo1))
        (Hset : setlist xs vs rho_clo1 = Some rho_clo2)
        (Hbs : big_step_GC_when_needed H' rho_clo2 e r (c - cost (Eapp f t ys)) m),
        big_step_GC_when_needed H rho (Eapp f t ys) r c m
  | Eval_halt_need :
      forall (H : heap block) (rho : env) (x : var) (v : value) (c m : nat),
        c >= cost (Ehalt x) ->
        M.get x rho = Some v ->
        size_heap H = m ->
        big_step_GC_when_needed H rho (Ehalt x) (Res (v, H)) c m
  | Eval_GC_need :
      forall (H H' : heap block) (rho : env) (e : exp) (r : ans) (c : nat) (m m' : nat),
        (* Garbage collect H *)
        live (env_locs rho (occurs_free e)) H H' ->
        size_heap H' = m' ->
        (* Collect only if it's needed *)
        Hmax <= m' ->
        c >= m' ->
        big_step_GC_when_needed H' rho e r (c - m') m ->
        big_step_GC_when_needed H rho e r c (max m m').
  
  Fixpoint noGC {Heap rho e v c m} (H : big_step Heap rho e v c m) : Prop :=
    match H with
      | Eval_oot H rho e c m Hsize Hcost => True
      | Eval_constr H H' rho x t ys e vs l r c m Hcost Hget Halloc Hbs => noGC Hbs
      | Eval_proj H rho x t n y e l v vs r c m Hcost Hgety Hgetl Hargs Hbs => noGC Hbs
      | Eval_case H rho y cl l t vs e r c m Hcost Hgety Hgetl Hfind Hbs => noGC Hbs
      | Eval_fun H H' H'' rho rho_clo rho' B env_loc e r c m Hcost Hres Halloc
                 Hfuns Hbs => noGC Hbs
      | Eval_app H H' rho rho_clo rho_clo1 rho_clo2 B f f' t xs e l env_loc vs
                 ys r c m Hcost Hgetf Hgetl Hget_env Hfind Hargs Hredef Hset Hbs => noGC Hbs
      | Eval_halt H rho x v c m Hcost Hget Heq => True
      | Eval_GC H H' rho e r c m m' Hgc Hsize Hbs => False
    end.
  
  (** Size of the [big_step] derivation *)
  Fixpoint size_big_step {Heap rho e v c m} (H : big_step Heap rho e v c m) : nat :=
    match H with
      | Eval_oot H rho e c m Hsize Hcost => 0
      | Eval_constr H H' rho x t ys e vs l r c m Hcost Hget Halloc Hbs => 1 + size_big_step Hbs
      | Eval_proj H rho x t n y e l v vs r c m Hcost Hgety Hgetl Hargs Hbs => 1 + size_big_step Hbs
      | Eval_case H rho y cl l t vs e r c m Hcost Hgety Hgetl Hfind Hbs => 1 + size_big_step Hbs
      | Eval_fun H H' H'' rho rho_clo rho' B env_loc e r c m Hcost Hres Halloc
                 Hfuns Hbs => 1 + size_big_step Hbs
      | Eval_app H H' rho rho_clo rho_clo1 rho_clo2 B f f' t xs e l env_loc vs
                 ys r c m Hcost Hgetf Hgetl Hget_env Hfind Hargs Hredef Hset Hbs => 1 + size_big_step Hbs
      | Eval_halt H rho x v c m Hcost Hget Heq => 0
      | Eval_GC H H' rho e r c m m' Hgc Hsize Hbs => S (size_big_step Hbs)
    end.

  Definition is_res (r : ans) : Prop :=
    match r with
      | Res _ =>  True
      | _ => False
    end.

  Lemma val_loc_in_dom (H1 H2 : heap block) (v1 v2 : value) :
    (v1, H1) ≈ (v2, H2) ->
    val_loc v1 \subset dom H1 ->
    val_loc v2 \subset dom H2.
  Proof.
    intros Heq Hin.
    rewrite res_equiv_eq in Heq.
    destruct v1; destruct v2; try contradiction.
    - destruct (Hin l) as [b Hb].
      reflexivity. simpl in Heq. rewrite Hb in Heq. 
      eapply Singleton_Included.
      destruct b.
      + destruct (get l0 H2) eqn:Heq'; try contradiction. 
        now eexists; eauto.
      + destruct (get l0 H2) eqn:Heq'; try contradiction. 
        now eexists; eauto.
    - simpl; now eauto with Ensembles_DB. 
  Qed.

  Lemma env_locs_in_dom S (H1 H2 : heap block) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2.
  Proof.
    intros Heq Hsub l [y [Hin Hget]].
    destruct (M.get y rho2) as [v |] eqn:Hget1; try now inv Hget.
    edestruct Heq as [_ [v' [Hget2 Heqv]]]; eauto. 
    symmetry in Heqv. eapply val_loc_in_dom; eauto.
    eapply Included_trans; [| eassumption ].
    eapply get_In_env_locs; eauto.
  Qed.     

  Lemma locs_in_dom (H1 H2 : heap block) (b1 b2 : block) :
    block_equiv (H1, b1) (H2, b2) ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2.
  Proof.
    intros Hb Hin.
    destruct b1; destruct b2; try contradiction.
    - simpl in *. destruct Hb as [Heq Hall]; subst.
      (* yikes. maybe write lemma? *)
      induction Hall; try now eauto with Ensembles_DB.
      simpl in *. eapply Union_Included.
       eapply val_loc_in_dom; eauto.
       now eapply Union_Included_l; eauto. 
       eapply IHHall. now eapply Union_Included_r; eauto.
     - simpl in *. eapply env_locs_in_dom; eauto.
  Qed.

  Lemma res_equiv_exists_loc H1 H2 v1 v2 l1 :
    (v1, H1) ≈ (v2, H2) ->
    l1 \in val_loc v1 ->
    exists l2, l2 \in val_loc v2 /\ (Loc l1, H1) ≈ (Loc l2, H2).
  Proof.
    intros Heq Hin. rewrite res_equiv_eq in Heq.
    destruct v1; destruct v2; try contradiction; inv Hin.
    eexists; split. reflexivity. rewrite res_equiv_eq.
    eassumption.
  Qed.

  Lemma heap_env_equiv_exists_loc S H1 H2 rho1 rho2 l1 :
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    l1 \in env_locs rho1 S ->
    exists l2, l2 \in env_locs rho2 S /\ (Loc l1, H1) ≈ (Loc l2, H2).
  Proof.
    intros Heq Hin. edestruct Hin as [x [Hin' Hget]].
    destruct (M.get x rho1) as [v1 |] eqn:Hget1; [| now inv Hget].
    edestruct Heq as [[v2 [Hget2 Heq']] _]; eauto.
    destruct v1; [| now inv Hget].
    destruct v2; [| rewrite res_equiv_eq in Heq'; contradiction ].
    inv Hget. eexists; split; eauto.
    eapply get_In_env_locs; eauto. reflexivity.
  Qed.

  Lemma block_equiv_exists_loc H1 H2 b1 b2 l1 :
    block_equiv (H1, b1) (H2, b2) ->
    l1 \in locs b1 ->
    exists l2, l2 \in locs b2 /\ (Loc l1, H1) ≈ (Loc l2, H2).
  Proof.
    intros Hb Hin.
    destruct b1; destruct b2; try contradiction; simpl in Hin.
    - destruct Hb as [Heq Hall]. subst. 
      induction Hall. now inv Hin.
      simpl in Hin.
      inv Hin.
      + edestruct res_equiv_exists_loc as [l2 [Hl2in Heq]]; eauto.
        eexists. split; eauto. left. eassumption.
      + edestruct IHHall as [l2 [Hl2in Heq]]; eauto.
        eexists. split; eauto. right. eassumption.
    - eapply heap_env_equiv_exists_loc; eauto.
  Qed.

  Lemma heap_equiv_post S H1 H2 l1 n b1 :
    S |- H1 ≃ H2 ->
    In _ ((post H1 ^ n) S) l1 ->
    get l1 H1 = Some b1 ->
    exists l2 b2, In _ ((post H2 ^ n) S) l2 /\ get l2 H2 = Some b2 /\
             block_equiv (H1, b1) (H2, b2).
  Proof.
    intros Heq.
    revert l1 b1. induction n as [| n IHn]; intros l1 b1 Hin Hget.
    - edestruct Heq as [[le Heq'] _]; eauto.
    - simpl in Hin. simpl.
      destruct Hin as [l1' [b1' [Hin [Hget' Hin']]]]. 
      edestruct IHn as [l2' [b2' [Hpost [Hget2 Heqb]]]]; eauto.
      simpl in Heqb.
      edestruct block_equiv_exists_loc as [l2 [Hl2in Hleq]]; eauto.
      rewrite res_equiv_eq in Hleq. simpl in Hleq. rewrite Hget in Hleq.
      destruct (get l2 H2) as [b2 |] eqn:Hgetl2; try contradiction.
      exists l2, b2. split; [| split; now eauto ].
      eexists. eexists. split; eauto.
  Qed.
   

  Lemma heap_equiv_respects_well_formed S H1 H2 :
    S |- H1 ≃ H2 ->
    well_formed (reach' H1 S) H1 ->
    well_formed (reach' H2 S) H2.
  Proof.
    intros Heq Hwf l2 b2 [n [_ Hin]] Heq2.
    symmetry in Heq. 
    edestruct heap_equiv_post as [l1 [b1 [Hpost1 [Hget1 Heq1]]]]; eauto.
    eapply Hwf in Hget1; [| eexists; split; [ now constructor | now eauto ]].
    eapply locs_in_dom; eauto. symmetry; eassumption.
  Qed.
  
  Lemma heap_equiv_in_dom S S' H1 H2 :
    S |- H1 ≃ H2 ->
    S' \subset S ->
    S' \subset dom H1 ->
    S' \subset dom H2.
  Proof.
    intros Heq Hsub Hsub1 l Hin.
    edestruct Hsub1 as [b Hget]; eauto.
    edestruct Heq as [[b' [Hget' _]] _]; eauto.
    eexists; eauto.
  Qed.

  Lemma def_closures_env_locs_in_dom S H H' rho rho' B B0 ct l :
    def_closures B B0 rho H ct l = (H', rho') ->
    env_locs rho S \subset dom H ->
    env_locs rho' (S :|: name_in_fundefs B) \subset dom H'.
  Proof.
    revert S rho rho' H H'; induction B; intros S rho rho' H H' Hdef Hsub; simpl.
    - simpl in Hdef.
      destruct (def_closures B B0 rho H ct l) as [H'' rho''] eqn:Hdef'.
      destruct (alloc _ H'') as [l' H'''] eqn:Hal. inv Hdef.
      rewrite alloc_dom; [| eassumption ].
      rewrite env_locs_set_In; [| now eauto with Ensembles_DB ].
      simpl. eapply Included_Union_compat.
      reflexivity.
      eapply Included_trans; [| eapply IHB; eassumption ].
      eapply env_locs_monotonic.
      now eauto with Ensembles_DB.
    - rewrite Union_Empty_set_neut_r. inv Hdef. eassumption.
  Qed.

  Lemma def_closures_env_reach S H H' rho rho' B B0 ct l :
    def_closures B B0 rho H ct l = (H', rho') ->
    l \in (reach' H (env_locs rho S)) ->
    l \in (reach' H' (env_locs rho' (S :|: name_in_fundefs B))).
  Proof.
    revert S rho rho' H H'; induction B; intros S rho rho' H H' Hdef Hin; simpl.
    - simpl in Hdef.
      destruct (def_closures B B0 rho H ct l) as [H'' rho''] eqn:Hdef'.
      destruct (alloc _ H'') as [l' H'''] eqn:Hal. inv Hdef.
      exists 1. split. constructor.
      exists l'. eexists. split. simpl.
      eexists v. split. right. left. reflexivity.
      rewrite M.gss. reflexivity.
      split. eapply gas; eassumption.
      simpl. right. left. reflexivity.
    - rewrite Union_Empty_set_neut_r. inv Hdef.
      eassumption.
  Qed.

  Lemma well_formed_post_n_alloc_same (S : Ensemble loc) (H H' : heap block)
        b l n :
    well_formed (reach' H S) H  ->
    S \subset dom H ->
    alloc b H = (l, H') ->
    (post H ^ n) S <--> (post H' ^ n) S.
  Proof.
    intros Hwf Hdom Hal. split; intros l' Hin.
    - revert l' Hin; induction n; simpl in *; intros l' Hin.
      + eassumption.
      + destruct Hin as [l'' [b' [Hin [Hget Hin']]]].
        eapply IHn in Hin.
        eexists. eexists. split. eassumption.
        split; [| eassumption ].
        erewrite gao; try eassumption.
        intros Heq; subst. 
        erewrite alloc_fresh in Hget; try eassumption.
        discriminate.
    - revert l' Hin; induction n; simpl in *; intros l' Hin.
      + eassumption.
      + destruct Hin as [l'' [b' [Hin [Hget Hin']]]].
        eapply IHn in Hin.
        eexists. eexists. split. eassumption.
        split; [| eassumption ].
        eapply reachable_in_dom in Hdom; [| eassumption ].
        edestruct Hdom as [b'' Hget''].
        eexists; split; [| exact Hin ]. now constructor.
        erewrite gao in Hget; try eassumption.
        intros Heq; subst.
        erewrite alloc_fresh in Hget''; try eassumption.
        discriminate.
  Qed.

  Lemma well_formed_reach_alloc_same (S : Ensemble loc) (H H' : heap block)
        b l :
    well_formed (reach' H S) H  ->
    S \subset dom H ->
    alloc b H = (l, H') ->
    reach' H S <--> reach' H' S.
  Proof.
    intros Hwf Hdom Hal. split; intros l' [n [_ Hin]].
    - eapply (well_formed_post_n_alloc_same S H H') in Hin; eauto.
      eexists; split; eauto. constructor.
    - eapply (well_formed_post_n_alloc_same S H H') in Hin; eauto.
      eexists; split; eauto. constructor.
  Qed.

  Lemma well_formed_reach_alloc_in_dom (S : Ensemble var) (H H' : heap block)
        (rho : env) (x : var) (b : block) (l : loc) :
    well_formed (reach' H (env_locs rho S)) H  ->
    env_locs rho S \subset dom H ->
    post H (locs b) \subset reach' H (env_locs rho S) ->
    alloc b H = (l, H') ->
    locs b \subset dom H ->
    well_formed (reach' H' (env_locs (M.set x (Loc l) rho) (Union _ S [set x]))) H'.
  Proof with now eauto with Ensembles_DB.
    intros Hwf Hsub Hpost Ha Hin.
    intros l1 b1 Hin1 Hget.
    destruct (loc_dec l l1); subst.
    - erewrite gas in Hget; eauto. inv Hget.
      eapply Included_trans. eassumption.
      eapply dom_subheap. eapply alloc_subheap. eassumption.
    - erewrite gao in Hget; eauto.
      rewrite env_locs_set_In in Hin1; [| now eauto with Ensembles_DB ].
      rewrite reach'_Union in Hin1.
      rewrite <- (well_formed_reach_alloc_same (env_locs _ _)) in Hin1; try eassumption.
      + inv Hin1.
        * rewrite reach_unfold in H0. inv H0.
          inv H1. contradiction.
          simpl in H1. rewrite post_Singleton in H1; [| now erewrite gas; eauto ].
          rewrite reach_unfold in H1. inv H1.
          { eapply Included_trans; [| now eapply dom_subheap; eapply alloc_subheap; eauto ].
            assert (Has : locs b1 \subset post H (locs b)).
            { intros l' Hlocs. eexists. eexists.
              split. eassumption. split. eassumption. eassumption. }
            eapply Included_trans. eassumption.
            eapply Included_trans. eassumption.
            eapply reachable_in_dom; eassumption.  }
          { assert (Heqp : post H (locs b) <--> post H' (locs b)).
            { eapply well_formed_post_n_alloc_same with (n := 1); try eassumption.
              rewrite reach_unfold. eapply well_formed_Union.
              intros l2 b2 Hin2 Hget2.
              assert (Has : locs b2 \subset post H (locs b)).
            { intros l' Hlocs. eexists. eexists.
              split. eassumption. split. eassumption. eassumption. }
            eapply Included_trans. eassumption.
            eapply Included_trans. eassumption.
            eapply reachable_in_dom; eassumption.
            eapply well_formed_antimon; [| eassumption ].
            rewrite (reach'_idempotent _ (env_locs rho S)).
            eapply reach'_set_monotonic. eassumption. }
            rewrite <- Heqp in H0.
            eapply well_formed_reach_alloc_same in H0; try eassumption.
            eapply Included_trans;
              [| now eapply dom_subheap; eapply alloc_subheap; eauto ].
            eapply Hwf; try eassumption.
            eapply reach'_idempotent. eapply reach'_set_monotonic; [| eassumption ].
            eassumption.
            eapply well_formed_antimon; [| eassumption ].
            rewrite (reach'_idempotent _ (env_locs rho S)).
            eapply reach'_set_monotonic. eassumption.
            eapply Included_trans; [| eapply reachable_in_dom ]; eauto. }
        * eapply Included_trans;
          [| now eapply dom_subheap; eapply alloc_subheap; eauto ].
          eapply Hwf; try eassumption.
          eapply reach'_set_monotonic; [| eassumption ]...
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic.
        eapply env_locs_monotonic...
      + eapply Included_trans; [| exact Hsub ].
        eapply env_locs_monotonic...
  Qed.

  Lemma restrict_env_env_locs rho rho' S :
    restrict_env S rho rho' ->
    env_locs rho' (Full_set _) \subset env_locs rho S. 
  Proof.
    intros [H1 [H2 H3]] l [x [_ H]].
    destruct (M.get x rho') eqn:Hget; try contradiction.
    exists x. split.
    eapply H3. unfold key_set, In. now rewrite Hget.
    eapply H2 in Hget. now rewrite Hget.
  Qed.    

  Lemma def_closures_post_reach
        (S : Ensemble var) (H H' : heap block) (rho rho' : env)
        (B B0 : fundefs) (ct : cTag) (l : loc) :
    def_closures B B0 rho H ct l = (H', rho') ->
    post H [set l] \subset (reach' H (env_locs rho S)) ->
    post H' [set l] \subset (reach' H' (env_locs rho' (S :|: name_in_fundefs B))).
  Proof.
    revert S rho rho' H H'; induction B; intros S rho rho' H H' Hdef Hsub; simpl.
    - simpl in Hdef.
      destruct (def_closures B B0 rho H ct l) as [H'' rho''] eqn:Hdef'.
      destruct (alloc _ H'') as [l' H'''] eqn:Hal. inv Hdef.
      intros l1 [l2 [b2 [Hin1 [Hget2 Hin2]]]]. inv Hin1. 
      exists 2. split. constructor.
      exists l2. eexists. split. simpl.
      eexists l'. eexists. split. simpl.
      eexists v. split. right. left. reflexivity.
      rewrite M.gss. reflexivity.
      split. eapply gas; eassumption.
      simpl. right. left. reflexivity.
      split; eauto.
    - rewrite Union_Empty_set_neut_r. inv Hdef.
      eassumption.
  Qed.

  Lemma well_formed_reach_alloc_def_funs S H H' rho rho' B B0 l ct rho_clo :
    well_formed (reach' H (env_locs rho S)) H ->
    env_locs rho S \subset dom H ->
    get l H = Some (Env rho_clo) ->
    env_locs rho_clo (Full_set _ ) \subset (reach' H (env_locs rho S)) ->
    def_closures B B0 rho H ct l = (H', rho') ->
    well_formed (reach' H' (env_locs rho' (Union _ S (name_in_fundefs B)))) H'.
  Proof with now eauto with Ensembles_DB.
    revert rho rho' H H'; induction B; intros rho rho' H H' Hwf Hsub Hget Hlocs Hdef; simpl.
    - simpl in Hdef.
      destruct (def_closures B B0 rho H ct l) as [H'' rho''] eqn:Hdef'.
      destruct (alloc _ H'') as [l' H'''] eqn:Hal. inv Hdef.
      rewrite (Union_commut [set v]), Union_assoc.
      eapply well_formed_reach_alloc_in_dom; [| | | eassumption |].
      + eapply IHB; eassumption.
      + eapply def_closures_env_locs_in_dom; eauto.
      + simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
        rewrite post_Singleton with (b := Env rho_clo).
        * simpl. intros l1 Hin.
          eapply def_closures_post_reach. eassumption.
          rewrite post_Singleton; eauto. simpl. eassumption.
          rewrite post_Singleton with (b := Env rho_clo).
          eassumption. eapply def_funs_subheap; eauto.
        * eapply def_funs_subheap; eauto.
      +  eapply Included_trans;
        [| now eapply dom_subheap; eapply def_funs_subheap; eauto ].
         simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
         eapply Singleton_Included. eexists; eauto.
    - inv Hdef. rewrite Union_Empty_set_neut_r. eassumption.
  Qed.

  Lemma Forall2_nthN' (A B : Type) (R : A -> B -> Prop) (l1 : list A) 
        (l2 : list B) (n : N) (v1 : A) (v2 : B):
    Forall2 R l1 l2 ->
    nthN l1 n = Some v1 ->
    nthN l2 n = Some v2 ->
    R v1 v2.
  Proof.
    intros Hall. revert n. induction Hall; intros n Hnth1 Hnth2.
    - now inv Hnth1.
    - destruct n.
      + inv Hnth1. inv Hnth2. eassumption.
      + eapply IHHall; eauto.
  Qed. 

  Lemma in_dom_closed (S : Ensemble loc) (H : heap block) :
    closed S H ->
    S \subset dom H.
  Proof. 
    intros Hc l1 Hr.
    edestruct Hc as [v2 [Hget' Hdom]]; eauto.
    repeat eexists; eauto.
  Qed.

  Lemma closed_post_n_in_S (S : Ensemble loc) (H : heap block) (n : nat) :
    closed S H ->
    (post H ^ n) S \subset S.
  Proof. 
    induction n; intros Hc l1 Hr.
    - eassumption.
    - edestruct Hr as [l2 [b [Hin1 [Hget Hin2]]]]; eauto.
      eapply IHn in Hin1; [| eassumption ].
      edestruct Hc as [b1 [Hget2 Hsub]]; try eassumption.
      subst_exp. eapply Hsub. eassumption.
  Qed.

  Lemma closed_reach_in_S (S : Ensemble loc) (H : heap block) :
    closed S H ->
    reach' H S \subset S.
  Proof. 
    intros Hc l1 Hr.
    edestruct Hr as [n [_ Hr']].
    eapply closed_post_n_in_S; eauto.
  Qed.

  Lemma res_approx_weakening_alt (S1 S2 : Ensemble loc) (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) (i : nat) :
    closed S1 H1 -> closed S2 H2 ->
    res_approx_fuel' i (v1, H1) (v2, H2) ->
    H1 ⊑ H1' -> 
    H2 ⊑ H2' ->
    (val_loc v1) \subset dom H1 ->
    (val_loc v2) \subset dom H2 ->
    post H1 (val_loc v1) \subset S1 ->
    post H2 (val_loc v2) \subset S2 ->
    res_approx_fuel' i (v1, H1') (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2.
    revert v1 v2 Heq; induction i using lt_wf_rec1;
    intros v1 v2 Heq Hdom1 Hdom2 Hpost1 Hpost2.
    destruct v1 as [ l1 | B1 f1]; destruct v2 as [ l2 | V2 f2]; try contradiction. 
    { edestruct Hdom1 as [b1 Hget1]; eauto. reflexivity.
      edestruct Hdom2 as [b2 Hget2]; eauto. reflexivity.
      specialize (Hsub1 _ _ Hget1).
      specialize (Hsub2 _ _ Hget2).
      simpl in Hget1, Hget2, Hsub1, Heq. 
      simpl.
      rewrite Hsub1. rewrite Hget1 in Heq. destruct b1.
      - edestruct Heq as [vs2 [Hgetl2 Hall]]; eauto.
        subst_exp.
        eexists; split; [ now eauto |].
        intros i' Hlt.
        eapply Forall2_monotonic_strong
        with (R :=
                fun l3 l4 =>
                  val_loc l3 \subset dom H1 ->
                  val_loc l4 \subset dom H2 -> res_approx_fuel i' (l3, H1) (l4, H2)).
        * intros v1' v2' Hin1 Hin2 Hyp.
          assert (Hinv1 : val_loc v1' \subset dom H1).
          { eapply Included_trans; [| now eapply in_dom_closed; eauto ].
            eapply Included_trans; [| eassumption ].
            simpl. rewrite post_Singleton; [| eassumption ].
            eapply In_Union_list. eapply in_map. eassumption. }
          assert (Hinv2 : val_loc v2' \subset dom H2).
          { eapply Included_trans; [| now eapply in_dom_closed; eauto ].
            eapply Included_trans; [| eassumption ].
            simpl. rewrite post_Singleton; [| eassumption ].
            eapply In_Union_list. eapply in_map. eassumption. }
          rewrite res_approx_fuel_eq. eapply H; eauto.
          rewrite <- res_approx_fuel_eq. eapply Hyp; eauto.
          eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
          eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Forall2_monotonic; [| eauto ].
          intros. eassumption.
      - edestruct Heq as [rho2 [Hgetl2 Hall]]; eauto.
        subst_exp.
        eexists; split; [ now eauto |].
        intros x.
        edestruct Hall as [[v1 [v2 [Hs1 [Hs2 Hi]]]] | Hnone]; eauto.
        left. repeat eexists; eauto. intros i' Hlt.
        rewrite res_approx_fuel_eq. eapply H; eauto.
        + rewrite <- res_approx_fuel_eq. eapply Hi. eassumption.
        + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
          eapply Included_trans; [| eassumption ].
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption. 
        + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
          eapply Included_trans; [| eassumption ].
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption.
        + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption.
        + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption. }
    { simpl in *; eassumption. }
  Qed.


  Corollary res_equiv_weakening_alt (S1 S2 : Ensemble loc) (H1 H2 H1' H2' : heap block)
            (v1 v2 : value) :
    closed S1 H1 -> closed S2 H2 ->
    (v1, H1) ≈ (v2, H2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    (val_loc v1) \subset dom H1 ->
    (val_loc v2) \subset dom H2 ->
    post H1 (val_loc v1) \subset S1 ->
    post H2 (val_loc v2) \subset S2 ->
    (v1, H1') ≈ (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2 Hp1 Hp2 Hin1 Hin2 n. destruct (Heq n) as [Heq1 He2].
    split; rewrite res_approx_fuel_eq.
    eapply (res_approx_weakening_alt S1 S2 H1 H2 H1' H2'); eauto.
    now rewrite <- res_approx_fuel_eq.
    eapply (res_approx_weakening_alt S2 S1 H2 H1 H2' H1'); eauto.
    now rewrite <- res_approx_fuel_eq. 
  Qed.


  Lemma heap_env_approx_weakening_alt S S1 S2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     post H1 (env_locs rho1 S) \subset S1 ->
     post H2 (env_locs rho2 S) \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     heap_env_approx S (H1', rho1) (H2', rho2).
   Proof.
     intros Hwf1 Hwf2 He1 He2 Hp1 Hp2 [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
     edestruct Heq1 as [x' [Hget' Heq']]; eauto.
     eexists; split; eauto.
     eapply (res_equiv_weakening_alt _ _ H1 H2); eauto.
     eapply Included_trans; [| eassumption ].
     now eapply get_In_env_locs; eauto.
     eapply Included_trans; [| eassumption ].
     now eapply get_In_env_locs; eauto.
     eapply Included_trans; [| eassumption ].
     eapply post_set_monotonic.
     now eapply get_In_env_locs; eauto.
     eapply Included_trans; [| eassumption ].
     eapply post_set_monotonic.
     now eapply get_In_env_locs; eauto.
   Qed.
   
   Corollary heap_env_equiv_weaking_alt S S1 S2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     post H1 (env_locs rho1 S) \subset S1 ->
     post H2 (env_locs rho2 S) \subset S2 ->
     S |- (H1, rho1) ⩪ (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     S |- (H1', rho1) ⩪ (H2', rho2).
   Proof.
     intros. split.
     now eapply (heap_env_approx_weakening_alt _ _ _ H1 H2); eauto.
     now eapply (heap_env_approx_weakening_alt _ _ _ H2 H1); eauto; symmetry.
   Qed.
   

  Lemma heap_env_approx_alloc_alt S S1 S2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2 ->
    post H1 (locs b1) \subset S1 ->
    post H2 (locs b2) \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    block_equiv (H1, b1) (H2, b2) ->
    heap_env_approx S (H1', M.set x (Loc l1) rho1) (H2', M.set x (Loc l2) rho2).
  Proof.
    intros Hc1 Hc2 Hsub1 Hsub2 Hl1 Hl2 Hp1 Hp2 Heq Ha1 Ha2 Hb y v1 Hin Hget.
    destruct (peq x y); subst.
    - rewrite M.gss in Hget. inv Hget.
      eexists; split. rewrite M.gss. reflexivity.
      rewrite res_equiv_eq. simpl.
      erewrite gas; eauto. erewrite gas; eauto.
      simpl in Hb. destruct b1; destruct b2; try contradiction.
      + destruct Hb as [Heq' Hall]; subst.
        split; eauto.
        eapply Forall2_monotonic_strong; eauto.
        intros. 
        eapply res_equiv_weakening_alt.
        * exact Hc1.
        * exact Hc2.
        * eassumption.
        * now eapply alloc_subheap; eauto.
        * now eapply alloc_subheap; eauto.
        * eapply Included_trans; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply post_set_monotonic.
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply post_set_monotonic.
          eapply In_Union_list. eapply in_map. eassumption.
      + simpl in *.
        eapply heap_env_equiv_weaking_alt; [ exact Hc1 | exact Hc2 | | | | | | |]; try eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
    - rewrite M.gso in Hget; eauto.
      destruct Heq as [Heq1 Heq2].
      edestruct Heq1 as [v2 [Hget2 Hb']]; eauto.
      constructor; eauto. now intros Hc; inv Hc; eauto.
      eexists.
      rewrite M.gso; eauto. split; eauto.
      eapply res_equiv_weakening_alt.
      + exact Hc1.
      + exact Hc2.
      + eassumption.
      + now eapply alloc_subheap; eauto.
      + now eapply alloc_subheap; eauto.
      + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| now apply Hsub1 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| now apply Hsub2 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        eapply Included_trans; [| now apply Hsub1 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        eapply Included_trans; [| now apply Hsub2 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
  Qed.

  Corollary heap_env_equiv_alloc_alt S S1 S2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2 ->
    post H1 (locs b1) \subset S1 ->
    post H2 (locs b2) \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪ (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    block_equiv (H1, b1) (H2, b2) ->
    S |- (H1', M.set x (Loc l1) rho1) ⩪ (H2', M.set x (Loc l2) rho2).
  Proof.
    intros. split. now eapply (heap_env_approx_alloc_alt S S1 S2); eauto.
    eapply (heap_env_approx_alloc_alt S S2 S1); eauto; symmetry; eassumption.
  Qed.

  Lemma well_formed_def_funs S1 H1 H1' rho1 rho1'  B B0 c l :
    well_formed S1 H1 ->
    l \in dom H1 ->
    (H1', rho1') = def_closures B B0 rho1 H1 c l ->
    well_formed S1 H1'.
  Proof.
    revert H1' rho1'; induction B;
    intros H1' rho1' Hc Hsub Heq; [| inv Heq; now eauto ].
    simpl in Heq. destruct (def_closures B B0 rho1 H1 c l) as [H'' rho''] eqn:Hdef.
    destruct (alloc _ H'') as [l' H'''] eqn:Heq'.
    inv Heq. eapply well_formed_alloc; [| eassumption | ]; eauto.
    simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
    eapply Singleton_Included.
    eapply dom_subheap. eapply def_funs_subheap; eauto.
    eassumption.
  Qed.


  Lemma def_funs_exists_new_set S S1 H1 H1' rho1 rho1' rho_clo B B0 c l :
    closed S1 H1 ->
    env_locs rho1 (Setminus _ S (name_in_fundefs B)) \subset S1 ->
    get l H1 = Some (Env rho_clo) ->
    env_locs rho_clo (Full_set _) \subset S1 ->
    (H1', rho1') = def_closures B B0 rho1 H1 c l ->
    exists S1', S1 \subset S1' /\ closed S1' H1' /\
           env_locs rho1' S \subset S1'.
  Proof with now eauto with Ensembles_DB.
    revert S H1' rho1'; induction B; intros S H1' rho1' Hc Henv Hget Hsub Heq.
    - simpl in Heq. destruct (def_closures B B0 rho1 H1 c l) as [H'' rho''] eqn:Hdef.
      destruct (alloc _ H'') as [l' H'''] eqn:Heq'.
      inv Heq.
      edestruct IHB as [S1' [Hsub' [Hc' Henv']]]; eauto.
      eapply Included_trans; [| now apply Henv ].
      eapply env_locs_monotonic. simpl. rewrite <- !Setminus_Union.
      reflexivity.
      eexists (l' |: (l |: S1')). split. 
      now eauto with Ensembles_DB.
      split.
      + eapply closed_alloc_Union; [| | eassumption ];
        simpl; try now eauto with Ensembles_DB.
        intros l1 Hin; inv Hin.
        * inv H. eexists.
          split. eapply def_funs_subheap; now eauto.
          eapply Included_trans. eassumption. now eauto with Ensembles_DB.
        * eapply Hc' in H. destruct H as [v' [Hgetv HsubS]].
          eexists. split; eauto.
          eapply Included_trans...
      + eapply Included_trans. now eapply env_locs_set_Inlcuded'.
        now eauto with Ensembles_DB.
    - simpl in Henv.
      rewrite Setminus_Empty_set_neut_r in Henv; inv Heq.
      eexists. split; eauto. reflexivity.
  Qed.
  
  Lemma heap_env_approx_restrict_env S S' H1 H2 rho1 rho1' rho2 rho2' :
    heap_env_approx S (H1, rho1) (H2, rho2) ->
    S' \subset S ->
    restrict_env S' rho1 rho1' ->
    restrict_env S' rho2 rho2' ->
    heap_env_approx (Full_set _) (H1, rho1') (H2, rho2').
  Proof. 
    intros Ha Hsub [Heq1 [Hsub1 Hk1]] [Heq2 [Hsub2 Hk2]] x l Hin Hget.
    edestruct Ha as [l' [Hget' Heq]].
    eapply Hsub. eapply Hk1. unfold key_set, In. now rewrite Hget; eauto.
    eapply Hsub1. eassumption.
    eexists. split; eauto.
    rewrite <- Heq2. eassumption. eapply Hk1.
    unfold key_set, In. now rewrite Hget; eauto.
  Qed.

  Corollary heap_env_equiv_restrict_env S S' H1 H2 rho1 rho1' rho2 rho2' :
    S |- (H1, rho1) ⩪ (H2, rho2) ->
    S' \subset S ->
    restrict_env S' rho1 rho1' ->
    restrict_env S' rho2 rho2' ->
    Full_set var |- (H1, rho1') ⩪ (H2, rho2').
  Proof.
    intros [? ?] ? ? ?.
    split; now eapply heap_env_approx_restrict_env; eauto.
  Qed.

  Lemma Included_post_n_reach' (H : heap block) (S : Ensemble loc) (n : nat) :
    (post H ^ n) S \subset reach' H S.
  Proof.
    intros l Hp. eexists; eauto. split; eauto. constructor.
  Qed.

  Lemma heap_env_equiv_def_funs S S1 S2 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 c l1 l2 :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S (name_in_fundefs B)) \subset S1 ->
    env_locs rho2 (Setminus _ S (name_in_fundefs B)) \subset S2 ->
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->
    env_locs clo_rho1 (Full_set _) \subset S1 ->
    env_locs clo_rho2 (Full_set _) \subset S2 ->
    (occurs_free_fundefs B0) \subset (Setminus _ S (name_in_fundefs B)) ->
    (Loc l1, H1) ≈ (Loc l2, H2) ->             
    Setminus _ S (name_in_fundefs B) |- (H1, rho1) ⩪ (H2, rho2) ->
    S |- (def_closures B B0 rho1 H1 c l1) ⩪ (def_closures B B0 rho2 H2 c l2).
  Proof with (now eauto with Ensembles_DB).
    revert S rho1 rho2; induction B;
    intros S rho1 rho2 Hc1 Hc2 Hinl1 Hinl2 He1 He2 Hg1 Hg2 Hsub Hloc Heq; simpl; eauto.
    - destruct (def_closures B B0 rho1 H1 c l1) as [H1' rho1'] eqn:Hd1.
      destruct (def_closures B B0 rho2 H2 c l2) as [H2' rho2'] eqn:Hd2.
      destruct (alloc (Constr c [FunPtr B0 v; Loc l1]) _) as [l1' H1''] eqn:Ha1.
      destruct (alloc (Constr c [FunPtr B0 v; Loc l2]) _) as [l2' H2''] eqn:Ha2.
      edestruct (def_funs_exists_new_set (S \\ [set v]) S1 H1 H1' rho1 rho1' clo_rho1 B) as [S1' [HsubS1 [Hcl1 Henv1]]]; eauto.
      eapply Included_trans; [| now apply Hinl1 ]. simpl. rewrite <- !Setminus_Union...
      edestruct (def_funs_exists_new_set (S \\ [set v]) S2 H2 H2' rho2 rho2' clo_rho2 B) as [S2' [HsubS2 [Hcl2 Henv2]]]; eauto.
      eapply Included_trans; [| now apply Hinl2 ]. simpl. rewrite <- !Setminus_Union...
      eapply heap_env_equiv_alloc_alt; (try now apply Ha1); (try now apply Ha2); eauto.
      + simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
        eapply Singleton_Included. eapply dom_subheap.
        eapply def_funs_subheap. now eauto. now eexists; eauto.
      + simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
        eapply Singleton_Included. eapply dom_subheap.
        eapply def_funs_subheap. now eauto. now eexists; eauto.
      + simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
        rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].
        eapply Included_trans...
      + simpl. rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
        rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].
        eapply Included_trans...
      + setoid_rewrite <- Hd1. setoid_rewrite <- Hd2.
        simpl in Heq, Hinl1, Hinl2. rewrite <- !Setminus_Union in Heq, Hinl1, Hinl2.
        eapply IHB; try eassumption.
        eapply Included_trans; [ eassumption |]. simpl. rewrite <- !Setminus_Union...
      + simpl. split. now eauto.
        constructor.
        * rewrite res_equiv_eq. simpl; split; eauto.
        *  constructor. eapply res_equiv_weakening_alt.
           now apply Hc1. now apply Hc2. eassumption.
           now eapply def_funs_subheap; eauto.
           now eapply def_funs_subheap; eauto.
           eapply Singleton_Included. now eexists; eauto.
           eapply Singleton_Included. now eexists; eauto.
           simpl. rewrite post_Singleton; [ | eassumption ].
           eassumption. 
           simpl. rewrite post_Singleton; [ | eassumption ].
           eassumption. 
           now constructor.
    - simpl. rewrite Setminus_Empty_set_neut_r in Heq.
      eassumption.
  Qed.

  Lemma well_formed_reach_def_closed_same (S : Ensemble loc) (H H' : heap block) B B0 rho rho' ct l :
    well_formed (reach' H S) H  ->
    In loc (dom H) l ->
    S \subset dom H ->
    def_closures B B0 rho H ct l = (H', rho') ->
    reach' H S <--> reach' H' S.
  Proof.
    intros Hwf Hdom HS; revert H' rho'; induction B; intros H' rho' Hdef. 
    - simpl in Hdef.
      destruct (def_closures B B0 rho H ct ) as [H'' rho''] eqn:Hdef'.
      destruct (alloc _ H'') as [l' H'''] eqn:Ha. inv Hdef.
      assert (Heq :reach' H'' S <--> reach' H' S).
      { eapply well_formed_reach_alloc_same; eauto.
        eapply well_formed_def_funs; eauto.
        rewrite <- IHB; [| reflexivity ]. eassumption.
        eapply Included_trans. eassumption.
        eapply dom_subheap. eapply def_funs_subheap.
        eauto. }
      rewrite <- Heq, IHB; reflexivity.
    - inv Hdef. reflexivity.
  Qed.
      
  Lemma big_step_deterministic  H1 H2 rho1 rho2 e r1 r1' c1 m1 r2 r2' c2 m2 :
    well_formed (reach' H1 (env_locs rho1 (occurs_free e))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free e))) H2 ->
    env_locs rho1 (occurs_free e) \subset dom H1 ->
    env_locs rho2 (occurs_free e) \subset dom H2 ->
    big_step H1 rho1 e r1 c1 m1 -> (* D1 *)
    big_step H2 rho2 e r2 c2 m2 -> (* D2 *)
    r1 = Res r1' -> r2 = Res r2' ->
    (occurs_free e) |- (H1, rho1) ⩪ (H2, rho2) ->
                      r1' ≈ r2'.
  Proof with now eauto with Ensembles_DB.
    (* Lexicographic induction on the size of the first derivation and the size of the second derivation *)
    intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2. remember (size_big_step Hbs1) as n.
    revert H1 H2 rho1 rho2 e r1 r1' c1 m1 r2 r2' c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Heqn Hbs2.
    induction n as [n IH1] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e r1 r1' c1 m1 r2 r2' c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Heqn Hbs2.
    subst.
    remember (size_big_step Hbs2) as m.
    revert H1 H2 rho1 rho2 e r1 r1' c1 m1 r2 r2' c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2 Heqm IH1.
    induction m as [m IH2] using lt_wf_rec1.  
    intros H1 H2 rho1 rho2 e r1 r1' c1 m1 r2 r2' c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2
           Heqm IH1 Heq1 Heq2 Heq.
    
    destruct Hbs1; simpl in *.
    - (* D1 : OOT *) discriminate.
    - (* D1 : Eval_constr *)
      subst m. remember (Econstr x t ys e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_constr *)
        subst.
        eapply IH1 with (Hbs1 := Hbs1);
          [ | | | | | reflexivity | | reflexivity | reflexivity |]. 
        * omega.
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
          eapply well_formed_reach_alloc with (H := H); eauto.
          eapply Included_trans; [| now apply reach'_extensive ].
          simpl. eapply FromList_env_locs; eauto. normalize_occurs_free...
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
          eapply well_formed_reach_alloc with (H := H0) (l := l0); eauto.
          eapply Included_trans; [| now apply reach'_extensive ].
          simpl. eapply FromList_env_locs; eauto. normalize_occurs_free...
        * eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
          eapply Included_trans. eapply env_locs_set_Inlcuded.
          eapply Union_Included. eapply Singleton_Included.
          now eapply alloc_In_dom; eauto.
          eapply Included_trans. eassumption.
          eapply dom_subheap. now eapply alloc_subheap; eauto.
        * eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
          eapply Included_trans. eapply env_locs_set_Inlcuded.
          eapply Union_Included. eapply Singleton_Included.
          now eapply alloc_In_dom; eauto.
          eapply Included_trans. eassumption.
          eapply dom_subheap. now eapply alloc_subheap; eauto.
        * eassumption.
        * eapply (heap_env_equiv_alloc _ _ _ H H0); eauto. 
          eapply reach'_closed. eassumption. eassumption.
          eapply reach'_closed. eassumption. eassumption.
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply FromList_env_locs; eauto. normalize_occurs_free...
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply FromList_env_locs; eauto. normalize_occurs_free...
          eapply heap_env_equiv_antimon. eassumption.
          eapply Setminus_Included_Included_Union. now eapply occurs_free_Econstr_Included.
          split. reflexivity.
          eapply Forall2_symm_strong; [| eapply heap_env_equiv_getlist_Forall2 ].
          intros. now symmetry. now split; eapply Heq.
          rewrite occurs_free_Econstr... eassumption. eassumption.
      + (* D2 : Eval_GC *)
        assert (Hex : exists  (Hbs1' : big_step H rho (Econstr x t ys e) (Res r1') c m0),
                        size_big_step Hbs1' = S (size_big_step Hbs1)).
        { exists (Eval_constr H H' rho x t ys e vs l (Res r1') c m0 Hcost Hget Halloc Hbs1).
          reflexivity. }
        destruct Hex as [Hbs1' Hsize']. 
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1');
          [ | | | | | reflexivity | | reflexivity | reflexivity |]; try eassumption.
        * omega. 
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst. eapply IH1 with (Hbs1 := Hbs0);
            [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
          omega.
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_proj *)
      subst m. remember (Eproj x t n y e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_proj *)
        eapply IH1 with (Hbs1 := Hbs1); [ | | | | | reflexivity | | reflexivity | reflexivity |];
        try eassumption.
        * omega.
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
          eapply env_locs_set_Inlcuded.
          rewrite <-reach_spec. eassumption. now eauto with Ensembles_DB.
          eapply Union_Included.
          intros l1 Hin. eexists 1.
          split. now constructor. eexists l. eexists.
          repeat split; eauto; simpl. eexists; split; eauto.
          now rewrite Hgety. eapply In_Union_list; [| eassumption ].
          eapply in_map. now eapply nthN_In; eauto.
          now apply reach'_extensive.
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
          eapply env_locs_set_Inlcuded.
          rewrite <-reach_spec. eassumption. now eauto with Ensembles_DB.
          eapply Union_Included.
          intros l1 Hin. eexists 1. split.
          now constructor.
          eexists l0. eexists. repeat split; eauto; simpl.
          eexists; split; eauto.
          now rewrite Hgety0. eapply In_Union_list; [| eassumption ].
          eapply in_map. now eapply nthN_In; eauto.
          now apply reach'_extensive.
        * eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
          eapply Included_trans. eapply env_locs_set_Inlcuded.
          eapply Union_Included; [| eassumption ].
          eapply Included_trans; [| now eapply reachable_in_dom; eauto ].
          intros l1 Hin. eexists 1. split.
          now constructor.
          eexists l. eexists. repeat split; eauto; simpl.
          eexists; split; eauto. now rewrite Hgety.
          eapply In_Union_list; [| eassumption ].
          eapply in_map. now eapply nthN_In; eauto.
        * eapply Included_trans.
          eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
          eapply Included_trans. eapply env_locs_set_Inlcuded.
          eapply Union_Included; [| eassumption ].
          eapply Included_trans; [| now eapply reachable_in_dom; eauto ].
          intros l1 Hin. eexists 1. split.
          now constructor.
          eexists l0. eexists. repeat split; eauto; simpl.
          exists y; split; eauto. now rewrite Hgety0.
          eapply In_Union_list; [| eassumption ].
          eapply in_map. now eapply nthN_In; eauto.
        * eapply heap_env_equiv_set.
          eapply heap_env_equiv_antimon. eassumption.
          eapply Setminus_Included_Included_Union. now eapply occurs_free_Eproj_Included.
          eapply Heq in Hgety0. 
          destruct Hgety0 as [l2' [Hget' Heq']]. subst_exp.
          { rewrite res_equiv_eq in Heq'. simpl in Heq'.
            rewrite Hgetl, Hgetl0 in Heq'.  destruct Heq' as [_ Hall].
            symmetry.
            eapply Forall2_nthN' with (v1 := v0) (v2 := v) in Hall.
            eapply Hall; eassumption. eassumption. eassumption. }
          { eapply occurs_free_Eproj... }
      + (* D2 : Eval_GC *)
        assert (Hex : exists  (Hbs1' : big_step H rho (Eproj x t n y e) (Res r1') c m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
        { exists (Eval_proj H rho x t n y e l v vs (Res r1') c m0 Hcost Hgety Hgetl Hargs Hbs1).
          reflexivity. }
        destruct Hex as [Hbs1' Hsize'].
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1');
          [ | | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst. eapply IH1 with (Hbs1 := Hbs0);
            [| | | | | reflexivity | | reflexivity | reflexivity |]; try eassumption.
          omega.
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_case *)
      subst m. remember (Ecase y cl) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_case *)
        eapply Heq in Hgety. edestruct Hgety as [l' [Hget Heql']].
        subst_exp. rewrite res_equiv_eq in Heql'. simpl in Heql'.
        rewrite Hgetl, Hgetl0 in Heql'. destruct Heql' as [Heqt Hall]. subst.
        subst_exp.
        eapply IH1 with (Hbs1 := Hbs1);
          [ | | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption; eauto.
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          rewrite occurs_free_Ecase_Included. reflexivity.
          eapply cps_util.findtag_In. eassumption.
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          rewrite occurs_free_Ecase_Included. reflexivity.
          eapply cps_util.findtag_In. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic.
          rewrite occurs_free_Ecase_Included. reflexivity.
          eapply cps_util.findtag_In. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic.
          rewrite occurs_free_Ecase_Included. reflexivity.
          eapply cps_util.findtag_In. eassumption.
        * eapply heap_env_equiv_antimon.
          eassumption.
          rewrite occurs_free_Ecase_Included. reflexivity.
          eapply cps_util.findtag_In. eassumption.
        * eauto.
      + (* D2 : Eval_GC *)
        assert (Hex : exists  (Hbs1' : big_step H rho (Ecase y cl) (Res r1') c m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
        { exists (Eval_case H rho y cl l t vs e (Res r1') c m0 Hcost Hgety Hgetl Hfind Hbs1). reflexivity. }
        destruct Hex as [Hbs1' Hsize'].
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1');
          [ | | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst.
          eapply IH1 with (Hbs1 := Hbs0);
            [| | | | | reflexivity | | reflexivity | reflexivity |]; try eassumption.
          omega.
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_fun *)
      subst m. remember (Efun B e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_fun *) 
        eapply IH1 with (Hbs1 := Hbs1);
        [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
          eapply well_formed_reach_alloc_def_funs; [ | | | | eassumption ].
          eapply well_formed_alloc; [| eassumption | ]. 
          rewrite <- well_formed_reach_alloc_same; eassumption.
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [ | eassumption ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [ eassumption |].
          now eapply dom_subheap; eapply alloc_subheap; eauto.
          now erewrite gas; eauto.
          eapply Included_trans; [| now eapply reach'_extensive ].
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply env_locs_monotonic. normalize_occurs_free...
        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
          eapply well_formed_reach_alloc_def_funs; [ | | | | eassumption ].
          eapply well_formed_alloc; [| eassumption | ]. 
          rewrite <- well_formed_reach_alloc_same; eassumption.
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [ | eassumption ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [ eassumption |].
          now eapply dom_subheap; eapply alloc_subheap; eauto.
          now erewrite gas; eauto.
          eapply Included_trans; [| now eapply reach'_extensive ].
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply env_locs_monotonic. normalize_occurs_free...
        * eapply Included_trans. eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
          eapply def_closures_env_locs_in_dom; [eassumption | ].
          eapply Included_trans. eassumption.
          eapply dom_subheap. now eapply alloc_subheap; eauto.
        * eapply Included_trans. eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
          eapply def_closures_env_locs_in_dom; [eassumption | ].
          eapply Included_trans. eassumption.
          eapply dom_subheap. now eapply alloc_subheap; eauto.
        * eapply heap_env_equiv_antimon with (S1 := occurs_free (Efun B e) :|: name_in_fundefs B);
          [| now apply occurs_free_Efun_Included ].
          setoid_rewrite <- Hfuns0. setoid_rewrite <- Hfuns.
          eapply heap_env_equiv_def_funs.
          (* closed H' *)
          eapply reach'_closed. rewrite reach'_alloc; [ | eassumption | ].
          eapply well_formed_alloc. eassumption. eassumption.
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [| now eapply reach'_extensive ].
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans. eassumption. eapply dom_subheap.
          eapply alloc_subheap. eassumption.
          (* closed H0' *)
          eapply reach'_closed. rewrite reach'_alloc; [ | eassumption | ].
          eapply well_formed_alloc. eassumption. eassumption.
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans; [| now eapply reach'_extensive ].
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply env_locs_monotonic. normalize_occurs_free...
          eapply Included_trans. eassumption. eapply dom_subheap.
          eapply alloc_subheap. eassumption.
          (* env locs rho \subset reach H' *)
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply env_locs_monotonic...
          (* env locs rho0 \subset reach H'0 *)
          eapply Included_trans; [| now apply reach'_extensive ].
          eapply env_locs_monotonic...
          (* get env_loc H' *)
          now erewrite gas; eauto.
          (* get env_loc0 H'0 *)
          now erewrite gas; eauto.
          (* env locs rho_clo \subset reach H' *)
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [| now apply reach'_extensive ].
          normalize_occurs_free...
          (* env locs rho_clo0 \subset reach H0' *)
          eapply Included_trans. eapply restrict_env_env_locs. eassumption.
          eapply Included_trans; [| now apply reach'_extensive ].
          normalize_occurs_free...
          (* fv subset *)
          rewrite Setminus_Union_distr.
          rewrite Setminus_Disjoint. normalize_occurs_free...
          normalize_occurs_free. eapply Union_Disjoint_l.
          eapply Disjoint_sym. now apply occurs_free_fundefs_name_in_fundefs_Disjoint.
          eapply Disjoint_Setminus_l. reflexivity.
          (* (Loc env_loc, H') ≈ (Loc env_loc0, H'0) *)
          rewrite res_equiv_eq. simpl.
          erewrite gas; [| eassumption ]. erewrite gas; [| eassumption ]. 
          (* |- (H', rho) ⩪ (H'0, rho0) *)
          eapply heap_env_equiv_restrict_env; [| | eassumption | eassumption ].
          eapply heap_env_equiv_weaking_cor; try eassumption.
          eapply alloc_subheap; eassumption.
          eapply alloc_subheap; eassumption.
          normalize_occurs_free...
          eapply heap_env_equiv_antimon with (S1 := occurs_free (Efun B e));
            [| now eauto with Ensembles_DB ].
          eapply heap_env_equiv_weaking_cor; try eassumption.
          eapply alloc_subheap; eassumption.
          eapply alloc_subheap; eassumption.
      + (* D2 : Eval_GC *)
        assert (Hex : exists  (Hbs1' : big_step H rho (Efun B e) (Res r1') c m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
        { exists (Eval_fun H H' H'' rho rho_clo rho' B env_loc e (Res r1') c m0 Hcost Hres Halloc Hfuns Hbs1).
          reflexivity. }
        destruct Hex as [Hbs1' Hsize'].
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [| | |  | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst.
          eapply IH1 with (Hbs1 := Hbs0);
            [| | | | | reflexivity | | reflexivity | reflexivity |]; try eassumption.
          omega.
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_app *)
      subst m. remember (Eapp f t ys) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_app *)
        assert (Hgetf' := Hgetf). assert (Hgetl' := Hgetl).
        eapply Heq in Hgetf; [| normalize_occurs_free; now eauto with Ensembles_DB ].
        destruct Hgetf as [l' [Hget Hequiv]]. repeat subst_exp.
        rewrite res_equiv_eq in Hequiv. simpl in Hequiv.
        rewrite Hgetl, Hgetl0 in Hequiv. destruct Hequiv as [_ Hall].
        inv Hall. inv H6. clear H8. rewrite res_equiv_eq in H4, H5.
        simpl in H4, H5. inv H4. rewrite Hget_env, Hget_env0 in H5. 
        repeat subst_exp.
        assert (Henv1 :  env_locs rho_clo (Full_set var) \subset
                         reach' H (env_locs rho (occurs_free (Eapp f t ys)))).
        { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| now eapply Included_post_n_reach' with (n := 2) ].
          simpl. rewrite env_locs_Singleton; try eassumption. simpl. rewrite post_Singleton; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
          rewrite post_Singleton; try eassumption. eapply env_locs_monotonic... }
        assert (Henv2 :  env_locs rho_clo0 (Full_set var) \subset
                         reach' H0 (env_locs rho0 (occurs_free (Eapp f t ys)))).
        { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| now eapply Included_post_n_reach' with (n := 2) ].
          simpl. rewrite env_locs_Singleton; try eassumption. simpl. rewrite post_Singleton; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
          rewrite post_Singleton; try eassumption. eapply env_locs_monotonic... }
        assert (Hvs1 : Union_list (map val_loc vs) \subset
                       env_locs rho (occurs_free (Eapp f t ys))).
        { rewrite <- env_locs_FromList; eauto. normalize_occurs_free.
          eapply env_locs_monotonic... }
        assert (Hvs2 : Union_list (map val_loc vs0) \subset
                       env_locs rho0 (occurs_free (Eapp f t ys))).
        { rewrite <- env_locs_FromList; eauto. normalize_occurs_free.
          eapply env_locs_monotonic... }
        eapply IH1 with (rho1 := rho_clo2) (rho2 := rho_clo4) (Hbs1 := Hbs1);
          [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * { eapply well_formed_antimon. 
            - eapply reach'_set_monotonic. eapply env_locs_monotonic.
              eapply occurs_free_in_fun.
              eapply find_def_correct. eassumption.
            - rewrite Union_commut.
              eapply well_formed_antimon.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              eapply Included_Union_compat.
              eapply Included_Union_compat with (s2' := Full_set _); [ reflexivity |]...
              reflexivity.
              eapply well_formed_reach_setlist; [| | eassumption ].
              + rewrite Union_commut.
                eapply well_formed_reach_alloc_def_funs; try eassumption.
                * eapply well_formed_antimon; [| eassumption ].
                  eapply Included_trans; [| now eapply reach'_idempotent ]. 
                  eapply reach'_set_monotonic. eassumption.
                * eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
                  eassumption.
                * eapply reach'_extensive.
              + eapply well_formed_def_funs; [| now eexists; eauto | now eauto ]. 
                rewrite <- well_formed_reach_def_closed_same; [| | | | eassumption ].
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eassumption.
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eassumption.
                now eexists; eauto.
                eapply Included_trans; eauto. }
        * { eapply well_formed_antimon. 
            - eapply reach'_set_monotonic. eapply env_locs_monotonic.
              eapply occurs_free_in_fun.
              eapply find_def_correct. eassumption.
            - rewrite Union_commut.
              eapply well_formed_antimon.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              eapply Included_Union_compat.
              eapply Included_Union_compat with (s2' := Full_set _); [ reflexivity |]...
              reflexivity.
              eapply well_formed_reach_setlist; [| | eassumption ].
              + rewrite Union_commut.
                eapply well_formed_reach_alloc_def_funs; [| | | | eassumption]; try eassumption.
                * eapply well_formed_antimon; [| eassumption ].
                  eapply Included_trans; [| now eapply reach'_idempotent ]. 
                  eapply reach'_set_monotonic. eassumption.
                * eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
                  eassumption.
                * eapply reach'_extensive.
              + eapply well_formed_def_funs; [| | now eauto ]; try (now eexists; eauto). 
                rewrite <- well_formed_reach_def_closed_same; [| | | | eassumption ].
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eassumption.
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eassumption.
                now eexists; eauto.
                eapply Included_trans; eauto. }
        * eapply Included_trans. eapply env_locs_monotonic. eapply occurs_free_in_fun.
          eapply find_def_correct. eassumption. rewrite Union_commut.
          eapply Included_trans. eapply env_locs_setlist_Included; eauto.
          eapply Union_Included.
          rewrite Union_commut.
          eapply def_closures_env_locs_in_dom; try eassumption.
          eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
          eapply Included_trans; [| now apply Henv1 ].
          eapply env_locs_monotonic...
          eapply Included_trans; [| eapply dom_subheap; eapply def_funs_subheap; now eauto ].
          eapply Included_trans; eassumption.
        * eapply Included_trans. eapply env_locs_monotonic. eapply occurs_free_in_fun.
          eapply find_def_correct. eassumption. rewrite Union_commut.
          eapply Included_trans. eapply env_locs_setlist_Included; eauto.
          eapply Union_Included.
          rewrite Union_commut.
          eapply def_closures_env_locs_in_dom; try eassumption.
          eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
          eapply Included_trans; [| now apply Henv2 ].
          eapply env_locs_monotonic...
          eapply Included_trans; [| eapply dom_subheap; eapply def_funs_subheap; now eauto ].
          eapply Included_trans; eassumption.
        * { eapply heap_env_equiv_setlist; try eassumption.
            + eapply heap_env_equiv_antimon with (S1 := occurs_free_fundefs B0 :|: name_in_fundefs B0);
              [| eapply Included_trans;
                 [ eapply Included_Setminus_compat;
                   [eapply occurs_free_in_fun; eapply find_def_correct; eassumption | reflexivity ]
                 | now eauto with Ensembles_DB ]].
              setoid_rewrite <- Hredef. setoid_rewrite <- Hredef0.
              eapply heap_env_equiv_def_funs; try eassumption.
              * eapply reach'_closed; eassumption.
              * eapply reach'_closed; eassumption.
              * eapply Included_trans; [| now apply Henv1 ].
                eapply env_locs_monotonic...
              * eapply Included_trans; [| now apply Henv2 ].
                eapply env_locs_monotonic...
              * rewrite Setminus_Union_distr.
                rewrite Setminus_Disjoint. now eauto with Ensembles_DB.
                eapply Disjoint_sym. now apply occurs_free_fundefs_name_in_fundefs_Disjoint.
              * rewrite res_equiv_eq. simpl. rewrite Hget_env, Hget_env0.
                eassumption.
              * eapply heap_env_equiv_antimon; [ eassumption | ]... 
            + eapply heap_env_equiv_getlist_Forall2; eauto.
              eapply heap_env_equiv_weaking_cor; try eassumption.
              eapply def_funs_subheap. now eauto.
              eapply def_funs_subheap. now eauto. normalize_occurs_free... }
      + (* D2 : Eval_GC *)
        assert (Hex : exists (Hbs1' : big_step H rho (Eapp f t ys) (Res r1') c m0),
                        size_big_step Hbs1' = S (size_big_step Hbs1)).
        { exists (Eval_app H H' rho rho_clo rho_clo1 rho_clo2 B f f' t xs e l env_loc vs ys (Res r1') c m0 Hcost Hgetf Hgetl Hget_env Hfind Hargs Hredef Hset Hbs1).
          reflexivity. }
        destruct Hex as [Hbs1' Hsize'].
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1');
          [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst.
          eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
          omega.
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv. eapply collect_heap_eq. eassumption.      
    - (* D1 : Eval_halt *)
      subst m. remember (Ehalt x) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_halt *)
        eapply Heq in Hget; eauto. destruct Hget as [l' [Hget Hequiv]].
        inv Heq1; inv Heq2. subst_exp. eassumption.
      + (* D2 : Eval_GC *)
        assert (Hex : exists  (Hbs1' : big_step H rho (Ehalt x) (Res (v, H)) c (size_heap H)), size_big_step Hbs1' = 0).
        { exists (Eval_halt H rho x v c (size_heap H) Hcost Hget eq_refl). eauto. }
        destruct Hex as [Hbs1' Hsize'].
        inv Heq1.
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1');
          [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
        * omega.
        * eapply heap_equiv_respects_well_formed; [| eassumption ].
          destruct Hgc as [_ Hequiv]. exact Hequiv.
        * eapply heap_equiv_in_dom.
          destruct Hgc as [_ Hequiv]. exact Hequiv.
          reflexivity. eassumption.
        * intros. subst. eapply IH1 with (Hbs1 := Hbs1);
            [| | | | | reflexivity | | reflexivity | reflexivity | ]; try eassumption.
          omega. 
        * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
          eapply reach_heap_env_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_GC *)
      eapply IH1 with (Hbs1 := Hbs1); [| | | | | reflexivity | eassumption | | | ].
      + omega.
      + eapply heap_equiv_respects_well_formed; [| eassumption ].
        destruct Hgc as [_ Hequiv]. exact Hequiv.
      + eassumption.
      + eapply heap_equiv_in_dom.
        destruct Hgc as [_ Hequiv]. exact Hequiv.
        reflexivity. eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; try eassumption.
        symmetry. eapply reach_heap_env_equiv.
        eapply collect_heap_eq. eassumption.
  Qed.
  
  Lemma big_step_perfect_gc_heap_eq H1 H2 rho1 rho2 e (r : ans) c m :
    big_step_perfect_GC H1 rho1 e r c m ->
    (occurs_free e) |- (H1, rho1) ⩪ (H2, rho2) ->
    (exists r', big_step_perfect_GC H2 rho2 e r c m /\
           ans_equiv r r').
  Abort.

  Lemma heap_eq_respects_heap_env_equiv S H1 H2 rho :
    (env_locs rho S) |- H1 ≡ H2 ->
    S |- (H1, rho) ⩪ (H2, rho).
  Proof.
  Abort.

End SpaceSem.
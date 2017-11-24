(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps cps_util eval List_util Ensembles_util functions
        identifiers Heap.heap Heap.heap_defs Heap.heap_equiv tactics.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Module SpaceSem (H : Heap).
  
  Module Equiv := HeapEquiv H.
  
  Context (cloTag : cTag).

  Import H Equiv.Defs Equiv.Defs.HL Equiv.

  (* The cost of evaluating the head *)
  (* TODO make semantics parametric in the cost model *)
  Definition cost (e : exp) : nat :=
    match e with
      | Econstr x t ys e => 1 + length ys
      | Ecase y cl => 1 
      | Eproj x t n y e => 1
      | Efun B e => fundefs_num_fv B + 1
      | Eapp f t ys => 1 + length ys
      | Eprim x p ys e => 1 + length ys
      | Ehalt x => 1
    end.

   
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
        (Hfuns : def_closures B B rho H' env_loc = (H'', rho'))
        (Hbs : big_step H'' rho' e r (c - cost (Efun B e)) m),
        big_step H rho (Efun B e) r c m
  | Eval_app :
      forall (H H' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Eapp f t ys))
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
        (Hfuns : def_closures B B rho H' env_loc = (H'', rho'))

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
        
        (Hbs : big_step_perfect_GC H'' rho_clo2 e r (c - cost (Eapp f t ys)) m),
        big_step_perfect_GC H rho (Eapp f t ys) r c (max m m')
  | Eval_halt_per :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_perfect_GC H rho (Ehalt x) (Res (l, H)) c m.

  (** Deterministic semantics with garbage collection upon function entry.
    * We will show that it takes asymptotically the same amount of space as perfect garbage collection *)
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
  | Eval_proj_gc :
      forall (H : heap block) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Hnth : nthN vs n = Some v)
        
        (Hbs : big_step_GC H (M.set x v rho) e r (c - 1) m),
        
        big_step_GC H rho (Eproj x t n y e) r c m
  | Eval_case_gc :
      forall (H : heap block) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (vs : list value) (e : exp) (r : ans) (c m m' : nat)
        (Hcost : c >= cost (Ecase y cl))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Htag : findtag cl t = Some e)
        
        (Hbs : big_step_GC H rho e r (c - cost (Ecase y cl)) m),
        
        big_step_GC H rho (Ecase y cl) r c m
  | Eval_fun_gc :
      forall (H H' H'' : heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (e : exp) (r : ans) (c : nat) (m : nat)
        (Hcost : c >= cost (Efun B e))
        (* find the closure environment *)
        (Hres : restrict_env (occurs_free_fundefs B) rho rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' env_loc = (H'', rho'))
        
        (Hbs : big_step_GC H'' rho' e r (c - cost (Efun B e)) m),

        big_step_GC H rho (Efun B e) r c m
    
  | Eval_app_gc :
      forall (H H' H'' : heap block) (rho rho_clo rho_clo1 rho_clo2 : env) (B : fundefs)
        (f f' : var) (t : cTag) (xs : list var) (e : exp) (l env_loc: loc)
        (vs : list value) (ys : list var) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Eapp f t ys))
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
        
        (Hbs : big_step_GC H'' rho_clo2 e r (c - cost (Eapp f t ys)) m),
        big_step_GC H rho (Eapp f t ys) r c (max m m')
  | Eval_halt_gc :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC H rho (Ehalt x) (Res (l, H)) c m.


  Fixpoint def_funs (B B0 : fundefs) rho :=
    match B with
      | Fcons f _ _ _ B =>
        M.set f (FunPtr B0 f) (def_funs B B0 rho)
      | Fnil => rho
    end.

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
      forall (H H' : heap block) (rho rho' : env) (x : var) (t : cTag)
        (ys :list var) (e : exp) (vs : list value) (l : loc) (r : ans)
        (c m : nat)
        (Hcost :  c >= cost (Econstr x t ys e))
        (Hget : getlist ys rho = Some vs)
        (Halloc : alloc (Constr t vs) H = (l, H'))
              
        (Hbs : big_step_GC_cc H' (M.set x (Loc l) rho) e r (c - cost (Econstr x t ys e)) m),

        big_step_GC_cc H rho (Econstr x t ys e) r c m
  | Eval_proj_per_cc :
      forall (H : heap block) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l : loc) (v : value) (vs : list value)
        (r : ans) (c m : nat)
        (Hcost : c >= cost (Eproj x t n y e))
        (Hgety : M.get y rho = Some (Loc l))
        (Hgetl : get l H = Some (Constr t vs))
        (Hnth : nthN vs n = Some v)

        (Hbs : big_step_GC_cc H (M.set x v rho) e r (c - 1) m),
        
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
      forall (H : heap block) (rho rho_clo rho' : env) (B : fundefs)
        (env_loc : loc) (ct : cTag) (e : exp) (r : ans) (c : nat) (m m' : nat)
        (Hcost : c >= cost (Efun B e))
        (* add the functions in the environment *)
        (Hfuns : def_funs B B rho = rho')
        
        (Hbs : big_step_GC_cc H rho' e r (c - cost (Efun B e)) m),
        
        big_step_GC_cc H rho (Efun B e) r c m
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
        
        (Hbs : big_step_GC_cc H' rho_clo e r (c - cost (Eapp f ct ys)) m),
        big_step_GC_cc H rho (Eapp f ct ys) r c (max m m')
  | Eval_halt_per_cc :
      forall H rho x l c m
        (Hcost : c >= cost (Ehalt x))
        (Hget : M.get x rho = Some l)
        (Hsize : size_heap H = m),
        big_step_GC_cc H rho (Ehalt x) (Res (l, H)) c m.
  
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
        (env_loc : loc) (e : exp) (r : ans) (size c m : nat)
        (Hcost: c >= cost (Efun B e))
        (* No GC is needed *)
        (Hheap : size_heap H < Hmax)
        (* find the closure environment *)
        (Hres : restrict_env (occurs_free_fundefs B) rho rho_clo)
        (* allocate the closure environment *)
        (Halloc : alloc (Env rho_clo) H = (env_loc, H'))
        (* allocate the closures *)
        (Hfuns : def_closures B B rho H' env_loc = (H'', rho'))
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
          eapply heap_env_equiv_heap_equiv.
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
          eapply heap_env_equiv_heap_equiv.
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
          eapply heap_env_equiv_heap_equiv.
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
          eapply heap_env_equiv_heap_equiv.
          eapply collect_heap_eq. eassumption.
    - (* D1 : Eval_app *)
      subst m. remember (Eapp f t ys) as e'. destruct Hbs2; inv Heqe'; simpl in *.
      + (* D2 : OOT *) discriminate.
      + (* D2 : Eval_app *)
        assert (Hgetf' := Hgetf). assert (Hgetl' := Hgetl).
        eapply Heq in Hgetf; [| normalize_occurs_free; now eauto with Ensembles_DB ].
        destruct Hgetf as [l' [Hget Hequiv]]. repeat subst_exp.
        rewrite res_equiv_eq in Hequiv. simpl in Hequiv.
        rewrite Hgetl, Hgetl0 in Hequiv. destruct Hequiv as [Hv1 Hv2].
        rewrite res_equiv_eq in Hv1, Hv2.
        simpl in Hv1, Hv2. inv Hv1. rewrite Hget_env, Hget_env0 in Hv2. 
        repeat subst_exp.
        assert (Henv1 :  env_locs rho_clo (Full_set var) \subset
                         reach' H (env_locs rho (occurs_free (Eapp f t ys)))).
        { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| now eapply Included_post_n_reach' with (n := 2) ].
          simpl. rewrite env_locs_Singleton; try eassumption. simpl. rewrite post_Singleton; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l.
          rewrite post_Singleton; try eassumption. eapply env_locs_monotonic... }
        assert (Henv2 :  env_locs rho_clo0 (Full_set var) \subset
                         reach' H0 (env_locs rho0 (occurs_free (Eapp f t ys)))).
        { normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| now eapply Included_post_n_reach' with (n := 2) ].
          simpl. rewrite env_locs_Singleton; try eassumption. simpl. rewrite post_Singleton; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l.
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
          eapply heap_env_equiv_heap_equiv. eapply collect_heap_eq. eassumption.      
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
          eapply heap_env_equiv_heap_equiv.
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
        symmetry. eapply heap_env_equiv_heap_equiv.
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
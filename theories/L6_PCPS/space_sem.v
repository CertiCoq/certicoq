(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
     MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps eval List_util Ensembles_util functions identifiers.


Module Type Heap.

  Parameter loc : Type.
  
  Parameter heap : Type -> Type. 
  
  Parameter emp : forall {A}, heap A.
  
  Parameter get : forall {A : Type}, loc -> heap A -> option A.
  
  Parameter set : forall {A : Type}, A -> loc -> heap A -> heap A.
  
  Parameter alloc : forall {A : Type}, A -> heap A -> loc * heap A.

  Parameter gss :
    forall A (x : A) (l : loc) (H : heap A),
      get l (set x l H) = Some x. 

  Parameter gso :
    forall A (x : A) (l1 l2 : loc) (H : heap A),
      l1 <> l2 ->
      get l1 (set x l2 H) = get l1 H. 

  Parameter gas :
    forall A (x : A) (l : loc) (H H' : heap A),
      alloc x H = (l, H') ->
      get l H' = Some x. 

  Parameter gao :
    forall A (x : A) (l1 l2 : loc) (H H' : heap A),
      l1 <> l2 ->
      alloc x H = (l1, H') ->
      get l2 H' = get l1 H'. 

  Parameter alloc_fresh :
    forall A (x : A) (l : loc) (H H' : heap A),
      alloc x H = (l, H') ->
      get l H = None.
  
  (** The restriction of a heap in a given domain *)
  Parameter restrict : forall {A}, Ensemble loc -> heap A -> heap A -> Prop.  
  
  Parameter restrict_In :
    forall A (x : A) (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      l \in S -> 
      get l H' = get l H. 
  
  Parameter restrict_notIn :
    forall A (x : A) (l : loc) (S : Ensemble loc) (H H' : heap A),
      restrict S H H' ->
      ~ l \in S -> 
      get l H = get l H'.

  (** The size of a heap *)
  Parameter size : forall {A}, heap A -> nat -> Prop.
  
  Parameter size_emp :
    forall (A : Type), @size A emp 0.

  Parameter size_alloc :
    forall (A : Type) (x : A) (H : heap A) (s : nat),
      size H s ->
      size (snd (alloc x H)) (s + 1).

  Parameter splits : forall {A}, heap A -> heap A -> heap A -> Prop. 

  Parameter splits_spec_Some :
    forall {A} (H1 H2 H : heap A) (l : loc) (v : A),
      splits H H1 H2 ->
      get l H = Some v ->
      (get l H1 = Some v /\ get l H2 = None) /\
      (get l H2 = None /\ get l H2 = Some v).

  Parameter splits_spec_None :
    forall {A} (H1 H2 H : heap A) (l : loc),
      splits H H1 H2 ->
      get l H = None ->
      get l H1 = None /\ get l H2 = None.

End Heap.

Module Sem (H : Heap).

  Import H.

  (* All the values are boxed *)
  Definition env := M.t loc.
  
  Inductive val : Type :=
  | Vconstr: cTag -> list loc -> val
  | Vfun: env -> fundefs -> val.

  (** The result of the evaluation *)
  Definition res := (loc * heap val)%type.

  (** Equivalence of results *)
  Inductive res_equiv : res -> res -> Prop :=
  | Vconstr_eq :
      forall l1 l2 H1 H2 c1 ls1 c2 ls2,
        get l1 H1 = Some (Vconstr c1 ls1) ->
        get l1 H1 = Some (Vconstr c2 ls2) ->
        Forall2 (fun l1 l2 => res_equiv (l1, H1) (l2, H2)) ls1 ls2 ->
        res_equiv (l1, H1) (l2, H2)
  | Vfun_eq :
      forall l1 l2 H1 H2 rho1 rho2 B,
        get l1 H1 = Some (Vfun rho1 B) ->
        get l1 H1 = Some (Vfun rho2 B) ->
        (forall x,  x \in (occurs_free_fundefs B) ->
               (exists l1 l2, M.get x rho1 = Some l1 /\
                        M.get x rho2 = Some l2 /\
                        res_equiv (l1, H1) (l2, H2)) \/
               (M.get x rho1 = None /\ M.get x rho2 = None)) ->
        res_equiv (l1, H1) (l2, H2).
  
  Infix "≈" := res_equiv (at level 70, no associativity).


  (** The locations that appear on values *)
  Definition locs (v : val) : Ensemble loc :=
    match v with
      | Vconstr t ls => FromList ls
      | Vfun rho B =>
        (* Take only the relevant part of the environment instead of its domain *)
        image' (fun x => M.get x rho) (occurs_free_fundefs B)
    end.
  
  Definition post (H : heap val) (S : Ensemble loc) :=
    [ set l : loc | exists l' v, l' \in S /\ get l H = Some v /\ l' \in locs v].

  (** TODO: move this to functions.v *)
  Fixpoint app {A} (f : A -> A) n  : A ->  A :=
    fun x =>
      match n with
        | 0 => x
        | S n' => f (app f n' x)
      end.
  
  Infix "^" := app (at level 30, right associativity) : fun_scope.

  Definition lfp {A} (f : Ensemble A -> Ensemble A) :=
    \bigcup_( n : nat ) ((f ^ n) (Empty_set A)).
  
  (** Least fixed point characterization of heap reachability. *)
  Definition reach (H : heap val) (Si : Ensemble loc) : Ensemble loc :=
    lfp (fun S => Union _ Si (post H S)).

  
  Fixpoint def_funs (B : fundefs) (l : loc) (rho : env) {struct B}
  : env :=
    match B with
      | Fcons f _ _ _ B' =>
        M.set f l (def_funs B' l rho)
      | Fnil => rho
    end.

  Variable (pr : M.t (list loc -> heap val -> option (loc * heap val))).

  Inductive big_step :
    heap val -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    res -> (* The location of the final result (?) *)
    nat -> (* The number of applications in the derivation *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_constr :
      forall (H H' : heap val) (rho rho' : env) (x : var) (t : cTag) (ys :list var)
        (e : exp) (ls : list loc) (l : loc) (r : res) (c : nat) (m : nat),
        getlist ys rho = Some ls ->
        alloc (Vconstr t ls) H = (l, H') ->
        M.set x l rho = rho' ->
        big_step H' rho' e r c m ->
        big_step H rho (Econstr x t ys e) r c m
  | Eval_proj :
      forall (H : heap val) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l l' : loc) (ls : list loc) (r : res) (c m : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) -> 
        nthN ls n = Some l' ->
        big_step H (M.set x l' rho) e r c m ->
        big_step H rho (Eproj x t n y e) r c m
  | Eval_case :
      forall (H : heap val) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (ls : list loc)
        (e : exp) (r : res) (c m : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) ->
        findtag cl t = Some e ->
        big_step H rho e r c m ->
        big_step H rho (Ecase y cl) r c m
  | Eval_fun :
      forall (H H' : heap val) (rho : env) (B : fundefs)
        (l : loc) (e : exp) (r : res)
        (c : nat) (m : nat),
        alloc (Vfun rho B) H = (l, H') ->  
        big_step H' (def_funs B l rho) e r c m ->
        big_step H rho (Efun B e) r c m
  | Eval_app : 
      forall (H : heap val) (rho rho' rho'' : env) (B : fundefs) (f : var) (t : cTag)
        (xs : list var) (e : exp) (l : loc) (ls : list loc) (ys : list var)
        (r : res) (c : nat) (m : nat),
        M.get f rho = Some l ->
        get l H = Some (Vfun rho' B) -> 
        getlist ys rho = Some ls ->
        find_def f B = Some (t, xs, e) ->
        setlist xs ls (def_funs B l rho') = Some rho'' ->
        big_step H rho'' e r c m ->
        big_step H rho (Eapp f t ys) r (c+1) m
  | Eval_prim :
      forall (H H' : heap val) (rho rho' : env) (x : var) (f : prim) f' (ys :list var)
        (e : exp) (ls : list loc) (l : loc) (r : res) (c : nat) (m : nat),
        getlist ys rho = Some ls ->
        M.get f pr = Some f' ->
        f' ls H = Some (l, H') -> 
        big_step H' (M.set x l rho) e r c m ->
        big_step H rho (Eprim x f ys e) r c m
  | Eval_halt :
      forall H rho x l m,
        M.get x rho = Some l ->
        size H m ->
        big_step H rho (Ehalt x) (l, H) 0 m
  | Eval_GC :
      forall (H H1 H2 : heap val) (rho : env) (e : exp) (r : res) (c : nat) (m m' : nat),
        splits H H1 H2 -> (* H = H1 ⊎ H2*)
        (* Whatever can be reached it can be reached from the H1 portion of the heap.
           Alternative (more direct?) characterization of garbage here
           might also be useful here *)
        (reach H (image' (fun x => M.get x rho) (occurs_free e)) <-->
         reach H1 (image' (fun x => M.get x rho) (occurs_free e))) ->
        size H m' ->
        big_step H1 rho e r c m ->
        big_step H rho e r c (max m m').

End Sem.
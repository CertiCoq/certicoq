(* Relation for Dead Parameter Elimination. Part of the CertiCoq project.
 * Author: Katja Vassilev, 2019
 *)

Require Import L6.cps L6.cps_util L6.set_util L6.hoisting L6.identifiers L6.ctx
        L6.Ensembles_util L6.alpha_conv L6.List_util L6.functions L6.lambda_lifting
        L6.eval L6.logical_relations L6.hoare.
Require Import compcert.lib.Coqlib.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(* S is the set of the dropped parameters of the function we're in. We need it
   to make sure that these are not used anywhere in the program, and so the proof will go through.
   Everything that we want to keep we want to make sure that is not in S.
   the list of booleans is the L parameters of the function we are calling and we need it so that
   the application has the right arity.
 *)
Inductive Live_args (S : Ensemble var) : list var -> list bool -> list var -> Prop :=
| ALive_nil : Live_args S [] [] []
| ALive_cons_L :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var),
      Live_args S xs bs ys ->
      Live_args S (x :: xs) (false :: bs) ys
| ALive_cons_keep :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var),
      Live_args S xs bs ys ->
      ~ x \in S -> 
      Live_args S (x :: xs) (true :: bs) (x :: ys).

Definition eliminated_funs L : Ensemble var :=
  [set f | exists bs, L f = Some bs /\ Exists (fun x => x = false) bs]. 

(* S is the set of formal parameters that have been dropped from the *current* function.
   That is, whatever is in S, is undefined in the environment when we execute the code. *)
Inductive Live_body (L : var -> option (list bool)) (S : Ensemble var) :  exp -> exp -> Prop := 
| BLive_Constr : 
  forall (x : var) (ys : list var) (ct : cTag) (e : exp) (e' : exp), 
    Disjoint _ (FromList ys) (S :|: eliminated_funs L) -> 
    Live_body L S e e' ->
    Live_body L S (Econstr x ct ys e) (Econstr x ct ys e')
| BLive_Prim : 
  forall (x : var) (g : prim) (ys : list var) (e : exp) (e' : exp), 
    Disjoint _ (FromList ys) (S :|: eliminated_funs L) -> 
    Live_body L S e e' ->
    Live_body L S (Eprim x g ys e) (Eprim x g ys e')
| BLive_Proj : 
  forall (x : var) (ct : cTag) (n : N) (y : var) (e : exp) (e' : exp), 
    ~ y \in (S :|: eliminated_funs L) ->
    Live_body L S e e' ->
    Live_body L S (Eproj x ct n y e) (Eproj x ct n y e')
| BLive_Case: 
  forall (x : var) (ce : list (cTag * exp)) (ce' : list (cTag * exp)),
    ~ x \in (S :|: eliminated_funs L) ->
    Forall2 (fun p1 p2 => fst p1 = fst p2 /\ Live_body L S (snd p1) (snd p2)) ce ce' -> 
    Live_body L S (Ecase x ce) (Ecase x ce')
| BLive_Halt : 
    forall (x : var),
      ~ x \in (S :|: eliminated_funs L) ->
      Live_body L S (Ehalt x) (Ehalt x)
| BLive_App_Unknown :
    forall (f : var) (ys : list var) (ft : fTag),
      (* Unknown function application, f is not in the list of top-level
         function definitions. Therefore, it must be a parameter of the current
         function *)
      ~ f \in (S :|: eliminated_funs L) ->
      Disjoint _ (FromList ys) (S :|: eliminated_funs L) -> 
      L f = None -> 
      Live_body L S (Eapp f ft ys) (Eapp f ft ys)
| BLive_App_Known :
    forall (f : var) (ys : list var) (ys' : list var) (ft : fTag) (bs : list bool),
      L f = Some bs ->
      ~ f \in S ->
      Live_args (S :|: eliminated_funs L) ys bs ys' ->
      Live_body L S (Eapp f ft ys) (Eapp f ft ys'). 

  
Inductive Live_params : list var -> list bool -> list var -> Ensemble var -> Prop :=
| PLive_nil : Live_params [] [] [] (Empty_set _)
| PLive_cons_L :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var) (S : Ensemble var),
      Live_params xs bs ys S ->
      Live_params (x :: xs) (false :: bs) ys (x |: S)
| PLive_cons_keep :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var) (S : Ensemble var),
      Live_params xs bs ys S ->
      Live_params (x :: xs) (true :: bs) (x :: ys) S. 
 

Inductive Live_fundefs (L : var -> option (list bool)) : fundefs -> fundefs -> Prop := 
| FLive_nil : 
  Live_fundefs L Fnil Fnil
| FLive_cons : 
  forall (F : fundefs) (F' : fundefs) (e : exp) (e' : exp) (xs ys : list var) (bs : list bool)
    (g : var) (ft : fTag) (S : Ensemble var), 
    L g = Some bs ->  
    Live_params xs bs ys S -> 
    Live_body L S e e' ->
    Live_fundefs L F F' ->
    Live_fundefs L (Fcons g ft xs e F) (Fcons g ft ys e' F'). 


Inductive Live (L : var -> option (list bool)) : fundefs -> exp -> fundefs -> exp -> Prop := 
| Live_toplevel :
    forall B e B' e',
      domain L <--> name_in_fundefs B -> (* XXX New *)
      Live_fundefs L B B' ->
      Live_body L (Empty_set _) e e' -> 
      Live L B e B' e'. 
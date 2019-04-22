(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
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

Fixpoint check_list_equality (l1 : list var) (l2 : list var) : bool := 
match (l1, l2) with 
| ([], []) => true
| (hd1 :: tl1, hd2 :: tl2) => if (peq hd1 hd2) then check_list_equality tl1 tl2 else false 
| _ => false
end. 

Fixpoint drop_args (ys : list var) (bs : list bool) : list var := 
match ys, bs with 
| [], [] => ys
|y :: ys', b :: bs' => 
  if (eqb b true) then y :: (drop_args ys' bs')
  else drop_args ys' bs'
| _, _ => ys
end. 
(* 
Fixpoint Drop_args (ys : list var) (bs : list bool) (ys' : list var) : Prop := 
let xs' := drop_args ys bs in
if check_list_equality xs' ys' then True
else False. 
 *)


(* S is the set of the dropped parameters of the function we're in. We need it
   to make sure that these are not used anywhere in the program, and so the proof will go through.
   Everything that we want to keep we want to make sure that is not in S.
   the list of booleans is the drop parameters of the function we are calling and we need it so that
   the application has the right arity.
 *)
Inductive Drop_args (S : Ensemble var) : list var -> list bool -> list var -> Prop :=
| ADrop_nil : Drop_args S [] [] []
| ADrop_cons_drop :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var),
      Drop_args S xs bs ys ->
      Drop_args S (x :: xs) (false :: bs) ys
| ADrop_cons_keep :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var),
      Drop_args S xs bs ys ->
      ~ x \in S -> 
      Drop_args S (x :: xs) (true :: bs) (x :: ys).

Definition dropped_funs drop : Ensemble var :=
  [set f | exists bs, drop f = Some bs /\ Exists (fun x => x = false) bs]. 

(* S is the set of formal parameters that have been dropped from the *current* function.
   That is, whatever is in S, is undefined in the environment when we execute the code. *)
Inductive Drop_body (drop : var -> option (list bool)) (S : Ensemble var) :  exp -> exp -> Prop := 
| BDrop_Constr : 
  forall (x : var) (ys : list var) (ct : cTag) (e : exp) (e' : exp), 
    Disjoint _ (FromList ys) (S :|: dropped_funs drop) -> 
    Drop_body drop S e e' ->
    Drop_body drop S (Econstr x ct ys e) (Econstr x ct ys e')
| BDrop_Prim : 
  forall (x : var) (g : prim) (ys : list var) (e : exp) (e' : exp), 
    Disjoint _ (FromList ys) (S :|: dropped_funs drop) -> 
    Drop_body drop S e e' ->
    Drop_body drop S (Eprim x g ys e) (Eprim x g ys e')
| BDrop_Proj : 
  forall (x : var) (ct : cTag) (n : N) (y : var) (e : exp) (e' : exp), 
    ~ y \in (S :|: dropped_funs drop) ->
    Drop_body drop S e e' ->
    Drop_body drop S (Eproj x ct n y e) (Eproj x ct n y e')
| BDrop_Case: 
  forall (x : var) (ce : list (cTag * exp)) (ce' : list (cTag * exp)),
    ~ x \in (S :|: dropped_funs drop) ->
    Forall2 (fun p1 p2 => fst p1 = fst p2 /\ Drop_body drop S (snd p1) (snd p2)) ce ce' -> 
    Drop_body drop S (Ecase x ce) (Ecase x ce')
| BDrop_Halt : 
    forall (x : var),
      ~ x \in (S :|: dropped_funs drop) ->
      Drop_body drop S (Ehalt x) (Ehalt x)
| BDrop_App_Unknown :
    forall (f : var) (ys : list var) (ft : fTag),
      (* Unknown function application, f is not in the list of top-level
         function definitions. Therefore, it must be a parameter of the current
         function *)
      ~ f \in (S :|: dropped_funs drop) ->
      Disjoint _ (FromList ys) (S :|: dropped_funs drop) -> 
      drop f = None -> 
      Drop_body drop S (Eapp f ft ys) (Eapp f ft ys)
| BDrop_App_Known :
    forall (f : var) (ys : list var) (ys' : list var) (ft : fTag) (bs : list bool),
      drop f = Some bs ->
      ~ f \in S ->
      Drop_args (S :|: dropped_funs drop) ys bs ys' ->
      Drop_body drop S (Eapp f ft ys) (Eapp f ft ys').

  
Inductive Drop_params : list var -> list bool -> list var -> Ensemble var -> Prop :=
| PDrop_nil : Drop_params [] [] [] (Empty_set _)
| PDrop_cons_drop :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var) (S : Ensemble var),
      Drop_params xs bs ys S ->
      Drop_params (x :: xs) (false :: bs) ys (x |: S)
| PDrop_cons_keep :
    forall (x : var) (xs : list var) (bs: list bool) (ys : list var) (S : Ensemble var),
      Drop_params xs bs ys S ->
      Drop_params (x :: xs) (true :: bs) (x :: ys) S.


Inductive Drop_body_fundefs (drop : var -> option (list bool)) : fundefs -> fundefs -> Prop := 
| FDrop_nil : 
  Drop_body_fundefs drop Fnil Fnil
| FDrop_cons : 
  forall (F : fundefs) (F' : fundefs) (e : exp) (e' : exp) (xs ys : list var) (bs : list bool)
    (g : var) (ft : fTag) (S : Ensemble var), 
    drop g = Some bs ->  
    Drop_params xs bs ys S -> 
    Drop_body drop S e e' ->
    Drop_body_fundefs drop F F' ->
    Drop_body_fundefs drop (Fcons g ft xs e F) (Fcons g ft ys e' F'). 


Inductive Drop (drop : var -> option (list bool)) : fundefs -> exp -> fundefs -> exp -> Prop := 
| Drop_toplevel :
    forall B e B' e',
      Drop_body_fundefs drop B B' ->
      Drop_body drop (Empty_set _) e e' -> 
      Drop drop B e B' e. 
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

Fixpoint Drop_args (ys : list var) (bs : list bool) (ys' : list var) : Prop := 
let xs' := drop_args ys bs in
if check_list_equality xs' ys' then True
else False. 

Inductive Drop_body (f : var) (bs : list bool) : exp -> exp -> Prop := 
| BDrop_Constr : 
  forall (x : var) (ys : list var) (ct : cTag) (e : exp) (e' : exp), 
  Drop_body f bs e e' ->
  Drop_body f bs (Econstr x ct ys e') (Econstr x ct ys e')
| BDrop_App_Same :
  forall (ys : list var) (ys' : list var) (ft : fTag),
  Drop_args ys bs ys' ->
  Drop_body f bs (Eapp f ft ys) (Eapp f ft ys')
| BDrop_App_Diff :
  forall (ys : list var) (ft : fTag),
  Drop_body f bs (Eapp f ft ys) (Eapp f ft ys)
| BDrop_Halt : 
  forall (x : var), 
  Drop_body f bs (Ehalt x) (Ehalt x)
(* Note that this case is impossible *)
| BDrop_Fun : 
  forall (B : fundefs) (e : exp), 
  Drop_body f bs (Efun B e) (Efun B e)
| BDrop_Prim : 
  forall (x : var) (g : prim) (ys : list var) (e : exp) (e' : exp), 
  Drop_body f bs e e' ->
  Drop_body f bs (Eprim x g ys e) (Eprim x g ys e')
| BDrop_Proj : 
  forall (x : var) (ct : cTag) (n : N) (y : var) (e : exp) (e' : exp), 
  Drop_body f bs e e' ->
  Drop_body f bs (Eproj x ct n y e) (Eproj x ct n y e')
| BDrop_Case: 
  forall (x : var) (ce : list (cTag * exp)) (ce' : list (cTag * exp)),
  (*Drop_case f bs ce ce' ->*)
  Drop_body f bs (Ecase x ce) (Ecase x ce'). 

Inductive Drop_case (f : var) (bs : list bool) : list (cTag * exp) -> list (cTag * exp) -> Prop := 
| CDrop_nil : 
  forall (x : var),
  Drop_case f bs [] []
| CDrop_cons : 
  forall (ct : cTag) (e : exp) (e' : exp) (ce : list (cTag * exp)) (ce' : list (cTag * exp)), 
  Drop_body f bs e e' ->
  Drop_case f bs ce ce'->
  Drop_case f bs ((ct, e) :: ce) ((ct, e') :: ce'). 

Inductive Drop_body_fundefs (f : var) (bs : list bool) : fundefs -> fundefs -> Prop := 
| FDrop_nil : 
  Drop_body_fundefs f bs Fnil Fnil
| FDrop_cons : 
  forall (F : fundefs) (F' : fundefs) (e : exp) (e' : exp) (xs : list var)
  (g : var) (ft : fTag), 
  Drop_body f bs e e' ->
  Drop_body_fundefs f bs F F' ->
  Drop_body_fundefs f bs (Fcons g ft xs e F) (Fcons g ft xs e' F'). 

Inductive Drop (S : Ensemble var) : fundefs -> exp -> fundefs -> exp -> Prop := 
| Drop_Fnil : forall (e : exp) , Drop S Fnil e Fnil e
| Drop_Fcons : 
  forall (F : fundefs) (F' : fundefs) (F'' : fundefs) (e : exp) (e' : exp) (e'' : exp)
  (f : var) (xs : list var) (xs' : list var) (bs : list bool) 
  (ef : exp) (ef' : exp) (ft : fTag), 
  Drop S F e F' e' -> 
  Filter S xs xs' ->
  Drop_body f bs ef ef' ->
  Drop_body f bs e' e'' ->
  Drop_body_fundefs f bs F' F'' ->
  Drop S (Fcons f ft xs ef F) e (Fcons f ft xs' ef' F'') e''. 

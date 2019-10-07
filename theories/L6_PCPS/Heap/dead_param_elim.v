(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Katja Vassilev, 2018
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

Inductive live_fun : Type := 
| Live: list (list var) -> list (list bool) -> live_fun. 

Fixpoint bool_live (L : live_fun) : list (list bool) := 
match L with
| Live yss bss => bss
end. 

(* list of list of variables corresponding to list of fundefs *)
Fixpoint get_vars (B : fundefs) : list (list var) := 
match B with 
| Fcons f ft xs e B' => xs :: (get_vars B')
| Fnil => []
end. 

Fixpoint get_funs (B : fundefs) : list var := 
match B with 
| Fcons f ft xs e B' => f :: get_funs B' 
| Fnil => []
end. 

(* Get list of list of bools corresponding to fundefs *)
Fixpoint get_bool_false (ys : list var) : list bool := 
match ys with 
| y :: ys' => false :: get_bool_false ys'
| [] => []
end. 

Fixpoint get_bool_true (ys : list var) : list bool :=
match ys with 
| [] => []
| y :: ys' => true :: get_bool_true ys'
end. 

Fixpoint get_bools (B : fundefs) : list (list bool) := 
match B with 
| Fcons f ft ys e B' => get_bool_false ys :: get_bools B'
| Fnil => []
end. 

(* Make initial live function *)
Fixpoint get_live_initial (B : fundefs) : live_fun := 
let yss := get_vars B  in
let bss := get_bools B  in 
(Live yss bss). 

Fixpoint contains (xs : list var) (y : var) : bool := 
match xs with 
| [] => false
| x :: xs' => if (peq x y) then true else contains xs' y
end. 

(* Replace nth variable of list*)
Fixpoint replace_nth (X : Type) (n : nat) (ys : list X) (x : X) : list X := 
match n, ys with
| 0, y :: ys' => x :: ys'
| S n', y :: ys' => y :: (replace_nth X n' ys' x)
| _, _ => ys
end. 
Arguments replace_nth {X}. 

Fixpoint find_fun (x : var) (funs : list var) (n : nat) : bool * nat := 
match funs with 
| [] => (false, n)
| f :: funs' => if (peq f x) then (true, n) else find_fun x funs' (n+1)
end. 

(* FUNCTIONS EXPLICITLY ALTERING LIVE FUNCTION *)

Fixpoint add_escaping (x : var) (L : live_fun) (funs : list var) : live_fun :=
let (b, n) := find_fun x funs 0 in
if b then 
  match L with 
  | Live yss bss =>
    let ys := nth n yss [] in
    let bs := get_bool_true ys in
    let bss' := replace_nth n bss bs in
    Live yss bss'
  end
else L. 

Fixpoint add_escapings (xs : list var) (L : live_fun) (funs : list var) (f : var) : live_fun :=
if contains funs f then 
match xs with 
| x :: xs' => add_escapings xs' (add_escaping x L funs) funs f
| [] => L
end
else L. 

Fixpoint add_escapings' (xs : list var) (L : live_fun) (funs : list var) : live_fun :=
match xs with 
| x :: xs' => add_escapings' xs' (add_escaping x L funs) funs
| [] => L
end. 

(* Find the relevant variable and unL it if necessary *)
Fixpoint add_var_helper (x : var) (ys : list var) (bs : list bool) : list bool := 
match ys, bs with 
| y :: ys', b :: bs' => if (peq x y) then (true :: bs') else (b :: (add_var_helper x ys' bs'))
| _, _ => bs
end. 

(* UnL a variable *)
Fixpoint add_var (x : var) (L : live_fun) (n : nat) : live_fun := 
match L with
| Live yss bss => 
  let ys := nth n yss [] in
  let bs := nth n bss [] in
  let bs' := add_var_helper x ys bs in
  let bss' := replace_nth n bss bs' in 
  Live yss bss'
end. 

(* UnL a list of variables *)
Fixpoint add_vars (xs : list var) (L : live_fun) (n : nat) : live_fun := 
match xs with 
| [] => L
| x :: xs' => add_vars xs' (add_var x L n) n
end. 

Fixpoint add_fun_args (n : nat) (xs : list var) (bs : list bool) (L : live_fun) : live_fun :=
match (xs, bs) with 
| ([], []) => L
| (x :: xs', b :: bs') => 
  if (eqb b true) then let L' := add_var x L n in add_fun_args n xs' bs' L'
  else add_fun_args n xs' bs' L
| _ => L
end. 

Fixpoint add_fun_vars (f : var) (funs : list var) (xs : list var) (L : live_fun) (m : nat) : live_fun :=
let (b, n) := find_fun f funs 0 in
if b then (
  let bss := bool_live L in
  let bs := nth n bss [] in
  add_fun_args m xs bs L
)
else add_vars xs L m. 

(* IDENTIFYING ESCAPING FUNCTIONS *)

Fixpoint escaping_fun_exp (e : exp) (L : live_fun) (funs : list var) := 
match e with 
| Eapp f t ys =>
  add_escapings' ys L funs 
| Econstr x t ys e' => escaping_fun_exp e' (add_escapings' ys L funs) funs 
| Eproj x t n y e' => escaping_fun_exp e' L funs
| Ecase x P => 
  (fix mapM_LD (l : list (ctor_tag * exp)) (L : live_fun) := 
  match l with 
  | [] => L
  | (c', e') :: l' =>
    let L' := escaping_fun_exp e' L funs in mapM_LD l' L'
  end) P L
| Ehalt x => add_escaping x L funs
| Efun fl e' => L
| Eprim x fs ys e' => escaping_fun_exp e' L funs
end. 

Fixpoint escaping_fun_fundefs (B : fundefs) (L : live_fun) (funs : list var) := 
match B with 
| Fcons f ft xs e B' => 
  let L' := escaping_fun_exp e L funs in
  escaping_fun_fundefs B' L' funs
| Fnil => L
end. 

(* LIVE PARAMETER ANALYSIS *)

Fixpoint live_expr (B : fundefs) (L : live_fun) (funs : list var) (n : nat) (e : exp) : live_fun := 
match e with 
| Econstr x t ys e' => 
  let L' := add_vars ys L n in
  live_expr B L' funs n e'
| Eproj x t m y e' => 
  let L' := add_var y L n in
  live_expr B L' funs n e'
| Ecase x P => 
  let L' := add_var x L n in
  (fix mapM_LD  (l : list (ctor_tag * exp))  (L : live_fun) := 
  match l with 
  | [] => L
  | (c', e') :: l'=>
    let L' := live_expr B L funs n e' in
    mapM_LD l' L'
  end) P L'
| Ehalt x => add_var x L n 
| Eapp f t ys =>  
  let L' := add_var f L n in
  let L'' := add_fun_vars f funs ys L' n in
  L''
| Efun fl e' => L
| Eprim x f ys e' =>  
  let L' := add_var f L n in
  let L'' := add_vars ys L' n in
  live_expr B L'' funs n e'
end. 

(* One pass through fundefs to L variables and keep track of live variables *)
Fixpoint live (B : fundefs) (L : live_fun) (funs : list var) (n : nat) : live_fun := 
match B with 
| Fcons f ft xs e B' => 
  let L' := live_expr B L funs n e in
  live B' L' funs (n+1)
| Fnil => L
end. 

Fixpoint check_list_equality (l1 : list bool) (l2 : list bool) : bool := 
match (l1, l2) with 
| ([], []) => true
| (hd1 :: tl1, hd2 :: tl2) => if (eqb hd1 hd2) then check_list_equality tl1 tl2 else false 
| _ => false
end. 

Fixpoint check_list_list_equality (l1 : list (list bool)) (l2 : list (list bool)) : bool := 
match (l1, l2) with
|([], []) => true
|(hd1 :: tl1, hd2 :: tl2) => if (check_list_equality hd1 hd2) then check_list_list_equality tl1 tl2 else false
| _ => false
end. 

Fixpoint live_equality (L1: live_fun) (L2 : live_fun) : bool := 
match (L1, L2) with
|(Live yss1 bss1, Live yss2 bss2) =>
  check_list_list_equality bss1 bss2
end. 

Fixpoint num_vars (B : fundefs) (n : nat) : nat := 
match B with 
| Fcons f ft xs e B' => num_vars B' (n + length(xs))
| Fnil => n
end. 

(* Iteratively create live functions for B, when they are equal, stop *)
(* Note that a naive upper bound for the number of passes is the number of total variables
   as at each step, if the process doesn't terminate at least one variable must be eliminated *)
Fixpoint find_live_helper (B : fundefs) (prev_L : live_fun) (funs : list var) (n : nat) : live_fun := 
match n with 
| 0 => prev_L
| S n' => 
  let curr_L := live B prev_L funs 0 in 
  if (live_equality prev_L curr_L) then prev_L
  else find_live_helper B curr_L funs n'
end. 

Fixpoint find_live (e : exp) : live_fun := 
match e with 
| Efun B e' =>
  let funs := get_funs B in
  let initial_L := get_live_initial B in
  let L' := escaping_fun_exp e' (escaping_fun_fundefs B initial_L funs) funs in
  let n := num_vars B 0 in
  find_live_helper B L' funs n
| _ => Live [[]] [[]]
end. 

Fixpoint live_args (ys : list var) (bs : list bool) : list var := 
match ys, bs with 
| [], [] => ys
| y :: ys', b :: bs' => 
  if (eqb b true) then y :: (live_args ys' bs')
  else live_args ys' bs'
| _, _ => ys
end. 

(* ELIMINATING VARIABLES *)

Fixpoint eliminate_expr (L : live_fun) (funs : list var) (e : exp) : exp := 
match e with 
| Econstr x t ys e' => Econstr x t ys (eliminate_expr L funs e')
| Eproj x t m y e' => Eproj x t m y (eliminate_expr L funs e')
| Ecase x P =>
  let P' := (fix mapM_LD (l : list (ctor_tag * exp)) : list (ctor_tag * exp) :=
  match l with 
  | [] => l
  | (c', e') :: l' => (c', eliminate_expr L funs e') :: mapM_LD l'
  end) P in
  Ecase x P'
| Ehalt x => Ehalt x
| Efun fl e' => e
| Eprim x f ys e' => Eprim x f ys (eliminate_expr L funs e')
| Eapp f t ys => 
  let (b, n) := find_fun f funs 0 in
  if b then (
    let bss := bool_live L in
    let ys' := live_args ys (nth n bss []) in
    Eapp f t ys')
  else Eapp f t ys
end. 

Fixpoint eliminate_fundefs (B : fundefs) (L : live_fun) (funs : list var) (n : nat) := 
match L with 
| Live yss bss =>
  match B with 
  | Fcons f ft ys e B' => 
    let ys' := live_args ys (nth n bss []) in
    let e' := eliminate_expr L funs e in
    Fcons f ft ys' e' (eliminate_fundefs B' L funs (n + 1))
  | Fnil => B
  end 
end. 

Fixpoint eliminate (e : exp) : exp := 
match e with 
| Efun B e' =>
  let funs := get_funs B in
  let L := find_live e in 
  let B' := eliminate_fundefs B L funs 0 in
  let e'' := eliminate_expr L funs e' in
  Efun B' e''
| _ => e
end. 










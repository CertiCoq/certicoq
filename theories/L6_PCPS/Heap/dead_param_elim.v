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

Inductive dropping_fun : Type := 
| Dropping: list (list var) -> list (list bool) -> dropping_fun. 

Fixpoint bool_drop (drop : dropping_fun) : list (list bool) := 
match drop with
| Dropping yss bss => bss
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

(* Make initial dropping function *)
Fixpoint get_drop_initial (B : fundefs) : dropping_fun := 
let yss := get_vars B  in
let bss := get_bools B  in 
(Dropping yss bss). 

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

Fixpoint add_escaping (x : var) (drop : dropping_fun) (funs : list var) : dropping_fun :=
let (b, n) := find_fun x funs 0 in
if b then 
  match drop with 
  | Dropping yss bss =>
    let ys := nth n yss [] in
    let bs := get_bool_true ys in
    let bss' := replace_nth n bss bs in
    Dropping yss bss'
  end
else drop. 

Fixpoint add_escapings (xs : list var) (drop : dropping_fun) (funs : list var) (f : var) : dropping_fun :=
if contains funs f then 
match xs with 
| x :: xs' => add_escapings xs' (add_escaping x drop funs) funs f
| [] => drop
end
else drop. 

Fixpoint add_escapings' (xs : list var) (drop : dropping_fun) (funs : list var) : dropping_fun :=
match xs with 
| x :: xs' => add_escapings' xs' (add_escaping x drop funs) funs
| [] => drop
end. 

(* Find the relevant variable and undrop it if necessary *)
Fixpoint add_var_helper (x : var) (ys : list var) (bs : list bool) : list bool := 
match ys, bs with 
| y :: ys', b :: bs' => if (peq x y) then (true :: bs') else (b :: (add_var_helper x ys' bs'))
| _, _ => bs
end. 

(* Undrop a variable *)
Fixpoint add_var (x : var) (drop : dropping_fun) (n : nat) : dropping_fun := 
match drop with
| Dropping yss bss => 
  let ys := nth n yss [] in
  let bs := nth n bss [] in
  let bs' := add_var_helper x ys bs in
  let bss' := replace_nth n bss bs' in 
  Dropping yss bss'
end. 

(* Undrop a list of variables *)
Fixpoint add_vars (xs : list var) (drop : dropping_fun) (n : nat) : dropping_fun := 
match xs with 
| [] => drop
| x :: xs' => add_vars xs' (add_var x drop n) n
end. 

Fixpoint add_fun_args (n : nat) (xs : list var) (bs : list bool) (drop : dropping_fun) : dropping_fun :=
match (xs, bs) with 
| ([], []) => drop
| (x :: xs', b :: bs') => 
  if (eqb b true) then let drop' := add_var x drop n in add_fun_args n xs' bs' drop'
  else add_fun_args n xs' bs' drop
| _ => drop
end. 

Fixpoint add_fun_vars (f : var) (funs : list var) (xs : list var) (drop : dropping_fun) (m : nat) : dropping_fun :=
let (b, n) := find_fun f funs 0 in
if b then (
  let bss := bool_drop drop in
  let bs := nth n bss [] in
  add_fun_args m xs bs drop
)
else add_vars xs drop m. 

Fixpoint escaping_fun_exp (e : exp) (drop : dropping_fun) (funs : list var) := 
match e with 
| Eapp f t ys =>
  add_escapings' ys drop funs 
| Econstr x t ys e' => escaping_fun_exp e' (add_escapings' ys drop funs) funs 
| Eproj x t n y e' => escaping_fun_exp e' drop funs
| Ecase x P => 
  (fix mapM_LD (l : list (cTag * exp)) (drop : dropping_fun) := 
  match l with 
  | [] => drop
  | (c', e') :: l' =>
    let drop' := escaping_fun_exp e' drop funs in mapM_LD l' drop'
  end) P drop
| Ehalt x => drop
| Efun fl e' => drop
| Eprim x fs ys e' => escaping_fun_exp e' drop funs
end. 

Fixpoint escaping_fun_fundefs (B : fundefs) (drop : dropping_fun) (funs : list var) := 
match B with 
| Fcons f ft xs e B' => 
  let drop' := escaping_fun_exp e drop funs in
  escaping_fun_fundefs B' drop' funs
| Fnil => drop
end. 

Fixpoint live_expr (B : fundefs) (drop : dropping_fun) (funs : list var) (n : nat) (e : exp) : dropping_fun := 
match e with 
| Econstr x t ys e' => 
  let drop' := add_vars ys drop n in
  live_expr B drop' funs n e'
| Eproj x t m y e' => 
  let drop' := add_var y drop n in
  live_expr B drop' funs n e'
| Ecase x P => 
  let drop' := add_var x drop n in
  (fix mapM_LD  (l : list (cTag * exp))  (drop : dropping_fun) := 
  match l with 
  | [] => drop
  | (c', e') :: l'=>
    let drop' := live_expr B drop funs n e' in
    mapM_LD l' drop'
  end) P drop'
| Ehalt x => add_var x drop n 
| Eapp f t ys =>  
  let drop' := add_var f drop n in
  let drop'' := add_fun_vars f funs ys drop' n in
  drop''
| Efun fl e' => drop
| Eprim x f ys e' =>  
  let drop' := add_var f drop n in
  let drop'' := add_vars ys drop' n in
  live_expr B drop'' funs n e'
end. 

(* One pass through fundefs to drop variables and keep track of live variables *)
Fixpoint live (B : fundefs) (drop : dropping_fun) (funs : list var) (n : nat) : dropping_fun := 
match B with 
| Fcons f ft xs e B' => 
  let drop' := live_expr B drop funs n e in
  live B' drop' funs (n+1)
| Fnil => drop
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

Fixpoint drop_equality (drop1: dropping_fun) (drop2 : dropping_fun) : bool := 
match (drop1, drop2) with
|(Dropping yss1 bss1, Dropping yss2 bss2) =>
  check_list_list_equality bss1 bss2
end. 

Fixpoint num_vars (B : fundefs) (n : nat) : nat := 
match B with 
| Fcons f ft xs e B' => num_vars B' (n + length(xs))
| Fnil => n
end. 

(* Inductively create dropping functions for B, when they are equal, stop *)
(* Note that a naive upper bound for the number of passes is the number of total variables
   as at each step, if the process doesn't terminate at least one variable must be dropped *)
Fixpoint find_drop_helper (B : fundefs) (prev_drop : dropping_fun) (funs : list var) (n : nat) : dropping_fun := 
match n with 
| 0 => prev_drop
| S n' => 
  let curr_drop := live B prev_drop funs 0 in 
  if (drop_equality prev_drop curr_drop) then prev_drop
  else find_drop_helper B curr_drop funs n'
end.

Fixpoint find_drop (e : exp) : dropping_fun := 
match e with 
| Efun B e' =>
  let funs := get_funs B in
  let initial_drop := get_drop_initial B in
  let drop' := escaping_fun_exp e' (escaping_fun_fundefs B initial_drop funs) funs in
  let n := num_vars B 0 in
  (* initial_drop *)
  (* drop' *)
  find_drop_helper B drop' funs n
| _ => Dropping [[]] [[]]
end. 

Fixpoint drop_args (ys : list var) (bs : list bool) : list var := 
match ys, bs with 
| [], [] => ys
| y :: ys', b :: bs' => 
  if (eqb b true) then y :: (drop_args ys' bs')
  else drop_args ys' bs'
| _, _ => ys
end. 

Fixpoint dropper_expr (drop : dropping_fun) (funs : list var) (e : exp) : exp := 
match e with 
| Econstr x t ys e' => Econstr x t ys (dropper_expr drop funs e')
| Eproj x t m y e' => Eproj x t m y (dropper_expr drop funs e')
| Ecase x P =>
  let P' := (fix mapM_LD (l : list (cTag * exp)) : list (cTag * exp) :=
  match l with 
  | [] => l
  | (c', e') :: l' => (c', dropper_expr drop funs e') :: mapM_LD l'
  end) P in
  Ecase x P'
| Ehalt x => Ehalt x
| Efun fl e' => e
| Eprim x f ys e' => Eprim x f ys (dropper_expr drop funs e')
| Eapp f t ys => 
  let (b, n) := find_fun f funs 0 in
  if b then (
    let bss := bool_drop drop in
    let ys' := drop_args ys (nth n bss []) in
    Eapp f t ys')
  else Eapp f t ys
end. 

Fixpoint dropper_fundefs (B : fundefs) (drop : dropping_fun) (funs : list var) (n : nat) := 
match drop with 
| Dropping yss bss =>
  match B with 
  | Fcons f ft ys e B' => 
    let ys' := drop_args ys (nth n bss []) in
    let e' := dropper_expr drop funs e in
    Fcons f ft ys' e' (dropper_fundefs B' drop funs (n + 1))
  | Fnil => B
  end 
end. 

Fixpoint dropper (e : exp) : exp := 
match e with 
| Efun B e' =>
  let funs := get_funs B in
  let drop := find_drop e in 
  let B' := dropper_fundefs B drop funs 0 in
  let e'' := dropper_expr drop funs e' in
  Efun B' e''
| _ => e
end. 










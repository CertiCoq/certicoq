(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Katja Vassilev, 2018
 *)

Require Import L6.cps L6.identifiers L6.ctx L6.set_util L6.state.
Require Import compcert.lib.Coqlib Common.exceptionMonad.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(* Map from function identifier to its live parameter list *)
Definition live_fun : Type :=  M.t (list bool).

Definition get_fun_vars (m : live_fun) (f : var) := M.get f m. 

Definition set_fun_vars (m : live_fun) (f : var) (b : list bool) := M.set f b m. 

(* Get list of list of bools corresponding to fundefs *)
Fixpoint get_bool_false {A} (ys : list A) : list bool := 
match ys with 
| y :: ys' => false :: get_bool_false ys'
| [] => []
end. 

Fixpoint get_bool_true {A} (ys : list A) : list bool :=
match ys with 
| [] => []
| y :: ys' => true :: get_bool_true ys'
end. 

(* Make initial live function *)
Fixpoint init_live_fun_aux (m : live_fun) (B : fundefs) : live_fun :=
  match B with
  | Fcons f ft xs e B' => init_live_fun_aux (set_fun_vars m f (get_bool_false xs)) B'
  | Fnil => m
end. 


Definition get_live_initial (B : fundefs) : live_fun := init_live_fun_aux (M.empty _) B.

Definition add_escaping (L : live_fun) (f : var) : live_fun :=
  match get_fun_vars L f with
  | Some bs => set_fun_vars L f (get_bool_true bs)
  | None => L
  end.

Fixpoint add_escapings (L : live_fun) (fs : list var) : live_fun :=
  fold_left add_escaping fs L.


(* IDENTIFYING ESCAPING FUNCTIONS *)
Fixpoint escaping_fun_exp (e : exp) (L : live_fun) := 
match e with 
| Eapp f t ys => add_escapings L ys
| Econstr x t ys e' => escaping_fun_exp e' (add_escapings L ys)
| Eproj x t n y e' => escaping_fun_exp e' (add_escaping L y)
| Eletapp x f ft ys e' => escaping_fun_exp e' (add_escapings L ys)
| Ecase x P => 
  (fix mapM_LD (l : list (ctor_tag * exp)) (L : live_fun) := 
     match l with 
     | [] => L
     | (c', e') :: l' =>
       let L' := escaping_fun_exp e' L in mapM_LD l' L'
     end) P L
| Ehalt x => add_escaping L x
| Efun fl e' => escaping_fun_exp e' (escaping_fun_fundefs fl L)
| Eprim x fs ys e' => escaping_fun_exp e' (add_escapings L ys)
end
with escaping_fun_fundefs (B : fundefs) (L : live_fun) := 
       match B with 
       | Fcons f ft xs e B' => 
         let L' := escaping_fun_exp e L in
         escaping_fun_fundefs B' L'
       | Fnil => L
       end. 

(* LIVE PARAMETER ANALYSIS *)

Definition add_list (xs : list var) (s : PS.t)  :=
  fold_left (fun s x => PS.add x s) xs s.

Definition add_fun_vars (L : live_fun) (f : var) (xs : list var) (S : PS.t) : PS.t :=
  let fix aux xs (bs : list bool) S :=
      match xs, bs with
      | [], _ | _, [] => S
      | x :: xs, b :: bs =>
        if b then aux xs bs (PS.add x S) else aux xs bs S
      end in
  match get_fun_vars L f with
  | Some bs => aux xs bs S
  | None => add_list xs S
  end.

(* Returns a set that's an underapproximation of the live vars in e *) 
Fixpoint live_expr (L : live_fun) (e : exp) (S : PS.t) : PS.t := 
match e with 
| Econstr x t ys e' => 
  live_expr L e' (add_list ys S)
| Eproj x t m y e' =>
  live_expr L e' (PS.add y S)
| Eletapp x f ft ys e' =>
  let S' := PS.add f S in
  let S'' := add_fun_vars L f ys S' in
  live_expr L e' S''
| Ecase x P =>
  let S' := PS.add x S in
  (fix mapM_LD  (S: PS.t) (l : list (ctor_tag * exp)) : PS.t := 
     match l with 
     | [] => S
     | (c', e') :: l'=>
       let S' := live_expr L e' S in
       mapM_LD S' l'
     end) S P
| Ehalt x => PS.add x S 
| Eapp f t ys =>  
  let S' := PS.add f S in
  add_fun_vars L f ys S
| Efun fl e' => S (* Should not happen, assuming hoisted program *)
| Eprim x f ys e' => live_expr L e' (add_list ys S)
end.

Definition update_live_fun (L : live_fun) (f : var) (xs : list var) (S : PS.t) : option (live_fun * bool):=
  match get_fun_vars L f with
  | Some bs =>
    let fix update_bs xs bs : (list bool * bool) :=
        match xs, bs with
        | [], _ | _, [] => ([], false)
        | x :: xs, b :: bs =>
          let (bs', d) := update_bs xs bs in
          let b' := PS.mem x S in
          (b' :: bs', (negb (eqb b b') || d))
        end in
    let (bs, diff) := update_bs xs bs in
    Some (set_fun_vars L f bs, diff)
  | None => None
  end.


(* One pass through fundefs to L variables and keep track of live variables *)
Fixpoint live (B : fundefs) (L : live_fun) (diff : bool) : option (live_fun * bool) := 
match B with 
| Fcons f ft xs e B' => 
  let S := live_expr L e PS.empty in
  match update_live_fun L f xs S with
  | Some (L', d) => live B' L' (d || diff)
  | None => None
  end  
| Fnil => Some (L, diff)
end. 

(* Iteratively create live functions for B, when they are equal, stop *)
(* Note that a naive upper bound for the number of passes is the number of total variables
   as at each step, if the process doesn't terminate at least one variable must be eliminated *)
Fixpoint find_live_helper (B : fundefs) (prev_L : live_fun) (n : nat) : option live_fun := 
match n with 
| 0 => Some prev_L
| S n' =>
  match live B prev_L false with
  | Some (curr_L, diff) =>
    if diff then find_live_helper B curr_L n' else Some curr_L (* should be equal to prevL *)
  | None => None
  end
end.

Fixpoint num_vars (B : fundefs) (n : nat) : nat := 
match B with 
| Fcons f ft xs e B' => num_vars B' (n + length(xs))
| Fnil => n
end. 


Fixpoint find_live (e : exp) : option live_fun := 
  match e with 
  | Efun B e' =>
    let initial_L := get_live_initial B in
    let L' := escaping_fun_exp e' (escaping_fun_fundefs B initial_L) in
    let n := num_vars B 0 in
    find_live_helper B L' n
  | _ => Some (M.empty _)
  end. 

(* ELIMINATING VARIABLES *)

Fixpoint live_args (ys : list var) (bs : list bool) : list var := 
match ys, bs with 
| [], [] => ys
| y :: ys', b :: bs' => 
  if (eqb b true) then y :: (live_args ys' bs')
  else live_args ys' bs'
| _, _ => ys
end. 

Definition is_nil {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ :: _ => false
  end.

  
Fixpoint eliminate_expr (L : live_fun) (e : exp) : exp := 
match e with 
| Econstr x t ys e' => Econstr x t ys (eliminate_expr L e')
| Eproj x t m y e' => Eproj x t m y (eliminate_expr L e')
| Eletapp x f ft ys e' =>
  match get_fun_vars L f with
  | Some bs =>
    let ys' := live_args ys bs in
    if is_nil ys' then
    (* All arguments are redundant, keep the first.
     * I'm not sure if this is the optimal strategy.
     * An alternative would be to construct a unit value and pass as the argument
     * but that may be better or worse in terms of allocation *)
      match ys with
      | [] => Eletapp x f ft [] (eliminate_expr L e')
      | [y] | _ :: y :: _ => Eletapp x f ft [y] (eliminate_expr L e')
      end
    else 
      Eletapp x f ft ys' (eliminate_expr L e')
  | None => Eletapp x f ft ys (eliminate_expr L e')
  end
| Ecase x P =>
  let P' := (fix mapM_LD (l : list (ctor_tag * exp)) : list (ctor_tag * exp) :=
  match l with 
  | [] => l
  | (c', e') :: l' => (c', eliminate_expr L e') :: mapM_LD l'
  end) P in
  Ecase x P'
| Ehalt x => Ehalt x
| Efun fl e' => e
| Eprim x f ys e' => Eprim x f ys (eliminate_expr L e')
| Eapp f t ys => 
  match get_fun_vars L f with
  | Some bs =>
    let ys' := live_args ys bs in
    if is_nil ys' then
      match ys with
      | [] => Eapp f t []
      | [y] | _ :: y :: _ => Eapp f t [y]
      end
    else       
      Eapp f t ys'
  | None => Eapp f t ys 
  end
end.


Fixpoint eliminate_fundefs (B : fundefs) (L : live_fun) : option fundefs := 
  match B with 
  | Fcons f ft ys e B' =>
    match get_fun_vars L f with
    | Some bs =>
      let ys' := live_args ys bs in
      let ys'' :=
          if is_nil ys' then
            match ys with
            | [] => []
            | [y] |  _ :: y ::  _  => [y]    (* avoid keeping the (empty) closure environment (?) *)
            end
          else ys'
      in 
      let e' := eliminate_expr L e in
      match eliminate_fundefs B' L with
      | Some B'' => Some (Fcons f ft ys'' e' B'')
      | None => None
      end
    | None => None
    end
  | Fnil => Some Fnil
  end. 

Fixpoint eliminate (e : exp) : exp := 
match e with 
| Efun B e' =>
  match find_live e with
  | Some L => 
    match eliminate_fundefs B L with
    | Some B' => 
      let e'' := eliminate_expr L e' in
      Efun B' e''
    | None => e
    end
  | None => e
  end
| _ => e
end.

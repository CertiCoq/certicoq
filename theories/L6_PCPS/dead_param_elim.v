(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Katja Vassilev, 2018
 *)

Require Import L6.cps L6.identifiers L6.ctx L6.set_util L6.state.
Require Import compcert.lib.Coqlib Common.compM Common.Pipeline_utils.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.


Import MonadNotation.
Open Scope monad_scope.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(* Map from function identifier to its live parameter list *)
Definition live_fun : Type :=  M.t (list bool).

Definition get_fun_vars (m : live_fun) (f : var) := M.get f m. 

Definition set_fun_vars (m : live_fun) (f : var) (b : list bool) :=
  match b with
  | [] => m
  | _ => M.set f b m
  end. 

(* Apply bit mask to argument list*)
Fixpoint live_args (ys : list var) (bs : list bool) : list var := 
  match ys, bs with 
  | [], [] => ys
  | y :: ys', b :: bs' => 
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end. 

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
  fold_left (fun L '(c', e') => escaping_fun_exp e' L) P L
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

Definition add_fun_vars (L : live_fun) (f : var) (xs : list var) (S : PS.t) : PS.t :=
  match get_fun_vars L f with
  | Some bs =>
    let xs' := live_args xs bs in
    union_list S xs'
  | None => union_list S xs
  end.

(* Returns a set that's an underapproximation of the live vars in e *) 
Fixpoint live_expr (L : live_fun) (e : exp) (S : PS.t) : PS.t := 
match e with 
| Econstr x t ys e' => 
  live_expr L e' (union_list S ys)
| Eproj x t m y e' =>
  live_expr L e' (PS.add y S)
| Eletapp x f ft ys e' =>
  let S' := PS.add f S in
  let S'' := add_fun_vars L f ys S' in
  live_expr L e' S''
| Ecase x P =>
  PS.add x (fold_left (fun S '(c', e') => live_expr L e' S) P S)
| Ehalt x => PS.add x S 
| Eapp f t ys =>  
  let S' := PS.add f S in
  add_fun_vars L f ys S'
| Efun fl e' => S (* Should not happen, assuming hoisted program *)
| Eprim x f ys e' => live_expr L e' (union_list S ys)
end.

Fixpoint update_bs (S : PS.t) xs (bs : list bool) : (list bool * bool) :=
  match xs, bs with
  | [], _ | _, [] => (bs, false)
  | x :: xs, b :: bs =>
    let (bs', d) := update_bs S xs bs in
    if b then (b :: bs', d) (* if the bit is on don't change it *)
    else
      let b' := PS.mem x S in
      (b' :: bs', (negb (eqb b b') || d))
  end.

Definition update_live_fun (L : live_fun) (f : var) (xs : list var) (S : PS.t) : option (live_fun * bool):=
  match get_fun_vars L f with
  | Some bs =>
    let (bs, diff) := update_bs S xs bs in
    if diff then Some (set_fun_vars L f bs, diff)
    else  Some (L, diff)
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

Definition is_nil {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ :: _ => false
  end.


Definition arityMap : Type := M.t fun_tag.

Definition elimM := @compM' arityMap.

(* Single pass to create arity map. Assumes that initial fun_tags are consistent with arities *)
Fixpoint make_arityMap (e : exp) (m : arityMap) : arityMap :=
  match e with
  | Econstr _ _ _ e => make_arityMap e m
  | Ecase x bs =>
    fold_left (fun m p => make_arityMap (snd p) m) bs m 
  | Eproj _ _ _ _ e => make_arityMap e m
  | Eletapp x f ft xs e =>
    make_arityMap e (M.set (Positive_as_DT.of_succ_nat (length xs)) ft m)
  | Efun B e =>
    make_arityMap e (make_arityMap_fundefs B m)
  | Eapp f ft xs => M.set (Positive_as_DT.of_succ_nat (length xs)) ft m
  | Eprim _ _ _ e => make_arityMap e m
  | Ehalt x => m
  end
with make_arityMap_fundefs (B : fundefs) (m : arityMap) : arityMap :=
       match B with
       | Fcons f ft xs e B =>
         let m := M.set (Positive_as_DT.of_succ_nat (length xs)) ft m in
         make_arityMap_fundefs B (make_arityMap e m)
       | Fnil => m
       end.

Definition get_fun_tag (n : nat) : elimM fun_tag :=
  st <- get_state tt ;;
  let m := st in
  let p := Positive_as_DT.of_succ_nat n in
  match M.get p m with
  | Some t => ret t
  | None =>
    ft <- get_ftag (N.of_nat n) ;;
    put_state (M.set p ft m) ;;
    ret ft
  end.       
  

Definition show_bool (b : bool) : string :=
  if b then "true" else "false".


Fixpoint show_bool_list (bs : list bool) : string :=
  match bs with
  | [] => ""
  | b :: bs =>
    String.concat " " [show_bool b ; show_bool_list bs]
  end.



Fixpoint eliminate_expr (L : live_fun) (e : exp) : elimM exp := 
match e with 
| Econstr x t ys e' =>
  e'' <- eliminate_expr L e' ;;
  ret (Econstr x t ys e'')
| Eproj x t m y e' =>
  e'' <- eliminate_expr L e' ;;
  ret (Eproj x t m y e'')
| Eletapp x f ft ys e' =>
  f_str <- get_pp_name f ;;
  (* state.log_msg (String.concat " " ["Letapp" ; f_str ]) ;; *)
  match get_fun_vars L f with
  | Some bs =>
    ys_or <- get_pp_names_list ys ;;    
    (* state.log_msg (String.concat " " ("bs" ::  show_bool_list bs :: "Original Params" :: ys_or )) ;;  *)
    let ys' := live_args ys bs in
    e'' <- eliminate_expr L e';;
    ft <- get_fun_tag (length ys') ;;
    ys_names <- get_pp_names_list ys' ;;
    (* state.log_msg (String.concat " " ["Function entry" ; f_str ; "found"; "id"; cps_show.show_pos f]) ;; *)
    (* state.log_msg (String.concat " " ("New params" :: ys_names)) ;;    *)
    ret (Eletapp x f ft ys' e'')
  | None =>
    e'' <- eliminate_expr L e' ;;
    ret (Eletapp x f ft ys e'')
  end
| Ecase x P =>
  P' <- (fix mapM_LD (l : list (ctor_tag * exp)) : elimM (list (ctor_tag * exp)) :=
          match l with 
          | [] => ret []
          | (c', e') :: l' =>
            e' <- eliminate_expr L e';;
            l' <- mapM_LD l' ;;
            ret ((c', e') :: l')
          end) P ;;
  ret (Ecase x P')
| Ehalt x => ret (Ehalt x)
| Efun fl e' => ret e
| Eprim x f ys e' =>
  e'' <- eliminate_expr L e' ;;
  ret (Eprim x f ys e'')
| Eapp f ft ys => 
  match get_fun_vars L f with
  | Some bs =>
    let ys' := live_args ys bs in
    ft <- get_fun_tag (length ys') ;;
    ret (Eapp f ft ys')
  | None => ret (Eapp f ft ys)
  end
end.


Fixpoint eliminate_fundefs (B : fundefs) (L : live_fun) : elimM fundefs := 
  match B with 
  | Fcons f ft ys e B' =>
    match get_fun_vars L f with
    | Some bs =>
      let ys' := live_args ys bs in
      f_str <- get_pp_name f ;;
      ys_names <- get_pp_names_list ys' ;;
      ys_or <- get_pp_names_list ys ;;
      (* state.log_msg (String.concat " " ["Def Function entry" ; f_str ; "found" ; "id"; cps_show.show_pos f]) ;; *)
      (* state.log_msg (String.concat " " ("Def New params" :: ys_names)) ;; *)
      (* state.log_msg (String.concat " " ("bs" ::  show_bool_list bs :: "Original Params" :: ys_or )) ;; *)
      e' <- eliminate_expr L e ;;
      B'' <- eliminate_fundefs B' L ;;
      ft <- get_fun_tag (length ys') ;;
      ret (Fcons f ft ys' e' B'')
    | None => failwith "Known function not found in live_fun map"
    end
  | Fnil => ret Fnil
  end. 
           
Fixpoint eliminate (e : exp) (c_data : comp_data) : error exp * comp_data := 
  match e with 
  | Efun B e' =>
    match find_live e with
    | Some L =>
      let m := make_arityMap e (M.empty _) in
      match run_compM (eliminate_fundefs B L) c_data m with
      | (Ret B', (c_data, m)) => 
        match run_compM (eliminate_expr L e') c_data m with
        | (Ret e'', (c_data, m)) =>
          (Ret (Efun B' e''), c_data)
        | (Err s, (c_data, m)) => (Err s, c_data)
        end
      | (Err s, (c_data, m)) => (Err s, c_data)
      end
    | None => (Err "Dead param elim: find_live failed", c_data)
    end
  | e => (Ret e, c_data)
  end.

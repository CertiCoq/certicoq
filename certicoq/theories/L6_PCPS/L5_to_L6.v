(* Convertion from 
       cpstrans.cps  (L5)
              to
       cps.exp (L6)
    resulting in globally unique names  

  2015 - Olivier Savary Belanger 




   DONE: fix recursive definition of list-based convert for termination checker
      for some reason wouldn't accept termination even when rewritten with fold_right, had to pull up all 3 list-based convert as definitions 
   DONE : modify convert_v s.t. it doesn't bind Var and KVar to a new name (e.g. by returning list of bindings) 
   DONE: fix conversion of functions, branches to new syntax (datatypes instead of lists) 
   TODO : populate the types (ty atm) within expressions

new

*)     
Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Bool.
Require Maps.
Require Recdef.
Import Nnat.
Require Import CpdtTactics.


Require Import List.




(* Add LoadPath "../L5_CPS" as CPS.
Add LoadPath "../common" as Common.
Add LoadPath "../L4_deBruijn" as L4. *)


Require Import CPS.cpstrans. (* using cps for db cps terms *)
Require Import cps. (* shadows exp from simple_cps for nominal cps terms *)
Require Import cps_util.


(* returns list of numbers from n to n+m (excluding n+m) and the positive n+m (next available pos) *)
Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
  match m with
  | O => (nil, n)
  | S m' =>
    let (l, nm ) := (fromN (n+1) (m')) in
    (n::l, nm)
  end.





(* placeholder *)
Variable default_tag : M.elt.
Definition dcon_to_tag: dcon -> tag := N.succ_pos. (* should probably change dcon to positive in simple_cps *)
Variable var_tag : M.elt.
Variable kvar_tag : M.elt.
Variable rec_tag : M.elt.

Variable ty_fun : positive. (* Regular function (lam) in simple_cps *)
Variable ty_con : positive. (* continuation in simple_cps *)
Variable ty : positive.  (* everything else *)


(*  
  NOTE:  use slower ctx_bind_proj' since this relies on opaque proofs
 
create a context binding m projections of var n to var (n+1+m)
 i.e. each binding has form  ({| let var (n + m + 1) := \pi_(m-1) var n in [] |})
   
  *)
           
Function ctx_bind_proj (n:positive) (m:N) {wf N.lt m}: exp_ctx :=
  if N.eqb m 0%N then
    Hole_c
  else
    let ctx_p' := ctx_bind_proj n (N.pred m) in
    Eproj_c (Pos.add n (N.succ_pos m)) ty (N.pred m ) n ctx_p'.
Proof.
  intros. apply N.lt_pred_l.  apply N.eqb_neq in teq. assumption. apply N.lt_wf_0. 
Defined.



Fixpoint ctx_bind_proj' (n:positive) (m:nat): exp_ctx :=
  match m with
    | O => Hole_c
    | S m' =>
      let ctx_p' := ctx_bind_proj' n m' in
      Eproj_c (Pos.add n (Pos.of_succ_nat m)) ty (N.of_nat m') n ctx_p'
  end.





Fixpoint fnlst_length (vs:fnlst) : nat :=
  match vs with
    | flnil => 0
    | flcons e fds' => S (fnlst_length fds')
  end.





(* 
  sv is a stack used to convert variable indices to name
sk is a stack mapping continuation indices to name
n is the next available name.

returns pair of converted expression e' and the next available variable name n'
        The names bound in e' are exactly [n, n'[

note : var "2" is taken as an external function standing for "halt"
       var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 


*)
Fixpoint convert (e:cps) (sv:list var) (sk:list var) (n:var) (*{| struct e |}*) : exp * var :=
       match e with
       | Halt_c v => let (ll, n') := convert_v v sv sk n in
                     let (ctx_v, vn) := ll in
                         (app_ctx_f ctx_v (Eapp (2%positive) (vn::nil) ), n')
       | Ret_c k v => let (ll1, n') := convert_v k sv sk n in
                      let (ctx_k, kn) := ll1 in
                      let (ll2, n'') := convert_v v sv sk n' in
                      let (ctx_v, vn) := ll2 in
                       (app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp kn (vn::nil)), n'')
       | Call_c f k v =>
         let (ll1, n') := convert_v f sv sk n in
         let (ctx_f, fn) := ll1 in
         let (ll2, n'') := convert_v k sv sk n' in
         let (ctx_k, kn) := ll2 in
         let (ll3, n''') := convert_v v sv sk n'' in
         let (ctx_v, vn) := ll3 in
         let ctx_fkv := comp_ctx_f ctx_f (comp_ctx_f ctx_k ctx_v) in
         (app_ctx_f ctx_fkv (Eapp fn (vn::kn::nil)), n''')
         
      | Match_c v bl =>
        let (ll, n') := convert_v v sv sk n in
        let (ctx_v, vn) := ll in
        let (fl, n'') := convert_branches bl sv sk n' in
        let (fds, tvl) := fl in
         (app_ctx_f ctx_v (Efun fds (Ecase vn tvl)), n'')
       end
(* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh name *)
    with convert_v (v:val_c) (sv: list var) (sk: list var) (n:var) (* {| struct v |} *): (exp_ctx * var * var) :=
           match v with
           | Var_c m => (Hole_c, (nth (N.to_nat m) sv (1%positive)), n)   (* {| ( Econstr_c n ty var_tag ((nth (N.to_nat m) sv (1%positive))::nil)  Hole_c, Pos.succ n  ) |} *)
           | KVar_c m => (Hole_c, (nth (N.to_nat m) sk (1%positive)), n) (* {| ( Econstr_c n ty kvar_tag ((nth (N.to_nat m) sk (1%positive))::nil) Hole_c, Pos.succ n) |} *)
           | Lam_c e => let (e', n') := convert e (n::sv) ((Pos.succ n)::sk) (Pos.add n (2%positive)) in
                        let fds := Fcons n' ty_fun (n::(Pos.succ n)::nil) e' Fnil in
                        (Efun1_c fds Hole_c, n' , (Pos.succ n'))
           | Cont_c e => let (e', n') := convert e sv (n::sk) (Pos.succ n) in
                         let fds := Fcons n' ty_con (n::nil) e' Fnil in
                         (Efun1_c fds Hole_c, n',  Pos.succ n')
           | Con_c dcn lv => 
             let (ll, n') := convert_v_list lv sv sk n in
             let (lv_ctx, nl) := ll in
             (comp_ctx_f lv_ctx (Econstr_c n' ty (dcon_to_tag dcn) nl Hole_c), n', Pos.succ n') 
           | Fix_c le i =>
             let nt := fnlst_length le in (* length of the mutually recursive block *)
             let (nfds, newn) := fromN n nt in
             let (fds, n') := convert_fds le (nfds++sv) sk n newn in
             (* the record should disappear during shrink reduction *) 
             (Efun1_c fds Hole_c, (nth (N.to_nat i) nfds (1%positive)),  n' )
           end
(*  convert a list of simple_cps cps functions into 
 (1) a set of cps.exp functions (fundefs), each referring to a local variable (n+1), a local continuation variable (n+2) and the functions name (pushed to sv before calling convert_fds
 (2) the next fresh name

arguments are: 
 - fds : the list of functions to convert
 - sv : the stack of names for local variables, including the names for the set of functions being converted
 - sk : the stack of names for continuation variables
 - currn : name of the next function to convert
 - n     : next available name 

 *)
with  convert_fds ( fds : fnlst)  (sv: list var) (sk : list var) (currn : var) (n : var) : (fundefs * var)  :=
  match fds with
    | flnil => (Fnil, n)
    | flcons e fds' =>
      let (ce, n') := convert e (n::sv) ((Pos.succ n)::sk) ((Pos.add n 2)) in
        let (cfds, n'') := convert_fds fds' sv sk (Pos.succ currn) n' in
        (Fcons currn ty_fun (n::(Pos.succ n)::nil) ce cfds, n'')
  end
with convert_v_list (lv :vals_c) (sv : list var) (sk: list var) (n: var) : (exp_ctx * list var * var) :=
  match lv with
    | vcnil => (Hole_c, nil, n)
    | vccons v lv' =>
      let '(ctx_v, vn , n') := convert_v v sv sk n in
      let '(ctx_lv', ln', n'') := convert_v_list lv' sv sk n' in
      (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'')

  end
(* Translates a list of branch cps into
   (1) a set of cps.exp functions (fundefs) representing the branches' continuation
   (2) a list of pairs grouping the tag with their continuation name
   (3) the next fresh name *)
with convert_branches (bl: branches_c) (sv: list var) (sk: list var) (n:var) (* {| struct bl |} *): (fundefs * list (tag * var) * var)  :=
    (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *)
    match bl with
      | brnil_c => (Fnil, nil, n)
      | brcons_c dcn m e bl' =>
        let '(cfds, cbl, n') := convert_branches bl' sv sk n in
        let ctx_p := ctx_bind_proj' (Pos.succ n') (N.to_nat m) in 
        let (xs, nm2) := fromN (Pos.add n' 2) (N.to_nat m) in
        let (ce, n'') :=  convert e (xs++sv) sk nm2 in 
        (Fcons n' ty_con ((Pos.succ n')::nil) (app_ctx_f ctx_p ce) cfds, ((dcon_to_tag dcn), n')::cbl ,   n'')
    end.

Definition convert_top (e:cps) : exp :=
  let (er, n) := convert e nil nil (3%positive) in er.


(*
 {| Example e1 : expression.exp := Lam_e (Var_e 0).  |}
{|  Example e2 : expression.exp := Lam_e (Lam_e (Var_e 1)).  |}
{|  Eval vm_compute in cps_cvt_prog e1.  |}
{|  Eval vm_compute in convert_top (cps_cvt_prog e1).  |}
 *)

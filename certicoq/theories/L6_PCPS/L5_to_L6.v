(* Convertion from 
       L4.L5A.cps  (L5a)
              to
       cps.exp (L6)
    resulting in globally unique names  

  2016 - Olivier Savary Belanger 

   TODO : populate the types (ty atm) within expressions



 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Maps.
Require Coq.funind.Recdef.
Import Nnat.
Require Import CpdtTactics.


Require Import ExtLib.Data.List.
Require Import L4.VarInstance.
Require Import L4.simpleCPSAA.
Require Import L4.L5a.

Require Import cps.
Require Import cps_util.
Require Import ctx.




  
(* placeholder *)
Variable default_tag : M.elt.
Variable var_tag : M.elt.
Variable kvar_tag : M.elt.
Variable rec_tag : M.elt.

Variable ty_fun : positive. (* Regular function (lam) in simple_cps *)
Variable ty_con : positive. (* continuation in simple_cps *)
Variable ty : positive.  (* everything else *)

Definition dcon_to_tag:dcon -> tag := N.succ_pos. (* should probably change dcon to positive in simple_cps *)


(* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
  match m with
  | O => (nil, n)
  | S m' =>
    let (l, nm ) := (fromN (n+1) (m')) in
    (n::l, nm)
  end.


(* Bind the m first projections of var r to variables [n, n+m[ *)
Fixpoint ctx_bind_proj (r:positive) (m:nat) (n:var) : (exp_ctx * var) :=
  match m with
    | O => (Hole_c, n)
    | S m' =>
      let (ctx_p', n') := ctx_bind_proj r m' n in
      (Eproj_c  n' ty (N.of_nat m') r ctx_p', Pos.succ n')
  end.

Definition s_map := M.t var.
Definition s_empty := M.empty var.

Definition get_s (a:M.elt) (sig:s_map):=
  match M.get a sig with
    | None => (1%positive)
    | Some v => v
  end.

Fixpoint set_s_list (lx ly:list var) (sig:s_map) :=
  match (lx, ly) with
    | (x::lx', y::ly') =>
      set_s_list lx' ly' (M.set x y sig)
    | _ => sig
  end.

(* 
  sv is a map used to convert variable indices to name
sk is a stack mapping continuation indices to name
n is the next available name.

returns pair of converted expression e' and the next available variable name n'
        The names bound in e' are exactly [n, n'[

note : var "2" is taken as an external function standing for "halt"
       var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 


 *)

Fixpoint convert (e:cps) (sv: s_map) (sk:s_map) (n:var) (*  {struct e } *): exp * var :=
       match e with
       | Halt_c v => let '(ctx_v, vn, n') := convert_v v sv sk n in
                         (app_ctx_f ctx_v (Eapp (2%positive) (vn::nil) ), n')
       | Ret_c k v => let '(ctx_k, kn, n') := convert_v k sv sk n in
                      let '(ctx_v, vn, n'') := convert_v v sv sk n' in
                       (app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp kn (vn::nil)), n'')
       | Call_c f k v =>
         (Eapp (get_s f sv) ((get_s v sv)::(get_s k sk)::nil) , n)
         
       | Match_c v bl =>
         let fix convert_branches (bl:list  ((dcon * nat) * ((list NVar)* cps))) (sv: s_map) (sk:s_map) (r:var) (n:var)  (* { struct bl } *): (list (tag * exp) * var)  :=
             (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *)
             match bl with
               | nil => ( nil, n)
               | ((dcn, m),(xs, e))::bl' =>
                 let (cbl, n') := convert_branches bl' sv sk r n in
                 let (ctx_p, n'') := ctx_bind_proj r m n' in 
                 let (names, _) := fromN n' m in
                 let sv' := set_s_list xs names sv in
                 let (ce, n''') :=  convert e sv' sk n'' in
                 (((dcon_to_tag dcn), (app_ctx_f ctx_p ce))::cbl , n''') 
             end in
         let '(ctx_v, vn, n') := convert_v v sv sk n in
         let '(cbls, n'') := convert_branches bl sv sk vn n' in
         (app_ctx_f ctx_v (Ecase vn cbls), n'')
       | Proj_c v m k =>
         let '(ctx_v, vn, n') := convert_v v sv sk n in
         let '(ctx_k, vk, n'') := convert_v k sv sk n' in
         (app_ctx_f (comp_ctx_f ctx_v ctx_k) (Eproj n'' ty (N.of_nat m) vn  (Eapp vk (n''::nil))), Pos.succ n'')
       end
(* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh 

Ret_c M N -> 
 let m = [[M]] in
  let n = [[N]] in
   App_e m n

*)
with convert_v (v:val_c) (sv: s_map) (sk: s_map) (n:var) (* { struct v }  *): (exp_ctx * var * var) :=
       match v with
         | Var_c m => (Hole_c, get_s m sv , n)   (* {| ( Econstr_c n ty var_tag ((nth (N.to_nat m) sv (1%positive))::nil)  Hole_c, Pos.succ n  ) |} *)
         | KVar_c m => (Hole_c, get_s m sk, n) (* {| ( Econstr_c n ty kvar_tag ((nth (N.to_nat m) sk (1%positive))::nil) Hole_c, Pos.succ n) |} *)
         | Lam_c x k e => let (e', n') := convert e (M.set x n sk) (M.set k (Pos.succ n) sk) (Pos.add n (2%positive)) in
                          let fds := Fcons n' ty_fun (n::(Pos.succ n)::nil) e' Fnil in
                          (Efun1_c fds Hole_c, n' , (Pos.succ n'))
         | Cont_c k e => let (e', n') := convert e sv (M.set k n sk) (Pos.succ n) in
                         let fds := Fcons n' ty_con (n::nil) e' Fnil in
                         (Efun1_c fds Hole_c, n',  Pos.succ n')
         | Con_c dcn lv =>
           let fix convert_v_list (lv :list val_c) (sv : s_map) (sk: s_map) (n: var)(* {struct lv} *): (exp_ctx * list var * var) :=
               match lv with
                 | nil => (Hole_c, nil, n)
                 | v::lv' =>
                   let '(ctx_v, vn , n') := convert_v v sv sk n in
                   let '(ctx_lv', ln', n'') := convert_v_list lv' sv sk n' in
                   (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'')
                     
               end in
           let '(lv_ctx, nl, n') := convert_v_list lv sv sk n in
             (comp_ctx_f lv_ctx (Econstr_c n' ty (dcon_to_tag dcn) nl Hole_c), n', Pos.succ n') 
         | Fix_c lbt =>
           (*  convert a list of simple_cps cps functions into 
               (1) a set of cps.exp functions (fundefs), each referring to a local variable (n+1), a local continuation variable (n+2) and the functions name (pushed to sv before calling convert_fds
 (2) the next fresh name

arguments are: 
 - fds : the l ist of functions to convert
 - sv : the stack of names for local variables, including the names for the set of functions being converted
 - sk : the stack of names for continuation variables
 - fnames : names given to each of the function left to convert in fds
 - n     : next available name 

 *)
           let fix convert_fds (fds : list (var * val_c))  (sv: s_map) (sk : s_map) (fnames : list var) (n : var) (*{struct fds} *): (fundefs * var)  :=
               match (fds, fnames) with
                 | ((f,v)::fds', currn::fnames') =>
                   (match v with
                      | Lam_c x k e =>            
                        let (ce, n') := convert e (M.set x n sv) (M.set k (Pos.succ n) sk) (Pos.add n 2%positive) in
                        let (cfds, n'') := convert_fds fds' sv sk fnames' n' in
                        (Fcons currn ty_fun (n::(Pos.succ n)::nil) ce cfds, n'')
                      | _ => (Fnil, n) (* this should not happen *)
                    end) 
                 | (_, _) => (Fnil, n)
               end in
           let (fnames, fbodys) := List.split lbt in (* length of the mutually recursive block *)
           let (nfds, newn) := fromN n (length lbt) in
           let sv' := set_s_list fnames nfds sv in
           let (fds, n') := convert_fds lbt sv' sk nfds newn in
           (* the record should disappear during shrink reduction *) 
           (Efun1_c fds (Econstr_c n' ty default_tag nfds Hole_c), n',  (Pos.succ n') )
       end.

Definition convert_top (e:cps) : exp :=
  let (er, n) := convert e s_empty s_empty (3%positive) in er.







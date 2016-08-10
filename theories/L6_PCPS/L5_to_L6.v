(* Convertion from 
       L4.L5A.cps  (L5a)
              to
       cps.exp (L6)
    resulting in globally unique names  

  2016 - Olivier Savary Belanger 


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
Require Import L4.simpleCPSAA.
Require Import SquiggleEq.varImplZ.
Require Import L4.L5a.

Require Import cps.
Require Import cps_util.
Require Import ctx.




Parameter halt: prim.
Parameter halt_tag: fTag.

                   
(* placeholder *)
Definition tag := positive.
Variable default_tag : tag.
Variable var_tag : tag.
Variable kvar_tag : tag.
Variable rec_tag : tag.
Variable fun_tag: tag.
Variable kon_tag: tag.
                    
Definition dcon_to_tag:dcon -> cTag :=
  fun x => N.succ_pos (snd x). (* should probably change dcon to positive in simple_cps *)


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
      (Eproj_c  n' rec_tag (N.of_nat m') r ctx_p', Pos.succ n')
  end.


Definition t_map := M.t tag.
Definition t_empty := M.empty tag.


Definition get_t (a:M.elt) (sig:t_map) :=
  match M.get a sig with
    | None => default_tag
    | Some v => v
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
sk is a map from continuation indices to name
tgm is a map from name to its tag
n is the next available name.

returns pair of converted expression e', the next available variable name n' and the updated tag environment

        The names bound in e' are exactly [n, n'[

note : var "2" is taken as an external function standing for "halt"
       var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 



 *)

Fixpoint convert (e:cps) (sv: s_map) (sk:s_map) (tgm:t_map) (n:var) (*  {struct e } *): exp * var * t_map :=
       match e with
       | Halt_c v => let '(ctx_v, vn, n', tgm) := convert_v v sv sk tgm n in
                         (app_ctx_f ctx_v (Eprim n' halt (vn::nil) (Eapp n' halt_tag nil)), (Pos.succ n'), tgm)
       | Ret_c k v => let '(ctx_k, kn, n', tgm) := convert_v k sv sk tgm n in
                      let '(ctx_v, vn, n'', tgm) := convert_v v sv sk tgm n' in
                       (app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp  kn (get_t kn tgm) (vn::nil)), n'', tgm)
       | Call_c f k v =>
         let fv := if (varInterface.varClass f):bool then sv else sk in
         let kv := if (varInterface.varClass k):bool then sv else sk in
         let vv := if (varInterface.varClass v):bool then sv else sk in
         (* flipping around so the continuation comes first *)
         let f' := get_s f fv in
         (Eapp f' (get_t f' tgm) ((get_s k kv)::(get_s v vv)::nil) , n, tgm)
         
       | Match_c v bl =>
         let fix convert_branches (bl:list  ((dcon * nat) * ((list NVar)* cps))) (sv: s_map) (sk:s_map) (tgm:t_map) (r:var)  (n:var)  (* { struct bl } *): (list (cTag * exp) * var * t_map)  :=
             (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *)
             match bl with
               | nil => ( nil, n, tgm)
               | ((dcn, m),(xs, e))::bl' =>
                 let '(cbl, n', tgm) := convert_branches bl' sv sk tgm r n in
                 let (ctx_p, n'') := ctx_bind_proj r m n' in 
                 let (names, _) := fromN n' m in
                 let sv' := set_s_list xs names sv in
                 let '(ce, n''', tgm) :=  convert e sv' sk tgm n'' in
                 (((dcon_to_tag dcn), (app_ctx_f ctx_p ce))::cbl , n''', tgm) 
             end in
         let '(ctx_v, vn, n', tgm) := convert_v v sv sk tgm n in
         let '(cbls, n'', tgm) := convert_branches bl sv sk tgm vn n' in
         (app_ctx_f ctx_v (Ecase vn cbls), n'', tgm)
       | Proj_c v m k =>
         let '(ctx_v, vn, n', tgm) := convert_v v sv sk tgm n in
         let '(ctx_k, vk, n'', tgm) := convert_v k sv sk tgm n' in
         (app_ctx_f (comp_ctx_f ctx_v ctx_k) (Eproj n'' rec_tag (N.of_nat m) vn  (Eapp vk kon_tag (n''::nil))), Pos.succ n'', tgm)
       end
(* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh 

Ret_c M N -> 
 let m = [[M]] in
  let n = [[N]] in
   App_e m n

*)
with convert_v (v:val_c) (sv: s_map) (sk: s_map) (tgm:t_map) (n:var) (* { struct v }  *): (exp_ctx * var * var * t_map) :=
       match v with
         | Var_c m => (Hole_c, get_s m sv , n, tgm)   (* {| ( Econstr_c n ty var_tag ((nth (N.to_nat m) sv (1%positive))::nil)  Hole_c, Pos.succ n  ) |} *)
         | KVar_c m => (Hole_c, get_s m sk, n, tgm) (* {| ( Econstr_c n ty kvar_tag ((nth (N.to_nat m) sk (1%positive))::nil) Hole_c, Pos.succ n) |} *)
         | Lam_c x k e => let '(e', n', tgm) := convert e (M.set x n sv) (M.set k (Pos.succ n) sk) tgm (Pos.add n (2%positive)) in
                          (* flipping around so the continuation comes first *)
                          let fds := Fcons n' fun_tag ((Pos.succ n)::n::nil) e' Fnil in
                          (Efun1_c fds Hole_c, n' , (Pos.succ n'), tgm)
         | Cont_c k e => let '(e', n', tgm) := convert e sv (M.set k n sk) tgm (Pos.succ n) in
                         let fds := Fcons n' kon_tag (n::nil) e' Fnil in
                         (Efun1_c fds Hole_c, n',  Pos.succ n', tgm)
         | Con_c dcn lv =>
           let fix convert_v_list (lv :list val_c) (sv : s_map) (sk: s_map) (tgm:t_map) (n: var)(* {struct lv} *): (exp_ctx * list var * var * t_map) :=
               match lv with
                 | nil => (Hole_c, nil, n, tgm)
                 | v::lv' =>
                   let '(ctx_v, vn , n', tgm) := convert_v v sv sk tgm n in
                   let '(ctx_lv', ln', n'', tgm) := convert_v_list lv' sv sk tgm n' in
                   (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'', tgm)
                     
               end in
           let '(lv_ctx, nl, n', tgm) := convert_v_list lv sv sk tgm n in
           
             (comp_ctx_f lv_ctx (Econstr_c n' (dcon_to_tag dcn) (List.rev nl) Hole_c), n', Pos.succ n', (M.set n' (dcon_to_tag dcn) tgm)) 
         | Fix_c lbt =>
           (*  convert a list of simple_cps cps functions into 
               (1) a set of cps.exp functions (fundefs), each referring to a local variable (n+1), a local continuation variable (n+2) and the functions name (pushed to sv before calling convert_fds
 (2) the next fresh name

arguments are: 
 - fds : the l ist of functions to convert
 - sv : the stack of names for local variables, including the names for the set of functions being converted
 - sk : the stack of names for continuation variables
 - tgm : a map from the variable names to the tag of what is bound to them
 - fnames : names given to each of the function left to convert in fds
 - n     : next available name 

 *)
           let fix convert_fds (fds : list (var * val_c))  (sv: s_map) (sk : s_map) (tgm:t_map) (fnames : list var) (n : var) (*{struct fds} *): (fundefs * var * t_map)  :=
               match (fds, fnames) with
                 | ((f,v)::fds', currn::fnames') =>
                   (match v with
                      | Lam_c x k e =>            
                        let '(ce, n', tgm) := convert e (M.set x n sv) (M.set k (Pos.succ n) sk) tgm (Pos.add n 2%positive) in
                        let '(cfds, n'', tgm) := convert_fds fds' sv sk tgm fnames' n' in
                        (Fcons currn fun_tag (n::(Pos.succ n)::nil) ce cfds, n'', tgm)
                      | _ => (Fnil, n, tgm) (* this should not happen *)
                    end) 
                 | (_, _) => (Fnil, n, tgm)
               end in
           let (fnames, fbodys) := List.split lbt in (* length of the mutually recursive block *)
           let (nfds, newn) := fromN n (length lbt) in
           let sv' := set_s_list fnames nfds sv in
           let '(fds, n', tgm) := convert_fds lbt sv' sk tgm nfds newn in
           (* the record should disappear during shrink reduction *) 
           (Efun1_c fds (Econstr_c n' rec_tag nfds Hole_c), n',  (Pos.succ n'), tgm )
       end.

Definition convert_top (e:cps) : exp :=
  let '(er, n, tgm) := convert e s_empty s_empty t_empty (3%positive) in er.







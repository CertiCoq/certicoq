(* Convertion from 
       L4.L5A.cps  (L5a)
              to
       cps.exp (L6)
    resulting in globally unique names  

  2016 - Olivier Savary Belanger 


 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Libraries.Maps.
Require Coq.funind.Recdef.
Import Nnat.
Require Import CpdtTactics.


(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
Add LoadPath "../L1_QuotedCoq" as L1.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4.
(******)

Require Export Common.Common.  (* shared namespace *)
Require Import ExtLib.Data.List.
Require Import L4.L4a_to_L5.
Require Import SquiggleEq.varImplZ.
Require Import L4.L5a.

Require Import L6.cps.
Require Import L6.cps_util.
Require Import L6.ctx.





                   
(* placeholder *)
Definition tag := positive.
Variable default_tag : tag.
Variable fun_tag: tag.
Variable kon_tag: tag.



Definition L5_conId := dcon.

Theorem L5_conId_dec: forall x y:L5_conId, {x = y} + {x <> y}.
Proof.
  intros. destruct x,y.
  assert (H:=inductive_dec i i0).
  destruct H.
  - destruct (eq_dec n n0).
    + subst. left. auto.
    + right. intro. apply n1. inversion H. auto.
  - right; intro; apply n1. inversion H; auto.
Defined.
    
Definition L6_conId := cTag.


Definition conId_map:= list (L5_conId * L6_conId).






Fixpoint dcon_to_tag (a:L5_conId) (sig:conId_map) :=
  match sig with
    | nil => default_tag
    | ((cId, tag)::sig') => match L5_conId_dec a cId with
                              | left _ => tag
                              | right _ => dcon_to_tag a sig'
                            end
  end.




(* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
  match m with
  | O => (nil, n)
  | S m' =>
    let (l, nm ) := (fromN (n+1) (m')) in
    (n::l, nm)
  end.


(* Bind the m first projections of var r to variables [n, n+m[ *)
Fixpoint ctx_bind_proj (tg:cTag) (r:positive) (m:nat) (n:var) : (exp_ctx * var) :=
  match m with
    | O => (Hole_c, n)
    | S m' =>
      let (ctx_p', n') := ctx_bind_proj tg r m' n in
      (Eproj_c  n' tg (N.of_nat m') r ctx_p', Pos.succ n')
  end.



Definition t_map := M.t fTag.
Definition t_empty:t_map := M.empty _.

(* get the iTag of a variable, i_tag if not found *)
(*
Fixpoint get_t (n:var) (sig:t_map): iTag :=
  match M.get n sig with
    | None => i_tag
    | Some v => v
  end. *)

(* get the fTag of a variable, fun_tag if not found *)
Fixpoint get_f (n:var) (sig:t_map): fTag :=
  match M.get n sig with
    | None => fun_tag
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

note : var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 



 *)

(* environment threaded for conversion 
 conId_map maps the dcon to the right tag pointing to the constructor info (cEnv not passed around)
 t_map maps var name to their tag, allowing to index applications with the right function tag  
*)
Definition conv_env:Type := conId_map *  t_map.

Fixpoint convert (e:cps) (sv: s_map) (sk:s_map) (tgm:conv_env) (n:var) (*  {struct e } *): exp * var * conv_env :=
       match e with
       | Halt_c v => let '(ctx_v, vn, n', tgm) := convert_v v sv sk tgm n in
                         (app_ctx_f ctx_v (Ehalt vn), (Pos.succ n'), tgm)
       | Ret_c k v => let '(ctx_k, kn, n', tgm) := convert_v k sv sk tgm n in
                      let '(ctx_v, vn, n'', tgm) := convert_v v sv sk tgm n' in
                       (app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp  kn kon_tag (vn::nil)), n'', tgm)
       | Call_c f k v =>
         let fv := if (varInterface.varClass f):bool then sv else sk in
         let kv := if (varInterface.varClass k):bool then sv else sk in
         let vv := if (varInterface.varClass v):bool then sv else sk in
         (* flipping around so the continuation comes first *)
         let f' := get_s f fv in
         (Eapp f' (get_f f' (snd tgm)) ((get_s k kv)::(get_s v vv)::nil) , n, tgm)
         
       | Match_c v bl =>
         let fix convert_branches (bl:list  ((dcon * nat) * ((list NVar)* cps))) (sv: s_map) (sk:s_map) (tgm:conv_env) (r:var)  (n:var)  (* { struct bl } *): (list (cTag * exp) * var * conv_env)  :=
             (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *)
             match bl with
               | nil => ( nil, n, tgm)
               | ((dcn, m),(xs, e))::bl' =>
                 let lxs := List.length xs in 
                 let '(cbl, n', tgm) := convert_branches bl' sv sk tgm r n in
                 let tg := dcon_to_tag dcn (fst tgm) in
                 let (ctx_p, n'') := ctx_bind_proj tg r lxs n' in 
                 let (names, _) := fromN n' lxs in
                 let sv' := set_s_list xs names sv in
                 let '(ce, n''', tgm) :=  convert e sv' sk tgm n'' in
                 ((tg, (app_ctx_f ctx_p ce))::cbl , n''', tgm)
             end in
         let '(ctx_v, vn, n', tgm) := convert_v v sv sk tgm n in
         let '(cbls, n'', tgm) := convert_branches bl sv sk tgm vn n' in
         (app_ctx_f ctx_v (Ecase vn cbls), n'', tgm)
       end
(* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh 

Ret_c M N -> 
 let m = [[M]] in
  let n = [[N]] in
   App_e m n

*)
with convert_v (v:val_c) (sv: s_map) (sk: s_map) (tgm:conv_env) (n:var) (* { struct v }  *): (exp_ctx * var * var * conv_env) :=
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
           let fix convert_v_list (lv :list val_c) (sv : s_map) (sk: s_map) (tgm:conv_env) (n: var)(* {struct lv} *): (exp_ctx * list var * var * conv_env) :=
               match lv with
                 | nil => (Hole_c, nil, n, tgm)
                 | v::lv' =>
                   let '(ctx_v, vn , n', tgm) := convert_v v sv sk tgm n in
                   let '(ctx_lv', ln', n'', tgm) := convert_v_list lv' sv sk tgm n' in
                   (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'', tgm)
                     
               end in
           let '(lv_ctx, nl, n', tgm) := convert_v_list lv sv sk tgm n in
           
             (comp_ctx_f lv_ctx (Econstr_c n' (dcon_to_tag dcn (fst tgm)) (List.rev nl) Hole_c), n', Pos.succ n', tgm) 
         | Fix_c lbt i =>
           (match lbt with
             | nil => (Hole_c, (1%positive), n, tgm) (* malformed input, should not happen *) 
             | (fvars, _)::_ =>          
           (*  convert_fds:
               convert a list of simple_cps cps functions into 
               (1) a set of cps.exp functions (fundefs), each referring to a local variable (n+1), a local continuation variable (n+2) and the functions name (pushed to sv before calling convert_fds
               (2) the next fresh name
            assumes that lv1 = lv2 = ... (see comment in L5a.v for about Fix_c)  
            returns the name of the *i*th function as bound variable

            
arguments are: 
 - fds : the l ist of functions to convert
 - sv : the stack of names for local variables, including the names for the set of functions being converted
 - sk : the stack of names for continuation variables
 - tgm : a map from the variable names to the tag of what is bound to them
 - fnames : names given to each of the function left to convert in fds
 - n     : next available name 


 08/27/2016 - updated for directly-named functions in L5a instead of building a record
 09/08/2016 - now passing conv_env, containing a reverse cEnv to populate Econstr with the right cTag
 *)
           let fix convert_fds (fds : list (list var * val_c))  (sv: s_map) (sk : s_map) (tgm:conv_env) (fnames : list var) (n : var) (*{struct fds} *): (fundefs * var * conv_env)  :=
               match (fds, fnames) with
                 | ((_,v)::fds', currn::fnames') =>
                   (match v with
                      | Lam_c x k e =>            
                        let '(ce, n', tgm) := convert e (M.set x n sv) (M.set k (Pos.succ n) sk) tgm (Pos.add n 2%positive) in
                        let '(cfds, n'', tgm) := convert_fds fds' sv sk tgm fnames' n' in
                        let (tgm1, tgm2) := tgm in 
                        (Fcons currn fun_tag (n::(Pos.succ n)::nil) ce cfds, n'', (tgm1, M.set currn fun_tag tgm2))
                      | _ => (Fnil, n, tgm) (* this should not happen *)
                    end) 
                 | (_, _) => (Fnil, n, tgm)
               end in
           let (nfds, newn) := fromN n (length fvars) in
           let sv' := set_s_list fvars nfds sv in
           let '(fds, n', tgm) := convert_fds lbt sv' sk tgm nfds newn in
           (Efun1_c fds Hole_c, nth i nfds (1%positive), n', tgm )
             end)
       end.


Definition ienv := list (string * nat * itypPack).  

Fixpoint convert_cnstrs (cct:list positive) (itC:list Cnstr) (ind:inductive) (nCon:N) (niT:iTag) ce (dcm:conId_map) :=
 match (cct, itC) with  
   | (cn::cct', cst::icT') =>
     let (_, ccn) := cst in
         convert_cnstrs cct' icT' ind (nCon+1)%N niT (M.set cn (niT, N.of_nat ccn, nCon) ce) (((ind,nCon), cn)::dcm)
   | (_, _) => (ce, dcm)
 end.
               
Fixpoint convert_typack typ (idBundle:string) (n:nat) (ice:(iEnv * cEnv* iTag * cTag * conId_map)) : (iEnv * cEnv * cTag * iTag * conId_map) :=
  let '(ie, ce, niT, ncT, dcm) := ice in 
  match typ with
    | nil => ice
    | (mkItyp itN itC ) ::typ' => 
      let (cct, ncT) := fromN ncT (length itC) in
      let (ce, dcm) := convert_cnstrs cct itC (mkInd idBundle n) 0 niT ce dcm in
      let ityi := combine cct (map (fun (c:Cnstr) => let (_, n) := c in N.of_nat n) itC) in
       convert_typack typ' idBundle (n+1) (M.set niT ityi ie, ce,  ncT, (Pos.succ niT), dcm)
  end.
      
Fixpoint convert_env' (g:ienv) (ice:iEnv * cEnv * cTag * iTag * conId_map) : (iEnv * cEnv * conId_map) :=
  let '(ie, ce, niT, ncT, dcm) := ice in 
  match g with      
    | nil => (ie, ce, dcm)
    | (id, n, ty)::g' =>
      (* id is name of mutual pack, n is number of type in mutual pack, ty is mutual pack *)
      (* constructors are indexed with : name (string) of the mutual pack with which projection of the ty, and indice of the constructor *)      
      convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm)) 

  end.

Definition convert_env (g:ienv): (iEnv*cEnv * conId_map) := convert_env' g (M.empty iTyInfo, M.empty cTyInfo, 1%positive, 1%positive, nil).

Definition convert_top (ee:ienv*cps) : (cEnv*exp) :=
  let '(_, cG, dcm) := convert_env (fst ee) in 
  let '(er, n, tgm) := convert (snd ee) s_empty s_empty (dcm, t_empty) (3%positive) in (cG, er).







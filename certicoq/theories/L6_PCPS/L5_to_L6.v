(* Convertion from 
       L4.L5A.cps  (L5a)
              to
       cps.exp (L6)
    resulting in a term with globally unique names  

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


(******
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
Add LoadPath "../L1_QuotedCoq" as L1.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
******)
Add LoadPath "../L4_deBruijn" as L4.

Require Export Common.Common.  (* shared namespace *)
Require Import ExtLib.Data.List.
Require Import L4.polyEval.
Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.varImplZ.
Require Import L4.L5a.
Require Import L4.variables.

Require Import L6.cps.
Require Import L6.cps_util.
Require Import L6.ctx.


Definition tag := positive.

Section Program.
  
  
  Variable default_tag : cTag.
  Variable default_itag: iTag.
  Variable fun_tag: fTag.
  Variable kon_tag: fTag.
  
  
  
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
  
 

(* dcon to generated cTag and the # of parameter for the inductive type of this constructor *) 
  Definition conId_map:= list (L5_conId * (cTag * nat)).


  Fixpoint dcon_to_info (a:L5_conId) (sig:conId_map) :=
    match sig with
      | nil => (default_tag, 0)
      | ((cId, inf)::sig') => match L5_conId_dec a cId with
                                | left _ => inf
                                | right _ => dcon_to_info a sig'
                              end
    end.

  Definition dcon_to_tag (a:L5_conId) (sig:conId_map) :=
    fst (dcon_to_info a sig).

  Definition dcon_to_p (a:L5_conId) (sig:conId_map) :=
    snd (dcon_to_info a sig).
  







  (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
  Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
    match m with
      | O => (nil, n)
      | S m' =>
        let (l, nm ) := (fromN (n+1) (m')) in
        (n::l, nm)
    end.
  

  (* Bind m projections (starting from the (p+1)th) of var r to variables [n, n+m[, returns the generated context and n+m *)
  Fixpoint ctx_bind_proj (tg:cTag) (r:positive) (m:nat) (n:var) (p:nat) : (exp_ctx * var) :=
    match m with
      | O => (Hole_c, n)
      | S m' =>
        let (ctx_p', n') := ctx_bind_proj tg r m' n p in
        (Eproj_c  n' tg (N.of_nat (m'+p)) r ctx_p', Pos.succ n')
    end.


  Definition nEnv := M.t Ast.name.
  Definition n_empty:nEnv := M.empty _.

  Definition t_info:Type := fTag.
  Definition t_map := M.t t_info.
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

  Definition get_s (a:NVar) (sig:s_map):=
    match M.get (fst a) sig with
      | None => (1%positive)
      | Some v => v
    end.

  Fixpoint set_s_list (lx:list NVar) (ly:list var) (sig:s_map) :=
    match (lx, ly) with
      | (x::lx', y::ly') =>
        set_s_list lx' ly' (M.set (fst x) y sig)
      | _ => sig
    end.






  (* environment threaded for conversion 
 conId_map maps the dcon to the right tag pointing to the constructor info (cEnv not passed around)
 t_map maps var name to their tag, allowing to index applications with the right function tag  
 note:want might to add f and k to t_map on way down 
   *)
  Definition conv_env:Type := conId_map *  t_map * nEnv.

  Definition set_nt (x:var) (tn: (Ast.name * t_info))  (tgm:conv_env):conv_env :=
    let '(t1, t2, t3) := tgm in
    (t1, M.set x (snd tn) t2, M.set x (fst tn) t3).


  Definition set_t (x:var) (ti: t_info)  (tgm:conv_env):conv_env :=
    let '(t1, t2, t3) := tgm in
    (t1, M.set x ti t2, t3).

  Definition set_n (x:var) (n:Ast.name) (tgm:conv_env):conv_env :=
    let '(t1,t2,t3) := tgm in
    (t1, t2, M.set x n t3).

  (* Add a list of function to the tag environment *)
  Fixpoint set_t_f_list (ns:list var) (ts:list NVar) (tgm:conv_env) :=
    match ns, ts with
      | n::ns', t::ts' => set_t_f_list ns' ts' (set_nt n (snd t, fun_tag) tgm)
      | _, _ => tgm
    end.
  

  (* 
  sv is a map used to convert variable indices to name
sk is a map from continuation indices to name
tgm is a map from id (positive) to its original name (if any) and tag
n is the next available name.

returns pair of converted expression e', the next available variable name n' and the updated tag environment

        The names bound in e' are exactly [n, n'[

note : var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 



   *)

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
        (Eapp f' (get_f f' (snd (fst tgm))) ((get_s k kv)::(get_s v vv)::nil) , n, tgm)
          
      | Match_c v bl =>
        let fix convert_branches (bl:list  ((dcon * nat) * ((list NVar)* cps))) (sv: s_map) (sk:s_map) (tgm:conv_env) (r:var)  (n:var)  (* { struct bl } *): (list (cTag * exp) * var * conv_env)  :=
            (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *)
            match bl with
              | nil => ( nil, n, tgm)
              | ((dcn, m),(xs, e))::bl' =>
                let lxs := List.length xs in 
                let '(cbl, n', tgm) := convert_branches bl' sv sk tgm r n in
                let tg := dcon_to_tag dcn (fst (fst tgm)) in
                (* take the first lxs projections on the scrutiny at the head of each branches
                   02/17 - We now erase parameters as part of this translation s.t. we don't offset those projections 
                   TODO - use the right tag for each projection *)
                   
                let (ctx_p, n'') := ctx_bind_proj tg r lxs n' 0 in 
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
           | Lam_c x k e =>
             let tgm := set_nt (Pos.succ n) (snd k, kon_tag) tgm in
             let tgm := set_n n (snd x) tgm in (* what about the tag of x? *)     
             let '(e', n', tgm) := convert e (M.set (fst x) n sv) (M.set (fst k) (Pos.succ n) sk) tgm (Pos.add n (2%positive)) in
             let tgm := set_t n' fun_tag tgm in  
             (* flipping around so the continuation comes first *)
             let fds := Fcons n' fun_tag ((Pos.succ n)::n::nil) e' Fnil in                         
             (Efun1_c fds Hole_c, n' , (Pos.succ n'), tgm) 
           | Cont_c k e =>
             let tgm := set_n n (snd k) tgm in (* maybe set the tag? *)
             let '(e', n', tgm) := convert e sv (M.set (fst k) n sk) tgm (Pos.succ n) in
             let fds := Fcons n' kon_tag (n::nil) e' Fnil in
             (Efun1_c fds Hole_c, n',  Pos.succ n', set_t n' kon_tag tgm )
           | Con_c dcn lv =>
             (* skips the first p values in lv and produce an expression context binding to the returned list of variables
                the converted values  *)
             let fix convert_v_list (lv :list val_c) (p:nat) (sv : s_map) (sk: s_map) (tgm:conv_env) (n: var)(* {struct lv} *): (exp_ctx * list var * var * conv_env) :=
                 match (p, lv) with
                   | (S p', v::lv') =>
                      convert_v_list lv' p' sv sk tgm n
                   | (0, v::lv') =>
                     let '(ctx_v, vn , n', tgm) := convert_v v sv sk tgm n in
                     let '(ctx_lv', ln', n'', tgm) := convert_v_list lv' 0 sv sk tgm n' in
                     (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'', tgm)
                   | _ =>  (Hole_c, nil, n, tgm)
                       
                 end in 
             let (ctag, nP) := (dcon_to_info dcn (fst (fst tgm))) in
             (* skip the first nP arguments which correspond to the inductive type's parameters *)
             let '(lv_ctx, nl, n', tgm) := convert_v_list lv nP sv sk tgm n in
             (comp_ctx_f lv_ctx (Econstr_c n' ctag nl Hole_c), n', Pos.succ n', set_t n' ctag tgm)
           | Fix_c lbt i =>
             (match lbt with
                | nil => (Hole_c, (1%positive), n, tgm) (* malformed input, should not happen *) 
                | (fvars, _ )::_ =>          
                  (* ) convert_fds:
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
                  let fix convert_fds (fds : list (list NVar * val_c))  (sv: s_map) (sk : s_map) (tgm:conv_env) (fnames : list var) (n : var) (*{struct fds} *): (fundefs * var * conv_env)  :=
                      match (fds, fnames) with
                        | ((_,v)::fds', currn::fnames') =>
                          (match v with
                             | Lam_c x k e =>                        
                               let '(ce, n', tgm) := convert e (M.set (fst x) n sv) (M.set (fst k) (Pos.succ n) sk) (set_nt (Pos.succ n) (snd k, kon_tag) (set_n n (snd x)  tgm)) (Pos.add n 2%positive) in
                               let '(cfds, n'', tgm) := convert_fds fds' sv sk tgm fnames' n' in
                               (Fcons currn fun_tag ((Pos.succ n)::n::nil) ce cfds, n'', tgm) (* todo: add the tag for x *)
                             | _ => (Fnil, n, tgm) (* this should not happen *)
                           end) 
                        | (_, _) => (Fnil, n, tgm)
                      end in
                  let (nfds, newn) := fromN n (length fvars) in
                  let sv' := set_s_list fvars nfds sv in
                  let tgm := set_t_f_list nfds fvars tgm in
                  let '(fds, n', tgm) := convert_fds lbt sv' sk tgm nfds newn in
                  (Efun1_c fds Hole_c, nth i nfds (1%positive), n', tgm )
              end)
         end.
  
  
  Definition ienv := list (string * nat * itypPack).  
  

  (** process a list of constructors from inductive type ind with iTag niT.  
    - update the cEnv with a mapping from the current cTag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of ind to the cTag of the current constructor

   nP: number of type parameters for this bundle, kept in the dcm to erase the right number of arguments
   *)
  Fixpoint convert_cnstrs (cct:list cTag) (itC:list Cnstr) (ind:inductive) (nP:nat) (nCon:N) (niT:iTag) (ce:cEnv) (dcm:conId_map) :=
    match (cct, itC) with  
      | (cn::cct', cst::icT') =>
        let (cname, ccn) := cst in
        convert_cnstrs cct' icT' ind nP (nCon+1)%N niT (M.set cn (nNamed cname, niT, N.of_nat (ccn), nCon) ce) (((ind,nCon), (cn, nP))::dcm)
      | (_, _) => (ce, dcm)
    end.


  (** For each inductive type defined in the mutually recursive bundle, 
    - use tag niT for this inductive datatype
    - reserve constructor tags for each constructors of the type
    - process each of the constructor, indicating they are the ith constructor of the nth type of idBundle
   np: number of type parameters for this bundle
   *)
  Fixpoint convert_typack typ (idBundle:string) (np:nat) (n:nat) (ice:(iEnv * cEnv*  cTag * iTag * conId_map)) : (iEnv * cEnv * cTag * iTag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in 
    match typ with
      | nil => ice
      | (mkItyp itN itC ) ::typ' => 
        let (cct, ncT') := fromN ncT (length itC) in
        let (ce', dcm') := convert_cnstrs cct itC (mkInd idBundle n) np 0 niT ce dcm in
        let ityi := combine cct (map (fun (c:Cnstr) => let (_, n) := c in N.of_nat n) itC) in
        convert_typack typ' idBundle np (n+1) (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
    end.
  
  Fixpoint convert_env' (g:ienv) (ice:iEnv * cEnv * cTag * iTag * conId_map) : (iEnv * cEnv * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in 
    match g with      
      | nil => (ie, ce, dcm)
      | (id, n, ty)::g' =>
        (* id is name of mutual pack, n is number of (type) parameters for this mutual pack, ty is mutual pack *)
        (* constructors are indexed with : name (string) of the mutual pack with which projection of the ty, and indice of the constructor *)      
        convert_env' g' (convert_typack ty id n 0 (ie, ce, ncT, niT, dcm)) 
    end.


  (* As we process the L5 inductive environment (ienv), we build:
 - an L6 inductive environment (iEnv) mapping tags (iTag) to constructors and their arities 
 - an L6 constructor environment (cEnv) mapping tags (cTag) to information about the constructors 
 - a map (conId_map) from L5 tags (conId) to L6 constructor tags (cTag)
convert_env' is called with the next available constructor tag and the next available inductive datatype tag, and inductive and constructor environment containing only the default "box" constructor/type
   *)
  Definition convert_env (g:ienv): (iEnv*cEnv * conId_map) :=
    let default_iEnv := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty iTyInfo) in
    let default_cEnv := M.set default_tag (nAnon, default_itag, 0%N, 0%N) (M.empty cTyInfo) in
    convert_env' g (default_iEnv, default_cEnv, (Pos.succ default_tag:cTag), (Pos.succ default_itag:iTag), nil).


  (** to convert from L5a to L6, first convert the environment (ienv) into a cEnv (map from constructor to info) and a conId_map (dcm) from L5 tags to L6 tags. Then, use that conId_map in the translation of the L5 term to incorporate the right L6 tag in the L6 term *)
  Definition convert_top (ee:ienv*cps) : (cEnv*nEnv*exp) :=
    let '(_, cG, dcm) := convert_env (fst ee) in 
    let '(er, n, tgm) := convert (snd ee) s_empty s_empty (dcm, t_empty, n_empty) (100%positive) in
    let '(_, _, nM) := tgm in
    (cG, nM, er).


End Program.
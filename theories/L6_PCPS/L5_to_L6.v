(* Convertion from
       L4.L5A.cps  (L5)
              to
       cps.exp (L6)
    resulting in a term with globally unique names

 *)


Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.polyEval.

Require Import L4.L4_5_to_L5.
Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega
  Coq.Program.Program Coq.micromega.Psatz.

Set Implicit Arguments.

Require Import SquiggleEq.varImplZ.

Require Import L6.cps.
Require Import L6.cps_util.
Require Import L6.ctx.

Require Import L4.variables.
Require compcert.lib.Maps.
Require Coq.funind.Recdef.
Require Import CpdtTactics.


(******
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
Add LoadPath "../L1_QuotedCoq" as L1.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
******)


(* Require Export Common.Common.  (* shared namespace *) *)


Definition tag := positive.

Section Program.

  (* starting ctor_tag and ind_tag for user-defined inductives *)
  Variable default_tag : ctor_tag.
  Variable default_itag: ind_tag.

  (* fun_tag for regular and continuation functions *)
  Variable func_tag: fun_tag.
  Variable kon_tag: fun_tag.



  Definition L5_conId := dcon.

  Theorem L5_conId_dec: forall x y:L5_conId, {x = y} + {x <> y}.
  Proof.
    intros. destruct x,y.
    assert (H:= AstCommon.inductive_dec i i0).
    destruct H.
    - destruct (classes.eq_dec n n0).
      + subst. left. auto.
      + right. intro. apply n1. inversion H. auto.
    - right; intro; apply n1. inversion H; auto.
  Defined.



  (* dcon to generated ctor_tag *)
  Definition conId_map:= list (L5_conId * ctor_tag).


  Fixpoint dcon_to_info (a:L5_conId) (sig:conId_map) :=
    match sig with
      | nil => default_tag
      | ((cId, inf)::sig') => match L5_conId_dec a cId with
                                | left _ => inf
                                | right _ => dcon_to_info a sig'
                              end
    end.

  Definition dcon_to_tag (a:L5_conId) (sig:conId_map) :=
    dcon_to_info a sig.








  (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
  Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
    match m with
      | O => (nil, n)
      | S m' =>
        let (l, nm ) := (fromN (n+1) (m')) in
        (n::l, nm)
    end.


  (* Bind m projections (starting from the (p+1)th) of var r to variables [n, n+m[, returns the generated context and n+m *)
  Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (m:nat) (n:var) (p:nat) : (exp_ctx * var) :=
    match m with
      | O => (Hole_c, n)
      | S m' =>
        let (ctx_p', n') := ctx_bind_proj tg r m' n p in
        (Eproj_c  n' tg (N.of_nat (m'+p)) r ctx_p', Pos.succ n')
    end.

  Definition t_info:Type := fun_tag.
  Definition t_map := M.t t_info.
  Definition t_empty:t_map := M.empty _.



  (* get the ind_tag of a variable, i_tag if not found *)
  (*
Fixpoint get_t (n:var) (sig:t_map): ind_tag :=
  match M.get n sig with
    | None => i_tag
    | Some v => v
  end. *)

  (* get the fun_tag of a variable, fun_tag if not found *)
  Fixpoint get_f (n:var) (sig:t_map): fun_tag :=
    match M.get n sig with
      | None => func_tag
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
 conId_map maps the dcon to the right tag pointing to the constructor info (ctor_env not passed around)
 t_map maps var name to their tag, allowing to index applications with the right function tag  
 note:want might to add f and k to t_map on way down 
   *)
  Definition conv_env:Type := conId_map *  t_map * name_env.

  Definition set_nt (x:var) (tn: (BasicAst.name * t_info))  (tgm:conv_env):conv_env :=
    let '(t1, t2, t3) := tgm in
    (t1, M.set x (snd tn) t2, M.set x (fst tn) t3).


  Definition set_t (x:var) (ti: t_info)  (tgm:conv_env):conv_env :=
    let '(t1, t2, t3) := tgm in
    (t1, M.set x ti t2, t3).

  Definition set_n (x:var) (n:BasicAst.name) (tgm:conv_env):conv_env :=
    let '(t1,t2,t3) := tgm in
    (t1, t2, M.set x n t3).

  (* Add a list of function to the tag environment *)
  Fixpoint set_t_f_list (ns:list var) (ts:list NVar) (tgm:conv_env) :=
    match ns, ts with
      | n::ns', t::ts' => set_t_f_list ns' ts' (set_nt n (snd t, func_tag) tgm)
      | _, _ => tgm
    end.

  Definition set_nvar  (xn:NVar)  (tgm:conv_env):conv_env :=
    let '(t1, t2, t3) := tgm in
    let (x, n) := xn in
    (t1,t2, M.set x n t3).



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
w


   *)

Section Notations.
  Require Import ExtLib.Data.Monads.OptionMonad.

  Notation CBTerm := (@terms.BTerm NVar L5Opid).
  Notation CTerm := (@terms.NTerm NVar L5Opid).

  Require Import ExtLib.Structures.Monads.

  Import Monad.MonadNotation.
  Open Scope monad_scope.
  Require Import SquiggleEq.ExtLibMisc.


Fixpoint convert (e:CTerm) (sv: s_map) (sk:s_map) (tgm:conv_env) (n:var) (*  {struct e } *): option (exp * var * conv_env) :=
    match e with
    | terms.oterm CHalt [bterm nil h] =>
      r <- convert_v h sv sk tgm n;;
      (match r with
      | (ctx_v, vn, n', tgm) =>
        ret (app_ctx_f ctx_v (Ehalt vn), (Pos.succ n'), tgm)
       end)
    | terms.oterm CRet [bterm [] k; bterm [] v]  =>
      r1 <- convert_v k sv sk tgm n;;
         let '(ctx_k, kn, n', tgm) := r1 in
         r2 <-  convert_v v sv sk tgm n';;
            let '(ctx_v, vn, n'', tgm) := r2 in
            ret (app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp  kn kon_tag (vn::nil)), n'', tgm)
    | terms.oterm CCall [bterm [] f; bterm [] k; bterm [] v] =>
                  f <-  getVar f;;
                  k <- getVar k;;
                  v <- getVar v;;
                  let fv := if (varInterface.varClass f):bool then sv else sk in
                  let kv := if (varInterface.varClass k):bool then sv else sk in
                  let vv := if (varInterface.varClass v):bool then sv else sk in
      (* flipping around so the continuation comes first *)
                  let f' := get_s f fv in
                  ret (Eapp f' (get_f f' (snd (fst tgm))) ((get_s k kv)::(get_s v vv)::nil) , n, tgm)
    | terms.oterm (CMatch ls) ((bterm [] v)::lbt) =>
      r1 <- convert_v v sv sk tgm n;;
         let '(ctx_v, vn, n', tgm) :=  r1 in
         r2 <- (fold_left (fun (co:option _) b =>
                             c <- co;;
                               let '(cbl, ls, sv, sk, tgm, r, n') := c in
                               let '(bterm xs e) := b in
                               (match ls with
                                | (dcn, m)::ls'  =>
                                  let lxs := List.length xs in
                                  let tg := dcon_to_tag dcn (fst (fst tgm)) in
                                  (* take the first lxs projections on the scrutiny at the head of each branches
                   02/17 - We now erase parameters as part of this translation s.t. we don't offset those projections
                   TODO - use the right tag for each projection *)

                                  let (ctx_p, n'') := ctx_bind_proj tg r lxs n' 0 in
                                  let (names, _) := fromN n' lxs in
                                  let sv' := set_s_list xs names sv in
                                  r2 <- convert e sv' sk tgm n'' ;;
                                     let '(ce, n''', tgm) :=  r2 in
                                     ret ((tg, (app_ctx_f ctx_p ce))::cbl , ls', sv, sk, tgm, r, n''')
                                |  _ => None
                                end)) lbt (ret (nil, ls, sv, sk, tgm, vn, n'))) ;;
            let '(cbls, ls, sv, sk, tgm, vn, n'') := r2 in
            ret (app_ctx_f ctx_v (Ecase vn cbls), n'', tgm)
    | _ => None
    end

  (* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh

ContApp_c M N ->
 let m = [[M]] in
  let n = [[N]] in
   App_e m n

   *)
  with convert_v (v:CTerm) (sv: s_map) (sk: s_map) (tgm:conv_env) (n:var) (* { struct v }  *): option (exp_ctx * var * var * conv_env) :=
         match v with
         | vterm v => if ((varClass v):bool (*== USERVAR*)) then ret (Hole_c, get_s v sv , n, tgm) else ret (Hole_c, get_s v sk, n, tgm)
         | terms.oterm CLambda [bterm [x; k] e] =>
             let tgm := set_nt (Pos.succ n) (snd k, kon_tag) tgm in
             let tgm := set_n n (snd x) tgm in (* what about the tag of x? *)
             r <- convert e (M.set (fst x) n sv) (M.set (fst k) (Pos.succ n) sk) tgm (Pos.add n (2%positive));;
             let '(e', n', tgm) := r in
             let tgm := set_t n' func_tag tgm in
             (* flipping around so the continuation comes first *)
             let fds := Fcons n' func_tag ((Pos.succ n)::n::nil) e' Fnil in
             ret (Efun1_c fds Hole_c, n' , (Pos.succ n'), tgm)
         | terms.oterm CKLambda [bterm [k] e] =>
           let tgm := set_n n (snd k) tgm in (* maybe set the tag? *)
           r <- convert e sv (M.set (fst k) n sk) tgm (Pos.succ n) ;;
             let '(e', n', tgm) := r in
             let fds := Fcons n' kon_tag (n::nil) e' Fnil in
             ret (Efun1_c fds Hole_c, n',  Pos.succ n', set_t n' kon_tag tgm )
         | terms.oterm  (CDCon dcn _) lv =>
           (* Produce an expression context binding to the returned list of variables
                the converted values  *)
           let fix convert_v_list lv  (sv : s_map) (sk: s_map) (tgm:conv_env) (n: var)(* {struct lv} *): option (exp_ctx * list var * var * conv_env) :=
               match lv with
               | (bterm _ v)::lv' =>
                 r1 <- convert_v v sv sk tgm n;;
                    let '(ctx_v, vn , n', tgm) := r1 in
                    r2 <- convert_v_list lv' sv sk tgm n';;
                 let '(ctx_lv', ln', n'', tgm) := r2 in
                 ret (comp_ctx_f ctx_v ctx_lv', (vn::ln'), n'', tgm)
               | nil => ret (Hole_c, nil, n, tgm)
               end in
           let ctag := (dcon_to_info dcn (fst (fst tgm))) in
           r <- convert_v_list lv sv sk tgm n ;;
           let '(lv_ctx, nl, n', tgm) := r in
           ret (comp_ctx_f lv_ctx (Econstr_c n' ctag nl Hole_c), n', Pos.succ n', set_t n' ctag tgm)
    | terms.oterm (CFix _ i) lbt =>
(*
           | Fix_c lbt i => *)
             (match lbt with
              | nil => ret (Hole_c, (1%positive), n, tgm) (* malformed input, should not happen *)
              | (bterm fvars _ )::_ =>
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
 09/08/2016 - now passing conv_env, containing a reverse ctor_env to populate Econstr with the right ctor_tag
                 *)
                let fix convert_fds (fds : list CBTerm)  (sv: s_map) (sk : s_map) (tgm:conv_env) (fnames : list var) (n : var) (*{struct fds} *): option (fundefs * var * conv_env)  :=
                    match (fds, fnames) with
                    | ((bterm _ v)::fds', currn::fnames') =>
                      (match v with
                       | terms.oterm CLambda [bterm [x; k] e] =>
                         r1 <- convert e (M.set (fst x) n sv) (M.set (fst k) (Pos.succ n) sk) (set_nt (Pos.succ n) (snd k, kon_tag) (set_n n (snd x)  tgm)) (Pos.add n 2%positive) ;;
                            let '(ce, n', tgm) := r1 in
                            r2 <- convert_fds fds' sv sk tgm fnames' n' ;;
                         let '(cfds, n'', tgm) := r2 in
                         ret (Fcons currn func_tag ((Pos.succ n)::n::nil) ce cfds, n'', tgm) (* todo: add the tag for x *)
                       | _ => ret (Fnil, n, tgm) (* this should not happen *)
                       end)
                    | (_, _) => ret (Fnil, n, tgm)
                    end in
                let (nfds, newn) := fromN n (length fvars) in
                let sv' := set_s_list fvars nfds sv in
                let tgm := set_t_f_list nfds fvars tgm in
                r <-  convert_fds lbt sv' sk tgm nfds newn;;
                  let '(fds, n', tgm) := r in
                  ret (Efun1_c fds Hole_c, nth i nfds (1%positive), n', tgm )
              end)

           | _ => None
         end.


  Definition ienv := list (string * AstCommon.itypPack).


  (** process a list of constructors from inductive type ind with ind_tag niT.
    - update the ctor_env with a mapping from the current ctor_tag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of ind to the ctor_tag of the current constructor

   *)
  Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr) (ind:BasicAst.inductive) (nCon:N) (unboxed : N) (boxed : N) (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
    match (cct, itC) with
      | (cn::cct', cst::icT') =>
        let (cname, ccn) := cst in
        let is_unboxed := Nat.eqb ccn 0 in
        let info := {| ctor_name := BasicAst.nNamed cname
                     ; ctor_ind_name := BasicAst.nNamed tyname
                     ; ctor_ind_tag := niT
                     ; ctor_arity := N.of_nat ccn
                     ; ctor_ordinal := if is_unboxed then unboxed else boxed
                     |} in
        convert_cnstrs tyname cct' icT' ind (nCon+1)%N
                       (if is_unboxed then unboxed + 1 else unboxed)
                       (if is_unboxed then boxed else boxed + 1)
                       niT
                       (M.set cn info ce)
                       (((ind,nCon), cn)::dcm (** Remove this now that params are always 0? *))
      | (_, _) => (ce, dcm)
    end.


  (** For each inductive type defined in the mutually recursive bundle,
    - use tag niT for this inductive datatype
    - reserve constructor tags for each constructors of the type
    - process each of the constructor, indicating they are the ith constructor of the nth type of idBundle
   np: number of type parameters for this bundle
   *)
  Fixpoint convert_typack typ (idBundle:string) (n:nat) (ice:(ind_env * ctor_env*  ctor_tag * ind_tag * conId_map)) : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match typ with
      | nil => ice
      | (AstCommon.mkItyp itN itC ) ::typ' =>
        let (cct, ncT') := fromN ncT (length itC) in
        let (ce', dcm') := convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 0 0 niT ce dcm in
        let ityi := combine cct (map (fun (c:AstCommon.Cnstr) => let (_, n) := c in N.of_nat n) itC) in
        convert_typack typ' idBundle (n+1) (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
    end.

  Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map) : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match g with
      | nil => ice
      | (id, ty)::g' =>
        (* id is name of mutual pack ty is mutual pack *)
        (* constructors are indexed with : name (string) of the mutual pack with which projection of the ty, and indice of the constructor *)
        convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
    end.


  (* As we process the L5 inductive environment (ienv), we build:
 - an L6 inductive environment (ind_env) mapping tags (ind_tag) to constructors and their arities
 - an L6 constructor environment (ctor_env) mapping tags (ctor_tag) to information about the constructors
 - a map (conId_map) from L5 tags (conId) to L6 constructor tags (ctor_tag)
convert_env' is called with the next available constructor tag and the next available inductive datatype tag, and inductive and constructor environment containing only the default "box" constructor/type
   *)
  Definition convert_env (g:ienv): (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map) :=
    let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
    let info := {| ctor_name := BasicAst.nAnon
                 ; ctor_ind_name := BasicAst.nAnon
                 ; ctor_ind_tag := default_itag
                 ; ctor_arity := 0%N
                 ; ctor_ordinal := 0%N
                 |} in
    let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
    convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).


  (** to convert from L5a to L6, first convert the environment (ienv) into a ctor_env (map from constructor to info) and a conId_map (dcm) from L5 tags to L6 tags. Then, use that conId_map in the translation of the L5 term to incorporate the right L6 tag in the L6 term *)
  Definition convert_top (ee:ienv*CTerm) : option (ctor_env*name_env*fun_env*ctor_tag*ind_tag * exp) :=
    let '(_, cG, ctag, itag,  dcm) := convert_env (fst ee) in
     r <- convert (snd ee) s_empty s_empty (dcm, t_empty, n_empty) (100%positive);;
    let '(er, n, tgm) := r in
    let '(_, _, nM) := tgm in
    let fenv:fun_env := M.set func_tag (2%N, (0%N::1%N::nil)) (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in
    ret (cG, nM, fenv, ctag, itag, er).
End Notations.

End Program.

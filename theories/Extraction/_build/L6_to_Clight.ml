open AST
open Archi
open Ascii
open BasicAst
open Basics
open BinInt
open BinNat
open BinPos
open Clight
open Clightdefs
open Cop
open Ctypes
open Datatypes
open Errors0
open Integers
open List0
open Maps
open Monad0
open MonadState
open Nat0
open OptionMonad
open PeanoNat
open StateMonad
open String1
open String0
open Cps
open Identifiers

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val print_Clight_dest_names' :
    Clight.program -> (int * name) list -> char list -> unit **)

let print_Clight_dest_names' = PrintClight.print_dest_names

(** val maxArgs : int **)

let maxArgs =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))

(** val makeArgList' : int list -> int list **)

let rec makeArgList' = function
| [] -> []
| _ :: vs' -> (N.of_nat (Datatypes.length vs')) :: (makeArgList' vs')

(** val makeArgList : int list -> int list **)

let makeArgList vs =
  rev (makeArgList' vs)

(** val compute_fEnv' : nat -> fEnv -> exp -> fEnv **)

let rec compute_fEnv' n fenv e =
  match n with
  | O -> fenv
  | S n' ->
    (match e with
     | Econstr (_, _, _, e') -> compute_fEnv' n' fenv e'
     | Ecase (_, cs) -> fold_left (compute_fEnv' n') (map snd cs) fenv
     | Eproj (_, _, _, _, e') -> compute_fEnv' n' fenv e'
     | Efun (fnd, e') ->
       compute_fEnv' n' (compute_fEnv_fundefs n' fnd fenv) e'
     | Eapp (_, t0, vs) ->
       M.set t0 ((N.of_nat (Datatypes.length vs)), (makeArgList vs)) fenv
     | Eprim (_, _, _, e') -> compute_fEnv' n' fenv e'
     | Ehalt _ -> fenv)

(** val compute_fEnv_fundefs : nat -> fundefs -> fEnv -> fEnv **)

and compute_fEnv_fundefs n fnd fenv =
  match n with
  | O -> fenv
  | S n' ->
    (match fnd with
     | Fcons (_, t0, vs, e, fnd') ->
       let fenv' =
         M.set t0 ((N.of_nat (Datatypes.length vs)), (makeArgList vs)) fenv
       in
       compute_fEnv_fundefs n' fnd' (compute_fEnv' n' fenv' e)
     | Fnil -> fenv)

(** val max_depth : exp -> nat **)

let rec max_depth = function
| Econstr (_, _, _, e') -> S (max_depth e')
| Ecase (_, cs) ->
  S (fold_left Nat.max (map (compose max_depth snd) cs) (S O))
| Eproj (_, _, _, _, e') -> S (max_depth e')
| Efun (fnd, e') -> S (Nat.max (max_depth_fundefs fnd) (max_depth e'))
| Eprim (_, _, _, e') -> S (max_depth e')
| _ -> S O

(** val max_depth_fundefs : fundefs -> nat **)

and max_depth_fundefs = function
| Fcons (_, _, _, e, fnd') ->
  S (Nat.max (max_depth e) (max_depth_fundefs fnd'))
| Fnil -> S O

(** val compute_fEnv : exp -> fEnv **)

let compute_fEnv e =
  compute_fEnv' (max_depth e) M.empty e

(** val get_allocs : exp -> int list **)

let rec get_allocs = function
| Econstr (x, _, _, e') -> x :: (get_allocs e')
| Ecase (_, cs) ->
  let rec helper = function
  | [] -> []
  | p :: cs' -> let (_, e') = p in app (get_allocs e') (helper cs')
  in helper cs
| Eproj (x, _, _, _, e') -> x :: (get_allocs e')
| Efun (fnd, e') -> app (get_allocs_fundefs fnd) (get_allocs e')
| Eprim (x, _, _, e') -> x :: (get_allocs e')
| _ -> []

(** val get_allocs_fundefs : fundefs -> int list **)

and get_allocs_fundefs = function
| Fcons (_, _, vs, e, fnd') ->
  app vs (app (get_allocs e) (get_allocs_fundefs fnd'))
| Fnil -> []

(** val max_allocs : exp -> nat **)

let rec max_allocs = function
| Econstr (_, _, vs, e') ->
  (match vs with
   | [] -> max_allocs e'
   | _ :: _ -> S (add (max_allocs e') (Datatypes.length vs)))
| Ecase (_, cs) ->
  let rec helper = function
  | [] -> O
  | p :: cs' -> let (_, e') = p in max (max_allocs e') (helper cs')
  in helper cs
| Eproj (_, _, _, _, e') -> max_allocs e'
| Efun (fnd, e') -> max (max_allocs_fundefs fnd) (max_allocs e')
| Eprim (_, _, _, e') -> max_allocs e'
| _ -> O

(** val max_allocs_fundefs : fundefs -> nat **)

and max_allocs_fundefs = function
| Fcons (_, _, vs, e, fnd') ->
  max (add (Datatypes.length vs) (max_allocs e)) (max_allocs_fundefs fnd')
| Fnil -> O

type n_iTyInfo = name * (((name * cTag) * int) * int) list

type n_iEnv = n_iTyInfo M.t

(** val update_iEnv : n_iEnv -> int -> cTyInfo -> n_iEnv **)

let update_iEnv ienv p = function
| (p0, ord) ->
  let (p1, arity) = p0 in
  let (p2, t0) = p1 in
  let (name0, nameTy) = p2 in
  (match M.get t0 ienv with
   | Some n ->
     let (nameTy0, iInf) = n in
     M.set t0 (nameTy0, ((((name0, p), arity), ord) :: iInf)) ienv
   | None -> M.set t0 (nameTy, ((((name0, p), arity), ord) :: [])) ienv)

(** val compute_iEnv : cEnv -> n_iEnv **)

let compute_iEnv cenv =
  M.fold update_iEnv cenv M.empty

type cRep =
| Coq_enum of int
| Coq_boxed of int * int

(** val make_cRep : cEnv -> cTag -> cRep option **)

let make_cRep cenv ct =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
    (M.get ct (Obj.magic cenv)) (fun p ->
    let (y, n) = p in
    let (_, a) = y in
    if N.eqb a 0
    then ret (Obj.magic coq_Monad_option) (Coq_enum n)
    else ret (Obj.magic coq_Monad_option) (Coq_boxed (n, a)))

(** val coq_val : coq_type **)

let coq_val =
  if ptr64
  then Tlong (Unsigned, { attr_volatile = false; attr_alignas = None })
  else Tint (I32, Unsigned, { attr_volatile = false; attr_alignas = None })

(** val uval : coq_type **)

let uval =
  if ptr64
  then Tlong (Unsigned, { attr_volatile = false; attr_alignas = None })
  else Tint (I32, Unsigned, { attr_volatile = false; attr_alignas = None })

(** val val_typ : typ **)

let val_typ =
  if ptr64 then AST.Tlong else Tany32

(** val coq_Init_int : int -> init_data **)

let coq_Init_int x =
  if ptr64 then Init_int64 (Int64.repr x) else Init_int32 (Int.repr x)

(** val add : expr -> expr -> expr **)

let add a b =
  Ebinop (Oadd, a, b, (Tpointer (coq_val, { attr_volatile = false;
    attr_alignas = None })))

(** val sub : expr -> expr -> expr **)

let sub a b =
  Ebinop (Osub, a, b, (Tpointer (coq_val, { attr_volatile = false;
    attr_alignas = None })))

(** val not : expr -> expr **)

let not a =
  Eunop (Onotbool, a, type_bool)

(** val c_int' : int -> coq_type -> expr **)

let c_int' n t0 =
  if ptr64
  then Econst_long ((Int64.repr n), t0)
  else Econst_int ((Int.repr n), t0)

(** val reserve :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> int ->
    int -> statement **)

let reserve allocIdent limitIdent gcIdent threadInfIdent tinfIdent funInf l =
  let arr = Evar (funInf, (Tarray (uval, l, noattr))) in
  Sifthenelse
  ((not (Ebinop (Ole, (Ederef (arr, uval)),
     (sub (Etempvar (limitIdent, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (Etempvar (allocIdent, (Tpointer (coq_val,
       { attr_volatile = false; attr_alignas = None }))))), type_bool))),
  (Ssequence ((Scall (None, (Evar (gcIdent, (Tfunction ((Tcons ((Tpointer
  (coq_val, noattr)), (Tcons ((Tpointer ((Tstruct (threadInfIdent, noattr)),
  noattr)), Tnil)))), Tvoid, { cc_vararg = false; cc_unproto = false;
  cc_structret = false })))), (arr :: ((Etempvar (tinfIdent, (Tpointer
  ((Tstruct (threadInfIdent, noattr)), noattr)))) :: [])))), (Sset
  (allocIdent, (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer ((Tstruct
  (threadInfIdent, noattr)), noattr)))), (Tstruct (threadInfIdent,
  noattr)))), allocIdent, (Tpointer (coq_val, { attr_volatile = false;
  attr_alignas = None })))))))), Sskip)

(** val makeTagZ : cEnv -> cTag -> int option **)

let rec makeTagZ cenv ct =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
    (Obj.magic make_cRep cenv ct) (fun rep ->
    match rep with
    | Coq_enum t0 ->
      ret (Obj.magic coq_Monad_option) (Z.of_N (N.add (N.shiftl t0 1) 1))
    | Coq_boxed (t0, a) ->
      ret (Obj.magic coq_Monad_option)
        (Z.of_N
          (N.add
            (N.shiftl a ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))) t0)))

(** val makeTag : cEnv -> cTag -> expr option **)

let makeTag cenv ct =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
    (Obj.magic makeTagZ cenv ct) (fun t0 ->
    ret (Obj.magic coq_Monad_option) (c_int' t0 coq_val))

(** val makeVar : AST.ident -> int -> int M.t -> expr **)

let makeVar threadInfIdent x m =
  match M.get x m with
  | Some _ ->
    Evar (x, (Tfunction ((Tcons ((Tpointer ((Tstruct (threadInfIdent,
      noattr)), noattr)), Tnil)), Tvoid, { cc_vararg = false; cc_unproto =
      false; cc_structret = false })))
  | None -> Etempvar (x, coq_val)

(** val assignConstructorS' :
    AST.ident -> int M.t -> int -> nat -> int list -> statement **)

let rec assignConstructorS' threadInfIdent map0 x cur = function
| [] -> Sskip
| v :: vs' ->
  (match vs' with
   | [] ->
     let vv = makeVar threadInfIdent v map0 in
     Sassign ((Ederef
     ((add (Ecast ((Etempvar (x, coq_val)), (Tpointer (coq_val,
        { attr_volatile = false; attr_alignas = None }))))
        (c_int' (Z.of_nat cur) coq_val)), coq_val)), vv)
   | _ :: _ ->
     let vv = makeVar threadInfIdent v map0 in
     let prog =
       assignConstructorS' threadInfIdent map0 x (Nat0.add cur (S O)) vs'
     in
     Ssequence ((Sassign ((Ederef
     ((add (Ecast ((Etempvar (x, coq_val)), (Tpointer (coq_val,
        { attr_volatile = false; attr_alignas = None }))))
        (c_int' (Z.of_nat cur) coq_val)), coq_val)), vv)), prog))

(** val assignConstructorS :
    AST.ident -> AST.ident -> cEnv -> n_iEnv -> int M.t -> int -> cTag -> int
    list -> statement option **)

let assignConstructorS allocIdent threadInfIdent cenv _ map0 x t0 vs =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
    (Obj.magic makeTag cenv t0) (fun tag ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (Obj.magic make_cRep cenv t0) (fun rep ->
      match rep with
      | Coq_enum _ -> ret (Obj.magic coq_Monad_option) (Sset (x, tag))
      | Coq_boxed (_, a) ->
        let stm = assignConstructorS' threadInfIdent map0 x O vs in
        ret (Obj.magic coq_Monad_option) (Ssequence ((Ssequence ((Ssequence
          ((Sset (x, (Ecast
          ((add (Etempvar (allocIdent, (Tpointer (coq_val, { attr_volatile =
             false; attr_alignas = None })))) (c_int' Z.one coq_val)),
          coq_val)))), (Sset (allocIdent,
          (add (Etempvar (allocIdent, (Tpointer (coq_val, { attr_volatile =
            false; attr_alignas = None }))))
            (c_int' (Z.of_N (N.add a 1)) coq_val)))))), (Sassign ((Ederef
          ((add (Ecast ((Etempvar (x, coq_val)), (Tpointer (coq_val,
             { attr_volatile = false; attr_alignas = None }))))
             (c_int' ((~-) 1) coq_val)), coq_val)), tag)))), stm))))

(** val isPtr : AST.ident -> int -> int -> statement **)

let isPtr isptrIdent retId v =
  Scall ((Some retId), (Evar (isptrIdent, (Tfunction ((Tcons (coq_val,
    Tnil)), (Tint (IBool, Unsigned, noattr)), { cc_vararg = false;
    cc_unproto = false; cc_structret = false })))), ((Ecast ((Etempvar (v,
    coq_val)), coq_val)) :: []))

(** val isBoxed : cEnv -> n_iEnv -> cTag -> bool **)

let isBoxed cenv _ ct =
  match make_cRep cenv ct with
  | Some rep ->
    (match rep with
     | Coq_enum _ -> false
     | Coq_boxed (_, _) -> true)
  | None -> false

(** val asgnFunVars :
    AST.ident -> int list -> int list -> statement option **)

let rec asgnFunVars argsIdent vs ind =
  match vs with
  | [] ->
    (match ind with
     | [] -> ret (Obj.magic coq_Monad_option) Sskip
     | _ :: _ -> None)
  | v :: vs' ->
    (match ind with
     | [] -> None
     | i :: ind' ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
         (asgnFunVars argsIdent vs' ind') (fun rest ->
         ret (Obj.magic coq_Monad_option) (Ssequence ((Sset (v, (Ederef
           ((add (Etempvar (argsIdent, (Tpointer (coq_val, { attr_volatile =
              false; attr_alignas = None })))) (c_int' (Z.of_N i) coq_val)),
           coq_val)))), rest))))

(** val asgnAppVars' :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> int list -> int list
    -> statement option **)

let rec asgnAppVars' argsIdent allocIdent threadInfIdent tinfIdent vs ind =
  match vs with
  | [] ->
    (match ind with
     | [] ->
       ret (Obj.magic coq_Monad_option) (Sassign ((Efield ((Ederef ((Etempvar
         (tinfIdent, (Tpointer ((Tstruct (threadInfIdent, noattr)),
         noattr)))), (Tstruct (threadInfIdent, noattr)))), allocIdent,
         (Tpointer (coq_val, { attr_volatile = false; attr_alignas =
         None })))), (Etempvar (allocIdent, (Tpointer (coq_val,
         { attr_volatile = false; attr_alignas = None }))))))
     | _ :: _ -> None)
  | v :: vs' ->
    (match ind with
     | [] -> None
     | i :: ind' ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
         (asgnAppVars' argsIdent allocIdent threadInfIdent tinfIdent vs' ind')
         (fun rest ->
         ret (Obj.magic coq_Monad_option) (Ssequence ((Sassign ((Ederef
           ((add (Etempvar (argsIdent, (Tpointer (coq_val, { attr_volatile =
              false; attr_alignas = None })))) (c_int' (Z.of_N i) coq_val)),
           coq_val)), (Etempvar (v, coq_val)))), rest))))

(** val asgnAppVars :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> int list -> int list
    -> statement option **)

let asgnAppVars argsIdent allocIdent threadInfIdent tinfIdent vs ind =
  match asgnAppVars' argsIdent allocIdent threadInfIdent tinfIdent vs ind with
  | Some s ->
    ret (Obj.magic coq_Monad_option) (Ssequence ((Sset (argsIdent, (Efield
      ((Ederef ((Etempvar (tinfIdent, (Tpointer ((Tstruct (threadInfIdent,
      noattr)), noattr)))), (Tstruct (threadInfIdent, noattr)))), argsIdent,
      (Tarray (uval, maxArgs, noattr)))))), s))
  | None -> None

(** val make_case_switch :
    AST.ident -> AST.ident -> int -> labeled_statements -> labeled_statements
    -> statement **)

let make_case_switch isptrIdent caseIdent x ls ls' =
  Ssequence ((isPtr isptrIdent caseIdent x), (Sifthenelse ((Etempvar
    (caseIdent, (Tint (IBool, Unsigned, noattr)))), (Sswitch ((Ebinop (Oand,
    (Ederef
    ((add (Ecast ((Etempvar (x, coq_val)), (Tpointer (coq_val,
       { attr_volatile = false; attr_alignas = None }))))
       (c_int' ((~-) 1) coq_val)), coq_val)), (Econst_int
    ((Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       1)))))))), coq_val)), coq_val)), ls)), (Sswitch ((Ebinop (Oshr,
    (Etempvar (x, coq_val)), (Econst_int ((Int.repr 1), coq_val)), coq_val)),
    ls')))))

(** val translate_body :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> exp -> fEnv -> cEnv -> n_iEnv -> int M.t -> statement option **)

let rec translate_body argsIdent allocIdent threadInfIdent tinfIdent isptrIdent caseIdent e fenv cenv ienv map0 =
  match e with
  | Econstr (x, t0, vs, e') ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (assignConstructorS allocIdent threadInfIdent cenv ienv map0 x t0 vs)
      (fun prog ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
        (translate_body argsIdent allocIdent threadInfIdent tinfIdent
          isptrIdent caseIdent e' fenv cenv ienv map0) (fun prog' ->
        ret (Obj.magic coq_Monad_option) (Ssequence (prog, prog'))))
  | Ecase (x, cs) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (let rec makeCases = function
       | [] -> ret (Obj.magic coq_Monad_option) (LSnil, LSnil)
       | p :: l' ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
           (translate_body argsIdent allocIdent threadInfIdent tinfIdent
             isptrIdent caseIdent (snd p) fenv cenv ienv map0) (fun prog ->
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
             (Obj.magic __) (makeCases l') (fun p' ->
             pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
               (Obj.magic __) (Obj.magic makeTagZ cenv (fst p)) (fun tag ->
               let (ls, ls') = p' in
               if isBoxed cenv ienv (fst p)
               then (match ls with
                     | LSnil ->
                       ret (Obj.magic coq_Monad_option) ((LScons (None, prog,
                         ls)), ls')
                     | LScons (_, _, _) ->
                       ret (Obj.magic coq_Monad_option) ((LScons ((Some
                         (Z.coq_land tag ((fun p->1+2*p) ((fun p->1+2*p)
                           ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
                           ((fun p->1+2*p) ((fun p->1+2*p) 1))))))))),
                         (Ssequence (prog, Sbreak)), ls)), ls'))
               else (match ls' with
                     | LSnil ->
                       ret (Obj.magic coq_Monad_option) (ls, (LScons (None,
                         prog, ls')))
                     | LScons (_, _, _) ->
                       ret (Obj.magic coq_Monad_option) (ls, (LScons ((Some
                         (Z.shiftr tag 1)), (Ssequence (prog, Sbreak)), ls')))))))
       in makeCases cs) (fun p ->
      let (ls, ls') = p in
      ret (Obj.magic coq_Monad_option)
        (make_case_switch isptrIdent caseIdent x ls ls'))
  | Eproj (x, _, n, v, e') ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (translate_body argsIdent allocIdent threadInfIdent tinfIdent
        isptrIdent caseIdent e' fenv cenv ienv map0) (fun prog ->
      ret (Obj.magic coq_Monad_option) (Ssequence ((Sset (x, (Ederef
        ((add (Ecast ((Etempvar (v, coq_val)), (Tpointer (coq_val,
           { attr_volatile = false; attr_alignas = None }))))
           (c_int' (Z.of_N n) coq_val)), coq_val)))), prog)))
  | Eapp (x, t0, vs) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (M.get t0 (Obj.magic fenv)) (fun inf ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
        (asgnAppVars argsIdent allocIdent threadInfIdent tinfIdent vs
          (snd inf)) (fun asgn ->
        let vv = makeVar threadInfIdent x map0 in
        ret (Obj.magic coq_Monad_option) (Ssequence (asgn, (Scall (None,
          (Ecast (vv, (Tpointer ((Tfunction ((Tcons ((Tpointer ((Tstruct
          (threadInfIdent, noattr)), noattr)), Tnil)), Tvoid, { cc_vararg =
          false; cc_unproto = false; cc_structret = false })), noattr)))),
          ((Etempvar (tinfIdent, (Tpointer ((Tstruct (threadInfIdent,
          noattr)), noattr)))) :: [])))))))
  | Ehalt x ->
    ret (Obj.magic coq_Monad_option) (Ssequence ((Sassign ((Ederef
      ((add (Etempvar (argsIdent, (Tpointer (coq_val, { attr_volatile =
         false; attr_alignas = None })))) (c_int' (Z.of_nat (S O)) coq_val)),
      coq_val)), (Etempvar (x, coq_val)))), (Sreturn None)))
  | _ -> None

(** val mkFun :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> int list -> statement -> coq_function **)

let mkFun argsIdent allocIdent limitIdent threadInfIdent tinfIdent caseIdent vs body =
  { fn_return = Tvoid; fn_callconv = cc_default; fn_params = ((tinfIdent,
    (Tpointer ((Tstruct (threadInfIdent, noattr)), noattr))) :: []);
    fn_vars =
    (app (map (fun x -> (x, coq_val)) vs) ((allocIdent, (Tpointer (coq_val,
      { attr_volatile = false; attr_alignas = None }))) :: ((limitIdent,
      (Tpointer (coq_val, { attr_volatile = false; attr_alignas =
      None }))) :: ((argsIdent, (Tpointer (coq_val, { attr_volatile = false;
      attr_alignas = None }))) :: ((caseIdent, (Tint (IBool, Unsigned,
      noattr))) :: []))))); fn_temps = []; fn_body = body }

(** val translate_fundefs :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> AST.ident -> fundefs -> fEnv -> cEnv -> n_iEnv
    -> int M.t -> (int * (Clight.fundef, coq_type) globdef) list option **)

let rec translate_fundefs argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fnd fenv cenv ienv map0 =
  match fnd with
  | Fcons (f, t0, vs, e, fnd') ->
    (match translate_fundefs argsIdent allocIdent limitIdent gcIdent
             threadInfIdent tinfIdent isptrIdent caseIdent fnd' fenv cenv
             ienv map0 with
     | Some rest ->
       (match translate_body argsIdent allocIdent threadInfIdent tinfIdent
                isptrIdent caseIdent e fenv cenv ienv map0 with
        | Some body ->
          let localVars = app vs (get_allocs e) in
          (match M.get t0 fenv with
           | Some inf ->
             let (l, locs) = inf in
             (match asgnFunVars argsIdent vs locs with
              | Some asgn ->
                (match M.get f map0 with
                 | Some gcArrIdent ->
                   ret (Obj.magic coq_Monad_option) ((f, (Gfun (Internal
                     (mkFun argsIdent allocIdent limitIdent threadInfIdent
                       tinfIdent caseIdent localVars (Ssequence ((Ssequence
                       ((Ssequence ((Ssequence ((Ssequence ((Sset
                       (allocIdent, (Efield ((Ederef ((Etempvar (tinfIdent,
                       (Tpointer ((Tstruct (threadInfIdent, noattr)),
                       noattr)))), (Tstruct (threadInfIdent, noattr)))),
                       allocIdent, (Tpointer (coq_val, { attr_volatile =
                       false; attr_alignas = None })))))), (Sset (limitIdent,
                       (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
                       ((Tstruct (threadInfIdent, noattr)), noattr)))),
                       (Tstruct (threadInfIdent, noattr)))), limitIdent,
                       (Tpointer (coq_val, { attr_volatile = false;
                       attr_alignas = None })))))))), (Sset (argsIdent,
                       (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
                       ((Tstruct (threadInfIdent, noattr)), noattr)))),
                       (Tstruct (threadInfIdent, noattr)))), argsIdent,
                       (Tarray (uval, maxArgs, noattr)))))))),
                       (reserve allocIdent limitIdent gcIdent threadInfIdent
                         tinfIdent gcArrIdent
                         (Z.of_N (N.add l ((fun p->2*p) 1)))))), asgn)),
                       body)))))) :: rest)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | Fnil -> ret (Obj.magic coq_Monad_option) []

(** val make_extern_decl :
    name M.t -> (int * (Clight.fundef, coq_type) globdef) -> bool ->
    (int * (Clight.fundef, coq_type) globdef) option **)

let make_extern_decl nenv def gv =
  let (vIdent, g) = def in
  (match g with
   | Gfun f0 ->
     (match f0 with
      | Internal f ->
        (match M.get vIdent nenv with
         | Some n ->
           (match n with
            | Coq_nAnon -> None
            | Coq_nNamed f_string ->
              Some (vIdent, (Gfun (External ((EF_external (f_string,
                (signature_of_type (type_of_params f.fn_params) f.fn_return
                  f.fn_callconv))), (type_of_params f.fn_params),
                f.fn_return, f.fn_callconv)))))
         | None -> None)
      | External (_, _, _, _) -> None)
   | Gvar v ->
     let { gvar_info = v_info; gvar_init = _; gvar_readonly = v_r;
       gvar_volatile = v_v } = v
     in
     if gv
     then Some (vIdent, (Gvar { gvar_info = v_info; gvar_init = [];
            gvar_readonly = v_r; gvar_volatile = v_v }))
     else None)

(** val make_extern_decls :
    name M.t -> (int * (Clight.fundef, coq_type) globdef) list -> bool ->
    (int * (Clight.fundef, coq_type) globdef) list **)

let rec make_extern_decls nenv defs gv =
  match defs with
  | [] -> []
  | fdefs :: defs' ->
    let decls = make_extern_decls nenv defs' gv in
    (match make_extern_decl nenv fdefs gv with
     | Some decl -> decl :: decls
     | None -> decls)

(** val body_external_decl :
    AST.ident -> AST.ident -> AST.ident -> int * (Clight.fundef, coq_type)
    globdef **)

let body_external_decl bodyIdent threadInfIdent tinfIdent =
  let params =
    type_of_params ((tinfIdent, (Tpointer ((Tstruct (threadInfIdent,
      noattr)), noattr))) :: [])
  in
  (bodyIdent, (Gfun (External ((EF_external (('b'::('o'::('d'::('y'::[])))),
  (signature_of_type params Tvoid cc_default))), params, Tvoid, cc_default))))

(** val translate_funs :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> exp ->
    fEnv -> cEnv -> n_iEnv -> int M.t -> (int * (Clight.fundef, coq_type)
    globdef) list option **)

let translate_funs argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent isptrIdent caseIdent e fenv cenv ienv m =
  match e with
  | Efun (fnd, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
      (translate_fundefs argsIdent allocIdent limitIdent gcIdent
        threadInfIdent tinfIdent isptrIdent caseIdent fnd fenv cenv ienv m)
      (fun funs ->
      let localVars = get_allocs e0 in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
        (Obj.magic translate_body argsIdent allocIdent threadInfIdent
          tinfIdent isptrIdent caseIdent e0 fenv cenv ienv m) (fun body ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
          (M.get mainIdent (Obj.magic m)) (fun gcArrIdent ->
          ret (Obj.magic coq_Monad_option) ((bodyIdent, (Gfun (Internal
            { fn_return = Tvoid; fn_callconv = cc_default; fn_params =
            ((tinfIdent, (Tpointer ((Tstruct (threadInfIdent, noattr)),
            noattr))) :: []); fn_vars =
            (app (map (fun x -> (x, coq_val)) localVars) ((allocIdent,
              (Tpointer (coq_val, { attr_volatile = false; attr_alignas =
              None }))) :: ((limitIdent, (Tpointer (coq_val,
              { attr_volatile = false; attr_alignas =
              None }))) :: ((argsIdent, (Tpointer (coq_val, { attr_volatile =
              false; attr_alignas = None }))) :: [])))); fn_temps = [];
            fn_body = (Ssequence ((Ssequence ((Ssequence ((Ssequence ((Sset
            (allocIdent, (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
            ((Tstruct (threadInfIdent, noattr)), noattr)))), (Tstruct
            (threadInfIdent, noattr)))), allocIdent, (Tpointer (coq_val,
            { attr_volatile = false; attr_alignas = None })))))), (Sset
            (limitIdent, (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
            ((Tstruct (threadInfIdent, noattr)), noattr)))), (Tstruct
            (threadInfIdent, noattr)))), limitIdent, (Tpointer (coq_val,
            { attr_volatile = false; attr_alignas = None })))))))), (Sset
            (argsIdent, (Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
            ((Tstruct (threadInfIdent, noattr)), noattr)))), (Tstruct
            (threadInfIdent, noattr)))), argsIdent, (Tarray (uval, maxArgs,
            noattr)))))))),
            (reserve allocIdent limitIdent gcIdent threadInfIdent tinfIdent
              gcArrIdent ((fun p->2*p) 1)))), body)) }))) :: funs))))
  | _ -> None

type 't nState = (int, 't) state

(** val getName : int nState **)

let getName =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun n ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      ((Obj.magic coq_MonadState_state).put (Pos.add n 1)) (fun _ ->
      ret (Obj.magic coq_Monad_state) n))

(** val make_ind_array : int list -> init_data list **)

let rec make_ind_array = function
| [] -> []
| n :: l' -> (coq_Init_int (Z.of_N n)) :: (make_ind_array l')

(** val pos2string' : int -> char list -> char list **)

let rec pos2string' p s =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p' -> pos2string' p' ('1'::s))
    (fun p' -> pos2string' p' ('0'::s))
    (fun _ -> '1'::s)
    p

(** val pos2string : int -> char list **)

let pos2string p =
  pos2string' p []

(** val show_pos : int -> char list **)

let show_pos =
  pos2string

(** val update_nEnv_fun_info : int -> int -> name M.t -> name M.t **)

let update_nEnv_fun_info f f_inf nenv =
  match M.get f nenv with
  | Some n ->
    (match n with
     | Coq_nAnon ->
       M.set f_inf (Coq_nNamed
         (append (append ('x'::[]) (show_pos f))
           ('_'::('i'::('n'::('f'::('o'::[]))))))) nenv
     | Coq_nNamed s ->
       M.set f_inf (Coq_nNamed
         (append s ('_'::('i'::('n'::('f'::('o'::[]))))))) nenv)
  | None ->
    M.set f_inf (Coq_nNamed
      (append (show_pos f) ('_'::('i'::('n'::('f'::('o'::[]))))))) nenv

(** val make_fundef_info :
    fundefs -> fEnv -> name M.t -> (((int * (Clight.fundef, coq_type)
    globdef) list * int M.t) * name M.t) option nState **)

let rec make_fundef_info fnd fenv nenv =
  match fnd with
  | Fcons (x, t0, _, e, fnd') ->
    (match M.get t0 fenv with
     | Some inf ->
       let (_, l) = inf in
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (make_fundef_info fnd' fenv nenv) (fun rest ->
         match rest with
         | Some rest' ->
           let (p, nenv') = rest' in
           let (defs, map0) = p in
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (Obj.magic getName) (fun info_name ->
             let len = Z.of_nat (Datatypes.length l) in
             let ind = { gvar_info = (Tarray (uval,
               (Z.add len ((fun p->2*p) 1)), noattr)); gvar_init =
               ((coq_Init_int (Z.of_nat (max_allocs e))) :: ((coq_Init_int
                                                               len) :: 
               (make_ind_array l))); gvar_readonly = true; gvar_volatile =
               false }
             in
             ret (Obj.magic coq_Monad_state) (Some ((((info_name, (Gvar
               ind)) :: defs), (M.set x info_name map0)),
               (update_nEnv_fun_info x info_name nenv'))))
         | None -> ret (Obj.magic coq_Monad_state) None)
     | None -> ret (Obj.magic coq_Monad_state) None)
  | Fnil -> ret (Obj.magic coq_Monad_state) (Some (([], M.empty), nenv))

(** val add_bodyinfo :
    AST.ident -> exp -> fEnv -> name M.t -> int M.t -> (int * (Clight.fundef,
    coq_type) globdef) list -> (((int * (Clight.fundef, coq_type) globdef)
    list * int M.t) * name M.t) option nState **)

let add_bodyinfo mainIdent e _ nenv map0 defs =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic getName) (fun info_name ->
    let ind = { gvar_info = (Tarray (uval, ((fun p->2*p) 1), noattr));
      gvar_init =
      ((coq_Init_int (Z.of_nat (max_allocs e))) :: ((coq_Init_int 0) :: []));
      gvar_readonly = true; gvar_volatile = false }
    in
    ret (Obj.magic coq_Monad_state) (Some ((((info_name, (Gvar
      ind)) :: defs), (M.set mainIdent info_name map0)),
      (M.set info_name (Coq_nNamed
        ('b'::('o'::('d'::('y'::('_'::('i'::('n'::('f'::('o'::[]))))))))))
        nenv))))

(** val make_funinfo :
    AST.ident -> exp -> fEnv -> name M.t -> (((int * (Clight.fundef,
    coq_type) globdef) list * int M.t) * name M.t) option nState **)

let make_funinfo mainIdent e fenv nenv =
  match e with
  | Econstr (_, _, _, _) -> ret (Obj.magic coq_Monad_state) None
  | Ecase (_, _) -> ret (Obj.magic coq_Monad_state) None
  | Eproj (_, _, _, _, _) -> ret (Obj.magic coq_Monad_state) None
  | Efun (fnd, e') ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (make_fundef_info fnd fenv nenv) (fun p ->
      match p with
      | Some p' ->
        let (p0, nenv') = p' in
        let (defs, map0) = p0 in
        add_bodyinfo mainIdent e' fenv nenv' map0 defs
      | None -> ret (Obj.magic coq_Monad_state) None)
  | Eapp (_, _, _) -> ret (Obj.magic coq_Monad_state) None
  | Eprim (_, _, _, _) -> ret (Obj.magic coq_Monad_state) None
  | Ehalt _ -> ret (Obj.magic coq_Monad_state) None

(** val global_defs :
    AST.ident -> AST.ident -> AST.ident -> exp -> (int * (Clight.fundef,
    coq_type) globdef) list **)

let global_defs gcIdent threadInfIdent isptrIdent _ =
  (gcIdent, (Gfun (External ((EF_external (('g'::('c'::[])), { sig_args =
    (val_typ :: []); sig_res = None; sig_cc = cc_default })), (Tcons
    ((Tpointer (coq_val, noattr)), (Tcons ((Tpointer ((Tstruct
    (threadInfIdent, noattr)), noattr)), Tnil)))), Tvoid,
    cc_default)))) :: ((isptrIdent, (Gfun (External ((EF_external
    (('i'::('s'::('_'::('p'::('t'::('r'::[])))))), { sig_args =
    (val_typ :: []); sig_res = None; sig_cc = cc_default })), (Tcons
    (coq_val, Tnil)), (Tint (IBool, Unsigned, noattr)), cc_default)))) :: [])

(** val make_defs :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> exp ->
    fEnv -> cEnv -> n_iEnv -> name M.t -> (name M.t * (int * (Clight.fundef,
    coq_type) globdef) list) option nState **)

let make_defs argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent isptrIdent caseIdent e fenv cenv ienv nenv =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic make_funinfo mainIdent e fenv nenv) (fun fun_inf' ->
    match fun_inf' with
    | Some p ->
      let (p0, nenv') = p in
      let (fun_inf, map0) = p0 in
      (match translate_funs argsIdent allocIdent limitIdent gcIdent mainIdent
               bodyIdent threadInfIdent tinfIdent isptrIdent caseIdent e fenv
               cenv ienv map0 with
       | Some fun_defs' ->
         let fun_defs = rev fun_defs' in
         ret (Obj.magic coq_Monad_state) (Some (nenv',
           (app (global_defs gcIdent threadInfIdent isptrIdent e)
             (app fun_inf fun_defs))))
       | None -> ret (Obj.magic coq_Monad_state) None)
    | None -> ret (Obj.magic coq_Monad_state) None)

(** val composites :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    composite_definition list **)

let composites argsIdent allocIdent limitIdent threadInfIdent heapInfIdent =
  (Composite (threadInfIdent, Struct, ((allocIdent, (Tpointer (coq_val,
    { attr_volatile = false; attr_alignas = None }))) :: ((limitIdent,
    (Tpointer (coq_val, { attr_volatile = false; attr_alignas =
    None }))) :: ((heapInfIdent,
    (tptr (Tstruct (heapInfIdent, noattr)))) :: ((argsIdent, (Tarray (uval,
    maxArgs, noattr))) :: [])))), noattr)) :: []

(** val mk_prog_opt :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> (AST.ident * (Clight.fundef, coq_type) globdef) list ->
    AST.ident -> bool -> Clight.program option **)

let mk_prog_opt argsIdent allocIdent limitIdent bodyIdent threadInfIdent heapInfIdent defs main add_comp =
  let composites0 =
    if add_comp
    then composites argsIdent allocIdent limitIdent threadInfIdent
           heapInfIdent
    else []
  in
  let res = make_program composites0 defs (bodyIdent :: []) main in
  (match res with
   | OK p -> Some p
   | Error _ -> None)

(** val wrap_in_fun : exp -> exp **)

let wrap_in_fun e = match e with
| Efun (_, _) -> e
| _ -> Efun (Fnil, e)

(** val add_inf_vars :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> name M.t -> name M.t **)

let add_inf_vars argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent nenv =
  M.set isptrIdent (Coq_nNamed ('i'::('s'::('_'::('p'::('t'::('r'::[])))))))
    (M.set argsIdent (Coq_nNamed ('a'::('r'::('g'::('s'::[])))))
      (M.set allocIdent (Coq_nNamed ('a'::('l'::('l'::('o'::('c'::[]))))))
        (M.set limitIdent (Coq_nNamed ('l'::('i'::('m'::('i'::('t'::[]))))))
          (M.set gcIdent (Coq_nNamed
            ('g'::('a'::('r'::('b'::('a'::('g'::('e'::('_'::('c'::('o'::('l'::('l'::('e'::('c'::('t'::[]))))))))))))))))
            (M.set mainIdent (Coq_nNamed ('m'::('a'::('i'::('n'::[])))))
              (M.set bodyIdent (Coq_nNamed ('b'::('o'::('d'::('y'::[])))))
                (M.set threadInfIdent (Coq_nNamed
                  ('t'::('h'::('r'::('e'::('a'::('d'::('_'::('i'::('n'::('f'::('o'::[]))))))))))))
                  (M.set tinfIdent (Coq_nNamed
                    ('t'::('i'::('n'::('f'::('o'::[]))))))
                    (M.set heapInfIdent (Coq_nNamed
                      ('h'::('e'::('a'::('p'::[])))))
                      (M.set numArgsIdent (Coq_nNamed
                        ('n'::('u'::('m'::('_'::('a'::('r'::('g'::('s'::[])))))))))
                        nenv))))))))))

(** val ensure_unique : name M.t -> name M.t **)

let ensure_unique l =
  M.map (fun x n ->
    match n with
    | Coq_nAnon -> Coq_nAnon
    | Coq_nNamed s -> Coq_nNamed (append s (append ('_'::[]) (show_pos x)))) l

(** val make_proj : expr -> nat -> nat -> expr list **)

let rec make_proj recExpr start = function
| O -> []
| S n ->
  let s = make_proj recExpr (S start) n in
  (Ederef
  ((add (Ecast (recExpr, (Tpointer (coq_val, { attr_volatile = false;
     attr_alignas = None })))) (c_int' (Z.of_nat start) coq_val)),
  coq_val)) :: s

(** val make_Asgn : expr list -> expr list -> statement **)

let rec make_Asgn les res =
  match les with
  | [] -> Sskip
  | hl :: les0 ->
    (match res with
     | [] -> Sskip
     | hr :: res0 -> Ssequence ((Sassign (hl, hr)), (make_Asgn les0 res0)))

(** val make_argList' :
    nat -> name M.t -> (name M.t * (AST.ident * coq_type) list) nState **)

let rec make_argList' n nenv =
  match n with
  | O -> ret (Obj.magic coq_Monad_state) (nenv, [])
  | S n' ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic getName) (fun new_id ->
      let new_name = append ('a'::('r'::('g'::[]))) (nat2string10 n') in
      let nenv0 = M.set new_id (Coq_nNamed new_name) nenv in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (make_argList' n' nenv0) (fun rest ->
        let (nenv1, rest_id) = rest in
        ret (Obj.magic coq_Monad_state) (nenv1, ((new_id,
          coq_val) :: rest_id))))

(** val make_argList :
    nat -> name M.t -> (name M.t * (AST.ident * coq_type) list) nState **)

let rec make_argList n nenv =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (make_argList' n nenv) (fun rest ->
    let (nenv0, rest_l) = rest in
    ret (Obj.magic coq_Monad_state) (nenv0, (rev rest_l)))

(** val make_constrAsgn' :
    AST.ident -> (AST.ident * coq_type) list -> nat -> statement **)

let rec make_constrAsgn' argv argList n =
  match argList with
  | [] -> Sskip
  | p :: argList' ->
    let (id, ty) = p in
    let s' = make_constrAsgn' argv argList' (S n) in
    Ssequence ((Sassign ((Ederef
    ((add (Ecast ((Etempvar (argv, coq_val)), (Tpointer (coq_val,
       { attr_volatile = false; attr_alignas = None }))))
       (c_int' (Z.of_nat n) coq_val)), coq_val)), (Evar (id, ty)))), s')

(** val make_constrAsgn :
    AST.ident -> (AST.ident * coq_type) list -> statement **)

let make_constrAsgn argv argList =
  make_constrAsgn' argv argList (S O)

(** val make_constructors :
    cEnv -> ident -> (((name * cTag) * int) * int) list -> name M.t -> (name
    M.t * (int * (Clight.fundef, coq_type) globdef) list) nState **)

let rec make_constructors cenv nTy ctrs nenv =
  match ctrs with
  | [] -> ret (Obj.magic coq_Monad_state) (nenv, [])
  | p :: ctrs0 ->
    let (p0, ord) = p in
    let (p1, n) = p0 in
    let (n0, _) = p1 in
    (match n0 with
     | Coq_nAnon ->
       ((fun f0 fp n -> if n=0 then f0 () else fp n)
          (fun _ -> make_constructors cenv nTy ctrs0 nenv)
          (fun _ -> make_constructors cenv nTy ctrs0 nenv)
          n)
     | Coq_nNamed nCtr ->
       ((fun f0 fp n -> if n=0 then f0 () else fp n)
          (fun _ ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic getName) (fun constr_fun_id ->
            let constr_body = Sreturn (Some (Econst_int
              ((Int.repr (Z.add (Z.shiftl (Z.of_N ord) 1) 1)), coq_val)))
            in
            let constr_fun = Internal { fn_return = coq_val; fn_callconv =
              cc_default; fn_params = []; fn_vars = []; fn_temps = [];
              fn_body = constr_body }
            in
            let nenv0 =
              M.set constr_fun_id (Coq_nNamed
                (append ('m'::('a'::('k'::('e'::('_'::[])))))
                  (append nTy (append ('_'::[]) nCtr)))) nenv
            in
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (make_constructors cenv nTy ctrs0 nenv0)
              (fun l ->
              let (nenv1, funs) = l in
              ret (Obj.magic coq_Monad_state) (nenv1, ((constr_fun_id, (Gfun
                constr_fun)) :: funs)))))
          (fun arr ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic getName) (fun constr_fun_id ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (Obj.magic getName) (fun argvIdent ->
              pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                (Obj.magic __) (Obj.magic make_argList (Pos.to_nat arr) nenv)
                (fun argList ->
                let (nenv0, argList0) = argList in
                let asgn_s = make_constrAsgn argvIdent argList0 in
                let header =
                  c_int'
                    (Z.of_N
                      (N.add
                        (N.shiftl arr ((fun p->2*p) ((fun p->1+2*p)
                          ((fun p->2*p) 1)))) ord)) coq_val
                in
                let constr_body = Ssequence ((Sassign ((Ederef
                  ((add (Ecast ((Etempvar (argvIdent, coq_val)), (Tpointer
                     (coq_val, { attr_volatile = false; attr_alignas =
                     None })))) (c_int' 0 coq_val)), coq_val)), header)),
                  (Ssequence (asgn_s, (Sreturn (Some
                  (add (Evar (argvIdent, (Tpointer ((Tpointer (coq_val,
                    { attr_volatile = false; attr_alignas = None })),
                    { attr_volatile = false; attr_alignas = None }))))
                    (c_int' 1 coq_val)))))))
                in
                let constr_fun = Internal { fn_return = coq_val;
                  fn_callconv = cc_default; fn_params =
                  (app argList0 ((argvIdent, (Tpointer ((Tpointer (coq_val,
                    { attr_volatile = false; attr_alignas = None })),
                    { attr_volatile = false; attr_alignas = None }))) :: []));
                  fn_vars = []; fn_temps = []; fn_body = constr_body }
                in
                let nenv1 =
                  M.set argvIdent (Coq_nNamed ('a'::('r'::('g'::('v'::[])))))
                    (M.set constr_fun_id (Coq_nNamed
                      (append ('m'::('a'::('k'::('e'::('_'::[])))))
                        (append nTy (append ('_'::[]) nCtr)))) nenv0)
                in
                pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                  (Obj.magic __) (make_constructors cenv nTy ctrs0 nenv1)
                  (fun l ->
                  let (nenv2, funs) = l in
                  ret (Obj.magic coq_Monad_state) (nenv2, ((constr_fun_id,
                    (Gfun constr_fun)) :: funs)))))))
          n))

(** val make_elim_Asgn : AST.ident -> AST.ident -> nat -> statement **)

let rec make_elim_Asgn argv valIdent arr =
  let argv_proj = make_proj (Etempvar (argv, coq_val)) O arr in
  let val_proj = make_proj (Etempvar (valIdent, coq_val)) O arr in
  make_Asgn argv_proj val_proj

(** val asgn_string_init : char list -> init_data list **)

let rec asgn_string_init = function
| [] -> (Init_int8 Int.zero) :: []
| c::s' ->
  let l = asgn_string_init s' in
  let i = Int.repr (Z.of_N (coq_N_of_ascii c)) in (Init_int8 i) :: l

(** val make_arrGV : int list -> (Clight.fundef, coq_type) globdef **)

let make_arrGV arrList =
  Gvar { gvar_info = (tarray tint (Z.of_nat (Datatypes.length arrList)));
    gvar_init = (map (fun n -> coq_Init_int (Z.of_N n)) arrList);
    gvar_readonly = true; gvar_volatile = false }

(** val pad_char_init : init_data list -> nat -> init_data list **)

let pad_char_init l n =
  let m = Nat0.sub n (Datatypes.length l) in
  app l (repeat (Init_int8 Int.zero) m)

(** val make_names_init : name list -> nat -> nat * init_data list **)

let rec make_names_init nameList n =
  match nameList with
  | [] -> (n, [])
  | n0 :: nameList' ->
    (match n0 with
     | Coq_nAnon ->
       let (max_len, init_l) = make_names_init nameList' n in
       let i = pad_char_init (asgn_string_init []) max_len in
       (max_len, (app i init_l))
     | Coq_nNamed s ->
       let (max_len, init_l) =
         make_names_init nameList' (max n (Nat0.add (length s) (S O)))
       in
       let i = pad_char_init (asgn_string_init s) max_len in
       (max_len, (app i init_l)))

(** val make_namesGV : name list -> (Clight.fundef, coq_type) globdef **)

let make_namesGV nameList =
  let (max_len, init_l) = make_names_init nameList (S O) in
  Gvar { gvar_info =
  (tarray (tarray tschar (Z.of_nat max_len))
    (Z.of_nat (Datatypes.length nameList))); gvar_init = init_l;
  gvar_readonly = true; gvar_volatile = false }

(** val make_eliminator :
    AST.ident -> AST.ident -> cEnv -> ident -> (((name * cTag) * int) * int)
    list -> name M.t -> (name M.t * (AST.ident * (Clight.fundef, coq_type)
    globdef) list) nState **)

let make_eliminator isptrIdent caseIdent _ nTy ctrs nenv =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic getName) (fun valIdent ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic getName) (fun ordIdent ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic getName) (fun argvIdent ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic getName) (fun elim_fun_id ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic getName) (fun _ ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (Obj.magic getName) (fun gv_arrIdent ->
              pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                (Obj.magic __) (Obj.magic getName) (fun gv_namesIdent ->
                pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                  (Obj.magic __)
                  (let rec make_elim_cases ctrs0 currOrd =
                     match ctrs0 with
                     | [] ->
                       ret (Obj.magic coq_Monad_state) (((LSnil, LSnil), []),
                         [])
                     | p :: ctrs1 ->
                       let (p0, ord) = p in
                       let (p1, n) = p0 in
                       let (nName, _) = p1 in
                       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                         (Obj.magic __) (make_elim_cases ctrs1 (S currOrd))
                         (fun temp ->
                         let (p2, arrList) = temp in
                         let (p3, nameList) = p2 in
                         let (ls, ls') = p3 in
                         let curr_s = Ssequence (Sskip, (Ssequence ((Sassign
                           ((Ederef
                           ((add (Ecast ((Etempvar (ordIdent, coq_val)),
                              (Tpointer (coq_val, { attr_volatile = false;
                              attr_alignas = None })))) (c_int' 0 coq_val)),
                           coq_val)), (c_int' (Z.of_nat currOrd) coq_val))),
                           (Ssequence
                           ((make_elim_Asgn argvIdent valIdent (N.to_nat n)),
                           Sbreak)))))
                         in
                         ((fun f0 fp n -> if n=0 then f0 () else fp n)
                            (fun _ ->
                            ret (Obj.magic coq_Monad_state) (((ls, (LScons
                              ((Some (Z.of_N ord)), curr_s, ls'))),
                              (nName :: nameList)), (n :: arrList)))
                            (fun _ ->
                            ret (Obj.magic coq_Monad_state) ((((LScons ((Some
                              (Z.of_N ord)), curr_s, ls)), ls'),
                              (nName :: nameList)), (n :: arrList)))
                            n))
                   in make_elim_cases ctrs O) (fun temp ->
                  let (p, arrList) = temp in
                  let (p0, nameList) = p in
                  let (ls, ls') = p0 in
                  let gv_names = make_namesGV nameList in
                  let gv_arr = make_arrGV arrList in
                  let elim_body =
                    make_case_switch isptrIdent caseIdent valIdent ls ls'
                  in
                  let elim_fun = Internal { fn_return = Tvoid; fn_callconv =
                    cc_default; fn_params = ((valIdent,
                    coq_val) :: ((ordIdent, (Tpointer (coq_val,
                    { attr_volatile = false; attr_alignas =
                    None }))) :: ((argvIdent, (Tpointer ((Tpointer (coq_val,
                    { attr_volatile = false; attr_alignas = None })),
                    { attr_volatile = false; attr_alignas =
                    None }))) :: []))); fn_vars = ((caseIdent, (Tint (IBool,
                    Unsigned, noattr))) :: []); fn_temps = []; fn_body =
                    elim_body }
                  in
                  let nenv0 =
                    M.set gv_namesIdent (Coq_nNamed
                      (append
                        ('n'::('a'::('m'::('e'::('s'::('_'::('o'::('f'::('_'::[])))))))))
                        nTy))
                      (M.set gv_arrIdent (Coq_nNamed
                        (append
                          ('a'::('r'::('i'::('t'::('i'::('e'::('s'::('_'::('o'::('f'::('_'::[])))))))))))
                          nTy))
                        (M.set ordIdent (Coq_nNamed
                          ('o'::('r'::('d'::('i'::('n'::('a'::('l'::[]))))))))
                          (M.set valIdent (Coq_nNamed
                            ('v'::('a'::('l'::[]))))
                            (M.set argvIdent (Coq_nNamed
                              ('a'::('r'::('g'::('v'::[])))))
                              (M.set elim_fun_id (Coq_nNamed
                                (append ('e'::('l'::('i'::('m'::('_'::[])))))
                                  nTy)) nenv)))))
                  in
                  ret (Obj.magic coq_Monad_state) (nenv0, ((gv_namesIdent,
                    gv_names) :: ((gv_arrIdent, gv_arr) :: ((elim_fun_id,
                    (Gfun elim_fun)) :: []))))))))))))

(** val make_interface :
    AST.ident -> AST.ident -> cEnv -> (int * n_iTyInfo) list -> name M.t ->
    (name M.t * (AST.ident * (Clight.fundef, coq_type) globdef) list) nState **)

let rec make_interface isptrIdent caseIdent cenv ienv_list nenv =
  match ienv_list with
  | [] -> ret (Obj.magic coq_Monad_state) (nenv, [])
  | p :: ienv_list' ->
    let (_, n) = p in
    let (n0, lCtr) = n in
    (match n0 with
     | Coq_nAnon -> make_interface isptrIdent caseIdent cenv ienv_list' nenv
     | Coq_nNamed nTy ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (make_constructors cenv nTy lCtr nenv) (fun l1 ->
         let (nenv0, def1) = l1 in
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (make_eliminator isptrIdent caseIdent cenv nTy lCtr nenv0)
           (fun l2 ->
           let (nenv1, def2) = l2 in
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __)
             (make_interface isptrIdent caseIdent cenv ienv_list' nenv1)
             (fun l3 ->
             let (nenv2, def3) = l3 in
             ret (Obj.magic coq_Monad_state) (nenv2,
               (app def1 (app def2 def3)))))))

(** val make_tinfoIdent : int **)

let make_tinfoIdent =
  (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))

(** val exportIdent : int **)

let exportIdent =
  (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))

(** val make_tinfo_rec :
    AST.ident -> int * (Clight.fundef, coq_type) globdef **)

let make_tinfo_rec threadInfIdent =
  (make_tinfoIdent, (Gfun (External ((EF_external
    (('m'::('a'::('k'::('e'::('_'::('t'::('i'::('n'::('f'::('o'::[])))))))))),
    { sig_args = []; sig_res = (Some val_typ); sig_cc = cc_default })), Tnil,
    (Tpointer ((Tstruct (threadInfIdent, noattr)), noattr)), cc_default))))

(** val export_rec : AST.ident -> int * (Clight.fundef, coq_type) globdef **)

let export_rec threadInfIdent =
  (exportIdent, (Gfun (External ((EF_external
    (('e'::('x'::('p'::('o'::('r'::('t'::[])))))), { sig_args =
    (val_typ :: []); sig_res = (Some val_typ); sig_cc = cc_default })),
    (Tcons ((Tpointer ((Tstruct (threadInfIdent, noattr)), noattr)), Tnil)),
    (Tpointer (coq_val, { attr_volatile = false; attr_alignas = None })),
    cc_default))))

(** val make_halt :
    AST.ident -> AST.ident -> name M.t -> ((name
    M.t * (AST.ident * (Clight.fundef, coq_type)
    globdef)) * (AST.ident * (Clight.fundef, coq_type) globdef)) nState **)

let make_halt threadInfIdent tinfIdent nenv =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic getName) (fun haltIdent ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic getName) (fun halt_cloIdent ->
      let nenv0 =
        M.set halt_cloIdent (Coq_nNamed
          ('h'::('a'::('l'::('t'::('_'::('c'::('l'::('o'::[])))))))))
          (M.set haltIdent (Coq_nNamed ('h'::('a'::('l'::('t'::[]))))) nenv)
      in
      ret (Obj.magic coq_Monad_state) ((nenv0, (haltIdent, (Gfun (Internal
        { fn_return = Tvoid; fn_callconv = cc_default; fn_params =
        ((tinfIdent, (Tpointer ((Tstruct (threadInfIdent, noattr)),
        noattr))) :: []); fn_vars = []; fn_temps = []; fn_body = (Sreturn
        None) })))), (halt_cloIdent, (Gvar { gvar_info =
        (tarray uval ((fun p->2*p) 1)); gvar_init = ((Init_addrof (haltIdent,
        Ptrofs.zero)) :: ((coq_Init_int 1) :: [])); gvar_readonly = true;
        gvar_volatile = false })))))

(** val make_call :
    AST.ident -> AST.ident -> expr -> AST.ident -> AST.ident -> expr ->
    AST.ident -> AST.ident -> statement **)

let make_call threadInfIdent tinfIdent closExpr fIdent envIdent argsExpr argIdent haltIdent =
  Ssequence ((Ssequence ((Ssequence ((Ssequence ((Ssequence ((Sset (fIdent,
    (Ederef
    ((add (Ecast (closExpr, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (c_int' (Z.of_nat O) coq_val)), coq_val)))),
    (Sset (envIdent, (Ederef
    ((add (Ecast (closExpr, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (c_int' (Z.of_nat (S O)) coq_val)),
    coq_val)))))), (Sassign ((Ederef
    ((add (Ecast (argsExpr, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (c_int' (Z.of_nat O) coq_val)), coq_val)),
    (Etempvar (envIdent, coq_val)))))), (Sassign ((Ederef
    ((add (Ecast (argsExpr, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (c_int' (Z.of_nat (S O)) coq_val)),
    coq_val)), (Evar (haltIdent, coq_val)))))), (Sassign ((Ederef
    ((add (Ecast (argsExpr, (Tpointer (coq_val, { attr_volatile = false;
       attr_alignas = None })))) (c_int' (Z.of_nat (S (S O))) coq_val)),
    coq_val)), (Etempvar (argIdent, coq_val)))))), (Scall (None, (Ecast
    ((Evar (fIdent, (Tfunction ((Tcons ((Tpointer ((Tstruct (threadInfIdent,
    noattr)), noattr)), Tnil)), Tvoid, { cc_vararg = false; cc_unproto =
    false; cc_structret = false })))), (Tpointer ((Tfunction ((Tcons
    ((Tpointer ((Tstruct (threadInfIdent, noattr)), noattr)), Tnil)), Tvoid,
    { cc_vararg = false; cc_unproto = false; cc_structret = false })),
    noattr)))), ((Etempvar (tinfIdent, (Tpointer ((Tstruct (threadInfIdent,
    noattr)), noattr)))) :: []))))

(** val make_n_calls :
    AST.ident -> AST.ident -> nat -> AST.ident -> AST.ident -> AST.ident ->
    expr -> (AST.ident * coq_type) list -> AST.ident -> AST.ident -> statement **)

let rec make_n_calls threadInfIdent tinfIdent n closIdent fIdent envIdent argsExpr argPairs retIdent haltIdent =
  match n with
  | O -> Sskip
  | S n0 ->
    (match n0 with
     | O ->
       (match argPairs with
        | [] -> Sskip
        | p :: _ ->
          let (argIdent, _) = p in
          make_call threadInfIdent tinfIdent (Etempvar (closIdent, (Tpointer
            (coq_val, { attr_volatile = false; attr_alignas = None }))))
            fIdent envIdent argsExpr argIdent haltIdent)
     | S n1 ->
       (match argPairs with
        | [] -> Sskip
        | p :: tl ->
          let (argIdent, _) = p in
          let s =
            make_n_calls threadInfIdent tinfIdent (S n1) closIdent fIdent
              envIdent argsExpr tl retIdent haltIdent
          in
          Ssequence (s, (Ssequence ((Sset (retIdent, (Ederef
          ((add (Ecast (argsExpr, (Tpointer (coq_val, { attr_volatile =
             false; attr_alignas = None }))))
             (c_int' (Z.of_nat (S O)) coq_val)), coq_val)))),
          (make_call threadInfIdent tinfIdent (Etempvar (retIdent, (Tpointer
            (coq_val, { attr_volatile = false; attr_alignas = None }))))
            fIdent envIdent argsExpr argIdent haltIdent))))))

(** val make_call_n_export_b :
    AST.ident -> AST.ident -> AST.ident -> name M.t -> nat -> bool ->
    AST.ident -> (name M.t * (AST.ident * (Clight.fundef, coq_type) globdef))
    nState **)

let make_call_n_export_b argsIdent threadInfIdent tinfIdent nenv n export haltIdent =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic getName) (fun callIdent ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic getName) (fun retIdent ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic getName) (fun clo_ident ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic getName) (fun f_ident ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic getName) (fun env_ident ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (Obj.magic make_argList n nenv) (fun t0 ->
              let tinfo_s = Sifthenelse ((Ebinop (Oeq, (Evar (tinfIdent,
                (Tpointer ((Tstruct (threadInfIdent, noattr)), noattr)))),
                (Ecast ((Econst_int ((Int.repr 0), tint)), (tptr tvoid))),
                tint)), (Scall ((Some tinfIdent), (Evar (make_tinfoIdent,
                (Tfunction (Tnil, (Tpointer ((Tstruct (threadInfIdent,
                noattr)), noattr)), { cc_vararg = false; cc_unproto = false;
                cc_structret = false })))), [])), Sskip)
              in
              let (nenv0, argsL) = t0 in
              let argsS = Efield ((Ederef ((Etempvar (tinfIdent, (Tpointer
                ((Tstruct (threadInfIdent, noattr)), noattr)))), (Tstruct
                (threadInfIdent, noattr)))), argsIdent, (Tpointer (coq_val,
                { attr_volatile = false; attr_alignas = None })))
              in
              let asgn_s =
                make_n_calls threadInfIdent tinfIdent n clo_ident f_ident
                  env_ident argsS (rev argsL) retIdent haltIdent
              in
              let export_s =
                if export
                then Scall ((Some retIdent), (Evar (exportIdent, (Tfunction
                       ((Tcons ((Tpointer ((Tstruct (threadInfIdent,
                       noattr)), noattr)), Tnil)), (Tpointer (coq_val,
                       { attr_volatile = false; attr_alignas = None })),
                       { cc_vararg = false; cc_unproto = false;
                       cc_structret = false })))), ((Etempvar (tinfIdent,
                       (Tpointer ((Tstruct (threadInfIdent, noattr)),
                       noattr)))) :: []))
                else Sset (retIdent, (Ederef
                       ((add (Ecast (argsS, (Tpointer (coq_val,
                          { attr_volatile = false; attr_alignas = None }))))
                          (c_int' (Z.of_nat (S O)) coq_val)), coq_val)))
              in
              let body_s = Ssequence ((Ssequence (tinfo_s, asgn_s)),
                (Ssequence (export_s, (Sreturn (Some (Etempvar (retIdent,
                (Tpointer (coq_val, { attr_volatile = false; attr_alignas =
                None })))))))))
              in
              let callStr =
                append ('c'::('a'::('l'::('l'::('_'::[]))))) (nat2string10 n)
              in
              let callStr0 =
                if export
                then append callStr
                       ('_'::('e'::('x'::('p'::('o'::('r'::('t'::[])))))))
                else callStr
              in
              let nenv1 =
                M.set env_ident (Coq_nNamed ('e'::('n'::('v'::('i'::[])))))
                  (M.set clo_ident (Coq_nNamed
                    ('c'::('l'::('o'::('s'::[])))))
                    (M.set callIdent (Coq_nNamed callStr0)
                      (M.set f_ident (Coq_nNamed ('f'::[]))
                        (M.set retIdent (Coq_nNamed ('r'::('e'::('t'::[]))))
                          nenv0))))
              in
              let params = (clo_ident, coq_val) :: argsL in
              let vars = (f_ident, (Tpointer (coq_val, { attr_volatile =
                false; attr_alignas = None }))) :: ((env_ident, (Tpointer
                (coq_val, { attr_volatile = false; attr_alignas =
                None }))) :: ((retIdent, (Tpointer (coq_val,
                { attr_volatile = false; attr_alignas = None }))) :: []))
              in
              ret (Obj.magic coq_Monad_state) (nenv1, (callIdent, (Gfun
                (Internal { fn_return = (Tpointer (Tvoid, noattr));
                fn_callconv = cc_default; fn_params = params; fn_vars = [];
                fn_temps = vars; fn_body = body_s }))))))))))

(** val tinf_def : AST.ident -> (Clight.fundef, coq_type) globdef **)

let tinf_def threadInfIdent =
  Gvar { gvar_info = (Tpointer ((Tstruct (threadInfIdent, noattr)), noattr));
    gvar_init = ((Init_space ((fun p->2*p) ((fun p->2*p) 1))) :: []);
    gvar_readonly = false; gvar_volatile = false }

(** val make_header :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> cEnv ->
    n_iEnv -> exp -> name M.t -> (name M.t * (AST.ident * (Clight.fundef,
    coq_type) globdef) list) option nState **)

let make_header argsIdent threadInfIdent tinfIdent isptrIdent caseIdent cenv ienv _ nenv =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic make_interface isptrIdent caseIdent cenv (M.elements ienv)
      nenv) (fun l ->
    let (nenv0, inter_l) = l in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic make_halt threadInfIdent tinfIdent nenv0) (fun l0 ->
      let (p, p0) = l0 in
      let (nenv1, halt_f) = p in
      let (halt_cloIdent, halt_clo_def) = p0 in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic make_call_n_export_b argsIdent threadInfIdent tinfIdent
          nenv1 (S O) false halt_cloIdent) (fun l1 ->
        let (nenv2, call_0) = l1 in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic make_call_n_export_b argsIdent threadInfIdent tinfIdent
            nenv2 (S (S O)) false halt_cloIdent) (fun l2 ->
          let (nenv3, call_2) = l2 in
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic make_call_n_export_b argsIdent threadInfIdent
              tinfIdent nenv3 (S O) true halt_cloIdent) (fun l3 ->
            let (nenv4, call_1) = l3 in
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __)
              (Obj.magic make_call_n_export_b argsIdent threadInfIdent
                tinfIdent nenv4 (S (S (S O))) true halt_cloIdent) (fun l4 ->
              let (nenv5, call_3) = l4 in
              ret (Obj.magic coq_Monad_state) (Some (nenv5,
                (halt_f :: ((halt_cloIdent, halt_clo_def) :: ((tinfIdent,
                (tinf_def threadInfIdent)) :: (call_0 :: (call_1 :: (call_2 :: (call_3 :: inter_l)))))))))))))))

(** val compile :
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
    AST.ident -> AST.ident -> exp -> cEnv -> name M.t -> (name
    M.t * Clight.program option) * Clight.program option **)

let compile argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent e cenv nenv =
  let e0 = wrap_in_fun e in
  let fenv = compute_fEnv e0 in
  let ienv = compute_iEnv cenv in
  let p'' =
    make_defs argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent
      threadInfIdent tinfIdent isptrIdent caseIdent e0 fenv cenv ienv nenv
  in
  let n =
    Pos.add
      (max_var e0 ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))))) 1
  in
  let p' = runState p'' n in
  (match fst p' with
   | Some p ->
     let (nenv0, defs) = p in
     let nenv1 =
       add_inf_vars argsIdent allocIdent limitIdent gcIdent mainIdent
         bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent
         isptrIdent (ensure_unique nenv0)
     in
     let forward_defs = make_extern_decls nenv1 defs false in
     let header_pre =
       make_header argsIdent threadInfIdent tinfIdent isptrIdent caseIdent
         cenv ienv e0 nenv1
     in
     let header_p =
       runState header_pre ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         1)))))))))))))))))))
     in
     (match fst header_p with
      | Some p0 ->
        let (nenv2, hdefs) = p0 in
        (((M.set make_tinfoIdent (Coq_nNamed
            ('m'::('a'::('k'::('e'::('_'::('t'::('i'::('n'::('f'::('o'::[])))))))))))
            (M.set exportIdent (Coq_nNamed
              ('e'::('x'::('p'::('o'::('r'::('t'::[]))))))) nenv2)),
        (mk_prog_opt argsIdent allocIdent limitIdent bodyIdent threadInfIdent
          heapInfIdent
          ((body_external_decl bodyIdent threadInfIdent tinfIdent) :: 
          (make_extern_decls nenv2 hdefs true)) mainIdent false)),
        (mk_prog_opt argsIdent allocIdent limitIdent bodyIdent threadInfIdent
          heapInfIdent
          ((make_tinfo_rec threadInfIdent) :: ((export_rec threadInfIdent) :: 
          (app forward_defs (app defs hdefs)))) mainIdent true))
      | None -> ((nenv1, None), None))
   | None -> ((nenv, None), None))

(** val empty_program : AST.ident -> Clight.program **)

let empty_program mainIdent =
  { prog_defs = []; prog_public = []; prog_main = mainIdent; prog_types = [];
    prog_comp_env = PTree.empty }

(** val stripOption : AST.ident -> Clight.program option -> Clight.program **)

let stripOption mainIdent = function
| Some p' -> p'
| None -> empty_program mainIdent

(** val print_Clight_dest_names :
    Clight.program -> (int * name) list -> char list -> unit **)

let print_Clight_dest_names =
  print_Clight_dest_names'

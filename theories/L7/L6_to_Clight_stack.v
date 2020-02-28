Require Import Common.compM.

Require Import Coq.ZArith.ZArith
        Coq.Program.Basics
        Coq.Strings.String
        Coq.Lists.List List_util.

Require Import ExtLib.Structures.Monads
        ExtLib.Data.Monads.OptionMonad
        ExtLib.Data.Monads.StateMonad
        ExtLib.Data.String.

Import MonadNotation ListNotations.
Open Scope monad_scope.

From MetaCoq.Template Require Import BasicAst.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values.


Require Import L6.set_util L6.cps L6.identifiers L6.cps_show L6.state.
Require Import Clightdefs.

(* Axioms that are only realized in ocaml *)
Variable (print_Clight : Clight.program -> unit).
Variable (print_Clight_dest : Clight.program -> String.string -> unit).
Variable (print_Clight_dest_names' : Clight.program -> list (positive * name) -> String.string -> unit).
Variable (print : String.string -> unit).


Section TRANSLATION.

(* Stand-in for arbitrary identifiers *)
Variable (argsIdent : ident).
Variable (allocIdent : ident).
Variable (limitIdent : ident).
Variable (gcIdent : ident).
Variable (mainIdent : ident).
Variable (bodyIdent : ident).
Variable (threadInfIdent : ident).
Variable (tinfIdent : ident).
Variable (heapInfIdent : ident).
Variable (numArgsIdent : ident).
Variable (isptrIdent : ident). (* ident for the is_ptr external function *)
Variable (caseIdent : ident). (* ident for the case variable , TODO: generate that automatically and only when needed *)
Variable (nParam:nat).


Definition show_name (name : BasicAst.name) : string :=
  match name with
  | nAnon => "anon"
  | nNamed d => d
  end.

Definition get_fname f (nenv : name_env) : string := 
  match M.get f nenv with
  | Some name => show_name name
  | None => "Undef"
  end.


Definition maxArgs := 1024%Z.

(* temporary function to get something working *)
(* returns (n-1) :: (n-2) :: ... :: 0 :: nil for a list of size n *)
Fixpoint makeArgList' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList' vs')
  end.

Definition makeArgList (vs : list positive) : list N := rev (makeArgList' vs).


Definition fun_info_env : Type := M.t (positive * fun_tag).

(* Compute a fun_env by looking at the number of arguments functions
   are applied to, assumes that all functions sharing the same tags have the same arity *)
Fixpoint compute_fun_env' (n : nat) (nenv : name_env) (fenv : fun_env)  (e : exp) : fun_env :=
  match n with
  | 0 => fenv
  | S n' =>
    match e with
    | Econstr x t vs e' => compute_fun_env' n' nenv fenv e'
    | Ecase x cs => fold_left (fun p e => compute_fun_env' n' nenv p e) (map snd cs) fenv
    | Eproj x t n v e' => compute_fun_env' n' nenv fenv e'
    | Eletapp x f t vs e' =>
      compute_fun_env' n' nenv (M.set t (N.of_nat (length vs), makeArgList vs) fenv) e'
    | Efun fnd e' =>
      let fenv' := compute_fun_env_fundefs n' nenv fnd fenv in
      compute_fun_env' n' nenv fenv' e'
    | Eapp x t vs => M.set t (N.of_nat (length vs) , makeArgList vs) fenv
    | Eprim x p vs e' => compute_fun_env' n' nenv fenv e'
    | Ehalt x => fenv
    end
  end
with compute_fun_env_fundefs n nenv fnd fenv : fun_env :=
  match n with
  | 0 => fenv
  | S n' =>
    match fnd with
    | Fnil => fenv
    | Fcons f t vs e fnd' =>
      let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
      let fenv'' := compute_fun_env' n' nenv fenv' e in
      compute_fun_env_fundefs n' nenv fnd' fenv''
    end
  end.


Fixpoint max_depth (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => S (max_depth e')
  | Ecase x cs => S (fold_left Nat.max (map (compose max_depth snd) cs) (S 0))
  | Eproj x t n v e' => S (max_depth e')
  | Eletapp x f t ys e' => S (max_depth e')
  | Efun fnd e' => S (Nat.max (max_depth_fundefs fnd) (max_depth e'))
  | Eapp x t vs => 1
  | Eprim x p vs e' => S (max_depth e')
  | Ehalt x => 1
  end
with max_depth_fundefs fnd :=
  match fnd with
  | Fnil => S 0
  | Fcons _ _ _ e fnd' => S (Nat.max (max_depth e) (max_depth_fundefs fnd'))
  end.

(* OS: this only computes fenv for known function. *)
Fixpoint compute_fun_env_fds fnd fenv:=
  match fnd with
  | Fnil => fenv
  | Fcons f t vs e fnd' =>
    let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
    compute_fun_env_fds fnd' fenv'
  end.

(* fun_env maps tags to function info  *)

(* fun_env maps tags to function info *)
Definition compute_fun_env (nenv : name_env) (e : exp) : fun_env :=
  compute_fun_env' (max_depth e) nenv (M.empty fun_ty_info) e.   

Fixpoint get_allocs (e : exp) : list positive :=
  match e with
  | Econstr x t vs e' => x :: (get_allocs e')
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => nil
       | cons (z, e') cs' => (get_allocs e' ++ helper cs')%list
       end) cs
  | Eproj x t n v e' => x :: (get_allocs e')
  | Eletapp x f t xs e' => x :: (get_allocs e')
  | Efun fnd e' => (get_allocs_fundefs fnd) ++ (get_allocs e')
  | Eapp x t vs => nil (* stores into args, not alloc new vars *)
  | Eprim x p vs e' => x :: (get_allocs e')
  | Ehalt x => nil
  end
with get_allocs_fundefs (fnd : fundefs) :=
       match fnd with
       | Fnil => nil
       | Fcons f t vs e fnd' => vs ++ (get_allocs e) ++ (get_allocs_fundefs fnd')
       end.

(* Max number of value-sized words allocated by the translation of expression e until the next function call
  For constructor: 1 word per argument + 1 for header if boxed (more than 1 param), otherwise 0 (since enum) *)
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    | nil => max_allocs e'
    | _ => S (max_allocs e' + length vs)
    end
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_allocs e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => 0
  | Efun fnd e' => max (max_allocs_fundefs fnd) (max_allocs e')
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
  end
with max_allocs_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => 0
  | Fcons f t vs e fnd' => max ((length vs) + (max_allocs e))
                              (max_allocs_fundefs fnd')
  end.

(* Compute the max number of parameters a function has in the term exp  *)
Fixpoint max_args (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => max_args e'
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_args e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_args e'
  | Eletapp x f n xs e' => max_args e'
  | Efun fnd e' => max (max_args_fundefs fnd) (max_args e')
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_args e'
  | Ehalt x => 2
  end
with max_args_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => 0
  | Fcons f t vs e fnd' => max (max (length vs) (max_args e))
                               (max_allocs_fundefs fnd')
  end.

(* Compute the max live roots of a expression/fundefs  *)
(* Will be the size of the stack frame array *)
Fixpoint max_live_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => 0
  | Fcons f t vs e fnd' => max (length vs + length (get_allocs e)) (* local vars + args for a function *)
                              (max_live_fundefs fnd')
  end.

(* named ienv *)
(* TODO: move this to cps and replace the current definition of ind_ty_info *)
(* 1) name of inductive type
   2) list containing
      2.1 name of the constructor
      2.2 tag of the contructor (in ctor_env)
      2.3 arity of the constructor
      2.4 ordinal of the constructor *)
Definition n_ind_ty_info : Type := BasicAst.name * list (BasicAst.name * ctor_tag * N * N).

Definition n_ind_env := M.t n_ind_ty_info.

Definition update_ind_env (ienv : n_ind_env) (p : positive) (cInf : ctor_ty_info) : n_ind_env :=
  let '{| ctor_name := name
        ; ctor_ind_name := nameTy
        ; ctor_ind_tag := t
        ; ctor_arity := arity
        ; ctor_ordinal := ord
        |} := cInf in
  match (M.get t ienv) with
  | None => M.set t (nameTy, ((name, p, arity, ord) :: nil)) ienv
  | Some (nameTy, iInf) => M.set t (nameTy, (name, p, arity, ord) :: iInf) ienv
  end.

Definition compute_ind_env (cenv : ctor_env) : n_ind_env :=
  M.fold update_ind_env cenv (M.empty _).


Inductive ctor_rep : Type :=
| enum : N -> ctor_rep
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| boxed : N -> N -> ctor_rep.
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)


Definition make_ctor_rep (cenv : ctor_env) (ct : ctor_tag) : error ctor_rep :=
  match M.get ct cenv with
  | Some p =>
    if ((ctor_arity p) =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p))
  | None => Err "make_ctor_rep: unknown constructor"
  end.

Notation threadStructInf := (Tstruct threadInfIdent noattr).
Notation threadInf := (Tpointer threadStructInf noattr).


Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                          {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                           {| attr_volatile := false; attr_alignas := None |}).


Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
(* NOTE for val: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition val := if Archi.ptr64 then ulongTy else uintTy.
Definition uval := if Archi.ptr64 then ulongTy else uintTy.
Definition sval := if Archi.ptr64 then longTy else intTy.
Definition val_typ := if Archi.ptr64 then  (AST.Tlong:typ) else (Tany32:typ).
Definition Init_int x := if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
Definition make_vint (z:Z) := if Archi.ptr64 then Vlong (Int64.repr z) else Values.Vint (Int.repr z).
Definition make_cint z t := if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.



(* CHANGE THIS FOR 32-bit or 64-bit mode  *)

(*
Notation val := ulongTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Notation uval := ulongTy.
Notation val_typ := (AST.Tlong:typ).
Notation Init_int x := (Init_int64 (Int64.repr x)).


Notation val := uintTy.
Notation uval := uintTy.
Notation val_typ := (Tany32:typ).
Notation Init_int x := (Init_int32 (Int.repr x)).
*)

Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer val noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := false;
                                 cc_unproto := false;
                                 cc_structret := false |}).


Notation valPtr := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).
Notation valPtrPtr := (Tpointer valPtr {| attr_volatile := false; attr_alignas := None |}).

Notation argvTy :=
  (Tpointer valPtr {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Fixpoint mkFunTyList (n : nat) : typelist :=
  match n with
  | 0 => Tnil
  | S n' => Tcons val (mkFunTyList n')
  end.

Definition mkFunTy (n : nat) :=
  (Tfunction (Tcons threadInf (mkFunTyList n)) Tvoid
             {|
               cc_vararg := false;
               cc_unproto := false;
               cc_structret := false |}).

Notation make_tinfoTy :=
  (Tfunction Tnil threadInf {|cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation exportTy :=
  (Tfunction (Tcons threadInf Tnil) valPtr {|cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).


Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).
Notation "'ptrptrVar' x" := (Etempvar x valPtrPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Notation allocPtr := (Etempvar allocIdent valPtr).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).

(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinf := (Etempvar tinfIdent threadInf).
Notation tinfd := (Ederef tinf threadStructInf).


Notation heapInf := (Tstruct heapInfIdent noattr).

Definition add (a b : expr) := Ebinop Oadd a b valPtr.
Notation " a '+'' b " := (add a b) (at level 30).

Definition sub (a b: expr) := Ebinop Osub a b valPtr.
Notation " a '-'' b " := (sub a b) (at level 30).

Definition int_eq (a b : expr) := Ebinop Oeq a b type_bool.
Notation " a '='' b " := (int_eq a b) (at level 35).

Definition not (a : expr) := Eunop Onotbool a type_bool.
Notation "'!' a " := (not a) (at level 40).

Notation seq := Ssequence.

Notation " p ';' q " := (seq p q)
                         (at level 100, format " p ';' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).

Definition c_int' n t := if Archi.ptr64 then Econst_long (Int64.repr n) t else Econst_int (Int.repr n%Z) t.

Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).



(* Shadow stack vars *)

(* Stack-related ids *)
Variable (stackframeTIdent : ident). (* the stack_frame type *)
Variable (frameIdent : ident). (* the stack frame of the current function *)
Variable (rootIdent : ident). (* live roots array *)
Variable (spIdent : ident). (* stack pointer *)
Variable (fpIdent : ident). (* frame pointer *)
(* Fields of stack_frame struct *)
Variable (nextFld : ident).
Variable (rootFld : ident).
Variable (prevFld : ident).

(* The type of the stack_frame struct *)
Definition stackframeT := Tstruct stackframeTIdent noattr.
(* The type of a pointer the stack_frame struct *)
Definition stackframeTPtr := Tpointer stackframeT noattr.
(* The type of the root array for each frame. *)
Definition rootT size := Tarray valPtr size noattr.

Definition rootTPtr := valPtrPtr.

(* local vars declared when a function uses the stack *)
(* struct stack_frame frame; val roots[MAX_LOCS]; val* sp; *)
Definition stack_decl size : list (ident * type)  :=
  (frameIdent, stackframeT) :: (* local variable for local stack frame *)
  (rootIdent, rootT size) :: (* local variable for the live array *)
  (spIdent, valPtrPtr) :: nil. (* local variable for the stack pointer *)


Definition init_stack : statement :=
  (* frame.next = roots; *)
  (Efield (Evar frameIdent stackframeT) nextFld valPtrPtr :::= Evar rootIdent rootTPtr);
  (* frame.roots = roots; *)
  (Efield (Evar frameIdent stackframeT) rootFld rootTPtr :::= Evar rootIdent rootTPtr);
  (* frame.prev = tinf->fp; *)
  (Efield (Evar frameIdent stackframeT) prevFld stackframeTPtr :::= Efield tinfd fpIdent stackframeTPtr);
  (* sp = roots; *)
  (spIdent ::= Evar rootIdent rootTPtr);
  (* tinfo->fp = &frame; *)
  (Efield tinfd fpIdent stackframeTPtr :::= Eaddrof (Evar frameIdent stackframeT) stackframeTPtr).

(* update the stack pointer of the stack before a call *)
Definition update_stack : statement :=
  (* frame.next = sp *)
  (Efield (Evar frameIdent stackframeT) nextFld valPtr :::= Evar spIdent valPtr).

(*reset the stack pointer after a call  *)
Definition reset_stack : statement :=
  (* sp = roots; *)
  (spIdent ::= Evar rootIdent rootTPtr).

Definition push_var (x : positive) :=
  (* */(unsigned long long **/) next = x  ;*)  
  Ederef (Evar spIdent valPtrPtr) valPtr :::= Eaddrof (var x) valPtr;
  (* (Field(ptrptrVar spIdent,Z.of_nat 0) :::= Eaddrof (var x) valPtr); *)
  (* sp = sp + 1*)
  (spIdent ::= Ebinop Oadd (ptrptrVar spIdent) (c_int (Z.of_N 1) valPtr) valPtrPtr).

Definition push_live_vars (xs : list positive) : statement * nat :=
  (fix aux xs no : statement * nat:=
     match xs with
     | nil => (Sskip, 0)
     | x :: xs =>
       let (stmt, no') := aux xs no in
       (push_var x; stmt, 1 + no')        
     end) xs 0.

(* Discard the current function frame before a function returns or calls an other function *)
Definition discard_frame (uses_stack : bool): statement :=
  (* tinfo->fp = frame.prev; *)
  if uses_stack then Efield tinfd fpIdent stackframeTPtr :::= Efield (Evar frameIdent stackframeT) prevFld valPtr
  else Sskip.

(* Qs:
   1. Evar vs Etempvar?
*)


(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition makeTagZ (cenv:ctor_env) (ct : ctor_tag) : error Z :=
  p <- make_ctor_rep cenv ct ;;
  match p with
  | enum t => ret ((Z.shiftl (Z.of_N t) 1) + 1)%Z
  | boxed t a => ret ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z
  end.

Definition makeTag (cenv: ctor_env) (ct : ctor_tag) : error expr :=
  t <- makeTagZ cenv ct ;;
  ret (c_int t val).

Definition mkFunVar x (locs : list N) := (Evar x (mkFunTy (length (firstn nParam locs)))).

Definition makeVar (x:positive) (fenv : fun_env) (map :fun_info_env) :=
  match M.get x map with
  | None => var x
  | Some (_ , t) =>
    match M.get t fenv with
    | None => var x
    | Some (_ , locs) => mkFunVar x locs
    end
  end.

(* OS: assignConstructor' without the rev *)
Fixpoint assignConstructorS'  (fenv : fun_env) (map: fun_info_env) (x : positive) (cur:nat) (vs : list positive): statement :=
  match vs with
  | nil => (* shouldn't be reached *)
       Sskip
  | cons v nil =>
    let vv := makeVar v fenv map in
    (Field(var x, Z.of_nat cur) :::= (*[val]*) vv)
  | cons v vs' =>
    let vv := makeVar v fenv map in
    let prog := assignConstructorS' fenv map x (cur+1)  vs'  in
         (* if v is a function name, funVar, otherwise lvar *)
             (Field(var x, Z.of_nat cur) :::= (*[val]*) vv; prog)
  end.


Definition assignConstructorS (cenv:ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map: fun_info_env) (x : positive) (t : ctor_tag) (vs : list positive) :=
  tag <- makeTag cenv t;;
  rep <- make_ctor_rep cenv t ;;
  match rep with
  | enum _ =>
    ret (x ::= tag)
  | boxed _ a =>
    let stm := assignConstructorS' fenv map x 0 vs in
    ret (x ::= [val] (allocPtr +' (c_int Z.one val));
         allocIdent ::= allocPtr +'
         (c_int (Z.of_N (a + 1)) val) ;
         Field(var x, -1) :::= tag; stm)
      end.

(* This is not valid in Clight if x is a Vptr, implementing instead as an external function
Definition isPtr (x : positive) :=
  int_eq
    (Ebinop Oand
            ([val] (var x))
            (c_int 1 val)
            val)
    (c_int 0 val).
 *)

Definition isPtr (retId:positive) (v:positive) :=
  Scall (Some retId) ptr ([val](var v) :: nil).

(* XXX before it was total *)
Definition isBoxed (cenv:ctor_env) (ienv : n_ind_env) (ct : ctor_tag) : error bool :=
  rep <- make_ctor_rep cenv ct ;; 
  match rep with
  | enum t => ret false
  | boxed t a => ret true
  end.

Fixpoint mkCallVars (fenv : fun_env) (map: fun_info_env) (n : nat) (vs : list positive) : error (list expr) :=
  match n , vs with
  | 0 , nil => ret nil
  | S n , cons v vs' =>
    let vv := makeVar v fenv map in
    rest <- mkCallVars fenv map n vs' ;;
    ret (vv :: rest)
  | _ , _ => Err "mkCallVars"
  end.

Definition mkCall (loc : option positive) (fenv : fun_env) (map: fun_info_env) (f : expr) n (vs : list positive) : error statement :=
  v <- (mkCallVars fenv map n (firstn nParam vs)) ;;
  ret (Scall loc f (tinf :: v)).

Fixpoint asgnFunVars' (vs : list positive) (ind : list N) : error statement :=
  match vs with
  | nil =>
    match ind with
    | nil => ret Sskip
    | cons _ _ => Err "asgnFunVars': nill expected"
    end
  | cons v vs' =>
    match ind with
    | nil => Err "asgnFunVars': cons expected"
    | cons i ind' =>
      rest <- asgnFunVars' vs' ind' ;;
      ret  (v ::= args[ Z.of_N i ] ; rest)
    end
  end.

Definition asgnFunVars (vs : list positive) (ind : list N) : error statement :=
  asgnFunVars' (skipn nParam vs) (skipn nParam ind).


Fixpoint asgnAppVars'' (vs : list positive) (ind : list N) (fenv : fun_env) (map : fun_info_env) (name : string) :
  error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | cons v vs' , cons i ind' =>
    let s_iv :=  args[ Z.of_N i ] :::= (makeVar v fenv map) in
    rest <- asgnAppVars'' vs' ind' fenv map name ;;
    ret (rest ; s_iv)
  | _, _ => Err ("asgnAppVars'' " ++ name)%string
  end.

Definition asgnAppVars' (vs : list positive) (ind : list N) (fenv : fun_env) (map : fun_info_env) name :
  error statement := asgnAppVars'' (skipn nParam vs) (skipn nParam ind) fenv map name.

Fixpoint get_ind {A} (Aeq : A -> A -> bool) (l : list A) (a : A) : error nat :=
  match l with
  | nil => Err "get_ind: cons expected"
  | x :: l' =>
    match Aeq a x with
    | true => ret 0
    | false =>
      n <- get_ind Aeq l' a ;;
      ret (S n)
    end
  end.

Fixpoint remove_AppVars (myvs vs : list positive) (myind ind : list N) : error (list positive * list N) :=
  match vs , ind with
  | nil , nil => ret (nil , nil)
  | v :: vs , i :: ind =>
    '(vs' , ind') <- remove_AppVars myvs vs myind ind ;;
     n <- get_ind Pos.eqb myvs v ;;
     match nth_error myind n with
     | Some i' =>
       match N.eqb i i' with
       | true => ret (vs' , ind')
       | false => ret (v :: vs' , i :: ind')
       end
     | None => ret (v :: vs' , i :: ind')
     end
  | _ , _ => Err "remove_AppVars"
  end.

Definition asgnAppVars_fast' (myvs vs : list positive) (myind ind : list N) (fenv : fun_env) (map : fun_info_env) name : error statement :=
  '(vs' , ind') <- remove_AppVars myvs (skipn nParam vs) myind (skipn nParam ind) ;;
  asgnAppVars'' vs' ind' fenv map name.

(* Optional, reduce register pressure *)
Definition asgnAppVars vs ind (fenv : fun_env) (map : fun_info_env) name :=
  s <- asgnAppVars' vs ind fenv map name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s).

Definition asgnAppVars_fast myvs vs myind ind (fenv : fun_env) (map : fun_info_env) name :=
  s <- asgnAppVars_fast' myvs vs myind ind fenv map name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s).

(* GC calls *)
Definition reserve_body (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
    (Scall None gc (arr :: tinf :: nil) ; allocIdent ::= Efield tinfd allocIdent valPtr)
    Sskip.  

Definition reserve (funInf : positive) (l : Z) (vs : list positive) (ind : list N) (fenv : fun_env) (map : fun_info_env) name : error statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  bef <- asgnAppVars'' (firstn nParam vs) (firstn nParam ind) fenv map name ;;
  aft <- asgnFunVars' (firstn nParam vs) (firstn nParam ind) ;;
  ret (Sifthenelse
         (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
         (bef ; Scall None gc (arr :: tinf :: nil) ; allocIdent ::= Efield tinfd allocIdent valPtr ; aft)
         Sskip).

Definition reserve_num (n : nat) (funInf : positive) (l : Z) (stack_vars : list positive) : statement * nat :=
  let (push, slots) := push_live_vars stack_vars in
  let make_gc_stack := push ; update_stack in
  let arr := (Evar funInf (Tarray uval l noattr)) in
  if (n =? 0)%nat then (Sskip, 0) else 
    ((Sifthenelse
        (!(Ebinop Ole (c_int (Z.of_nat n) val) (limitPtr -' allocPtr) type_bool))
        (make_gc_stack;
         Scall None gc (arr :: tinf :: nil) ;
         reset_stack;
         allocIdent ::= Efield tinfd allocIdent valPtr)
        Sskip), slots).

Definition make_case_switch (x:positive) (ls:labeled_statements) (ls': labeled_statements) :=
  (isPtr caseIdent x;
     Sifthenelse
       (bvar caseIdent)
       (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
       (Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
                ls')).


(** * Shadow stack strategy *)
(*

 1. Before the first non-tail call create a local (stored in the stack) array and a frame
    struct with pointer to the array and the previous frame. Modify the stack pointer of
    tinfo to point to the newly created stack frame
 2. Before the last (tail) call or return modify tinfo to point to the previous stack frame

 *)

(* To create the shadow stack:

   long long int live[MAX_live];
   frame_pointer fp = { next = *live; roots=*live; prev:=tinfo->sp}
   long long int *next = fp.next;
   tinfo->sp = *fp 
 *)

(* To push a value to the shadow stack:

   live[NEXT] := x;
   next = next + 1LLU;
*)

(* To discard the current stack:

  tinfo->sp = fp.prev
*)


(* Create a new shadow stack frame *)
(* Definition make_shadow_stack () : statement :=  *)

(* The program returns the translated code and the set of live vars at the next call *)

Definition is_init (stack_vars : option FVSet) :=
  match stack_vars with
  | None => false
  | Some s => true
  end.

Section Translation.

  Context (args_opt : bool).


  Section Body.
    Context (fun_vars : list positive)
            (loc_vars : FVSet) (* The set of local vars including definitions and arguments *)
            (l : N) (locs : list N) (fun_inf : positive)
            (uses_stack : bool) (nenv : M.t BasicAst.name).

(* Returns the statement and the number of stack slots needed *)

Fixpoint translate_body (e : exp) (fenv : fun_env) (cenv:ctor_env) (ienv : n_ind_env) (map : fun_info_env)
         (stack_vars : option FVSet) (slots : nat) : error (statement * nat):=
  match e with
  | Econstr x t vs e' =>
    prog <- assignConstructorS cenv ienv fenv map x t vs ;;
    progn <- translate_body e' fenv cenv ienv map stack_vars slots ;;
    ret ((prog ; (fst progn)), snd progn)
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (ctor_tag * exp)) : error (labeled_statements * labeled_statements * nat) :=
            match l with
            | nil => ret (LSnil, LSnil, slots)
            | cons p l' =>
              progn <- translate_body (snd p) fenv cenv ienv map stack_vars slots ;;
              pn <- makeCases l' ;;
              let (prog, n) := (progn : statement * nat) in
              let '(ls , ls', n') := (pn : labeled_statements * labeled_statements * nat) in
              p <- make_ctor_rep cenv (fst p) ;;
              match p with 
              | boxed t a =>
                let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                (match ls with
                 | LSnil =>
                   ret ((LScons None
                                (Ssequence prog Sbreak)
                                ls), ls', max n n')
                 | LScons _ _ _ =>
                   ret ((LScons (Some (Z.land tag 255))
                                (Ssequence prog Sbreak)
                                ls), ls', max n n')
                 end)
              | enum t =>
                let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                (match ls' with
                 | LSnil =>
                   ret (ls, (LScons None
                                    (Ssequence prog Sbreak)
                                    ls'), max n n')
                 | LScons _ _ _ =>
                   ret (ls, (LScons (Some (Z.shiftr tag 1))
                                    (Ssequence prog Sbreak)
                                    ls'), max n n')
                 end)
              end
         end) cs) ;;
      let '(ls , ls', slots') := p in
      ret ((make_case_switch x ls ls'), slots')
  | Eletapp x f t vs e' => 
    (* find local live vars *)
    let fvs_post_call := PS.inter (exp_fv e') loc_vars in
    let fvs := PS.remove x fvs_post_call in
    let fvs_list := PS.elements fvs in
    let fv_gc := if PS.mem x fvs_post_call then cons x nil else nil in
    (* push live vars to the stack. We're pushing exactly the vars that are live beyond the current point. *)
    let '(make_stack, stack_vars', slots_call) :=
        match stack_vars with
        | Some _ =>
          let (push, slots) := push_live_vars fvs_list in
          (push ; update_stack, Some fvs, slots)
        | Option =>
          let (push, slots) := push_live_vars fvs_list in
          (init_stack; push; update_stack, Some fvs, slots)
        end
    in
    match M.get t fenv with 
    | Some inf =>
      let name :=
          match M.get f nenv with
          | Some n => show_name n
          | None => "not an entry"
          end
      in
      asgn <- (if args_opt then asgnAppVars_fast fun_vars vs locs (snd inf) fenv map name
               else asgnAppVars vs (snd inf) fenv map name) ;;
      let vv :=  makeVar f fenv map in
      let pnum := min (N.to_nat (fst inf)) nParam in
      c <- (mkCall None fenv map ([Tpointer (mkFunTy pnum) noattr] vv) pnum vs) ;;
      let alloc := max_allocs e' in
      (* Call GC after the call if needed *)
      let (gc_call, slots_gc) := reserve_num alloc fun_inf (Z.of_N (l + 2)) fv_gc in
      progn <- translate_body e' fenv cenv ienv map stack_vars' (max slots (slots_call + slots_gc));;
      ret ((asgn ; Efield tinfd allocIdent valPtr :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
           make_stack;
           c;
           allocIdent ::= Efield tinfd allocIdent valPtr; limitIdent ::= Efield tinfd limitIdent valPtr;
           x ::= Field(args, Z.of_nat 1);
           gc_call;
           reset_stack; (* SP point to the beginning of the current frame *)
           fst progn),
           snd progn)
    | None => Err "translate_body: Unknown function application in Eletapp"
    end
  | Eproj x t n v e' =>
    progn <- translate_body e' fenv cenv ienv map stack_vars slots ;;
    ret ((x ::= Field(var v, Z.of_N n) ; fst progn), snd progn)
  | Efun fnd e => Err "translate_body: Nested function detected"
  | Eapp x t vs =>
    match M.get t fenv with
    | Some inf =>
      let name :=
          match M.get x nenv with
          | Some n => show_name n
          | None => "not an entry"
          end
      in
      asgn <- (if args_opt then asgnAppVars_fast fun_vars vs locs (snd inf) fenv map name else asgnAppVars vs (snd inf) fenv map name) ;;
      let vv := makeVar x fenv map in
      let pnum := min (N.to_nat (fst inf)) nParam in
      c <- (mkCall None fenv map ([Tpointer (mkFunTy pnum) noattr] vv) pnum vs) ;;
      (* IN the args opt version used to be : *)
      (* c <- (mkCall None fenv map ([mkFunTy pnum] vv) pnum vs) ;; *)
      ret ((asgn ; Efield tinfd allocIdent valPtr  :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
            discard_frame (uses_stack && is_init stack_vars); c), slots)
    | None => Err "translate_body: Unknown function application in Eapp"
    end
  | Eprim x p vs e => Err "translate_body: Primitives not supported"
  | Ehalt x =>
    (* set args[1] to x  and return *)
    ret ((args[ Z.of_nat 1 ] :::= (makeVar x fenv map));
           Efield tinfd allocIdent valPtr :::= allocPtr; Efield tinfd limitIdent valPtr :::= limitPtr;
           discard_frame (uses_stack && is_init stack_vars), slots)
    end.

End Body.

Definition mkFun
           (uses_stack : bool) (MAX_LIVE : Z)
           (vs : list positive) (* args *)
           (loc : list positive) (* local vars *)
           (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             ((tinfIdent , threadInf) :: (map (fun x => (x , val)) (firstn nParam vs)))
             ((map (fun x => (x , val)) ((skipn nParam vs) ++ loc)) ++ (if uses_stack then stack_decl MAX_LIVE else nil) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, boolTy) :: nil)
             nil
             body.

Fixpoint uses_stack (e : exp) : bool :=
  match e with
  | Econstr _ _ _ e => uses_stack e
  | Ecase x pats =>
    (fix aux l :=
       match l with
       | nil => false 
       | (c, e) :: xs =>
         (uses_stack e || aux xs)%bool
       end) pats
  | Eproj _ _ _ _ e => uses_stack e
  | Eletapp _ _ _ _ _ => true
  | Efun _ e => uses_stack e
  | Eapp _ _ _ => false
  | Eprim _ _ _  e => uses_stack e
  | Ehalt _ => false
  end.


Fixpoint translate_fundefs (fnd : fundefs) (fenv : fun_env) (cenv: ctor_env) (ienv : n_ind_env) (map : fun_info_env) nenv :
  error (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    rest <- translate_fundefs fnd' fenv cenv ienv map nenv ;;
    match M.get t fenv with
    | None => Err "translate_fundefs: Unknown function tag"
    | Some inf =>
      let '(l, locs) := inf in
      asgn <- asgnFunVars vs locs ;;
      match M.get f map with
      | None => Err "translate_fundefs: Unknown function"
      | Some gcArrIdent =>
        let name :=
            match M.get f nenv with
            | Some n => show_name n
            | None => "not an entry"
            end
        in
        res <- reserve (fst gcArrIdent) (Z.of_N (l + 2)) vs locs fenv map (name ++ " reserve");;
        let uses_stack := uses_stack e in
        let loc_vars := get_allocs e in
        let loc_ids := union_list (union_list PS.empty vs) loc_vars  in
        '(body, MAX_LOCS) <- translate_body vs loc_ids l locs (fst gcArrIdent) uses_stack nenv e fenv cenv ienv map None 0 ;;
        ret ((f , Gfun (Internal
                          (mkFun uses_stack (Z.of_nat MAX_LOCS) vs loc_vars
                                 ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                                   limitIdent ::= Efield tinfd limitIdent valPtr ;
                                   argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                   res) ;
                                   asgn ;
                                   body)))) :: rest)
      end
    end
  end.

Definition make_extern_decl (nenv:M.t BasicAst.name) (def:(positive * globdef Clight.fundef type)) (gv:bool)
  : option (positive * globdef Clight.fundef type) :=
  match def with
  | (fIdent, Gfun (Internal f)) =>
    (match M.get fIdent nenv with
     | Some (nNamed f_string) =>
       Some (fIdent, Gfun (External (EF_external f_string (signature_of_type (type_of_params (fn_params f)) (fn_return f) (fn_callconv f))) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f)))
     | _ => None
     end)
  | (vIdent, Gvar (mkglobvar v_info v_init v_r v_v)) =>
    if gv then 
      Some (vIdent, Gvar (mkglobvar v_info nil v_r v_v))
    else None
  | _ => None
  end.


Fixpoint make_extern_decls (nenv:name_env) (defs:list (positive * globdef Clight.fundef type)) (gv:bool) : list (positive * globdef Clight.fundef type) :=
  match defs with
  | fdefs::defs' =>
    let decls := make_extern_decls nenv defs' gv in
    match make_extern_decl nenv fdefs gv with
    | Some decl => decl :: decls
    | None => decls
    end
  | nil => nil
  end.

Definition body_external_decl : (positive * globdef Clight.fundef type) :=
  let params := (type_of_params ((tinfIdent, threadInf):: nil)) in
  (bodyIdent, Gfun (External (EF_external ("body"%string) (signature_of_type  params Tvoid cc_default)) params Tvoid cc_default)).

End Translation.

(* TODO move *)

Definition lift_error {A : Type} (o : option A) (s : string) : error A :=
  match o with
  | Some a => ret a
  | None => Err s
  end.

Fixpoint translate_funs (args_opt : bool) (e : exp) (fenv : fun_env) (cenv: ctor_env) (ienv : n_ind_env) (m : fun_info_env) nenv :
  error (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e =>                      (* currently assuming e is body *)
    let localVars := get_allocs e in (* ADD ALLOC ETC>>> HERE *)
    let MAX_LOCS := Z.of_nat (max (max_live_fundefs fnd) (length localVars)) in (* maximum number of live vars per functions *)
    funs <- translate_fundefs args_opt fnd fenv cenv ienv m nenv ;;
    '(gcArrIdent , _) <- lift_error (M.get mainIdent m) "translate_funs: Couldn't find main ident" ;;
    let gc_call := reserve_body gcArrIdent 2%Z in
    let uses_stack := uses_stack e in
    bodyn <- translate_body args_opt [] (union_list PS.empty localVars) N0 [] gcArrIdent uses_stack nenv e fenv cenv ienv m None 0 ;;
    let (body, slots) := (bodyn : statement * nat) in
    ret ((bodyIdent , Gfun (Internal
                              (mkfunction Tvoid
                                          cc_default
                                          ((tinfIdent, threadInf)::nil)
                                          ((map (fun x => (x , val)) localVars) ++ (if uses_stack then stack_decl (Z.of_nat slots) else nil) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::nil)
                                          nil
                                          (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                           limitIdent ::= Efield tinfd limitIdent valPtr ;
                                           argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                           gc_call;
                                           body))))
           :: funs)
  | _ => Err "Translate_funs: Missing toplevel function block"
  end.

Definition nState := @compM' positive.

Definition getName : nState positive :=
  '(cd, n) <- compM.get ;;
  compM.put (cd, n+1)%positive ;;
  ret n.

Fixpoint make_ind_array (l : list N) : list init_data :=
  match l with
  | nil => nil
  | n :: l' => (Init_int (Z.of_N n)) :: (make_ind_array l')
  end.

(* representation of pos as string *)
Fixpoint pos2string' p s :=
  match p with
  | xI p' => pos2string' p' (String "1" s)
  | xO p' => pos2string' p' (String "0" s)
  | xH => String "1" s
  end.

Definition pos2string p :=
 pos2string' p "".

(* Currently showing positive as decimal numbers *)
(* Definition show_pos x :=  pos2string x. (*nat2string10 (Pos.to_nat x). *) *)

Definition update_name_env_fun_info (f f_inf : positive) (nenv : name_env) : name_env :=
  match M.get f nenv with
  | None => M.set f_inf (nNamed (append (show_pos f) "_info")) nenv
  | Some n => match n with
              | nAnon => M.set f_inf (nNamed (append (append "x" (show_pos f)) "_info")) nenv
              | nNamed s => M.set f_inf (nNamed (append s "_info")) nenv
              end
  end.

(* see runtime for description and uses of fundef_info.
  In summary,
  fi[0] = number of words that can be allocated by function
  fi[1] = number of live roots at startof function
  rest = indices of live roots in args array
*)

Fixpoint make_fundef_info (fnd : fundefs) (fenv : fun_env) (nenv : name_env)
  : nState (list (positive * globdef Clight.fundef type) * fun_info_env * name_env) :=
  match fnd with
  | Fnil => ret (nil, M.empty (positive * fun_tag), nenv)
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => failwith "make_fundef_info: Unknown tag"
    | Some inf =>
      let '(n, l) := inf in
      rest <- make_fundef_info fnd' fenv nenv ;;
      let '(defs, map, nenv') := rest in
      info_name <- getName ;;
      let len := Z.of_nat (length l) in
      (* it should be the case that n (computed arity from tag) = len (actual arity) *)
      let ind :=
          mkglobvar
            (Tarray uval
                    (len + 2%Z)
                    noattr)
            ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int len) :: (make_ind_array l)) true false in
      ret ((info_name , Gvar ind) :: defs,
           M.set x (info_name , t) map,
           update_name_env_fun_info x info_name nenv')
    end
  end.
    


Fixpoint add_bodyinfo (e : exp) (fenv : fun_env) (nenv : name_env) (map: fun_info_env) (defs:list (positive * globdef Clight.fundef type)) :=
  info_name <- getName ;;
  let ind :=
      mkglobvar
        (Tarray uval
                2%Z
                noattr)
        ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int 0%Z) :: nil) true false in
  ret ((info_name , Gvar ind) :: defs,
       M.set mainIdent (info_name , 1%positive) map,
       M.set info_name (nNamed "body_info"%string) nenv).


(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Fixpoint make_funinfo (e : exp) (fenv : fun_env) (nenv : name_env)
  : nState (list (positive * globdef Clight.fundef type) * fun_info_env * name_env) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv;;
    let '(defs, map, nenv') := p in
    add_bodyinfo e' fenv nenv' map defs
  | _ => failwith "make_funinfo: Function block expected"
  end.


Definition global_defs (e : exp)
  : list (positive * globdef Clight.fundef type) :=
(*  let maxArgs := (Z.of_nat (max_args e)) in
  (allocIdent, Gvar (mkglobvar valPtr ((Init_int(Int.zero)) :: nil) false false))
    :: (limitIdent , Gvar (mkglobvar valPtr  ((Init_int(Int.zero)) :: nil) false false))
    :: (argsIdent , Gvar (mkglobvar (Tarray val maxArgs noattr)
                                    ((Init_int(Int.zero)) :: nil)
                                    false false))
    :: *)
    (gcIdent , Gfun (External (EF_external "gc"
                                              (mksignature (val_typ :: nil) None cc_default))
                                 (Tcons (Tpointer val noattr) (Tcons threadInf Tnil))
                                 Tvoid
                                 cc_default
    ))::
      (isptrIdent , Gfun (External (EF_external "is_ptr"
                                             (mksignature (val_typ :: nil) None cc_default))
                                (Tcons val Tnil) (Tint IBool Unsigned noattr)
                                cc_default
      ))
    :: nil.

Definition make_defs (args_opt : bool) (e : exp) (fenv : fun_env) (cenv: ctor_env) (ienv : n_ind_env) (nenv : name_env) :
  nState (name_env * (list (positive * globdef Clight.fundef type))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
  let '(fun_inf, map, nenv') := fun_inf' in
  match translate_funs args_opt e fenv cenv ienv map nenv with
  | Err s => failwith s
  | Ret fun_defs' =>
    let fun_defs := rev fun_defs' in
    ret (nenv', (global_defs e ++ fun_inf ++ fun_defs)%list)
  end.

Definition composites : list composite_definition :=
  Composite stackframeTIdent Struct
            ((nextFld, valPtrPtr) ::
             (rootFld, valPtrPtr) ::
             (prevFld, (tptr stackframeT)) :: nil)
            noattr ::
  Composite threadInfIdent Struct
            ((allocIdent, valPtr) ::
             (limitIdent, valPtr) ::
             (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) ::
             (argsIdent, (Tarray uval maxArgs noattr)) ::
             (fpIdent, (tptr stackframeT)) :: nil)
            noattr ::
   nil.

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) (add_comp:bool): error Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites defs (bodyIdent :: nil) main in
  match res with
  | Error e => Err "mk_prog_opt"
  | OK p => ret p
  end.

(* Wrap program in empty Efun if e.g. fully inlined *)
Definition wrap_in_fun (e:exp) :=
  match e with
  | Efun fds e' =>
    e
  | _ => Efun Fnil e
  end.

Definition inf_vars :=
  (isptrIdent, (nNamed "is_ptr"%string)) ::
  (argsIdent, (nNamed "args"%string)) ::
  (allocIdent, (nNamed "alloc"%string)) ::
  (limitIdent, (nNamed "limit"%string)) ::
  (gcIdent, (nNamed "garbage_collect"%string)) ::
  (mainIdent, (nNamed "main"%string)) ::
  (bodyIdent, (nNamed "body"%string)) ::
  (threadInfIdent, (nNamed "thread_info"%string)) ::
  (tinfIdent, (nNamed "tinfo"%string)) ::
  (heapInfIdent, (nNamed "heap"%string)) ::
  (caseIdent, (nNamed "arg"%string)) ::
  (numArgsIdent, (nNamed "num_args"%string)) ::
  (stackframeTIdent, (nNamed "stack_frame"%string)) ::
  (frameIdent, nNamed "frame"%string) ::
  (rootIdent, nNamed "roots"%string) ::
  (spIdent, nNamed "sp"%string) ::
  (fpIdent, nNamed "fp"%string) ::
  (nextFld, nNamed "next"%string) ::
  (rootFld, nNamed "root"%string) ::
  (prevFld, nNamed "prev"%string) :: nil.


Definition add_inf_vars (nenv: name_env): name_env :=
  List.fold_left (fun nenv inf => M.set (fst inf) (snd inf) nenv) inf_vars nenv.


Definition ensure_unique : M.t name -> M.t name :=
  fun l => M.map (fun x n =>
                    match n with
                    | nAnon =>  nAnon
                    | nNamed s => nNamed (append s (append "_"%string (show_pos x)))
                  end) l.

Fixpoint make_proj (recExpr:expr) (start:nat) (left:nat): list expr  :=
  match left with
  | 0 => nil
  | S n =>
    let s := make_proj recExpr (S start) n in
    (Field(recExpr, Z.of_nat start))::s
  end.

Fixpoint make_Asgn (les:list expr) (res:list expr) :=
  match les, res with
  | (hl::les), (hr:: res) =>
    Ssequence (Sassign hl hr) (make_Asgn les res)
  | _, _ => Sskip
  end.


Fixpoint make_argList' (n:nat) (nenv:name_env) : nState (name_env * list (ident * type)) :=
  match n with
  | 0 => ret (nenv, nil)
  | (S n') =>
    new_id <- getName;;
           let new_name := append "arg" (nat2string10 n') in
           let nenv := M.set new_id (nNamed new_name) nenv in
           rest <- make_argList' n' nenv;;
                let (nenv, rest_id) := rest in
                ret (nenv, (new_id,val)::rest_id)
  end.

Fixpoint make_argList (n:nat) (nenv:name_env) : nState (name_env * list (ident * type)) :=
  rest <- make_argList' n nenv;;
       let (nenv, rest_l) := rest in
       ret (nenv, rev rest_l).

Fixpoint make_constrAsgn' (argv:ident) (argList:list (ident * type)) (n:nat) :=
  match argList with
  | nil => Sskip
  | (id, ty)::argList' =>
    let s' := make_constrAsgn' argv argList' (S n) in
    (Sassign (Field(var argv, Z.of_nat n)) (Evar id ty) ; s')
  end.

Definition make_constrAsgn (argv:ident) (argList:list (ident * type)) :=
    make_constrAsgn' argv argList 1.

(* Compute the  header file comprising of:
 1 ) Constructors and eliminators for every inductive types in the n_ind_env
 2 ) Direct style calling functions for the original (named) functions
 *)

Fixpoint make_constructors
         (cenv : ctor_env)
         (nTy : BasicAst.ident)
         (ctors : list (BasicAst.name * ctor_tag * N * N))
         (nenv : name_env)
         : nState (name_env * (list (positive * globdef Clight.fundef type))) :=
  let make_name (nTy nCtor : BasicAst.ident) : BasicAst.name :=
    nNamed (append "make_" (append nTy (append "_" nCtor))) in
  match ctors with
  | nil => ret (nenv, nil)
  | (nAnon, tag, 0%N, ord) :: ctors =>
      make_constructors cenv nTy ctors nenv
  | (nAnon, ctag, Npos _ , _) :: ctors =>
      make_constructors cenv nTy ctors nenv
  | (nNamed nCtor, ctag, 0%N, ord) :: ctors => (* unboxed *)
      constr_fun_id <- getName;;
      let constr_body :=
         Sreturn (Some (Econst_int (Int.repr (Z.add (Z.shiftl (Z.of_N ord) 1) 1)) val)) in
      let constr_fun := Internal (mkfunction val cc_default nil nil nil constr_body) in
      let nenv :=
          M.set constr_fun_id (make_name nTy nCtor) nenv in
      (* elet cFun :=  (Internal (mkFun )) *)
      l <- make_constructors cenv nTy ctors nenv ;;
      let (nenv, funs) := l in
      ret (nenv, (constr_fun_id ,(Gfun constr_fun))::funs)
  | (nNamed nCtor, ctag, Npos arr, ord) :: ctors => (* boxed *)
      constr_fun_id <- getName;;
      argvIdent <- getName;;
      argList <- make_argList (Pos.to_nat arr) nenv;;
      let (nenv, argList) := argList in
      let asgn_s := make_constrAsgn argvIdent argList in
      let header := c_int (Z.of_N ((N.shiftl (Npos arr) 10) + ord)) val in
      let constr_body :=
          Ssequence (Sassign (Field(var argvIdent, 0%Z)) header)
                    (Ssequence asgn_s
                       (Sreturn (Some (add (Evar argvIdent argvTy) (c_int 1%Z val))))) in
      let constr_fun := Internal (mkfunction val cc_default
                                                (argList ++ ((argvIdent, argvTy) :: nil))
                                                nil nil constr_body) in
      let nenv :=
          M.set argvIdent (nNamed "argv"%string) (
            M.set constr_fun_id (make_name nTy nCtor) nenv) in
      (* elet cFun :=  (Internal (mkFun )) *)
      l <- make_constructors cenv nTy ctors nenv;;
      let (nenv, funs) := l in
      ret (nenv, (constr_fun_id, Gfun constr_fun) :: funs)
  end.


(* make a function discriminating over the different constructors of an inductive type *)

Notation charPtrTy := (Tpointer tschar noattr).
Notation nameTy    := (Tpointer charPtrTy noattr).
Notation arityTy   := (Tpointer val noattr).

Fixpoint make_elim_Asgn (argv:ident) (valIdent:ident) (arr:nat): statement :=
  let argv_proj := make_proj (var argv) 0%nat arr in
  let val_proj := make_proj (var valIdent) 0%nat arr in
  make_Asgn argv_proj val_proj.

Fixpoint asgn_string_init (s : string) : list init_data :=
  match s with
  | EmptyString => Init_int8 Int.zero :: nil
  | String c s' =>
      let i := Int.repr (Z.of_N (N_of_ascii c)) in
      Init_int8 i :: asgn_string_init s'
  end.

(* create a global variable with a string constant, return its id *)
Definition asgn_string_gv (s : string)
           : nState (ident * globdef Clight.fundef type) :=
  strIdent <- getName;;
  let len := String.length s in
  let init := asgn_string_init s in
  let gv := Gvar (mkglobvar (tarray tschar (Z.of_nat len)) init true false) in
  ret (strIdent, gv).

Definition asgn_string
           (charPtr:ident) (n:name)
           : nState (statement *  list (ident * globdef Clight.fundef type)) :=
  match n with
  | nAnon =>
    ret (Sassign (Field(Etempvar charPtr charPtrTy, 0%Z)) (Econst_int (Int.repr 0%Z) tschar) , nil)
  | nNamed s =>
    nam <- asgn_string_gv  s;;
        let '(i, gv) := nam in
        ret (Sassign (Etempvar charPtr charPtrTy) (Evar i charPtrTy), (i, gv)::nil)
  end.

Definition make_arrGV (arrList:list N): (globdef Clight.fundef type) :=
  Gvar (mkglobvar (tarray tint (Z.of_nat (length arrList)))
                     (List.map (fun n => Init_int (Z.of_N n)) arrList)
                     true
                     false).


Definition pad_char_init (l : list init_data) (n :nat) : list init_data :=
  let m := n - (length l) in
  l ++ List.repeat (Init_int8 Int.zero) m.

Fixpoint make_names_init (nameList : list name) (n : nat) : nat * list init_data :=
  match nameList with
  | nil => (n, nil)
  | nNamed s :: nameList' =>
      let (max_len, init_l) := make_names_init nameList' (max n (String.length s + 1)) in
      let i := pad_char_init (asgn_string_init s) max_len in
      (max_len, i ++ init_l)%list
  | nAnon :: nameList' =>
      let (max_len, init_l) := make_names_init nameList' n in
      let i := pad_char_init (asgn_string_init "") max_len in
      (max_len, i ++ init_l)%list
  end.

Definition make_namesGV (nameList : list name) : globdef Clight.fundef type :=
  let (max_len, init_l) := make_names_init nameList 1 in
  Gvar (mkglobvar (tarray (tarray tschar (Z.of_nat max_len))
                          (Z.of_nat (length nameList)))
                  init_l true false).

Definition make_eliminator
           (cenv : ctor_env)
           (nTy : BasicAst.ident)
           (ctors : list (BasicAst.name * ctor_tag * N * N))
           (nenv : name_env)
           : nState (name_env * (list (ident * globdef Clight.fundef type))) :=
  valIdent <- getName ;;
  ordIdent <- getName ;;
  argvIdent <- getName ;;
  elim_fun_id <- getName ;;
  nameIdent <- getName ;;
  gv_arrIdent <- getName ;;
  gv_namesIdent <- getName ;;
  temp <-
    (fix make_elim_cases
         (ctors : list (BasicAst.name * ctor_tag * N * N))
         (currOrd : nat)
         : nState (labeled_statements * labeled_statements * list name * list N) :=
       match ctors with
       | nil => ret (LSnil, LSnil, nil, nil)
       | (nName, ctag, n, ord) :: ctors =>
           temp <- make_elim_cases ctors (S currOrd) ;;
           let '(ls, ls', nameList, arrList) := temp in
(*           name_p <- asgn_string nameIdent nName;;
           let '(name_s, name_gv) := name_p in *)
           let curr_s :=
               (* Ssequence (* name_s *) Sskip *)
                 (Ssequence
                   (Sassign (Field(var ordIdent, 0%Z)) (c_int (Z.of_nat currOrd) val))
                   (Ssequence (make_elim_Asgn argvIdent valIdent (N.to_nat n))
                               Sbreak)) in
           (match n with
           | 0%N => ret (ls, LScons (Some (Z.of_N ord)) curr_s ls', nName :: nameList,  n::arrList)
           | Npos p => ret (LScons (Some (Z.of_N ord)) curr_s ls, ls', nName :: nameList, n::arrList)
           end)
         end) ctors 0 ;;
  let '(ls, ls', nameList, arrList) := temp in
  let gv_names := make_namesGV nameList in
  let gv_arr :=  make_arrGV arrList in
  let elim_body := (make_case_switch valIdent ls  ls') in
  let elim_fun :=
      Internal (mkfunction
                  Tvoid
                  cc_default
                  ((valIdent, val) :: (ordIdent, valPtr) :: (argvIdent, argvTy) :: nil)
                  ((caseIdent, boolTy) :: nil)
                  nil
                  elim_body) in
  let nenv :=
      set_list ((gv_namesIdent, nNamed (append "names_of_" nTy)) ::
                (gv_arrIdent, nNamed (append "arities_of_" nTy)) ::
                (ordIdent, nNamed "ordinal"%string) ::
                (valIdent, nNamed "val"%string) ::
                (argvIdent, nNamed "argv"%string) ::
                (elim_fun_id, nNamed (append "elim_" nTy)) ::
                nil) nenv in
  ret (nenv, (gv_namesIdent, gv_names) ::
             (gv_arrIdent, gv_arr) ::
             (elim_fun_id, Gfun elim_fun) :: nil).


Fixpoint make_interface
         (cenv : ctor_env)
         (ienv_list : list (positive * n_ind_ty_info))
         (nenv : name_env)
         : nState (name_env * (list (ident * globdef Clight.fundef type))) :=
  match ienv_list with
  | nil => ret (nenv, nil)
  | (_, (nAnon, _)) :: ienv_list' =>
    (* skip anon-types *)
      make_interface cenv ienv_list' nenv
  | (_, (nNamed nTy, lCtr)) :: ienv_list' =>
      l1 <- make_constructors cenv nTy lCtr nenv;;
      let (nenv, def1) := l1 in
      l2 <- make_eliminator cenv nTy lCtr nenv;;
      let (nenv, def2) := l2 in
      l3 <- make_interface cenv ienv_list' nenv;;
      let (nenv, def3) := l3 in
      ret (nenv, (def1 ++ def2 ++ def3))%list
  end.



Definition make_tinfoIdent := 20%positive.
Definition exportIdent := 21%positive.

Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  (make_tinfoIdent,
   Gfun (External (EF_external "make_tinfo"
                               (mksignature (nil) (Some val_typ) cc_default))
                  Tnil
                  threadInf
                  cc_default)).

Definition export_rec : positive * globdef Clight.fundef type :=
  (exportIdent,
   Gfun (External (EF_external "export"
                               (mksignature (cons val_typ nil) (Some val_typ) cc_default))
                  (Tcons threadInf Tnil)
                  valPtr
                  cc_default)).

(* generate a function equivalent to halt, received a tinfo, desired results is already in tinfo.args[1], and
 a halting continuation closure *)
Definition make_halt
           (nenv : name_env)
           : nState (name_env * (ident * globdef Clight.fundef type) * (ident * globdef Clight.fundef type)) :=
  haltIdent <- getName;;
  halt_cloIdent <- getName;;
  let nenv := M.set halt_cloIdent (nNamed "halt_clo"%string) (M.set haltIdent (nNamed "halt"%string) nenv) in
  ret (nenv, (haltIdent, Gfun (Internal (mkfunction Tvoid
                                                    cc_default
                                                    ((tinfIdent, threadInf) :: nil)
                                                    nil
                                                    nil
                                                    (Sreturn None)))),
       (halt_cloIdent, Gvar (mkglobvar  (tarray uval 2) ((Init_addrof haltIdent Ptrofs.zero) ::
                                                                                             Init_int 1 :: nil) true false))).


(* make b? call^n_export; call^n

call_export has n+1 arguments (all values), returns a value:
 a value containing the function closure
 followed by n arguments to the closure

the arguments are placed in args[2]...args[2+n-1]
halt is placed in args[1]
env is placed in args[0]

if b, then export the resulting value

TODO: fix the access to threadInf with Ederef
TODO: make a global threadinfo variable, make_tinfo if NULL, use it otherwise


 *)

Definition make_call
           (closExpr : expr)
           (fIdent : ident)
           (envIdent : ident)
           (argsExpr : expr)
           (argIdent : ident)
           (haltIdent : ident) : statement :=
  (fIdent ::=  (Field(closExpr , Z.of_nat 0));
  envIdent ::= (Field(closExpr, Z.of_nat 1));
  (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar envIdent val));
  (Sassign (Field(argsExpr, Z.of_nat 1)) (Evar haltIdent val));
  (Sassign (Field(argsExpr, Z.of_nat 2)) (Etempvar argIdent val));
  (call ([pfunTy] (funVar fIdent)))).

Fixpoint make_n_calls
         (n : nat)
         (closIdent : ident)
         (fIdent : ident)
         (envIdent : ident)
         (argsExpr : expr)
         (argPairs : list (ident * type))
         (retIdent : ident)
         (haltIdent : ident) : statement :=
  match n, argPairs with
  | S 0, (argIdent, argTy) :: tl =>
    make_call (Etempvar closIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent
  | S (S n), (argIdent, _) :: tl =>
    let s := make_n_calls (S n) closIdent  fIdent envIdent argsExpr tl retIdent haltIdent in
    Ssequence s
      (retIdent ::= (Field(argsExpr, Z.of_nat 1));
       make_call (Etempvar retIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent)
  | _, _ => Sskip
  end.


Definition make_call_n_export_b
           (nenv : name_env)
           (n : nat)
           (export : bool)
           (haltIdent : ident)
           : nState (name_env * (ident * globdef Clight.fundef type)) :=
    callIdent <- getName ;;
    retIdent <- getName ;;
    clo_ident <- getName ;;
    f_ident <- getName ;;
    env_ident <- getName ;;
    t <- make_argList n nenv ;;
    (*    let tinfo_s := if export then (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) else Sskip in *)
    let tinfo_s := Sifthenelse (Ebinop Oeq (Evar tinfIdent threadInf)
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) Sskip in
    let (nenv, argsL) := t in
    let argsS :=  (Efield tinfd argsIdent valPtr) in
    let left_args := make_proj argsS 2 n in
    let asgn_s := make_n_calls n clo_ident f_ident env_ident argsS (rev argsL) retIdent haltIdent in
    let export_s := if export then
                      Scall (Some retIdent) (Evar exportIdent exportTy) (cons tinf nil)
                     else
                       (retIdent ::= (Field(argsS, Z.of_nat 1))) in
    let body_s := Ssequence
                    (tinfo_s; asgn_s)
                    (export_s; Sreturn  (Some (Etempvar retIdent valPtr))) in
    let callStr := append "call_" (nat2string10 n) in
    let callStr := if export then append callStr "_export" else callStr in
    let nenv :=
      set_list ((env_ident, nNamed "envi"%string) ::
                (clo_ident, nNamed "clos"%string) ::
                (callIdent, nNamed callStr) ::
                (f_ident, nNamed "f"%string) ::
                (retIdent, nNamed "ret"%string) ::
                nil) nenv in
    (* if export, tinf is local, otherwise is a param *)
    let params := (clo_ident, val) :: argsL in
    let vars := (f_ident, valPtr) :: (env_ident, valPtr) :: (retIdent, valPtr) :: nil in
    ret (nenv, (callIdent, Gfun (Internal (mkfunction (Tpointer Tvoid noattr)
                                              cc_default params nil vars body_s)))).

Definition tinf_def : globdef Clight.fundef type :=
  Gvar (mkglobvar threadInf ((Init_space 4%Z)::nil) false false).


Definition make_empty_header (cenv:ctor_env) (ienv:n_ind_env) (e:exp) (nenv : M.t BasicAst.name) :
  nState (M.t BasicAst.name  * (list (ident * globdef Clight.fundef type))) :=
  ret (nenv, nil).


Definition make_header (cenv:ctor_env) (ienv:n_ind_env) (e:exp) (nenv : M.t BasicAst.name):  nState (M.t BasicAst.name  * (list (ident * globdef Clight.fundef type))) :=
  '(nenv, inter_l) <- make_interface cenv (M.elements ienv) nenv;;
  '(nenv, halt_f, (halt_cloIdent, halt_clo_def)) <- make_halt nenv;;
  '(nenv, call_0) <- make_call_n_export_b nenv 1 false halt_cloIdent;;
  '(nenv, call_2) <- make_call_n_export_b nenv 2 false halt_cloIdent;;
  '(nenv, call_1) <- make_call_n_export_b nenv 1 true halt_cloIdent;;
  '(nenv, call_3) <- make_call_n_export_b nenv 3 true halt_cloIdent;;
  ret (nenv, (halt_f::(halt_cloIdent, halt_clo_def)::(tinfIdent, tinf_def)::call_0::call_1::call_2::call_3::inter_l))%list.



(* end of header file *)

Section Check.

  Context (fenv : fun_env) (nenv : name_env).

  Fixpoint check_tags' (e : exp) (log : list string) :=
    match e with
    | Econstr _ _ _ e | Eproj _ _ _ _ e | Eprim _ _ _ e => check_tags' e log

    | Ecase _ bs =>
      fold_left (fun a b => check_tags' (snd b) a) bs log

    | Eletapp x f t ys e =>
      let s :=
          match M.get t fenv with
          | Some (n, l) =>
            "LetApp: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++ (nat2string10 (length l))
          | None =>
            "LetApp: Function " ++ get_fname f nenv ++ " was not found in fun_env"
          end
      in check_tags' e (s :: log)

    | Efun B e =>
      let s := check_tags_fundefs' B log in
      check_tags' e s

    | Eapp f t ys =>
      let s :=
          match M.get t fenv with
          | Some (n, l) =>
            "App: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++ (nat2string10 (length l))
          | None =>
            "App: Function " ++ get_fname f nenv ++ " was not found in fun_env"
          end
      in
      s :: log
    | Ehalt x => log
    end
  with check_tags_fundefs' (B : fundefs) (log : list string) : list string :=
         match B with
         | Fcons f t xs e B' =>
           let s :=
               match M.get t fenv with
               | Some (n, l) =>
                 "Definition " ++ get_fname f nenv ++ " has tag " ++ (pos2string t) ++ Pipeline_utils.newline ++
                 "Def: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++ (nat2string10 (length l))
               | None =>
                 "Def: Function " ++ get_fname f nenv ++ " was not found in fun_env"
               end
           in check_tags_fundefs' B' (s :: log)
         | Fnil => log
         end.

  Definition check_tags (e : exp) :=
    String.concat Pipeline_utils.newline (rev (check_tags' e [])).

End Check.


Definition compile (args_opt : bool) (e : exp) (cenv : ctor_env) (nenv0 : name_env) :
  error (M.t BasicAst.name * Clight.program * Clight.program) * string :=
  let e := wrap_in_fun e in
  let fenv := compute_fun_env nenv0 e in
  let ienv := compute_ind_env cenv in
  (* debug *)
  (* let dbg := (cps_show.show_exp nenv0 cenv false e) ++ Pipeline_utils.newline ++ log ++ Pipeline_utils.newline ++ check_tags fenv nenv0 e in *)
  (* end debug *)
  let p'' := make_defs args_opt e fenv cenv ienv nenv0 in
  (* state *)
  let n := ((max_var e 100) + 1)%positive in
  let comp_d := pack_data 1%positive 1%positive  1%positive 1%positive cenv fenv nenv0 [] in (* XXX dummy *)
  (* run compM *)
  let err : error (M.t BasicAst.name * Clight.program * Clight.program) :=
      let '(res, (p, m)) := run_compM p'' comp_d n in
      '(nenv1, defs) <- res ;;
       let nenv := (add_inf_vars (ensure_unique nenv1)) in
       let forward_defs := make_extern_decls nenv defs false in
       let header_pre := make_empty_header cenv ienv e nenv in
       (* let header_p := (header_pre.(runState) m%positive) in *)
       let comp_d := pack_data 1%positive 1%positive  1%positive 1%positive cenv fenv nenv [] in (* XXX dummy *)
       let header_p := run_compM header_pre comp_d 1000000%positive in (* should be m, but m causes collision in nenv for some reason *)
       '(nenv, hdefs) <- fst header_p ;;
        let decls := make_extern_decls nenv hdefs true in
       body <- mk_prog_opt (body_external_decl :: decls) mainIdent false;;
       head <- mk_prog_opt (make_tinfo_rec :: export_rec :: forward_defs ++ defs ++ hdefs)%list mainIdent true ;;
       ret (M.set make_tinfoIdent (nNamed "make_tinfo"%string)
                  (M.set exportIdent (nNamed "export"%string) nenv),
            body, head)
  in
  (err, "").

Definition err {A : Type} (s : String.string) : res A :=
  Error ((MSG s) :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil mainIdent nil eq_refl.

Definition stripOption (p : (option Clight.program)) : Clight.program :=
  match p with
  | None => empty_program
  | Some p' => p'
  end.

(* TODO explanation why this is needed *)
Definition print_Clight_dest_names : Clight.program -> list (positive * name) -> String.string -> unit :=
  fun p s l => print_Clight_dest_names' p s l.

Fixpoint print_err (errs : errmsg) : unit :=
  match errs with
  | nil => tt
  | cons e errs' =>
    match e with
    | MSG s => print s
    | CTX n => print " with context "
    | POS p => print " at position "
    end
  end.

Definition print_err_Clight (p : res Clight.program) : unit :=
  match p with
  | Error e => print_err e
  | OK p' => print_Clight p'
  end.

End TRANSLATION.

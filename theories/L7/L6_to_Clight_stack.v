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

Section TRANSLATION.

(* Stand-in for arbitrary identifiers *)
Variable (argsIdent : ident).
Variable (allocIdent : ident).
Variable (nallocIdent : ident).
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
  | x :: vs' => N.of_nat (length vs') :: makeArgList' vs'
  end.

Definition makeArgList (vs : list positive) : list N := rev (makeArgList' vs).

Definition fun_info_env : Type := M.t (positive * fun_tag).

(* Compute a fun_env by looking at the number of arguments functions
   are applied to, assumes that all functions sharing the same tags have the same arity *)
Fixpoint compute_fun_env' (nenv : name_env) (fenv : fun_env) (e : exp) {struct e} : fun_env :=
  match e with
  | Econstr x t vs e' => compute_fun_env' nenv fenv e'
  | Ecase x cs => fold_left (fun p '(_, e) => compute_fun_env' nenv p e) cs fenv
  | Eproj x t n v e' => compute_fun_env' nenv fenv e'
  | Eletapp x f t vs e' =>
    compute_fun_env' nenv (M.set t (N.of_nat (length vs), makeArgList vs) fenv) e'
  | Efun fnd e' =>
    let fenv' := compute_fun_env_fundefs nenv fnd fenv in
    compute_fun_env' nenv fenv' e'
  | Eapp x t vs => M.set t (N.of_nat (length vs), makeArgList vs) fenv
  | Eprim x p vs e' => compute_fun_env' nenv fenv e'
  | Ehalt x => fenv
  end
with compute_fun_env_fundefs nenv fnd fenv {struct fnd} : fun_env :=
  match fnd with
  | Fnil => fenv
  | Fcons f t vs e fnd' =>
    let fenv' := M.set t (N.of_nat (length vs), makeArgList vs) fenv in
    let fenv'' := compute_fun_env' nenv fenv' e in
    compute_fun_env_fundefs nenv fnd' fenv''
  end.

(* fun_env maps tags to function info (arity + indices in args array) *)
Definition compute_fun_env (nenv : name_env) (e : exp) : fun_env :=
  compute_fun_env' nenv (M.empty fun_ty_info) e.

(* Computes the local variables of a function body *) 
Fixpoint get_locals (e : exp) : list positive :=
  match e with
  | Econstr x t vs e' => x :: get_locals e'
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | [] => []
       | (_, e') :: cs' => (get_locals e' ++ helper cs')%list
       end) cs
  | Eproj x t n v e' => x :: get_locals e'
  | Eletapp x f t xs e' => x :: get_locals e'
  | Efun fnd e' => [] (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => []
  | Eprim x p vs e' => x :: get_locals e'
  | Ehalt x => []
  end.

(* Max number of value-sized words allocated by the translation of expression e until the next function call
   For constructor: 1 word per argument + 1 for header if boxed (more than 1 param), otherwise 0 (since enum) *)
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    | [] => max_allocs e'
    | _ => S (length vs + max_allocs e')
    end
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | [] => 0
       | (z, e') :: cs' => max (max_allocs e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => 0
  | Efun fnd e' => 0 (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
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
  | None => M.set t (nameTy, (name, p, arity, ord) :: nil) ienv
  | Some (nameTy, iInf) => M.set t (nameTy, (name, p, arity, ord) :: iInf) ienv
  end.

Definition compute_ind_env (cenv : ctor_env) : n_ind_env :=
  M.fold update_ind_env cenv (M.empty _).

Inductive ctor_rep : Type :=
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| enum : N -> ctor_rep
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)
| boxed : N -> N -> ctor_rep.

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

Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid cc_default).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer val noattr) (Tcons threadInf Tnil)) Tvoid cc_default).

Notation isptrTy := (Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr) cc_default).

Notation valPtr := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).
Notation valPtrPtr := (Tpointer valPtr {| attr_volatile := false; attr_alignas := None |}).

Notation argvTy := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Fixpoint mkFunTyList (n : nat) : typelist :=
  match n with
  | 0 => Tnil
  | S n' => Tcons val (mkFunTyList n')
  end.

Definition mkFunTy (n : nat) :=
  (Tfunction (Tcons threadInf (mkFunTyList n)) Tvoid cc_default).

Definition mkPrimTy (n : nat) :=
  (Tfunction (mkFunTyList n) val cc_default).

Notation make_tinfoTy :=
  (Tfunction Tnil threadInf cc_default).

Notation exportTy :=
  (Tfunction (Tcons threadInf Tnil) valPtr cc_default).


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

(** * Shadow stack definitions *)

(* Stack-related ids *)
Variable (stackframeTIdent : ident). (* the stack_frame type *)
Variable (frameIdent : ident). (* the stack frame of the current function *)
Variable (rootIdent : ident). (* live roots array *)
Variable (fpIdent : ident). (* frame pointer, part of thread_info *)
(* Fields of stack_frame struct *)
Variable (nextFld : ident).
Variable (rootFld : ident).
Variable (prevFld : ident).

(* The type of the stack_frame struct *)
Definition stackframeT := Tstruct stackframeTIdent noattr.
(* The type of a pointer the stack_frame struct *)
Definition stackframeTPtr := Tpointer stackframeT noattr.
(* The type of the root array for each frame. *)
Definition rootT size := Tarray val size noattr.
(* Pointer to the root array *)
Definition rootTPtr := valPtr.

(* local vars declared when a function uses the stack *)
(* struct stack_frame frame; val roots[MAX_LOCS]; *)
Definition stack_decl size : list (ident * type)  :=
  (frameIdent, stackframeT) :: (* local variable for local stack frame *)
  (rootIdent, rootT size) :: nil. (* local variable for the live array *)

(* Notation for handling the roots array *)
Notation roots := (Etempvar rootIdent valPtr).
Notation "'roots[' n ']'" := ( *(add roots (c_int n%Z val))) (at level 36).

(* Initialize local stack frame. Called before the first function call that uses the current stack *)
Definition init_stack : statement :=
  (* frame.next = roots; *)
  (Efield (Evar frameIdent stackframeT) nextFld valPtr :::= Evar rootIdent rootTPtr);
  (* frame.roots = roots; *)
  (Efield (Evar frameIdent stackframeT) rootFld rootTPtr :::= Evar rootIdent rootTPtr);
  (* frame.prev = tinf->fp; *)
  (Efield (Evar frameIdent stackframeT) prevFld stackframeTPtr :::= Efield tinfd fpIdent stackframeTPtr).


(* Updates the stack pointer and frame pointers before a call *)
(* b is true if the stack is already set. I.e. it's a call to the GC after a normal call *)
Definition set_stack (sp : N) (b : bool) : statement :=
if ((sp =? 0)%N || b)%bool then Sskip else 
  (* tinfo->fp = &frame; *)
  (Efield tinfd fpIdent stackframeTPtr :::= Eaddrof (Evar frameIdent stackframeT) stackframeTPtr).

(* Updates the stack pointer and frame pointers before a call *)
Definition update_stack (sp : N) : statement :=
  if (sp =? 0)%N then Sskip else 
    (* frame.next = root + SP *)
    (Efield (Evar frameIdent stackframeT) nextFld valPtr :::= (add roots (c_int (Z.of_N sp) val))).

(* Resets the frame pointer after a call, so that if subsequent calls don't use the stack the empty frame is not pushed. *)
(* b is true if it's a call to the GC after a normal call, so the stack will be reset anyway *)
Definition reset_stack (sp : N) (b : bool) : statement :=
  if ((sp =? 0)%N || b)%bool then Sskip else 
   (* Current frame points to the old frame again *)
   Efield tinfd fpIdent stackframeTPtr :::= Efield (Evar frameIdent stackframeT) prevFld valPtr.

(* Pushes single var in frame *)
Definition push_var (sp : N) (x : ident) :=
  roots[ Z.of_N sp ] :::= Evar x valPtr.

(* Pops single var from frame *)
Definition pop_var (sp : N) (x : ident) := 
  x ::= roots[ Z.of_N sp ].

Definition push_live_vars_offset (off : N) (xs : list ident) : statement * N :=
  (fix aux xs (n : N) (stmt : statement) : statement * N :=
     match xs with
     | nil => (stmt, n)
     | x :: xs => aux xs (n+1)%N (push_var n x; stmt)
     end) xs off Sskip.

Definition pop_live_vars_offset (off : N) (xs : list ident) : statement :=
  (fix aux xs n stmt : statement :=
     match xs with
     | nil => stmt
     | x :: xs => aux xs (n+1)%N (pop_var n x; stmt)
     end) xs off Sskip.

Definition push_live_vars (xs : list ident) : statement * N := push_live_vars_offset 0%N xs.

Definition pop_live_vars (xs : list ident) : statement := pop_live_vars_offset 0%N xs. 

(** * Shadow stack defs END *)

Section CODEGEN.

Variable (cenv : ctor_env). 
Variable (ienv : n_ind_env). 
(* fun_tag t ↦ (n, [0; ..; n-1]) where n = arity of the function with tag t *)
Variable (fenv : fun_env).
(* function name f ↦ (the name of f's fun_info, f's fun_tag) *)
Variable (fienv : fun_info_env). 

Definition make_ctor_rep (ct : ctor_tag) : error ctor_rep :=
  match M.get ct cenv with
  | Some p =>
    if (ctor_arity p =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p))
  | None => Err ("make_ctor_rep: unknown constructor with tag " ++ show_pos ct)
  end.

(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition makeTagZ (ct : ctor_tag) : error Z :=
  p <- make_ctor_rep ct ;;
  match p with
  | enum t => ret (Z.shiftl (Z.of_N t) 1 + 1)%Z
  | boxed t a => ret (Z.shiftl (Z.of_N a) 10 + Z.of_N t)%Z
  end.

Definition makeTag (ct : ctor_tag) : error expr :=
  t <- makeTagZ ct ;;
  ret (c_int t val).

(* To use variables in Clight expressions, need variable name and its type.
   Variables that refer to functions must have type
     void(struct thread_info *ti, val, ..)
                                  ------- n times
   where n = min(n_param, arity of the function).

   All other variables just have type val. 
*)

(* x is the name of the function,
   locs is the list [0; ..; arity(x) - 1],
   Returns a well-formed Evar node for referring to x. *)
Definition mkFunVar x (locs : list N) := Evar x (mkFunTy (length (firstn nParam locs))).

(* make_var x = Evar x t where t is x's C type *)
Definition makeVar (x : positive) :=
  match M.get x fienv with
  (* if x is a function name with tag t... *)
  | Some (_, t) =>
    match M.get t fenv with
    (* ...and tag t corresponds to a function with arity n, then x has function type *)
    | Some (_, locs) => mkFunVar x locs (* locs = [0; ..; n-1]. TODO: could just use n instead of locs *)
    | None => (* should be unreachable *) var x
    end
  (* otherwise, x is just a regular variable *)
  | None => var x
  end.

(* asgn_constr' x cur vs =
            x[cur] = vs[0];
        x[cur + 1] = vs[1];
                   .
                   .
     x[cur + |vs|] = vs[|vs| - 1] 

   Assumes |vs|>0. *)
Fixpoint assignConstructorS' (x : ident) (cur : nat) (vs : list ident) : statement :=
  match vs with
  | nil => (* shouldn't be reached *) Sskip
  | v :: nil => Field(var x, Z.of_nat cur) :::= (*[val]*) makeVar v
  | cons v vs' =>
    Field(var x, Z.of_nat cur) :::= (*[val]*) makeVar v;
    assignConstructorS' x (cur+1) vs'
  end.

(* asgn_constr x c vs = 
     code to set x to (Constr c vs)
     if boxed (i.e., |vs|>0), x is a heap pointer. *)
Definition assignConstructorS (x : ident) (t : ctor_tag) (vs : list ident) :=
  tag <- makeTag t ;;
  rep <- make_ctor_rep t ;;
  match rep with
  | enum _ => ret (x ::= tag)
  | boxed _ a =>
    ret (x ::= [val] (allocPtr +' c_int Z.one val);
         allocIdent ::= allocPtr +' c_int (Z.of_N (a + 1)) val;
         Field(var x, -1) :::= tag;
         assignConstructorS' x 0 vs)
  end.

(* Zoe: inlining the isPtr function to avoid extra function call in C *)
Definition isPtr (retId : ident) (v : ident) : expr :=
  Ebinop Oeq (Ebinop Oand (Evar v val) (Econst_int Int.one intTy) boolTy)
         (Econst_int Int.zero intTy) boolTy.

(* mk_call_vars n vs = Some (map make_var vs) if n = |vs| else None *)
Fixpoint mkCallVars (n : nat) (vs : list ident) : error (list expr) :=
  match n, vs with
  | 0, nil => ret nil
  | S n, cons v vs' =>
    rest <- mkCallVars n vs' ;;
    ret (makeVar v :: rest)
  | _, _ => Err "mkCallVars: n != |vs|"
  end.

(* mk_call f n vs = Some (f(tinfo, vs..)) if n = min(n_param, |vs|) else None *)
Definition mkCall (loc : option ident) (f : expr) (n : nat) (vs : list ident) : error statement :=
  v <- mkCallVars n (firstn nParam vs) ;;
  ret (Scall loc f (tinf :: v)).

(* mk_prim_call res pr ar vs = Some (res = pr(vs..)) if ar = min(n_param, |vs|) else None *)
Definition mkPrimCall (res : ident) (pr : ident) (ar : nat) (vs : list ident) : error statement :=
  args <- mkCallVars ar vs ;;  
  ret (Scall (Some res) ([mkPrimTy ar] (Evar pr (mkPrimTy ar))) args).

(* Load arguments from the args array.

   asgn_fun_vars' vs ind =
     vs[|ind| - 1] = args[ind[|ind| - 1]];
                   .
                   .
             vs[1] = args[ind[1]];
             vs[0] = args[ind[0]];

   Reads arguments from the args array at indices ind.
   Stores them in local variables vs.
*)
Fixpoint asgnFunVars' (vs : list ident) (ind : list N) : error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | v :: vs', i :: ind' =>
    rest <- asgnFunVars' vs' ind' ;;
    ret (v ::= args[ Z.of_N i ]; rest)
  | _, _ => Err "asgnFunVars': list lengths unequal"
  end.

(* Like asgn_fun_vars' but skip the first n_param arguments. *)
Definition asgnFunVars (vs : list ident) (ind : list N) : error statement :=
  asgnFunVars' (skipn nParam vs) (skipn nParam ind).

(* asgn_app_vars'' vs ind =
            args[ind[0]] = vs[0];
            args[ind[1]] = vs[1];
                         .
                         .
     args[ind[|ind| - 1] = vs[|ind| - 1];

   Reads arguments from local variables vs.
   Stores them in the args array at indices ind.
*)
Fixpoint asgnAppVars'' (vs : list ident) (ind : list N) (name : string) : error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | v :: vs', i :: ind' =>
    rest <- asgnAppVars'' vs' ind' name ;;
    ret (rest; args[ Z.of_N i ] :::= makeVar v)
  | _, _ => Err ("asgnAppVars'' " ++ name)%string
  end.

(* Like asgn_app_vars'', but skip the first n_param arguments. *)
Definition asgnAppVars' (vs : list ident) (ind : list N) (name : string) : error statement :=
  asgnAppVars'' (skipn nParam vs) (skipn nParam ind) name.

Fixpoint index_of {A} (eq : A -> A -> bool) (l : list A) (a : A) : error nat :=
  match l with
  | nil => Err "index_of: element not found"
  | x :: l' =>
    if eq a x then ret 0 else 
    n <- index_of eq l' a ;;
    ret (S n)
  end.

(* remove_app_vars myvs vs myind ind =
     if |vs| = |ind|
     then Some (unzip (zip vs ind \ zip myvs myind))
     else None *)
Fixpoint remove_AppVars (myvs vs : list ident) (myind ind : list N) : error (list ident * list N) :=
  match vs, ind with
  | nil, nil => ret (nil, nil)
  | v :: vs, i :: ind =>
    '(vs', ind') <- remove_AppVars myvs vs myind ind ;;
     n <- index_of Pos.eqb myvs v ;;
     match nth_error myind n with
     | Some i' => if N.eqb i i' then ret (vs', ind') else ret (v :: vs', i :: ind')
     | None => ret (v :: vs', i :: ind')
     end
  | _, _ => Err "remove_AppVars: list lengths unqual"
  end.

(* Like asgn_app_vars'' but ignore variables in myvs/indices in myind *)
Definition asgnAppVars_fast' (myvs vs : list ident) (myind ind : list N) (name : string) : error statement :=
  '(vs', ind') <- remove_AppVars myvs (skipn nParam vs) myind (skipn nParam ind) ;;
  asgnAppVars'' vs' ind' name.

(* To reduce register pressure while loading arguments from the args array,
   instead of emitting
     tinfo->args[..] = ..;
     tinfo->args[..] = ..;
     tinfo->args[..] = ..;
     tinfo->args[..] = ..;
   we'll first cache tinfo->args:
     args = tinfo->args;
     args[..] = ..;
     args[..] = ..;
     args[..] = ..;
     args[..] = ..; 
*)
Definition asgnAppVars vs ind name :=
  s <- asgnAppVars' vs ind name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr); s).

(* Like asgn_app_vars, but ignore variables in myvs/indices in myind *)
Definition asgnAppVars_fast myvs vs myind ind name :=
  s <- asgnAppVars_fast' myvs vs myind ind name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr); s).

Definition set_nalloc (num : expr) : statement :=
  Efield tinfd nallocIdent val :::= num. 

(** * GC call *)
Definition make_GC_call (num_allocs : nat) (stack_vars : list ident) (stack_offset : N) : statement * N :=
  let after_call := negb (stack_offset =? 0)%N in
  let (push, slots) := push_live_vars_offset stack_offset stack_vars in
  let make_gc_stack := push; update_stack slots; set_stack slots after_call in
  let discard_stack := pop_live_vars_offset stack_offset stack_vars; reset_stack slots after_call in
  let nallocs := c_int (Z.of_nat num_allocs) val in 
  if (num_allocs =? 0)%nat then (Sskip, stack_offset) else 
    ((Sifthenelse
        (!(Ebinop Ole nallocs (limitPtr -' allocPtr) type_bool))
        (make_gc_stack;
         set_nalloc nallocs;
         Scall None gc (tinf :: nil);
         discard_stack;
         allocIdent ::= Efield tinfd allocIdent valPtr;
         limitIdent ::= Efield tinfd limitIdent valPtr)
        Sskip), slots).

Definition make_case_switch (x : ident) (ls ls' : labeled_statements) :=
  Sifthenelse
    (isPtr caseIdent x)
    (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
    (Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
             ls').

(** * Shadow stack strategy *)
(* ZOE TODO: update text

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


Section Translation.

  Context (args_opt : bool).

  Section Body.
    Context
      (prim_map : list (kername * string * nat * positive))
      (fun_vars : list ident)
      (loc_vars : FVSet) (* The set of local vars including definitions and arguments *)
      (locs : list N)
      (nenv : M.t BasicAst.name).

    (* Returns the statement and the number of stack slots needed *)

    Fixpoint translate_body (e : exp) (slots : N) : error (statement * N):=
      match e with
      | Econstr x t vs e' =>
        stm_constr <- assignConstructorS x t vs ;;
        '(stm_e, slots) <- translate_body e' slots ;;
        ret ((stm_constr; stm_e), slots)
      | Ecase x cs =>
        '(ls, ls', slots) <-
          (fix makeCases (l : list (ctor_tag * exp)) : error (labeled_statements * labeled_statements * N) :=
             match l with
             | nil => ret (LSnil, LSnil, slots)
             | (c, e) :: l' =>
               '(prog, n) <- translate_body e slots ;;
               '(ls, ls', n') <- makeCases l' ;;
               p <- make_ctor_rep c ;;
               match p with 
               | boxed t a =>
                 match ls with
                 | LSnil => ret (LScons None (Ssequence prog Sbreak) ls, ls', N.max n n')
                 | LScons _ _ _ =>
                   let tag := (Z.shiftl (Z.of_N a) 10 + Z.of_N t)%Z in
                   ret (LScons (Some (Z.land tag 255)) (Ssequence prog Sbreak) ls, ls', N.max n n')
                 end
               | enum t =>
                 match ls' with
                 | LSnil => ret (ls, LScons None (Ssequence prog Sbreak) ls', N.max n n')
                 | LScons _ _ _ =>
                   let tag := (Z.shiftl (Z.of_N t) 1 + 1)%Z in
                   ret (ls, LScons (Some (Z.shiftr tag 1)) (Ssequence prog Sbreak) ls', N.max n n')
                 end
               end
             end) cs ;;
        ret (make_case_switch x ls ls', slots)
      | Eletapp x f t vs e' => 
        (* Compute the local variables that are live after the call  *)
        let fvs_post_call := PS.inter (exp_fv e') loc_vars in
        let fvs := PS.remove x fvs_post_call in
        let fvs_list := PS.elements fvs in
        (* Check if the new binding has to be pushed to the frame during the GC call *)                
        let fv_gc := if PS.mem x fvs_post_call then cons x nil else nil in
        (* push live vars to the stack. We're pushing exactly the vars that are live beyond the current point. *)
        let '(make_stack, slots_call) :=
          let (push, slots) := push_live_vars fvs_list in
          (push; update_stack slots; set_stack slots false, slots)
        in
        let discard_stack := (pop_live_vars fvs_list; reset_stack slots_call false) in
        match M.get t fenv with 
        | Some inf =>
          let name :=
            match M.get f nenv with
            | Some n => show_name n
            | None => "not an entry"
            end
          in
          asgn <- (if args_opt
                  then asgnAppVars_fast fun_vars vs locs (snd inf) name
                  else asgnAppVars vs (snd inf) name) ;;
          let pnum := min (N.to_nat (fst inf)) nParam in
          call_fn <- mkCall None ([Tpointer (mkFunTy pnum) noattr] (makeVar f)) pnum vs ;;
          let alloc := max_allocs e' in
          (* Call GC after the call if needed *)
          let '(gc_call, slots_gc) := make_GC_call alloc fv_gc slots_call in
          '(prog, slots) <- translate_body e' (N.max slots slots_gc);;
          Ret ((asgn;
                Efield tinfd allocIdent valPtr :::= allocPtr;
                Efield tinfd limitIdent valPtr :::= limitPtr;
                make_stack;
                call_fn;
                allocIdent ::= Efield tinfd allocIdent valPtr;
                limitIdent ::= Efield tinfd limitIdent valPtr;
                x ::= Field(args, Z.of_nat 1);
                gc_call;
                discard_stack;
                prog),
               slots)
        | None => Err "translate_body: Unknown function application in Eletapp"
        end
      | Eproj x t n v e' =>
        '(stm_e, slots) <- translate_body e' slots ;;
        Ret ((x ::= Field(var v, Z.of_N n); stm_e), slots)
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
          asgn <- (if args_opt
                  then asgnAppVars_fast fun_vars vs locs (snd inf) name
                  else asgnAppVars vs (snd inf) name) ;;
          let pnum := min (N.to_nat (fst inf)) nParam in
          call_fn <- (mkCall None ([Tpointer (mkFunTy pnum) noattr] (makeVar x)) pnum vs) ;;
          ret ((asgn;
                Efield tinfd allocIdent valPtr :::= allocPtr;
                Efield tinfd limitIdent valPtr :::= limitPtr;
                call_fn),
               slots)
        | None => Err "translate_body: Unknown function application in Eapp"
        end
      | Eprim x p vs e' =>    
        call_prim <- mkPrimCall x p (length vs) vs ;;
        '(stm_e, slots) <- translate_body e' slots ;;
        ret ((call_prim; stm_e), slots)
      | Ehalt x =>
        (* set args[1] to x  and return *)
        ret ((args[ Z.of_nat 1 ] :::= makeVar x;
              Efield tinfd allocIdent valPtr :::= allocPtr;
              Efield tinfd limitIdent valPtr :::= limitPtr),
             slots)
      end.

  End Body.

Definition mkFun
           (root_size : Z) (* size of roots array *)
           (vs : list ident) (* args *)
           (loc : list ident) (* local vars *)
           (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             ((tinfIdent , threadInf) :: (map (fun x => (x , val)) (firstn nParam vs)))
             ((map (fun x => (x , val)) ((skipn nParam vs) ++ loc)) ++ (stack_decl root_size) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, boolTy) :: nil)
             nil
             body.

Fixpoint translate_fundefs (fnd : fundefs) (nenv : name_env) : error (list (ident * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => Ret nil
  | Fcons f t vs e fnd' =>
    rest <- translate_fundefs fnd' nenv ;;
    match M.get t fenv with
    | None => Err "translate_fundefs: Unknown function tag"
    | Some inf =>
      let '(l, locs) := inf in
      asgn <- asgnFunVars vs locs ;; (* project remaining params out of args array *)
      let num_allocs := max_allocs e in
      let loc_vars := get_locals e in
      let var_set := union_list PS.empty vs in
      let loc_ids := union_list var_set loc_vars  in
      let live_vars := PS.elements (PS.inter (exp_fv e) var_set) in 
      let (gc, _) := make_GC_call num_allocs live_vars 0%N in
      '(body, stack_slots) <- translate_body vs loc_ids locs nenv e 0 ;;
      let stack_slots := N.max (N.of_nat (length live_vars)) stack_slots in
      Ret ((f , Gfun (Internal
                      (mkFun (Z.of_N stack_slots) vs loc_vars
                             ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                               limitIdent ::= Efield tinfd limitIdent valPtr ;
                               argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                               asgn ; 
                               init_stack ;
                               gc; 
                               body))))) :: rest)
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

Definition translate_program (args_opt : bool) (e : exp) nenv :
  error (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e => 
    let localVars := get_locals e in
    funs <- translate_fundefs args_opt fnd nenv ;;
    let allocs := max_allocs e in
    let (gc_call, _) := make_GC_call allocs nil (* no live roots to push *) 0%N in
    '(body, slots) <- translate_body args_opt [] (union_list PS.empty localVars) [] nenv e 0 ;;
    let argsExpr := Efield tinfd argsIdent (Tarray uval maxArgs noattr) in
    ret ((bodyIdent , Gfun (Internal
                              (mkfunction val
                                          cc_default
                                          ((tinfIdent, threadInf)::nil)
                                          ((map (fun x => (x , val)) localVars) ++ (stack_decl (Z.of_N slots)) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::nil)
                                          nil
                                          (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                           limitIdent ::= Efield tinfd limitIdent valPtr ;
                                           argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                           init_stack ;
                                           gc_call;
                                           body ;
                                           Sreturn (Some (Field(argsExpr, Z.of_nat 1))))))) :: funs)
  | _ => Err "translate_program: Missing toplevel function block"
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

End CODEGEN.

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
      let '(defs, fienv, nenv') := rest in
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
           M.set x (info_name , t) fienv,
           update_name_env_fun_info x info_name nenv')
    end
  end.

Definition add_bodyinfo (e : exp) (fenv : fun_env) (nenv : name_env) (fienv: fun_info_env) (defs:list (positive * globdef Clight.fundef type)) :=
  info_name <- getName ;;
  let ind :=
      mkglobvar
        (Tarray uval
                2%Z
                noattr)
        ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int 0%Z) :: nil) true false in
  ret ((info_name , Gvar ind) :: defs,
       M.set mainIdent (info_name , 1%positive) fienv,
       M.set info_name (nNamed "body_info"%string) nenv).


(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Definition make_funinfo (e : exp) (fenv : fun_env) (nenv : name_env)
  : nState (list (positive * globdef Clight.fundef type) * fun_info_env * name_env) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv;;
    let '(defs, fienv, nenv') := p in
    add_bodyinfo e' fenv nenv' fienv defs
  | _ => failwith "make_funinfo: Function block expected"
  end.


Definition global_defs (e : exp)
  : list (positive * globdef Clight.fundef type) :=
    (gcIdent , Gfun (External (EF_external "gc"
                                              (mksignature (val_typ :: nil) None cc_default))
                                 (Tcons threadInf Tnil)
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
  let '(fun_inf, fienv, nenv') := fun_inf' in
  match translate_program cenv fenv fienv args_opt e nenv with
  | Err s => failwith s
  | Ret fun_defs' =>
    let fun_defs := rev fun_defs' in
    ret (nenv', (global_defs e ++ fun_inf ++ fun_defs)%list)
  end.

(* Types declared at the begining of the program *)
Definition composites : list composite_definition :=
  Composite stackframeTIdent Struct
            ((nextFld, valPtr) ::
             (rootFld, valPtr) ::
             (prevFld, (tptr stackframeT)) :: nil)
            noattr ::
  Composite threadInfIdent Struct
            ((allocIdent, valPtr) ::
             (limitIdent, valPtr) ::
             (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) ::
             (argsIdent, (Tarray uval maxArgs noattr)) ::
             (fpIdent, (tptr stackframeT)) ::
             (nallocIdent, val) :: nil) (* Zoe : This is the number of allocations until the next GC call so that GC can perform a test. 
                                         * Note that it will be coerced to UL from ULL. That should be safe for the values we're using but 
                                         * consider changing it too. *)
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
  (nallocIdent, (nNamed "nalloc"%string)) ::
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

Definition make_argList (n:nat) (nenv:name_env) : nState (name_env * list (ident * type)) :=
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

Section Check. (* Just for debugging purposes. TODO eventually delete*)

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
                 "Definition " ++ get_fname f nenv ++ " has tag " ++ (show_pos t) ++ Pipeline_utils.newline ++
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
  let comp_d := pack_data 1%positive 1%positive  1%positive 1%positive cenv fenv nenv0 (M.empty nat) [] in (* XXX dummy *)
  (* run compM *)
  let err : error (M.t BasicAst.name * Clight.program * Clight.program) :=
      let '(res, (p, m)) := run_compM p'' comp_d n in
      '(nenv1, defs) <- res ;;
      let nenv := (add_inf_vars (ensure_unique nenv1)) in
      let forward_defs := make_extern_decls nenv defs false in
      body <- mk_prog_opt [body_external_decl] mainIdent false;;
      head <- mk_prog_opt (make_tinfo_rec :: export_rec :: forward_defs ++ defs)%list mainIdent true ;;
      ret (M.set make_tinfoIdent (nNamed "make_tinfo"%string)
                 (M.set exportIdent (nNamed "export"%string) nenv),
           body, head)
  in
  (err, "").

Definition err {A : Type} (s : String.string) : res A :=
  Error (MSG s :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil mainIdent nil eq_refl.

Definition stripOption (p : option Clight.program) : Clight.program :=
  match p with
  | None => empty_program
  | Some p' => p'
  end.

End TRANSLATION.

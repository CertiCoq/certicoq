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
Variable (args_id : ident).
Variable (alloc_id : ident).
Variable (nalloc_id : ident).
Variable (limit_id : ident).
Variable (gc_id : ident).
Variable (main_id : ident).
Variable (body_id : ident).
Variable (thread_info_id : ident).
Variable (tinfo_id : ident).
Variable (heap_info_id : ident).
Variable (num_args_id : ident).
Variable (isptr_id : ident). (* ident for the is_ptr external function *)
Variable (case_id : ident). (* ident for the case variable , TODO: generate that automatically and only when needed *)
Variable (n_param : nat).

Definition show_name (name : BasicAst.name) : string :=
  match name with
  | nAnon => "anon"
  | nNamed d => d
  end.

Definition get_fname f (nenv : name_env) : string := 
  match M.get f nenv with
  | Some name => show_name name
  | None => "not an entry"
  end.

Definition max_args := 1024%Z.

(* temporary function to get something working *)
(* returns (n-1) :: (n-2) :: ... :: 0 :: nil for a list of size n *)
Fixpoint make_arg_list' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => N.of_nat (length vs') :: make_arg_list' vs'
  end.

(* [0; ..; |vs| - 1] *)
Definition make_arg_list (vs : list positive) : list N := rev (make_arg_list' vs).

(* fun_info_env holds mappings f ↦ t where
     f is function name
     t is fun_tag associated with f
*)
Definition fun_info_env : Type := M.t fun_tag.

Definition hoisted_exp := (fundefs * exp)%type.

Definition mk_hoisted_exp (e : exp) : hoisted_exp :=
  match e with
  | Efun fds e => (fds, e)
  | _ => (Fnil, e)
  end.

(* Compute a fun_env by looking at the number of arguments functions
   are applied to, assumes that all functions sharing the same tags have the same arity.

   fun_env holds mappings
     t ↦ (|vs|, [0; ..; |vs| - 1]) 
   for each (Fcons f t vs _ _) in the expression being compiled.

   The list [0; ..; |vs| - 1] gives the locations of f's arguments in the args array.
   (Simple for now, but may get fancier with custom calling conventions)

   Since we are compiling hoisted programs, we need only look at the toplevel function definitions.
*)
Fixpoint compute_fun_env' (fenv : fun_env) (fds : fundefs) : fun_env :=
  match fds with
  | Fcons f t xs e fds =>
    compute_fun_env' (M.set t (N.of_nat (length xs), make_arg_list xs) fenv) fds
  | Fnil => fenv
  end.
Definition compute_fun_env : fundefs -> fun_env := compute_fun_env' (M.empty _).

(* Compute the bound variables of a function body *) 
Fixpoint get_locals' (e : exp) (acc : list ident) : list ident :=
  match e with
  | Econstr x t vs e' => get_locals' e' (x :: acc)
  | Ecase x cs => fold_left (fun acc '(_, e) => get_locals' e acc) cs acc
  | Eproj x t n v e' => get_locals' e' (x :: acc)
  | Eletapp x f t xs e' => get_locals' e' (x :: acc)
  | Efun fnd e' => [] (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => acc
  | Eprim x p vs e' => get_locals' e' (x :: acc)
  | Ehalt x => acc
  end.
Definition get_locals (e : exp) : list ident := get_locals' e [].

(* Max number of value-sized words allocated by the translation of expression e until the next function call
   For constructor: 1 word per argument + 1 for header if boxed (more than 1 param), otherwise 0 (since enum) *)
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    | [] => max_allocs e'
    | _ => S (length vs + max_allocs e')
    end
  | Ecase x cs => fold_left (fun allocs '(_, e) => max (max_allocs e) allocs) cs 0
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => 0
  | Efun fnd e' => 0 (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
  end.

(** * Clight abbreviations *)

Notation threadStructInf := (Tstruct thread_info_id noattr).
Notation threadInf := (Tpointer threadStructInf noattr).

Notation int_ty := (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |}).
Notation uint_ty := (Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}).
Notation long_ty := (Tlong Signed {| attr_volatile := false; attr_alignas := None |}).
Notation ulong_ty := (Tlong Unsigned {| attr_volatile := false; attr_alignas := None |}).

Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
(* NOTE for val: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition val := if Archi.ptr64 then ulong_ty else uint_ty.
Definition uval := if Archi.ptr64 then ulong_ty else uint_ty.
Definition sval := if Archi.ptr64 then long_ty else int_ty.
Definition val_typ := if Archi.ptr64 then  (AST.Tlong:typ) else (Tany32:typ).
(* [Init_int x] = a C int literal in an initializer, with value x *)
Definition Init_int x := if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
(* [make_vint z] = a C int value with value z *)
Definition make_vint (z:Z) := if Archi.ptr64 then Vlong (Int64.repr z) else Values.Vint (Int.repr z).
(* [make_cint z t] = C integer constant with value z of type t *)
Definition make_cint z t := if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.

(* void garbage_collect(struct thread_info *tinfo); *)
Notation gc_ty := (Tfunction (Tcons threadInf Tnil) Tvoid cc_default).

(* bool isptr(val); *)
Notation isptr_ty := (Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr) cc_default).

Notation val_ptr := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).

Notation bool_ty := (Tint IBool Unsigned noattr).

(* mk_fun_ty_list n = val, ..
                      ------- n times *)
Fixpoint mk_fun_ty_list (n : nat) : typelist :=
  match n with
  | 0 => Tnil
  | S n' => Tcons val (mk_fun_ty_list n')
  end.

(* mk_fun_ty n = void(struct thread_info *ti, val, ..)
                                              ------- n times
   The type of a function that takes n arguments in registers. *)
Definition mk_fun_ty (n : nat) :=
  (Tfunction (Tcons threadInf (mk_fun_ty_list n)) Tvoid cc_default).

(* mk_prim_ty n = val(val, ..)
                      ------- n times
   The type of a primop with arity n. *)
Definition mk_prim_ty (n : nat) :=
  (Tfunction (mk_fun_ty_list n) val cc_default).

(* struct thread_info *make_tinfo(void); *)
Notation make_tinfo_ty :=
  (Tfunction Tnil threadInf cc_default).

(* val *export(struct thread_info *ti); *)
Notation export_ty :=
  (Tfunction (Tcons threadInf Tnil) val_ptr cc_default).

Notation "'var' x" := (Etempvar x val) (at level 20).

Notation alloc_ptr := (Etempvar alloc_id val_ptr).
Notation limit_ptr := (Etempvar limit_id val_ptr).
Notation args := (Etempvar args_id val_ptr).
Notation gc := (Evar gc_id gc_ty).

(* changed tinfo to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinfo := (Etempvar tinfo_id threadInf).
Notation tinfd := (Ederef tinfo threadStructInf).

(* Notation heapInf := (Tstruct heap_info_id noattr). *)

Definition add (a b : expr) := Ebinop Oadd a b val_ptr.
Notation " a '+'' b " := (add a b) (at level 30).

Definition sub (a b: expr) := Ebinop Osub a b val_ptr.
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

Notation "'&' p " := (Eaddrof p (Tpointer (typeof p) noattr)) (at level 40).

Definition c_int' n t := if Archi.ptr64 then Econst_long (Int64.repr n) t else Econst_int (Int.repr n%Z) t.

Notation c_int := c_int'.

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([val_ptr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).

(** * Shadow stack definitions *)

(* Stack-related ids *)
Variable (stackframe_ty_id : ident). (* the stack_frame type *)
Variable (frame_id : ident). (* the stack frame of the current function *)
Variable (root_id : ident). (* live root array *)
Variable (fp_id : ident). (* frame pointer, part of thread_info *)
(* Fields of stack_frame struct *)
Variable (next_fld : ident).
Variable (root_fld : ident).
Variable (prev_fld : ident).

(* The type of the stack_frame struct *)
Definition stackframe_ty := Tstruct stackframe_ty_id noattr.
(* The type of a pointer the stack_frame struct *)
Definition stackframe_ty_ptr := Tpointer stackframe_ty noattr.
(* The type of the root array for each frame. *)
Definition root_ty size := Tarray val size noattr.
(* Pointer to the root array *)
Definition root_ty_ptr := val_ptr.

(* local vars declared when a function uses the stack *)
(* struct stack_frame frame; val root[MAX_LOCS]; *)
Definition stack_decl size : list (ident * type)  :=
  (frame_id, stackframe_ty) :: (* local variable for local stack frame *)
  (root_id, root_ty size) :: nil. (* local variable for the live array *)

(* Notation for handling the root array *)
Notation root := (Etempvar root_id val_ptr).
Notation "'root[' n ']'" := ( *(add root (c_int n%Z val))) (at level 36).

Notation frame := (Evar frame_id stackframe_ty).

(* Initialize local stack frame. Called before the first function call that uses the current stack *)
Definition init_stack : statement :=
  (* frame.next = root; *)
  (Efield frame next_fld val_ptr :::= Evar root_id root_ty_ptr);
  (* frame.root = root; *)
  (Efield frame root_fld root_ty_ptr :::= Evar root_id root_ty_ptr);
  (* frame.prev = tinf->fp; *)
  (Efield frame prev_fld stackframe_ty_ptr :::= Efield tinfd fp_id stackframe_ty_ptr).

(* Updates the stack pointer and frame pointers before a call *)
(* b is true if the stack is already set. I.e. it's a call to the GC after a normal call *)
Definition set_stack (sp : N) (b : bool) : statement :=
  if ((sp =? 0)%N || b)%bool then Sskip else 
  (* tinfo->fp = &frame; *)
  (Efield tinfd fp_id stackframe_ty_ptr :::= Eaddrof frame stackframe_ty_ptr).

(* Updates the stack pointer and frame pointers before a call *)
Definition update_stack (sp : N) : statement :=
  if (sp =? 0)%N then Sskip else 
  (* frame.next = root + SP *)
  (Efield frame next_fld val_ptr :::= (add root (c_int (Z.of_N sp) val))).

(* Resets the frame pointer after a call, so that if subsequent calls don't use the stack the empty frame is not pushed. *)
(* b is true if it's a call to the GC after a normal call, so the stack will be reset anyway *)
Definition reset_stack (sp : N) (b : bool) : statement :=
  if ((sp =? 0)%N || b)%bool then Sskip else 
  (* Current frame points to the old frame again *)
  Efield tinfd fp_id stackframe_ty_ptr :::= Efield frame prev_fld val_ptr.

(* Pushes single var in frame *)
Definition push_var (sp : N) (x : ident) :=
  root[ Z.of_N sp ] :::= Evar x val_ptr.

(* Pops single var from frame *)
Definition pop_var (sp : N) (x : ident) := 
  x ::= root[ Z.of_N sp ].

Definition push_live_vars_offset (off : N) (xs : list ident) : statement * N :=
  (fix aux xs (n : N) (stmt : statement) : statement * N :=
     match xs with
     | nil => (stmt, n)
     | x :: xs => aux xs (n+1)%N (root[ Z.of_N n ] :::= Evar x val_ptr (* TODO: cast? *); stmt)
     end) xs off Sskip.

Definition pop_live_vars_offset (off : N) (xs : list ident) : statement :=
  (fix aux xs n stmt : statement :=
     match xs with
     | nil => stmt
     | x :: xs => aux xs (n+1)%N (x ::= root[ Z.of_N n ] (* TODO: cast? *); stmt)
     end) xs off Sskip.

(* push_live_vars [x; y; ..] =
             .
             .
     root[1] = y;
     root[0] = x;
     /*skip*/
*)
Definition push_live_vars (xs : list ident) : statement * N := push_live_vars_offset 0%N xs.

(* pop_live_vars [x; y; ..] =
       .
       .
     y = root[1];
     x = root[0];
     /*skip*/
*)
Definition pop_live_vars (xs : list ident) : statement := pop_live_vars_offset 0%N xs. 

(** * Shadow stack defs END *)

Section CODEGEN.

Variable (cenv : ctor_env). 
Variable (fenv : fun_env).
Variable (fienv : fun_info_env). 

Inductive ctor_rep : Type :=
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| enum : N -> ctor_rep
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)
| boxed : N -> N -> ctor_rep.

Definition find_ctor_rep (ct : ctor_tag) : error ctor_rep :=
  match M.get ct cenv with
  | Some p =>
    if (ctor_arity p =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p))
  | None => Err ("find_ctor_rep: unknown constructor with tag " ++ show_pos ct)
  end.

(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition make_tag (ct : ctor_tag) : error expr :=
  p <- find_ctor_rep ct ;;
  match p with
  | enum t => ret (c_int (Z.shiftl (Z.of_N t) 1 + 1) val)
  | boxed t a => ret (c_int (Z.shiftl (Z.of_N a) 10 + Z.of_N t) val)
  end%Z.

(* To use variables in Clight expressions, need variable name and its type.
   Variables that refer to functions must have type
     void(struct thread_info *ti, val, ..)
                                  ------- n times
   where n = min(n_param, arity of the function).

   All other variables just have type val. 
*)

(* make_var x = Evar x t where t is x's C type *)
Definition mk_var (x : ident) :=
  match M.get x fienv with
  (* if x is a function name with tag t... *)
  | Some t =>
    match M.get t fenv with
    (* ...and tag t corresponds to a function with arity n, then x has function type *)
    | Some (_, locs) => Evar x (mk_fun_ty (length (firstn n_param locs)))
      (* TODO: could just use n instead of locs *)
    | None => (* should be unreachable *) var x
    end
  (* otherwise, x is just a regular variable *)
  | None => var x
  end.

(* asgn_constr_boxed x n vs =
            x[n] = vs[0];
        x[n + 1] = vs[1];
                   .
                   .
     x[n + |vs|] = vs[|vs| - 1] 

   Assumes |vs|>0. *)
Fixpoint asgn_constr_boxed (x : ident) (n : nat) (vs : list ident) : statement :=
  match vs with
  | nil => (* shouldn't be reached *) Sskip
  | v :: nil => Field(var x, Z.of_nat n) :::= mk_var v
  | cons v vs' =>
    Field(var x, Z.of_nat n) :::= mk_var v;
    asgn_constr_boxed x (n+1) vs'
  end.

(* asgn_constr x c vs = 
     code to set x to (Constr c vs)
     if boxed (i.e., |vs|>0), x is a heap pointer. *)
Definition asgn_constr (x : ident) (c : ctor_tag) (vs : list ident) :=
  tag <- make_tag c ;;
  rep <- find_ctor_rep c ;;
  match rep with
  | enum _ => ret (x ::= tag)
  | boxed _ a =>
    ret (x ::= [val] (alloc_ptr +' c_int Z.one val);
         alloc_id ::= alloc_ptr +' c_int (Z.of_N (a + 1)) val;
         Field(var x, -1) :::= tag;
         asgn_constr_boxed x 0 vs)
  end.

(* Zoe: inlining the isptr function to avoid extra function call in C *)
Definition isptr (v : ident) : expr :=
  Ebinop Oeq (Ebinop Oand (Evar v val) (Econst_int Int.one int_ty) bool_ty)
         (Econst_int Int.zero int_ty) bool_ty.

(* mk_call loc f vs = (loc = f(tinfo, first n variables in vs..)) *)
Definition mk_call (loc : option ident) (f : expr) (vs : list ident) : statement :=
  Scall loc f (tinfo :: map mk_var (firstn n_param vs)).

(* mk_prim_call res pr ar vs = (res = pr(vs..)) *)
Definition mk_prim_call (res : ident) (pr : ident) (vs : list ident) : statement :=
  Scall (Some res) (Evar pr (mk_prim_ty (length vs))) (map mk_var vs).

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
Fixpoint asgn_fun_vars' (vs : list ident) (ind : list N) : error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | v :: vs', i :: ind' =>
    rest <- asgn_fun_vars' vs' ind' ;;
    ret (v ::= args[ Z.of_N i ]; rest)
  | _, _ => Err "asgn_fun_vars': list lengths unequal"
  end.

(* Like asgn_fun_vars' but skip the first n_param arguments. *)
Definition asgn_fun_vars (vs : list ident) (ind : list N) : error statement :=
  asgn_fun_vars' (skipn n_param vs) (skipn n_param ind).

(* asgn_app_vars'' vs ind =
            args[ind[0]] = vs[0];
            args[ind[1]] = vs[1];
                         .
                         .
    args[ind[|ind| - 1]] = vs[|ind| - 1];

   Reads arguments from local variables vs.
   Stores them in the args array at indices ind.
*)
Fixpoint asgn_app_vars'' (vs : list ident) (ind : list N) (name : string) : error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | v :: vs', i :: ind' =>
    rest <- asgn_app_vars'' vs' ind' name ;;
    ret (rest; args[ Z.of_N i ] :::= mk_var v)
  | _, _ => Err ("asgn_app_vars'' " ++ name)%string
  end.

(* Like asgn_app_vars'', but skip the first n_param arguments. *)
Definition asgn_app_vars' (vs : list ident) (ind : list N) (name : string) : error statement :=
  asgn_app_vars'' (skipn n_param vs) (skipn n_param ind) name.

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
Fixpoint remove_app_vars (myvs vs : list ident) (myind ind : list N) : error (list ident * list N) :=
  match vs, ind with
  | nil, nil => ret (nil, nil)
  | v :: vs, i :: ind =>
    '(vs', ind') <- remove_app_vars myvs vs myind ind ;;
     n <- index_of Pos.eqb myvs v ;;
     match nth_error myind n with
     | Some i' => if N.eqb i i' then ret (vs', ind') else ret (v :: vs', i :: ind')
     | None => ret (v :: vs', i :: ind')
     end
  | _, _ => Err "remove_app_vars: list lengths unqual"
  end.

(* Like asgn_app_vars'' but ignore variables in myvs/indices in myind *)
Definition asgn_app_vars_fast' (myvs vs : list ident) (myind ind : list N) (name : string) : error statement :=
  '(vs', ind') <- remove_app_vars myvs (skipn n_param vs) myind (skipn n_param ind) ;;
  asgn_app_vars'' vs' ind' name.

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
Definition asgn_app_vars vs ind name :=
  s <- asgn_app_vars' vs ind name ;;
  ret (args_id ::= Efield tinfd args_id (Tarray uval max_args noattr); s).

(* Like asgn_app_vars, but ignore variables in myvs/indices in myind *)
Definition asgn_app_vars_fast myvs vs myind ind name :=
  s <- asgn_app_vars_fast' myvs vs myind ind name ;;
  ret (args_id ::= Efield tinfd args_id (Tarray uval max_args noattr); s).

(** * GC call *)
Definition make_gc_call (num_allocs : nat) (stack_vars : list ident) (stack_offset : N) : statement * N :=
  let after_call := negb (stack_offset =? 0)%N in
  let (push, slots) := push_live_vars_offset stack_offset stack_vars in
  let make_gc_stack := push; update_stack slots; set_stack slots after_call in
  let discard_stack := pop_live_vars_offset stack_offset stack_vars; reset_stack slots after_call in
  let nallocs := c_int (Z.of_nat num_allocs) val in 
  let set_nalloc := Efield tinfd nalloc_id val :::= nallocs in
  if (num_allocs =? 0)%nat then (Sskip, stack_offset) else 
    ((Sifthenelse
        (!(Ebinop Ole nallocs (limit_ptr -' alloc_ptr) type_bool))
        (make_gc_stack;
         set_nalloc;
         Scall None gc (tinfo :: nil);
         discard_stack;
         alloc_id ::= Efield tinfd alloc_id val_ptr;
         limit_id ::= Efield tinfd limit_id val_ptr)
        Sskip), slots).

(** * Shadow stack strategy *)
(* ZOE TODO: update text

 1. Before the first non-tail call create a local (stored in the stack) array and a frame
    struct with pointer to the array and the previous frame. Modify the stack pointer of
    tinfo to point to the newly created stack frame
 2. Before the last (tail) call or return modify tinfo to point to the previous stack frame

 *)

(* To create the shadow stack:

   long long int live[MAX_live];
   frame_pointer fp = { next = *live; root=*live; prev:=tinfo->sp}
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
      (fun_vars : list ident)
      (locals : FVSet) (* The set of local vars including definitions and arguments *)
      (locs : list N)
      (nenv : M.t BasicAst.name).

    Definition mk_fn_call f t ys :=
      match M.get t fenv with 
      | Some (arity, inds) =>
        let name := get_fname f nenv in
        asgn <- (if args_opt
                then asgn_app_vars_fast fun_vars ys locs inds name
                else asgn_app_vars ys inds name) ;;
        let arity := N.to_nat arity in
        let n := min arity n_param in
        if negb (length ys =? arity)%nat then Err "mk_fn_call: arity mismatch" else
        let call :=
          Scall None
                ([Tpointer (mk_fun_ty n) noattr] (mk_var f))
                (tinfo :: map mk_var (firstn n_param ys))
        in
        ret (asgn, call)
      | None => Err "mk_fun_call: unknown function application"
      end.

    Definition mk_cases (translate_body : exp -> error (statement * FVSet * N)) :=
      fix mk_cases l : error (labeled_statements * labeled_statements * FVSet * N) :=
        match l with
        | nil => ret (LSnil, LSnil, PS.empty, 0)%N
        | (c, e) :: l' =>
          '(prog, fvs_e, n_e) <- translate_body e ;;
          '(ls, ls', fvs_l', n_l') <- mk_cases l' ;;
          let fvs := PS.union fvs_e fvs_l' in
          let n := N.max n_e n_l' in
          p <- find_ctor_rep c ;;
          match p with 
          | boxed t a =>
            let tag :=
              match ls with
              | LSnil => None
              | LScons _ _ _ => Some (Z.land (Z.of_N t) 255)%Z
              end
            in
            ret (LScons tag (Ssequence prog Sbreak) ls, ls', fvs, n)
          | enum t =>
            let tag :=
              match ls' with
              | LSnil => None
              | LScons _ _ _ => Some (Z.of_N t)%Z
              end
            in
            ret (ls, LScons tag (Ssequence prog Sbreak) ls', fvs, n)
          end
        end.

    (* fvs ∪ ({x} ∩ locals) *)
    Definition add_local_fv fvs x := if PS.mem x locals then PS.add x fvs else fvs.

    (* fvs ∪ (FromList xs ∩ locals) *)
    Definition add_local_fvs fvs xs := fold_left add_local_fv xs fvs.

    (* Returns (C code for e, FV(e) ∩ locals, number of stack slots needed) 
       Number of stack slots needed =
         max(|(FV(e')\x)∩locals| for each Eletapp x f t ys e' we encounter in e) *)
    Fixpoint translate_body (e : exp) {struct e} : error (statement * FVSet * N) :=
      match e with
      | Econstr x t ys e' =>
        stm_constr <- asgn_constr x t ys ;;
        '(stm_e', fvs_e', n_e') <- translate_body e' ;;
        ret ((stm_constr; stm_e'), add_local_fvs (PS.remove x fvs_e') ys, n_e')
      | Ecase x cs =>
        '(boxed_cases, unboxed_cases, fvs_cs, n_cs) <- mk_cases translate_body cs ;;
        ret (Sifthenelse
              (isptr x)
              (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) boxed_cases)
              (Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val) unboxed_cases),
             add_local_fv fvs_cs x, n_cs)
      | Eletapp x f t ys e' =>
        (* Compute the local variables that are live after the call  *)
        '(prog, fvs_e', n_e') <- translate_body e' ;;
        let fvs := PS.elements (PS.remove x fvs_e') in
        (* Push live vars to the stack. We're pushing exactly the vars that are live beyond the current point. *)
        let '(make_stack, slots_call) :=
          let (push, slots) := push_live_vars fvs in
          (push; update_stack slots; set_stack slots false, slots)
        in
        let discard_stack := (pop_live_vars fvs; reset_stack slots_call false) in
        '(asgn, call) <- mk_fn_call f t ys ;;
        (* Check if the new binding has to be pushed to the frame during the GC call *)
        let fvs_gc := if PS.mem x fvs_e' then x :: nil else nil in
        (* Call GC after the call if needed *)
        let '(gc_call, slots_gc) := make_gc_call (max_allocs e') fvs_gc slots_call in
        ret ((asgn;
              Efield tinfd alloc_id val_ptr :::= alloc_ptr;
              Efield tinfd limit_id val_ptr :::= limit_ptr;
              make_stack;
              call;
              alloc_id ::= Efield tinfd alloc_id val_ptr;
              limit_id ::= Efield tinfd limit_id val_ptr;
              x ::= args[ Z.of_nat 1 ];
              gc_call;
              discard_stack;
              prog),
             add_local_fvs (PS.remove x fvs_e') (f :: ys),
             N.max slots_call (N.max slots_gc n_e'))
      | Eproj x t n y e' =>
        '(stm_e, fvs_e', n_e') <- translate_body e' ;;
        ret ((x ::= Field(var y, Z.of_N n); stm_e), add_local_fv (PS.remove x fvs_e') y, n_e')
      | Efun fnd e => Err "translate_body: Nested function detected"
      | Eapp f t ys =>
        '(asgn, call) <- mk_fn_call f t ys ;;
        ret ((asgn;
              Efield tinfd alloc_id val_ptr :::= alloc_ptr;
              Efield tinfd limit_id val_ptr :::= limit_ptr;
              call),
             add_local_fvs PS.empty (f :: ys), 0)%N
      | Eprim x p ys e' =>    
        '(stm_e, fvs_e', n_e') <- translate_body e' ;;
        ret ((Scall (Some x) (Evar p (mk_prim_ty (length ys))) (map mk_var ys);
              stm_e),
             add_local_fvs (PS.remove x fvs_e') ys, n_e')
      | Ehalt x =>
        (* set args[1] to x and return *)
        ret ((args[ Z.of_nat 1 ] :::= mk_var x;
              Efield tinfd alloc_id val_ptr :::= alloc_ptr;
              Efield tinfd limit_id val_ptr :::= limit_ptr),
             add_local_fv PS.empty x, 0)%N
      end.

  End Body.

Definition mk_fun
           (root_size : Z) (* size of root array *)
           (vs : list ident) (* args *)
           (loc : list ident) (* local vars *)
           (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             ((tinfo_id , threadInf) :: (map (fun x => (x , val)) (firstn n_param vs)))
             ((map (fun x => (x , val)) ((skipn n_param vs) ++ loc)) ++ (stack_decl root_size) ++ (alloc_id, val_ptr)::(limit_id, val_ptr)::(args_id, val_ptr)::(case_id, bool_ty) :: nil)
             nil
             body.

Fixpoint translate_fundefs (fnd : fundefs) (nenv : name_env) : error (list (ident * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => Ret nil
  | Fcons f t vs e fnd' =>
    rest <- translate_fundefs fnd' nenv ;;
    match M.get t fenv with
    | None => Err "translate_fundefs: Unknown function tag"
    | Some (l, locs) =>
      asgn <- asgn_fun_vars vs locs ;; (* project remaining params out of args array *)
      let num_allocs := max_allocs e in
      let loc_vars := get_locals e in
      let var_set := union_list PS.empty vs in
      let loc_ids := union_list var_set loc_vars in
      '(body, live_loc_ids, stack_slots) <- translate_body vs loc_ids locs nenv e ;;
      let live_vars := PS.elements (PS.inter live_loc_ids var_set) in 
      let (gc, _) := make_gc_call num_allocs live_vars 0%N in
      let stack_slots := N.max (N.of_nat (length live_vars)) stack_slots in
      Ret ((f , Gfun (Internal
                      (mk_fun (Z.of_N stack_slots) vs loc_vars
                             ((alloc_id ::= Efield tinfd alloc_id val_ptr ;
                               limit_id ::= Efield tinfd limit_id val_ptr ;
                               args_id ::= Efield tinfd args_id (Tarray uval max_args noattr);
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
  let params := (type_of_params ((tinfo_id, threadInf):: nil)) in
  (body_id, Gfun (External (EF_external ("body"%string) (signature_of_type  params Tvoid cc_default)) params Tvoid cc_default)).

End Translation.

(* TODO move *)
Definition lift_error {A : Type} (o : option A) (s : string) : error A :=
  match o with
  | Some a => ret a
  | None => Err s
  end.

Definition translate_program (args_opt : bool) (e : hoisted_exp) nenv :
  error (list (positive * globdef Clight.fundef type)) :=
  let '(fnd, e) := e in
  let localVars := get_locals e in
  funs <- translate_fundefs args_opt fnd nenv ;;
  let allocs := max_allocs e in
  let (gc_call, _) := make_gc_call allocs nil (* no live roots to push *) 0%N in
  '(body, _, slots) <- translate_body args_opt [] (union_list PS.empty localVars) [] nenv e ;;
  let argsExpr := Efield tinfd args_id (Tarray uval max_args noattr) in
  ret ((body_id , Gfun (Internal
                            (mkfunction val
                                        cc_default
                                        ((tinfo_id, threadInf)::nil)
                                        ((map (fun x => (x , val)) localVars) ++ (stack_decl (Z.of_N slots)) ++ (alloc_id, val_ptr)::(limit_id, val_ptr)::(args_id, val_ptr)::nil)
                                        nil
                                        (alloc_id ::= Efield tinfd alloc_id val_ptr ;
                                         limit_id ::= Efield tinfd limit_id val_ptr ;
                                         args_id ::= Efield tinfd args_id (Tarray uval max_args noattr);
                                         init_stack ;
                                         gc_call;
                                         body ;
                                         Sreturn (Some (Field(argsExpr, Z.of_nat 1))))))) :: funs).

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

(* see runtime for description and uses of fundef_info.
  In summary,
  fi[0] = number of words that can be allocated by function
  fi[1] = number of live roots at startof function
  rest = indices of live roots in args array
*)

Fixpoint make_fundef_info (fnd : fundefs) (fenv : fun_env)
  : error fun_info_env :=
  match fnd with
  | Fnil => ret (M.empty _)
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => Err "make_fundef_info: Unknown tag"
    | Some (n, l) =>
      fienv <- make_fundef_info fnd' fenv ;;
      (* it should be the case that n (computed arity from tag) = len (actual arity) *)
      ret (M.set x t fienv)
    end
  end.

Definition add_bodyinfo (fienv: fun_info_env) :=
  M.set main_id (1%positive) fienv.
  (* TODO: need to enforce the invariant that all other fun tags are greater than 1 *)

(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Definition make_funinfo (e : hoisted_exp) (fenv : fun_env) : error fun_info_env :=
  let '(fds, e) := e in
  fienv <- make_fundef_info fds fenv ;;
  ret (add_bodyinfo fienv).

Definition global_defs : list (positive * globdef Clight.fundef type) :=
    (gc_id , Gfun (External (EF_external "gc"
                                              (mksignature (val_typ :: nil) None cc_default))
                                 (Tcons threadInf Tnil)
                                 Tvoid
                                 cc_default
    ))::
      (isptr_id , Gfun (External (EF_external "is_ptr"
                                             (mksignature (val_typ :: nil) None cc_default))
                                (Tcons val Tnil) (Tint IBool Unsigned noattr)
                                cc_default
      ))
    :: nil.

Definition make_defs (args_opt : bool) (e : hoisted_exp) (fenv : fun_env) (cenv: ctor_env) (nenv : name_env) :
  error (list (positive * globdef Clight.fundef type)) :=
  fienv <- make_funinfo e fenv ;;
  fun_defs' <- translate_program cenv fenv fienv args_opt e nenv ;;
  ret (global_defs ++ rev fun_defs')%list.

(* Types declared at the begining of the program *)
Definition composites : list composite_definition :=
  Composite stackframe_ty_id Struct
            ((next_fld, val_ptr) ::
             (root_fld, val_ptr) ::
             (prev_fld, (tptr stackframe_ty)) :: nil)
            noattr ::
  Composite thread_info_id Struct
            ((alloc_id, val_ptr) ::
             (limit_id, val_ptr) ::
             (heap_info_id, (tptr (Tstruct heap_info_id noattr))) ::
             (args_id, (Tarray uval max_args noattr)) ::
             (fp_id, (tptr stackframe_ty)) ::
             (nalloc_id, val) :: nil) (* Zoe : This is the number of allocations until the next GC call so that GC can perform a test. 
                                         * Note that it will be coerced to UL from ULL. That should be safe for the values we're using but 
                                         * consider changing it too. *)
            noattr ::
   nil.

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) (add_comp:bool): error Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites defs (body_id :: nil) main in
  match res with
  | Error e => Err "mk_prog_opt"
  | OK p => ret p
  end.

Definition inf_vars :=
  (isptr_id, (nNamed "is_ptr"%string)) ::
  (args_id, (nNamed "args"%string)) ::
  (alloc_id, (nNamed "alloc"%string)) ::
  (nalloc_id, (nNamed "nalloc"%string)) ::
  (limit_id, (nNamed "limit"%string)) ::
  (gc_id, (nNamed "garbage_collect"%string)) ::
  (main_id, (nNamed "main"%string)) ::
  (body_id, (nNamed "body"%string)) ::
  (thread_info_id, (nNamed "thread_info"%string)) ::
  (tinfo_id, (nNamed "tinfo"%string)) ::
  (heap_info_id, (nNamed "heap"%string)) ::
  (case_id, (nNamed "arg"%string)) ::
  (num_args_id, (nNamed "num_args"%string)) ::
  (stackframe_ty_id, (nNamed "stack_frame"%string)) ::
  (frame_id, nNamed "frame"%string) ::
  (root_id, nNamed "roots"%string) ::
  (fp_id, nNamed "fp"%string) ::
  (next_fld, nNamed "next"%string) ::
  (root_fld, nNamed "root"%string) ::
  (prev_fld, nNamed "prev"%string) :: nil.


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

Definition add_inf_vars (nenv: name_env): name_env :=
  List.fold_left (fun nenv inf => M.set (fst inf) (snd inf) nenv) inf_vars nenv.

Definition ensure_unique : M.t name -> M.t name :=
  fun l => M.map (fun x n =>
                 match n with
                 | nAnon =>  nAnon
                 | nNamed s => nNamed (append s (append "_"%string (show_pos x)))
                 end) l.

Definition make_tinfo_id := 20%positive.
Definition export_id := 21%positive.

Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  (make_tinfo_id,
   Gfun (External (EF_external "make_tinfo"
                               (mksignature (nil) (Some val_typ) cc_default))
                  Tnil
                  threadInf
                  cc_default)).
                  
Definition export_rec : positive * globdef Clight.fundef type :=
  (export_id,
   Gfun (External (EF_external "export"
                               (mksignature (cons val_typ nil) (Some val_typ) cc_default))
                  (Tcons threadInf Tnil)
                  val_ptr
                  cc_default)).

Definition compile (args_opt : bool) (e : exp) (cenv : ctor_env) (nenv0 : name_env) :
  error (M.t BasicAst.name * Clight.program * Clight.program) * string :=
  let res :=
    let e := mk_hoisted_exp e in
    let fenv := compute_fun_env (fst e) in
    (* debug *)
    (* let dbg := (cps_show.show_exp nenv0 cenv false e) ++ Pipeline_utils.newline ++ log ++ Pipeline_utils.newline ++ check_tags fenv nenv0 e in *)
    (* end debug *)
    defs <- make_defs args_opt e fenv cenv nenv0 ;;
    let nenv := (add_inf_vars (ensure_unique nenv0)) in
    let forward_defs := make_extern_decls nenv defs false in
    body <- mk_prog_opt [body_external_decl] main_id false;;
    head <- mk_prog_opt (make_tinfo_rec :: export_rec :: forward_defs ++ defs)%list main_id true ;;
    ret (M.set make_tinfo_id (nNamed "make_tinfo"%string)
               (M.set export_id (nNamed "export"%string) nenv),
         body, head)
  in (res, "").

Definition err {A : Type} (s : String.string) : res A :=
  Error (MSG s :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil main_id nil eq_refl.

Definition strip_option (p : option Clight.program) : Clight.program :=
  match p with
  | None => empty_program
  | Some p' => p'
  end.

End TRANSLATION.

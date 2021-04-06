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

(* For proofs *)
Require Import
        compcert.common.Memory
        compcert.common.Globalenvs
        Coq.Relations.Relations
        Coq.Sets.Ensembles
        Lia
        L6.eval L6.algebra L6.Ensembles_util L6.ctx L6.scoping
        L7.ClightBigstep2.

Module O := Ptrofs.

Section CODEGEN.

Notation "'#|' xs '|'" := (Z.of_nat (length xs)).

Definition mapi {A B} (f : Z -> A -> B) :=
  fix go (i : Z) (xs : list A) : list B :=
    match xs with
    | [] => []
    | x :: xs => f i x :: go (i + 1)%Z xs
    end.

(** We only translate hoisted terms *)
Definition hoisted_exp := (fundefs * exp)%type.
Definition make_hoisted_exp (e : exp) : hoisted_exp :=
  match e with
  | Efun fds e => (fds, e)
  | _ => (Fnil, e)
  end.

Definition pretty_fun_name f (nenv : name_env) : string := 
  match M.get f nenv with
  | Some nAnon => "anon"
  | Some (nNamed n) => n
  | None => "not an entry"
  end.

(** The number of parameters to be passed as C function parameters *)
Variable (n_param : nat).

(** The size of the args array. No function can take more than max_args parameters. *)
Definition max_args := 1024%Z.

(** fun_env holds mappings
      f ↦ (|ys|, [0; ..; |ys| - 1]) 
    for each
      (Fcons f t ys _ _),
      (Eletapp _ f _ ys _), or
      (Eapp f _ ys)
    in the expression being compiled.

    The list [0; ..; |ys| - 1] gives the locations of f's arguments in the args array.
    (Simple for now, but may get fancier with custom calling conventions) *)
Fixpoint compute_fun_env' (fenv : fun_env) (e : exp) : fun_env :=
  match e with
  | Econstr x t ys e' => compute_fun_env' fenv e'
  | Ecase x cs => fold_left (fun fenv '(_, e) => compute_fun_env' fenv e) cs fenv
  | Eproj x t n v e' => compute_fun_env' fenv e'
  | Eletapp x f t ys e' =>
    compute_fun_env' (M.set f (N.of_nat (length ys), mapi (fun n _ => Z.to_N n) 0 ys) fenv) e'
  | Efun fds e' =>
    let fenv := compute_fun_env_fundefs fds fenv in
    compute_fun_env' fenv e'
  | Eapp f t ys => M.set f (N.of_nat (length ys), mapi (fun n _ => Z.to_N n) 0 ys) fenv
  | Eprim x p ys e' => compute_fun_env' fenv e'
  | Ehalt x => fenv
  end
with compute_fun_env_fundefs fds fenv : fun_env :=
  match fds with
  | Fnil => fenv
  | Fcons f t ys e fds' =>
    let fenv := M.set f (N.of_nat (length ys), mapi (fun n _ => Z.to_N n) 0 ys) fenv in
    let fenv := compute_fun_env' fenv e in
    compute_fun_env_fundefs fds' fenv
  end.
Definition compute_fun_env : hoisted_exp -> fun_env :=
  fun '(fds, e) => compute_fun_env' (M.empty _) (Efun fds e).

(** Max number of words allocated by e up to the next function call.
    (Only compute up to next function call because that's when GC will run next) *)
Fixpoint max_allocs (e : exp) : Z :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    (* Unboxed: no allocation necessary *)
    | [] => max_allocs e'
    (* Boxed: allocate 1 word for header + |vs| words for arguments *)
    | _ => 1 + #|vs| + max_allocs e'
    end
  | Ecase x cs => fold_left (fun allocs '(_, e) => Z.max (max_allocs e) allocs) cs 0
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => 0
  | Efun fds e' => 0 (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
  end%Z.

(** * Clight abbreviations *)

(** typedef intnat value; (See values.h, config.h)

    NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition value :=
  if Archi.ptr64
  then Tlong Unsigned noattr
  else Tint I32 Unsigned noattr.
Definition ast_value :=
  if Archi.ptr64 then AST.Tlong else Tany32.
Definition make_cint (z : Z) (t : type) : expr :=
  if Archi.ptr64
  then Econst_long (Int64.repr z) t
  else Econst_int (Int.repr z) t.

(** struct thread_info {
      value *alloc;
      value *limit;
      struct heap *heap;
      value args[MAX_ARGS];
      struct stack_frame *fp;
      value nalloc;
    };

    Zoe: nalloc is the number of allocations until the next GC call so that GC can perform a test. *)
Context (thread_info_id alloc_id limit_id heap_id args_id fp_id nalloc_id : ident).
Notation threadStructInf := (Tstruct thread_info_id noattr). 
Notation threadInf := (Tpointer threadStructInf noattr).
(* TODO: snake-case-ify; currently used by glue code generator *)

(** struct stack_frame {
      value *next;
      value *root;
      struct stack_frame *prev;
    }; *)
Context (stack_frame_id next_fld root_fld prev_fld : ident).
Notation stack_frame := (Tstruct stack_frame_id noattr).

(** Declarations for the above structs, in abstract syntax *)
Definition composites : list composite_definition :=
  Composite stack_frame_id Struct
            ((next_fld, tptr value) ::
             (root_fld, tptr value) :: 
             (prev_fld, tptr stack_frame) :: 
             nil)
            noattr ::
  Composite thread_info_id Struct
            ((alloc_id, tptr value) ::
             (limit_id, tptr value) ::
             (heap_id, tptr (Tstruct heap_id noattr)) ::
             (args_id, Tarray value max_args noattr) ::
             (fp_id, tptr stack_frame) ::
             (nalloc_id, value) ::
             nil)
            noattr ::
   nil.

(** Each generated function takes a (struct thread_info *tinfo) as argument *)
Context (tinfo_id : ident).
Notation tinfo := (Etempvar tinfo_id threadInf).
Notation tinfd := (Ederef tinfo threadStructInf).
Notation "tinfo->alloc" := (Efield tinfd alloc_id (tptr value)).
Notation "tinfo->limit" := (Efield tinfd limit_id (tptr value)).
Notation "tinfo->args" := (Efield tinfd args_id (Tarray value max_args noattr)).
Notation "tinfo->fp" := (Efield tinfd fp_id (tptr stack_frame)).
Notation "tinfo->nalloc" := (Efield tinfd nalloc_id value).

(** Each generated function body declares the following local variables:
      struct stack_frame frame;
      value roots[size];
    where size upper bounds the number of variables live at GC calls. *)
Context (frame_id roots_id : ident).
Definition roots_ty size := Tarray value size noattr.
Definition roots_array size := Evar roots_id (roots_ty size).
Notation frame := (Evar frame_id stack_frame).
Notation "frame.next" := (Efield frame next_fld (tptr value)).
Notation "frame.root" := (Efield frame root_fld (tptr value)).
Notation "frame.prev" := (Efield frame prev_fld (tptr stack_frame)).
Definition stack_decl size : list (ident * type) :=
  (frame_id, stack_frame) ::
  (roots_id, roots_ty size) :: nil.

(** Compcert doesn't allow checking whether pointers are even or odd.
    So the check for whether a value is a pointer or not is implemented
    by an external function
      bool is_ptr(value v); *)
Variable (isptr_id : ident).
Definition bool_ty := Tint IBool Unsigned noattr.
Definition isptr := Evar isptr_id (Tfunction (Tcons value Tnil) bool_ty cc_default).

(** void garbage_collect(struct thread_info *tinfo);
    struct thread_info *make_tinfo(void);
    value *export(struct thread_info *ti); *)
Variable (gc_id : ident).
Definition gc := Evar gc_id (Tfunction (Tcons threadInf Tnil) Tvoid cc_default).
Definition make_tinfo_ty := Tfunction Tnil threadInf cc_default.
Definition export_ty := Tfunction (Tcons threadInf Tnil) (tptr value) cc_default.
Variable (body_id : ident).

(** void __builtin_unreachable(void);
    For marking the default cases of switch blocks as unreachable. *)
Variable (builtin_unreachable_id : ident).
Definition builtin_unreachable : statement :=
  let f := Evar builtin_unreachable_id (Tfunction Tnil Tvoid cc_default) in
  Scall None f nil.

(** Each generated function body also declares the following temporary variables:
      value *alloc;
      value *limit;
      value ret;
      bool case_id;
      value *roots_temp;
    ret is used to store the results of tail calls.
    case_id is used to store the results of calls to isptr.
    roots_temp is used to store the roots array.
      Q: Why not just refer to the roots array using roots_id?
      A: roots_id is a fixed-size stack-allocated array.
         To refer to it, need to know its size to write (Evar roots_id (Tarray ..)).
         The size is computed together with the generated C code, in translate_body.
         Therefore, it's not available until after translate_body.
         To avoid doing two passes, we can refer to the roots array via roots_temp,
         which just has type (tptr value). Then, we can emit
           roots_temp = roots;
         at function entry to intiailize roots_temp properly.
*)
Notation alloc := (Etempvar alloc_id (tptr value)).
Notation limit := (Etempvar limit_id (tptr value)).
Variable (ret_id : ident).
Variable (case_id : ident).
Variable (roots_temp_id : ident).
Notation roots := (Etempvar roots_temp_id (tptr value)).

(** fun_ty n = value(struct thread_info *ti, value, .. min(n_param, n) times)
    prim_ty n = value(value, .. n times) *)
Definition value_tys (n : nat) : typelist := Nat.iter n (Tcons value) Tnil.
Definition fun_ty (n : nat) := Tfunction (Tcons threadInf (value_tys (min n_param n))) value cc_default.
Definition prim_ty (n : nat) := Tfunction (value_tys n) value cc_default.

Declare Scope C_scope.
Delimit Scope C_scope with C.

Notation "'var' x" := (Etempvar x value) (at level 20).
Notation "a '+'' b" := (Ebinop Oadd a b (tptr value)) (at level 30).
Notation "a '-'' b" := (Ebinop Osub a b (tptr value)) (at level 30).
Notation "a '<'' b" := (Ebinop Olt a b type_bool) (at level 40).
Notation "a '>>'' b" := (Ebinop Oshr a b value) (at level 30).
Notation "a '&'' b" := (Ebinop Oand a b value) (at level 30).
Notation "a '=='' b" := (Ebinop Oeq a b type_bool) (at level 40).
Notation " p '.;' q " := (Ssequence p q) (at level 100, format " p '.;' '//' q ") : C_scope.
Infix "::=" := Sset (at level 50).
Infix ":::=" := Sassign (at level 50).
Notation "'*' p " := (Ederef p value) (at level 40).
Notation "'&' p " := (Eaddrof p (Tpointer (typeof p) noattr)) (at level 40).
Definition c_int n t := if Archi.ptr64 then Econst_long (Int64.repr n) t else Econst_int (Int.repr n%Z) t.
Notation "a '.[' n ']'" :=
  ( *(Ecast a (tptr value) +' c_int n%Z value)) (at level 25). (* what is the type of int being added? *)

Definition statements : list statement -> statement := fold_right Ssequence Sskip.

Section CODEGEN.

Variable (cenv : ctor_env). 
Variable (fenv : fun_env).

Inductive ctor_rep : Type :=
(** [enum t] represents a constructor with no parameters with ordinal [t] *)
| enum : N -> ctor_rep
(** [boxed t a] represents a construct with arity [a] and ordinal [t]  *)
| boxed : N -> N -> ctor_rep.

Definition get_ctor_rep (c : ctor_tag) : error ctor_rep :=
  match M.get c cenv with
  | Some p =>
    if (ctor_arity p =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p))
  | None => Err ("find_ctor_rep: unknown constructor with tag " ++ show_pos c)
  end.

Definition rep_unboxed (t : N) : Z := Z.shiftl (Z.of_N t) 1 + 1.
Definition rep_boxed (t a : N) : Z := Z.shiftl (Z.of_N a) 10 + Z.of_N t.

Definition make_tag (r : ctor_rep) : expr :=
  c_int match r with
        | enum t => rep_unboxed t
        | boxed t a => rep_boxed t a
        end%Z
        value.

Section Body.

Context
  (locals : FVSet) (* The set of local variables including definitions and arguments *)
  (nenv : M.t BasicAst.name).

(** To use variables in Clight expressions, need variable name and its type.
    Variables that refer to top-level functions must have type
      void(struct thread_info *ti, val, ..)
                                   ------- n times
    where n = min(n_param, arity of the function).

    All other variables just have type val. *)
Definition make_var (x : ident) :=
  match M.get x fenv with
  | Some (_, locs) =>
    if PS.mem x locals
    then var x
    else Ecast (Evar x (fun_ty (length locs))) value
  | None => var x
  end.

Definition make_fun_call (destination : ident) f ys :=
  match M.get f fenv with 
  | Some (arity, inds) =>
    let arity := N.to_nat arity in
    if negb (length ys =? arity)%nat then
      Err ("make_fun_call: arity mismatch: " ++ pretty_fun_name f nenv)%string
    else
      ret (statements
             (map (fun '(y, i) => tinfo->args.[Z.of_N i] :::= make_var y)
                  (skipn n_param (combine ys inds)))%bool.;
           tinfo->alloc :::= alloc.;
           tinfo->limit :::= limit.;
           Scall (Some destination)
                 (Ecast (make_var f) (Tpointer (fun_ty (min arity n_param)) noattr))
                 (tinfo :: map make_var (firstn n_param ys)))%C
  | None => Err "make_fun_call: unknown function application"
  end.

Definition make_cases (translate_body : exp -> error (statement * FVSet * N)) :=
  fix make_cases l : error (labeled_statements * labeled_statements * FVSet * N) :=
    match l with
    | nil =>
      let unreachable_cases := LScons None builtin_unreachable LSnil in
      ret (unreachable_cases, unreachable_cases, PS.empty, 0)%N
    | (c, e) :: l' =>
      '(prog, fvs_e, n_e) <- translate_body e ;;
      '(ls, ls', fvs_l', n_l') <- make_cases l' ;;
      let fvs := PS.union fvs_e fvs_l' in
      let n := N.max n_e n_l' in
      p <- get_ctor_rep c ;;
      (** We don't need to insert break statements: our generated programs always
          return using Sreturn at the end, so fall-through is impossible. *)
      match p with
      | boxed t a => ret (LScons (Some (Z.of_N t)) prog ls, ls', fvs, n)
      | enum t => ret (ls, LScons (Some (Z.of_N t)) prog ls', fvs, n)
      end%C
    end.

(** Use limit and alloc to check whether nursery contains n words of free space.
    If not, run pre, invoke GC, then run post. *)
Definition create_space (n : Z) pre post : statement :=
  Sifthenelse
    (limit -' alloc <' c_int n value)
    (pre.;
     tinfo->nalloc :::= c_int n value.;
     Scall None gc (tinfo :: nil).;
     alloc_id ::= tinfo->alloc.;
     limit_id ::= tinfo->limit.;
     post)%C
    Sskip.

(** fvs ∪ ({x} ∩ locals) *)
Definition add_local_fv fvs x := if PS.mem x locals then PS.add x fvs else fvs.
Definition add_local_fvs fvs xs := fold_left add_local_fv xs fvs.

(** Returns (C code for e, FV(e) ∩ locals, number of stack slots needed) 
    Number of stack slots needed = 
      max(|FV(e')∩locals| for each Eletapp x f t ys e' we encounter in e) *)
Fixpoint translate_body (e : exp) {struct e} : error (statement * FVSet * N) :=
  match e with
  (** [[let x = Con c ys in e]] =
        if c is unboxed (and ys = []),
          x = (c<<1) + 1;
        if x is boxed,
          x = alloc + 1;
          alloc += 1 + |ys|;
          x[-1] = |ys|<<10 + c; (assume |ys|<256)
          x[0 .. |ys| - 1] = ys;
        [[e]] *)
  | Econstr x c ys e =>
    rep <- get_ctor_rep c ;;
    stm_constr <-
      match rep, ys with
      | enum t, [] => ret (x ::= make_tag rep)
      | enum _, _ :: _ => Err "translate_body: unboxed constructor given arguments"
      | boxed t a, _ :: _ =>
        ret (x ::= Ecast (alloc +' c_int 1 value) value.;
             alloc_id ::= alloc +' c_int (#|ys| + 1) value.;
             (var x).[-1] :::= make_tag rep.;
             statements (mapi (fun i y => (var x).[i] :::= make_var y) 0 ys))
      | boxed _ _, [] => Err "translate_body: boxed constructor not given arguments"
      end ;;
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((stm_constr.; stm_e), add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (** [[Ecase x cs]] = 
        if (isptr(x)) { switch on x[-1]&255 over boxed cases } 
        else { switch on x>>1 over unboxed cases } *)
  | Ecase x cs =>
    '(boxed_cases, unboxed_cases, fvs_cs, n_cs) <- make_cases translate_body cs ;;
    ret (Scall (Some case_id) isptr [make_var x].;
         Sifthenelse
           (Etempvar case_id bool_ty)
           (Sswitch ((make_var x).[-1] &' make_cint 255 value) boxed_cases)
           (Sswitch (make_var x >>' make_cint 1 value) unboxed_cases),
         add_local_fv fvs_cs x, n_cs)
  (** [[let x = f(y, ..) in e]] =
        store local variables live after call (= locals∩(FV(e)\x)) in roots array
        push frame onto shadow stack
        x = call f (may GC)
        retrieve new limit, alloc from tinfo
        if max_allocs(e) > 0,
          if (max_allocs(e) > limit - alloc) {
            if x live call (<-> x ∈ locals∩FV(e)), store it in roots array
            use GC to create max_allocs(e) words of free space on the heap
            if x live after call, retrieve it from roots (in case moved by GC)
          }
        retrieve other locals from roots array (in case moved by GC)
        pop frame from shadow stack
        [[e]] *)
  | Eletapp x f t ys e =>
    '(stm_e, live_after_call, n_e) <- translate_body e ;;
    let live_minus_x := PS.remove x live_after_call in
    let live_minus_x_list := PS.elements live_minus_x in
    let n_live_minus_x := Z.of_nat (length live_minus_x_list) in
    call <- make_fun_call x f ys ;;
    let retrieve_roots xs := statements (mapi (fun i x => x ::= roots.[i]) 0 xs) in
    let stm :=
      statements (mapi (fun i x => roots.[i] :::= make_var x) 0 live_minus_x_list).;
      frame.next :::= roots +' c_int n_live_minus_x value.;
      tinfo->fp :::= &frame.;
      call.;
      alloc_id ::= tinfo->alloc.;
      limit_id ::= tinfo->limit.;
      let allocs := max_allocs e in
      (if Z.eq_dec allocs 0%Z then Sskip else
       if PS.mem x live_after_call then
         create_space allocs
           (roots.[n_live_minus_x] :::= var x.;
            frame.next :::= roots +' c_int (1 + n_live_minus_x) value)
           (x ::= roots.[n_live_minus_x])
       else
         create_space allocs Sskip Sskip).;
      retrieve_roots live_minus_x_list.;
      tinfo->fp :::= frame.prev.;
      stm_e
    in
    ret (stm, add_local_fvs live_minus_x (f :: ys),
         N.max n_e (N.of_nat (PS.cardinal live_after_call)))
  (** [[let x = y.n in e]] = (x = y[n]; [[e]]) *)
  | Eproj x t n y e =>
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((x ::= (make_var y).[Z.of_N n].; stm_e), add_local_fv (PS.remove x fvs_e) y, n_e)
  | Efun fnd e => Err "translate_body: nested function detected"
  (** [[f(ys)]] =
        ret_temp = call f with arguments ys;
        return ret_temp *)
  | Eapp f t ys =>
    call <- make_fun_call ret_id f ys ;;
    ret ((call.; Sreturn (Some (var ret_id))), add_local_fvs PS.empty (f :: ys), 0)%N
  (** [[let x = p(ys) in e]] = (x = p(ys); [[e]]) *)
  | Eprim x p ys e =>    
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((Scall (Some x) (Evar p (prim_ty (length ys))) (map make_var ys).;
          stm_e),
         add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (** [[halt x]] = (store alloc and limit in tinfo; return x) *)
  | Ehalt x =>
    ret ((tinfo->alloc :::= alloc.;
          tinfo->limit :::= limit.;
          Sreturn (Some (make_var x))),
         add_local_fv PS.empty x, 0)%N
  end%C.

End Body.

Definition definition := (ident * globdef Clight.fundef type)%type.

Definition make_fun (size : Z) (xs locals : list ident) (body : statement) : function :=
  let make_decls := map (fun x => (x, value)) in
  mkfunction value cc_default
             ((tinfo_id, threadInf) :: make_decls (firstn n_param xs))
             (stack_decl size)%list
             ((alloc_id, tptr value) :: (limit_id, tptr value) :: (ret_id, value) ::
              (case_id, bool_ty) :: (roots_temp_id, tptr value) ::
              make_decls (skipn n_param xs ++ locals))%list
             body.

Definition init_shadow_stack_frame size :=
  (roots_temp_id ::= roots_array size.;
   frame.next :::= roots.;
   frame.root :::= roots.;
   frame.prev :::= tinfo->fp)%C.

Fixpoint translate_fundefs (fds : fundefs) (nenv : name_env) : error (list definition) :=
  match fds with
  | Fnil => Ret nil
  | Fcons f t xs e fds' =>
    defs <- translate_fundefs fds' nenv ;;
    match M.get f fenv with
    | None => Err "translate_fundefs: Unknown function name"
    | Some (_, locs) =>
      (** [[f(xs.., ys..) = e]] (where |xs| = n_param) =
            value f(thread struct_info *tinfo, value x, ..) {
              alloc = tinfo->alloc;
              limit = tinfo->limit;
              args = tinfo->args;
              For n_param <= i < |xs|+|ys|,
                y_i = args[locs_i];
              initialize shadow stack frame
              if max_allocs(e) > 0, TODO use unsigned comparison and leave this to compcert?
                if (max_allocs(e) > limit - alloc) {
                  store locals live in e into roots array
                  push frame onto shadow stack
                  use GC to create max_allocs(e) words of free space on the heap
                  retrieve locals from roots array
                  pop frame from shadow stack
                }
              [[e]]
            } *)
      let locals := PS.elements (exp_bv e) in
      let xs_set := union_list PS.empty xs in
      '(body, live_xs, stack_slots) <- translate_body (union_list xs_set locals) nenv e ;;
      let live_xs_list := PS.elements live_xs in 
      let n_live_xs := N.of_nat (length live_xs_list) in
      let allocs := max_allocs e in
      let stack_slots :=
        if Z.eq_dec allocs 0%Z
        then Z.of_N stack_slots
        else Z.of_N (N.max n_live_xs stack_slots)
      in
      let body :=
        alloc_id ::= tinfo->alloc.;
        limit_id ::= tinfo->limit.;
        statements (map (fun '(x, i) => x ::= tinfo->args.[Z.of_N i]) (skipn n_param (combine xs locs))).;
        init_shadow_stack_frame stack_slots.;
        (if Z.eq_dec allocs 0%Z then Sskip else
         create_space allocs
           (statements (mapi (fun i x => roots.[i] :::= var x) 0 live_xs_list).;
            frame.next :::= roots +' c_int (Z.of_N n_live_xs) value.;
            tinfo->fp :::= &frame)
           (statements (mapi (fun i x => x ::= roots.[i]) 0 live_xs_list).;
            tinfo->fp :::= frame.prev)).;
        body
      in
      ret ((f, Gfun (Internal (make_fun stack_slots xs locals body))) :: defs)
    end
  end%C.

(** [[let rec fds in e]] =
      [[fds]]
      value body(struct thread_info *tinfo) {
        alloc = tinfo->alloc;
        limit = tinfo->limit;
        args = tinfo->args;
        initialize shadow stack frame
        if max_allocs(e) > 0,
          use GC to create max_allocs(e) words of free space on the heap
          (no need to push or pop locals because nothing is live yet)
        [[e]]
      } *)
Definition translate_program (fds_e : hoisted_exp) (nenv : name_env) : error (list definition) :=
  let '(fds, e) := fds_e in
  let temps := PS.elements (exp_bv e) in
  funs <- translate_fundefs fds nenv ;;
  '(body, _, slots) <- translate_body (union_list PS.empty temps) nenv e ;;
  let body :=
    (alloc_id ::= tinfo->alloc.;
     limit_id ::= tinfo->limit.;
     init_shadow_stack_frame (Z.of_N slots).;
     let allocs := max_allocs e in
     (if Z.eq_dec allocs 0%Z then Sskip else
      create_space allocs Sskip Sskip).;
     body)%C
  in
  let locals := stack_decl (Z.of_N slots) in
  let temps :=
    (alloc_id, tptr value) :: 
    (limit_id, tptr value) :: 
    (ret_id, value) ::
    (case_id, bool_ty) ::
    (roots_temp_id, tptr value) ::
    map (fun x => (x, value)) temps in
  let fn := mkfunction value cc_default ((tinfo_id, threadInf) :: nil) locals temps body in
  ret ((body_id, Gfun (Internal fn)) :: funs).

End CODEGEN.

(* TODO: Why are these numbers OK? *)
Definition make_tinfo_id := 20%positive.
Definition export_id := 21%positive.

Variable (main_id : ident).
Definition inf_vars :=
  (isptr_id, nNamed "is_ptr") ::
  (args_id, nNamed "args") ::
  (alloc_id, nNamed "alloc") ::
  (nalloc_id, nNamed "nalloc") ::
  (limit_id, nNamed "limit") ::
  (gc_id, nNamed "garbage_collect") ::
  (main_id, nNamed "main") ::
  (body_id, nNamed "body") ::
  (thread_info_id, nNamed "thread_info") ::
  (tinfo_id, nNamed "tinfo") ::
  (stack_frame_id, nNamed "stack_frame") ::
  (frame_id, nNamed "frame") ::
  (roots_id, nNamed "roots") ::
  (fp_id, nNamed "fp") ::
  (next_fld, nNamed "next") ::
  (root_fld, nNamed "root") ::
  (prev_fld, nNamed "prev") :: 
  (make_tinfo_id, nNamed "make_tinfo") ::
  (export_id, nNamed "export") ::
  (builtin_unreachable_id, nNamed "__builtin_unreachable") ::
  (ret_id, nNamed "ret") ::
  (case_id, nNamed "case_id") ::
  (roots_temp_id, nNamed "roots_temp") ::
  [].

Definition add_inf_vars (nenv : name_env) : name_env :=
  List.fold_left (fun nenv '(x, name) => M.set x name nenv) inf_vars nenv.

Definition ensure_unique (l : M.t name) : M.t name :=
  M.map (fun x n =>
          match n with
          | nAnon => nAnon
          | nNamed s => nNamed (append s (append "_"%string (show_pos x)))
          end) l.

Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  let make_tinfo_fn := EF_external "make_tinfo" (mksignature nil (Some ast_value) cc_default) in
  (make_tinfo_id, Gfun (External make_tinfo_fn Tnil threadInf cc_default)).
                  
Definition export_rec : positive * globdef Clight.fundef type :=
  let sig := mksignature (cons ast_value nil) (Some ast_value) cc_default in
  let export_fn := EF_external "export" sig in
  (export_id, Gfun (External export_fn (Tcons threadInf Tnil) (tptr value) cc_default)).

Section Check. (* Just for debugging purposes. TODO eventually delete*)

Context (fenv : fun_env) (nenv : name_env).

Fixpoint check_tags' (e : exp) (log : list string) :=
  match e with
  | Econstr _ _ _ e | Eproj _ _ _ _ e | Eprim _ _ _ e => check_tags' e log
  | Ecase _ bs => fold_left (fun a '(_, e) => check_tags' e a) bs log
  | Eletapp x f t ys e =>
    let s :=
      match M.get t fenv with
      | Some (n, l) =>
        "LetApp: Function " ++ pretty_fun_name f nenv ++ " has arity " ++ show_binnat n ++
        " " ++ nat2string10 (length l)
      | None => "LetApp: Function " ++ pretty_fun_name f nenv ++ " was not found in fun_env"
      end
    in check_tags' e (s :: log)
  | Efun B e =>
    let s := check_tags_fundefs' B log in
    check_tags' e s
  | Eapp f t ys =>
    let s :=
      match M.get t fenv with
      | Some (n, l) =>
        "App: Function " ++ pretty_fun_name f nenv ++ " has arity " ++ show_binnat n ++
        " " ++ nat2string10 (length l)
      | None => "App: Function " ++ pretty_fun_name f nenv ++ " was not found in fun_env"
      end
    in s :: log
  | Ehalt x => log
  end
with check_tags_fundefs' (B : fundefs) (log : list string) : list string :=
  match B with
  | Fcons f t xs e B' =>
    let s :=
      match M.get t fenv with
      | Some (n, l) =>
        "Definition " ++ pretty_fun_name f nenv ++ " has tag " ++ show_pos t ++ Pipeline_utils.newline ++
        "Def: Function " ++ pretty_fun_name f nenv ++ " has arity " ++ show_binnat n ++ " " ++ nat2string10 (length l)
      | None => "Def: Function " ++ pretty_fun_name f nenv ++ " was not found in fun_env"
      end
    in
    let log := check_tags_fundefs' B' (s :: log) in
    check_tags' e log
  | Fnil => log
  end.

Definition check_tags (e : exp) :=
  String.concat Pipeline_utils.newline (rev (check_tags' e [])).

End Check.

Definition make_decl (nenv : name_env) (def : definition) (gv : bool) : option definition :=
  match def with
  | (f_id, Gfun (Internal (mkfunction ret_ty cc params vars temps body))) =>
    match M.get f_id nenv with
    | Some (nNamed f_string) =>
      let param_tys := type_of_params params in
      let ext_fn := EF_external f_string (signature_of_type param_tys ret_ty cc) in
      Some (f_id, Gfun (External ext_fn param_tys ret_ty cc))
    | _ => None
    end
  | (v_id, Gvar (mkglobvar v_info v_init v_r v_v)) =>
    if gv then Some (v_id, Gvar (mkglobvar v_info nil v_r v_v)) else None
  | _ => None
  end.

Fixpoint make_decls (nenv : name_env) (defs : list definition) (gv : bool) : list definition :=
  match defs with
  | def :: defs =>
    let decls := make_decls nenv defs gv in
    match make_decl nenv def gv with
    | Some decl => decl :: decls
    | None => decls
    end
  | nil => nil
  end.

Definition body_decl : definition :=
  let param_tys := type_of_params ((tinfo_id, threadInf):: nil) in
  let ext_fn := EF_external "body" (signature_of_type param_tys value cc_default) in
  (body_id, Gfun (External ext_fn param_tys value cc_default)).

Definition make_defs fds_e cenv nenv : error (list definition) :=
  let global_defs := 
    let gc_fn := EF_external "garbage_collect" (mksignature (ast_value :: nil) None cc_default) in
    let is_ptr_fn := EF_external "is_ptr" (mksignature (ast_value :: nil) None cc_default) in
    (gc_id, Gfun (External gc_fn (Tcons threadInf Tnil) Tvoid cc_default)) ::
    (isptr_id, Gfun (External is_ptr_fn (Tcons value Tnil) type_bool cc_default)) ::
    nil
  in
  let fenv := compute_fun_env fds_e in
  fun_defs' <- translate_program cenv fenv fds_e nenv ;;
  ret (global_defs ++ rev fun_defs')%list.

Definition make_prog (defs : list definition) (main : ident) (add_comp : bool) : error Clight.program :=
  let composites := if add_comp then composites else nil in
  match Ctypes.make_program composites defs (body_id :: nil) main with
  | Error e => Err "make_prog: Ctypes.make_program failed"
  | OK p => ret p
  end.

Definition compile e cenv nenv : error (name_env * Clight.program * Clight.program) * string :=
  let log := "" in
  (* let log :=
       cps_show.show_exp nenv0 cenv false e ++
       Pipeline_utils.newline ++ Pipeline_utils.newline ++
       check_tags fenv nenv0 e in *)
  let res :=
    header <- make_prog [body_decl] main_id false ;;
    let nenv := add_inf_vars (ensure_unique nenv) in
    defs <- make_defs (make_hoisted_exp e) cenv nenv ;;
    impl <- make_prog (make_tinfo_rec :: export_rec :: make_decls nenv defs false ++ defs)%list main_id true ;;
    ret (nenv, header, impl)
  in (res, log).

Section PROOF.

Definition get_ith {A} := @Coqlib.list_nth_z A.

Fixpoint set_ith {A} (xs : list A) (i : Z) (y : A) : list A :=
  match xs with
  | [] => []
  | x :: xs => if Z.eq_dec i 0 then y :: xs else x :: set_ith xs (Z.pred i) y
  end.

Lemma get_ith_range {A} (xs : list A) i y :
  get_ith xs i = Some y ->
  (0 <= i < #|xs|)%Z.
Proof.
  revert i; induction xs as [|x xs IHxs]; [easy|intros* Hget].
  cbn in Hget; destruct (Coqlib.zeq i 0) as [|Hne]; [subst|];
  change (length (x :: xs)) with (S (length xs)); [lia|].
  specialize (IHxs (Z.pred i) Hget); lia.
Qed.

Lemma set_ith_cons {A} (x : A) xs i y :
  set_ith (x :: xs) i y = if Z.eq_dec i 0 then y :: xs else x :: set_ith xs (Z.pred i) y.
Proof. reflexivity. Qed.

Lemma set_ith_len {A} (y : A) xs i :
  length (set_ith xs i y) = length xs.
Proof.
  revert i; induction xs as [|x xs IHxs]; [auto|intros i; cbn].
  destruct (Z.eq_dec i 0) as [|Hne]; [now subst|now cbn].
Qed.

Lemma get_ith_in_range {A} (xs : list A) i :
  (0 <= i < #|xs|)%Z ->
  exists x, get_ith xs i = Some x.
Proof.
  revert i; induction xs as [|x xs IHxs]; [cbn; lia|intros i Hi].
  cbn in *; destruct (Coqlib.zeq i 0); [eexists; reflexivity|apply IHxs; lia].
Qed.

Lemma ith_gss {A} (xs : list A) i y :
  (0 <= i < #|xs|)%Z ->
  get_ith (set_ith xs i y) i = Some y.
Proof.
  revert i; induction xs as [|x xs IHxs]; [cbn; lia|intros i Hi].
  cbn; destruct (Z.eq_dec i 0) as [Heq|Hne]; [now subst|].
  cbn in *; destruct (Coqlib.zeq i 0); [easy|apply IHxs; lia].
Qed.

Lemma ith_gso {A} (xs : list A) i j y :
  i <> j ->
  get_ith (set_ith xs i y) j = get_ith xs j.
Proof.
  revert i j; induction xs as [|x xs IHxs]; [easy|intros i j Hne].
  cbn; destruct (Z.eq_dec i 0); [subst|].
  - cbn; now destruct (Coqlib.zeq j 0).
  - cbn; destruct (Coqlib.zeq j 0); [easy|now rewrite IHxs].
Qed.

Lemma get_ith_prefix {A} (vs ws : list A) i :
  (i < #|vs|)%Z ->
  get_ith (vs ++ ws) i = get_ith vs i.
Proof.
  revert i; induction vs as [|v vs IHvs]; intros i.
  - cbn in *; intros H.
    destruct (get_ith ws i) as [w|] eqn:Hget; [|auto].
    apply get_ith_range in Hget; lia.
  - cbn in *; destruct (Coqlib.zeq i 0) as [|Hne]; [now subst|intros H].
    now rewrite IHvs; [|lia].
Qed.

Lemma get_ith_suffix {A} (vs ws : list A) i :
  (#|vs| <= i)%Z ->
  get_ith (vs ++ ws) i = get_ith ws (i - #|vs|).
Proof.
  revert i; induction vs as [|v vs IHvs]; intros i; cbn.
  - now replace (Z.of_nat 0 + i)%Z with i by lia.
  - destruct (Coqlib.zeq i 0) as [|Hne]; [now subst|intros H].
    rewrite IHvs; [|lia]; f_equal; lia.
Qed.

Definition All := fold_right and True.
Definition Ex := fold_right or False.
Definition Bigcup {A} := fold_right (Union _) (Empty_set A).

Lemma All_app xs ys : All (xs ++ ys) <-> All xs /\ All ys. Proof. induction xs; cbn; tauto. Qed.
Lemma All_cons x xs : All (x :: xs) <-> x /\ All xs. Proof. reflexivity. Qed.

Ltac sets := eauto with Ensembles_DB Decidable_DB.

Lemma Bigcup_app {A} xs ys : @Bigcup A (xs ++ ys) <--> Bigcup xs :|: Bigcup ys.
Proof. induction xs; cbn; [sets|]. rewrite IHxs; sets. Qed.
Lemma Bigcup_cons {A} x xs : @Bigcup A (x :: xs) <--> x :|: Bigcup xs. Proof. reflexivity. Qed.

Lemma fold_left_cons {A B} (f : A -> B -> A) x xs z :
  fold_left f (x :: xs) z = fold_left f xs (f z x).
Proof. reflexivity. Qed.

Lemma fold_left_ext_eq {A B} (f g : A -> B -> A) xs z :
  (forall z x, List.In x xs -> f z x = g z x) ->
  fold_left f xs z = fold_left g xs z.
Proof.
  revert z; induction xs as [|x xs IHxs]; [auto|intros z Heq; cbn].
  rewrite Heq by now left.
  intuition.
Qed.

Definition Forall2' {A B} (R : A -> B -> Prop) :=
  fix go xs ys :=
    match xs, ys with
    | [], [] => True
    | x :: xs, y :: ys => R x y /\ go xs ys
    | _, _ => False
    end.

Lemma Forall2'_spec {A B} (R : A -> B -> Prop) xs ys :
  Forall2' R xs ys <-> Forall2 R xs ys.
Proof.
  split; intros H.
  - generalize dependent ys; induction xs as [|x xs IHxs];
    destruct ys as [|y ys]; now inversion 1.
  - induction H; now cbn.
Qed.

Definition Forall3 {A B C} (R : A -> B -> C -> Prop) :=
  fix go xs ys zs :=
    match xs, ys, zs with
    | [], [], [] => True
    | x :: xs, y :: ys, z :: zs => R x y z /\ go xs ys zs
    | _, _, _ => False
    end.
(* TODO move the above lemmas/definitions to more proper places *)

Variable (pr : prims).
Variable (cenv : ctor_env).
Variable (fenv : fun_env).

(** * Basic facts about the code generator *)

Lemma bind_ret {A B} x (f : A -> error B) : (x <- Ret x ;; f x) = f x.
Proof. reflexivity. Qed.

Arguments Monad.bind : simpl never.
Arguments add_local_fvs : simpl never.
Arguments exp_fv : simpl never.
Arguments PS.cardinal : simpl never.

Ltac bind_step_in H x Hx :=
  match type of H with
  | context [_ <- ?e ;; _] => destruct e as [|x] eqn:Hx; [inv H|rewrite bind_ret in H]
  end.

Ltac bind_step x Hx :=
  match goal with
  | |- match _ <- ?e ;; _ with
      | Err _ => True
      | Ret _ => _
      end =>
    destruct e as [|x] eqn:Hx; [exact I|rewrite bind_ret]
  end.

Lemma add_local_fv_ok locals fvs x :
  FromSet (add_local_fv locals fvs x) <--> FromSet fvs :|: ([set x] :&: FromSet locals).
Proof.
  unfold add_local_fv; destruct (PS.mem x locals) eqn:Hin; [rewrite PS.mem_spec in Hin|].
  - rewrite FromSet_add.
    rewrite Intersection_Same_set; [apply Union_commut|].
    apply Singleton_Included.
    eapply FromSet_complete; sets.
  - assert (~ PS.In x locals) by (intros Hin'; now rewrite <- PS.mem_spec in Hin').
    assert (~ x \in FromSet locals) by (intros Hin'; now eapply FromSet_sound in Hin').
    rewrite Intersection_Disjoint; sets.
Qed.

Lemma add_local_fvs_ok locals fvs xs :
  FromSet (add_local_fvs locals fvs xs) <--> FromSet fvs :|: (FromList xs :&: FromSet locals).
Proof.
  revert fvs; induction xs as [|x xs IHxs]; intros fvs.
  - cbn; rewrite FromList_nil, Intersection_Empty_set_abs_l; sets.
  - unfold add_local_fvs in *; cbn; rewrite IHxs, add_local_fv_ok, FromList_cons.
    rewrite Intersection_Union_distr; sets.
Qed.

Lemma FromSet_remove x s : FromSet (PS.remove x s) <--> FromSet s \\ [set x].
Proof.
  unfold Same_set, FromSet, FromList; split; intros y Hy; unfold In in *.
  - rewrite <- MCList.InA_In_eq, PS.elements_spec1, PS.remove_spec in Hy.
    destruct Hy; split; [unfold In|intros Hin; inv Hin; auto].
    now rewrite <- MCList.InA_In_eq, PS.elements_spec1.
  - inv Hy; unfold In in *; rewrite <- MCList.InA_In_eq, PS.elements_spec1, PS.remove_spec in *.
    split; auto; intros Heq; subst; now apply H0.
Qed.

Lemma Intersection_extract_Setminus {U} (S1 S2 S3 : Ensemble U) :
  (S1 \\ S2) :&: S3 <--> (S1 :&: S3) \\ S2.
Proof. split; intros x Hx; inv Hx; now inv H. Qed.

Fixpoint translate_body_fvs locals nenv e {struct e} :
  match translate_body cenv fenv locals nenv e with
  | Ret (_, fvs, _) => FromSet fvs <--> occurs_free e :&: FromSet locals
  | _ => True
  end.
Proof.
  rename translate_body_fvs into IHe; destruct e.
  - cbn. bind_step rep Hrep.
    destruct rep as [t|t a], l as [|y ys]; try exact I; rewrite bind_ret;
    bind_step result He; destruct result as [[? fvs_e] ?];
    specialize (IHe locals nenv e); rewrite He in IHe;
    rewrite add_local_fvs_ok, FromSet_remove; normalize_occurs_free;
    rewrite Intersection_Union_distr, Union_commut;
    apply Same_set_Union_compat; sets;
    rewrite IHe, Intersection_extract_Setminus; sets.
  - cbn. bind_step cases Hcases; destruct cases as [[[??] fvs_cs] ?].
    rewrite add_local_fv_ok.
    revert dependent n; revert l0 l1 fvs_cs;
    induction l as [| [c e] ces IHces]; intros l0 l1 fvs_cs n Hcases; cbn in *.
    + inv Hcases; rewrite FromSet_empty; normalize_occurs_free; sets.
    + bind_step_in Hcases e' He'; destruct e' as [[? fvs_e] ?].
      bind_step_in Hcases ces' Hces'; destruct ces' as [[[??]fvs_ces]?].
      specialize (IHces _ _ _ _ eq_refl).
      bind_step_in Hcases rep Hrep.
      assert (fvs_cs = PS.union fvs_e fvs_ces) by (now destruct rep); subst.
      specialize (IHe locals nenv e); rewrite He' in IHe.
      normalize_occurs_free; rewrite FromSet_union, <- Union_assoc, IHces, IHe, !Intersection_Union_distr.
      split; repeat apply Union_Included; sets.
      eapply Included_trans; [|apply Included_Union_r].
      apply Included_Intersection_compat; sets.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    normalize_occurs_free; rewrite add_local_fv_ok, FromSet_remove, IHe.
    rewrite !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; sets.
    now rewrite Intersection_extract_Setminus.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    bind_step call Hcall; normalize_occurs_free.
    specialize (IHe locals nenv e); rewrite He in IHe.
    rewrite add_local_fvs_ok, FromSet_remove, IHe, FromList_cons, !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; sets.
    now rewrite Intersection_extract_Setminus.
  - exact I.
  - cbn. bind_step call Hcall. normalize_occurs_free.
    rewrite add_local_fvs_ok, FromList_cons, !Intersection_Union_distr, Union_commut, FromSet_empty.
    split; repeat apply Union_Included; sets.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    normalize_occurs_free; rewrite add_local_fvs_ok, FromSet_remove, IHe.
    rewrite !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; sets.
    now rewrite Intersection_extract_Setminus.
  - cbn. normalize_occurs_free; rewrite add_local_fv_ok, FromSet_empty; sets.
Qed.

Lemma max_ge_or m n p :
  N.to_nat (N.max m n) >= p <-> N.to_nat m >= p \/ N.to_nat n >= p.
Proof. lia. Qed.

Definition max_live locals e n :=
  forall C x f t ys e', e = C |[ Eletapp x f t ys e' ]| ->
  n >= PS.cardinal (PS.inter (exp_fv e') locals).

Fixpoint translate_body_n_slots locals nenv e {struct e} :
  match translate_body cenv fenv locals nenv e with
  | Ret (_, _, n_slots) => max_live locals e (N.to_nat n_slots)
  | _ => True
  end.
Proof.
  unfold max_live; rename translate_body_n_slots into IHe; destruct e.
  - cbn. bind_step rep Hrep.
    destruct rep as [t|t a], l as [|y' ys']; try exact I; rewrite bind_ret;
    bind_step result He; destruct result as [[? fvs_e] ?];
    specialize (IHe locals nenv e); rewrite He in IHe;
    intros C x f ft ys e' Hsubterm; destruct C; inv Hsubterm; now eapply IHe.
  - cbn. bind_step cases Hcases; destruct cases as [[[??] fvs_cs] ?].
    revert dependent n; revert l0 l1 fvs_cs;
    induction l as [| [c e] ces IHces]; intros l0 l1 fvs_cs n Hcases; cbn in *.
    + intros C x f t ys e' Hsubterm; destruct C; inv Hsubterm.
      apply (f_equal (@length _)) in H1; rewrite app_length in H1; cbn in H1; lia.
    + bind_step_in Hcases e' He'; destruct e' as [[? fvs_e] ?].
      bind_step_in Hcases ces' Hces'; destruct ces' as [[[??]fvs_ces]?].
      specialize (IHces _ _ _ _ eq_refl).
      bind_step_in Hcases rep Hrep.
      assert (n = N.max n0 n1) by (now destruct rep); subst; clear Hcases Hrep.
      specialize (IHe locals nenv e); rewrite He' in IHe.
      intros C x f t ys e' Hsubterm; destruct C; inv Hsubterm.
      destruct l3 as [| [c_ e_] ces_l].
      * inv H1. rewrite max_ge_or; left; now eapply IHe.
      * inv H1. rewrite max_ge_or; right.
        now eapply (IHces (Ecase_c v0 ces_l c0 C l4)).
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    intros C x f ft ys e' Hsubterm; destruct C; inv Hsubterm; now eapply IHe.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    bind_step call Hcall.
    specialize (IHe locals nenv e); rewrite He in IHe.
    intros C x g gt ys e' Hsubterm; destruct C; inv Hsubterm.
    2:{ rewrite max_ge_or; left; now eapply IHe. }
    rewrite max_ge_or, Nnat.Nat2N.id; right.
    pose proof translate_body_fvs locals nenv e' as Hfvs; rewrite He in Hfvs.
    rewrite exp_fv_correct, <- FromSet_intersection in Hfvs.
    apply Same_set_From_set, Proper_carinal in Hfvs; lia.
  - exact I.
  - cbn. bind_step call Hcall; intros C x g gt ys e' Hsubterm; destruct C; inv Hsubterm.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    intros C x f ft ys e' Hsubterm; destruct C; inv Hsubterm; now eapply IHe.
  - cbn. intros C x g gt ys e' Hsubterm; destruct C; inv Hsubterm.
Qed.

(** * Tools for reasoning about Clight *)

(** The C program produced by the code generator *)
Variable (prog : program).

(** Its global environment *)
Let prog_genv : genv := globalenv prog.

(** Bigstep evaluation of statements: unlike exec_stmt,
    - Force the trace to be empty
    - Force outcome to be Out_return (Some (v, value)) *)
Definition texec := fun '(env, tenv, m, stmt) '(tenv', m', v) =>
  exec_stmt prog_genv env tenv m stmt Events.E0 
            tenv' m' (Out_return (Some (v, value))).
Infix "⇓" := texec (at level 80, no associativity).

(** Bigstep evaluation of l- and r-values *)
Definition eval_expr_operator := fun '(env, tenv, m, e) v =>
  eval_expr prog_genv env tenv m e v.
Definition eval_lvalue_operator := fun '(env, tenv, m, e) '(b, o) =>
  eval_lvalue prog_genv env tenv m e b o.
Infix "⇓ᵣ" := eval_expr_operator (at level 80).
Infix "⇓ₗ" := eval_lvalue_operator (at level 80).

(** (env1, tenv1, m1, stmt1) "reduces to" (env2, tenv2, m2, stmt2) if every terminating
    execution starting from (env2, tenv2, m2, stmt2) can be used to construct an execution
    starting from (env1, tenv1, m1, stmt1) *)
Definition Clight_state_red := fun '(env1, tenv1, m1, stmt1) '(env2, tenv2, m2, stmt2) =>
  forall tenv' m' out,
  exec_stmt prog_genv env2 tenv2 m2 stmt2 Events.E0 tenv' m' out ->
  exec_stmt prog_genv env1 tenv1 m1 stmt1 Events.E0 tenv' m' out.
Infix "-->" := Clight_state_red (at level 80).

Lemma Cred_trans s1 s2 s3 :
  s1 --> s2 -> s2 --> s3 -> s1 --> s3.
Proof. destruct s1 as [[[??]?]?], s2 as [[[??]?]?], s3 as [[[??]?]?]; cbn; eauto. Qed.

Lemma Cred_seq_assoc env tenv m s1 s2 s3 :
  (env, tenv, m, ((s1.; s2).; s3))%C --> (env, tenv, m, (s1.; (s2.; s3)))%C.
Proof.
  intros tenv' m' v H; unfold "⇓" in *; inv H.
  - inv H10.
    + rewrite <- Events.Eapp_assoc. do 2 (eapply exec_Sseq_1; eauto).
    + constructor; [|easy]. eapply exec_Sseq_1; eauto.
  - now do 2 (constructor; [|easy]).
Qed.

Lemma Cred_skip env tenv m s :
  (env, tenv, m, (Sskip.; s))%C --> (env, tenv, m, s).
Proof.
  intros tenv' m' v H; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; [constructor|eauto].
Qed.

Lemma Cred_set env tenv m x v a s :
  (env, tenv, m, a) ⇓ᵣ v ->
  (env, tenv, m, (x ::= a.; s))%C --> (env, M.set x v tenv, m, s).
Proof.
  intros; intros ??? Hexec; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto; econstructor; eauto.
Qed.

Lemma Cred_set' env tenv m x v a :
  (env, tenv, m, a) ⇓ᵣ v ->
  (env, tenv, m, x ::= a) --> (env, M.set x v tenv, m, Sskip).
Proof. intros; intros ??? Hexec; inv Hexec; constructor; auto. Qed.

Lemma Cred_assign env tenv m a1 a2 v_pre v b o m' s :
  (env, tenv, m, a1) ⇓ₗ (b, o) ->
  (env, tenv, m, a2) ⇓ᵣ v_pre ->
  sem_cast v_pre (typeof a2) (typeof a1) m = Some v ->
  assign_loc prog_genv (typeof a1) m b o v m' ->
  (env, tenv, m, (a1 :::= a2.; s))%C --> (env, tenv, m', s).
Proof.
  intros; intros ??? Hexec; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto; econstructor; eauto.
Qed.

Lemma Cred_if env tenv m a v b s1 s2 s :
  (env, tenv, m, a) ⇓ᵣ v ->
  bool_val v (typeof a) m = Some b ->
  (env, tenv, m, (Sifthenelse a s1 s2.; s))%C -->
  (env, tenv, m, ((if b then s1 else s2).; s))%C.
Proof.
  intros; intros ??? Hexec; unfold "⇓"; inv Hexec.
  - eapply exec_Sseq_1; eauto; econstructor; eauto.
  - constructor; eauto; econstructor; eauto.
Qed.

Lemma Cred_if' env tenv m a v b s1 s2 :
  (env, tenv, m, a) ⇓ᵣ v ->
  bool_val v (typeof a) m = Some b ->
  (env, tenv, m, Sifthenelse a s1 s2) -->
  (env, tenv, m, if b then s1 else s2).
Proof. intros; intros ??? Hexec; unfold "⇓"; econstructor; eauto. Qed.

(** ** Memory & memory predicates *)

(** The code generator only emits code that loads/stores in single-word segments *)
Definition word_chunk := if Archi.ptr64 then Mint64 else Mint32.
Definition word_size := size_chunk word_chunk.
Definition load := Mem.load word_chunk.
Definition store := Mem.store word_chunk.

(** If 64-bit, Coq values will be represented using only Vlong, Vptr, and Vundef.
    If 32-bit, Coq values will be represented using only Vint, Vptr, and Vundef. *)
Definition val_wf v :=
  if Archi.ptr64 then match v with Vundef | Vlong _ | Vptr _ _ => True | _ => False end
  else match v with Vundef | Values.Vint _ | Vptr _ _ => True | _ => False end.

Lemma val_wf_load_result v :
  val_wf v -> Val.load_result word_chunk v = v.
Proof.
  unfold val_wf, Val.load_result, word_chunk;
  now destruct v, Archi.ptr64.
Qed.

Definition address := (block * Z)%type.

Inductive mpred :=
| Mapsto (bo : address) (p : permission) (vs : list Values.val)
| Sepcon (P Q : mpred)
| Exists {A} (F : A -> mpred)
| Mem (m : mem)
| Pure (P : Prop).
Notation "bo '↦_{' p '}' vs" := (Mapsto bo p vs) (at level 77).
Infix "⋆" := Sepcon (at level 78, right associativity).
Notation "'∃' x .. y , p" :=
  (Exists (fun x => .. (Exists (fun y => p)) ..))
  (at level 78, x binder, y binder, right associativity).

Definition mempty : mpred := Mem Mem.empty.

Definition dom_mem (m : mem) : Ensemble address :=
  fun '(b, o) => Mem.perm m b o Max Nonempty.

Definition dom_mapsto (b : block) (o : Z) (vs : list Values.val) :=
  fun '(b', o') => b = b' /\ (o <= o' < o + #|vs|*word_size)%Z.

Reserved Notation "m |=_{ S } P" (at level 79).
Fixpoint mpred_denote_aux (P : mpred) (S : Ensemble address) (m : mem) : Prop :=
  match P with
  | (b, o) ↦_{p} vs =>
    Mem.range_perm m b o (o + #|vs|*word_size) Cur p /\
    S <--> dom_mapsto b o vs /\
    All (map val_wf vs) /\
    (forall i v, get_ith vs i = Some v -> load m b (o + i*word_size) = Some v) /\
    (o >= 0)%Z /\ (o + #|vs|*word_size <= O.max_unsigned)%Z /\ (align_chunk word_chunk | o)%Z (* all addresses are representable *)
  | P ⋆ Q =>
    exists S1 S2, 
    S <--> S1 :|: S2 /\
    Disjoint _ S1 S2 /\
    m |=_{S1} P /\
    m |=_{S2} Q
  | Exists _ F => exists x, m |=_{S} F x
  | Mem m' => S <--> dom_mem m' /\ Mem.unchanged_on (fun b o => S (b, o)) m' m
  | Pure P => S \subset dom_mem m /\ P
  end
where "m |=_{ S } P" := (mpred_denote_aux P S m).

Definition mpred_denote (P : mpred) (m : mem) : Prop := m |=_{dom_mem m} P.
Notation "m |= P" := (mpred_denote P m) (at level 79).

Definition entails P Q := forall S m, m |=_{S} P -> m |=_{S} Q.
Infix "|--" := entails (at level 79).

Notation "P 'WITH' Q" := (∃ (_ : Q), P) (at level 78).

Ltac split_ands :=
  repeat match goal with |- _ /\ _ => split end.

Lemma sepcon_assoc P Q R S m :
  m |=_{S} (P ⋆ Q) ⋆ R <-> m |=_{S} P ⋆ (Q ⋆ R).
Proof.
  split; cbn.
  - intros [S1 [S2 [HS [HD [[S11 [S12 [HS1 [HD1 [HP HQ]]]]] HR]]]]].
    exists S11, (S12 :|: S2); rewrite HS, HS1 in *; split_ands; sets.
    exists S12, S2; sets.
  - intros [S1 [S2 [HS [HD [HP [S21 [S22 [HS2 [HD2 [HQ HR]]]]]]]]]].
    exists (S1 :|: S21), S22; rewrite HS, HS2 in *; split_ands; sets.
    exists S1, S21; sets.
Qed.

Lemma concretize_word_size : (word_size = 4 \/ word_size = 8)%Z.
Proof. unfold word_size, word_chunk; destruct Archi.ptr64; cbn; lia. Qed.

Arguments "+"%Z : simpl never.
Fixpoint max_allocs_nonneg e :
  (max_allocs e >= 0)%Z.
Proof.
  rename max_allocs_nonneg into IHe.
  destruct e; cbn; try solve [clear IHe; lia|apply IHe].
  - destruct l; [apply IHe|cbn; specialize (IHe e); lia].
  - remember 0%Z as init eqn:Hinit; rewrite Hinit in IHe; rewrite Hinit at 2.
    replace 0%Z with (Z.min init 0) by lia.
    clear Hinit; revert init; induction l as [| [c e] ces IHces]; [cbn; lia|intros init].
    cbn; specialize (IHe e).
    specialize (IHces (Z.max (max_allocs e) init)); lia.
Qed.

Ltac superlia :=
  unfold ident, PS.elt, cps.var, M.elt, PTree.elt in *;
  repeat match goal with
  | |- context [Z.of_nat ?e] =>
    lazymatch goal with
    | H : (0 <= Z.of_nat e)%Z |- _ => fail
    | _ => pose proof (Zle_0_nat e)
    end
  | H : context [Z.of_nat ?e] |- _ =>
    lazymatch goal with
    | H : (0 <= Z.of_nat e)%Z |- _ => fail
    | _ => pose proof (Zle_0_nat e)
    end
  | H : context [max_allocs ?e] |- _ =>
    lazymatch goal with
    | H : (max_allocs e >= 0)%Z |- _ => fail
    | _ => pose proof (max_allocs_nonneg e)
    end
  | H : get_ith ?xs ?i = Some _ |- _ =>
    lazymatch goal with
    | H : (0 <= i < #|xs|)%Z |- _ => fail
    | _ => pose proof (get_ith_range _ _ _ H)
    end
  | |- context [length (set_ith ?xs ?i ?y)] =>
    lazymatch goal with
    | H : length (set_ith xs i y) = length xs |- _ => fail
    | _ => pose proof (set_ith_len y xs i)
    end
  | H : context [length (set_ith ?xs ?i ?y)] |- _ =>
    lazymatch goal with
    | H : length (set_ith xs i y) = length xs |- _ => fail
    | _ => pose proof (set_ith_len y xs i)
    end
  end;
  (repeat rewrite app_length in *);
  change (size_chunk word_chunk) with word_size in *;
  rewrite ?Z.mul_add_distr_l, ?Z.mul_add_distr_r in *;
  (pose proof concretize_word_size);
  (pose proof O.max_signed_unsigned);
  (pose proof O.min_signed_neg);
  (pose proof O.wordsize_max_unsigned);
  (pose proof O.max_signed_pos);
  lia.

Lemma dom_mapsto_nil b o :
  dom_mapsto b o [] <--> Empty_set _.
Proof.
  unfold dom_mapsto; apply Ensemble_iff_In_iff; intros [b' o'].
  rewrite In_Empty_set; unfold In; cbn; superlia.
Qed.

Arguments Z.of_nat : simpl never.
Lemma dom_mapsto_cons b o v vs :
  dom_mapsto b o (v :: vs) <-->
  dom_mapsto b o [v] :|: dom_mapsto b (o + word_size) vs.
Proof.
  unfold dom_mapsto; apply Ensemble_iff_In_iff; intros [b' o'].
  rewrite In_or_Iff_Union; unfold In; cbn; superlia.
Qed.

Lemma dom_mapsto_app b o vs ws :
  dom_mapsto b o (vs ++ ws)%list <-->
  dom_mapsto b o vs :|: dom_mapsto b (o + #|vs|*word_size) ws.
Proof.
  unfold dom_mapsto; apply Ensemble_iff_In_iff; intros [b' o'].
  rewrite app_length, In_or_Iff_Union; unfold In; cbn; superlia.
Qed.

Lemma Disjoint_pair_simpl {A B} (S1 S2 : Ensemble (A * B)) :
  Disjoint _ S1 S2 <-> forall x y, ~ (S1 (x, y) /\ S2 (x, y)).
Proof.
  split; [intros [Hdis] x y Hxy; now destruct (Hdis (x, y))|].
  intros H; constructor; intros [x y] Hxy; apply (H x y); now inv Hxy.
Qed.

Lemma dom_mapsto_Disjoint_simpl b1 o1 vs1 b2 o2 vs2 :
  Disjoint _ (dom_mapsto b1 o1 vs1) (dom_mapsto b2 o2 vs2) <->
  b1 <> b2 \/
  #|vs1| = 0%Z \/
  #|vs2| = 0%Z \/
  (o1 + #|vs1|*word_size <= o2)%Z \/
  (o2 + #|vs2|*word_size <= o1)%Z.
Proof.
  rewrite Disjoint_pair_simpl; unfold dom_mapsto.
  split; [intros H|subst; cbn in *; superlia].
  destruct (Z_le_dec o1 o2).
  + specialize (H b1 o2); subst; cbn in *; superlia.
  + specialize (H b1 o1); subst; cbn in *; superlia.
Qed.

Lemma align_word_chunk_size : align_chunk word_chunk = word_size.
Proof. now unfold word_size, word_chunk; destruct Archi.ptr64. Qed.

Lemma mapsto_app S b o p vs ws m :
  m |=_{S} ((b, o) ↦_{p} vs ++ ws)%list <->
  m |=_{S} ((b, o) ↦_{p} vs) ⋆ ((b, o + #|vs|*word_size) ↦_{p} ws)%Z.
Proof.
  unfold mpred_denote_aux; split.
  - intros [Hperm [Hdom [Hwf [Hloads Hbounds]]]].
    rewrite dom_mapsto_app, map_app, All_app, app_length in *.
    do 2 eexists; split; [eassumption|].
    split_ands; try (sets||tauto||cbn in *; superlia||
                     unfold Mem.range_perm in *; intros o' Ho'; apply Hperm; superlia).
    + rewrite dom_mapsto_Disjoint_simpl; superlia.
    + intros i v Hget.
      apply Hloads; rewrite <- Hget.
      eapply get_ith_prefix, get_ith_range, Hget.
    + intros i v Hget.
      replace (o + #|vs|*word_size + i*word_size)%Z
        with (o + (#|vs| + i)*word_size)%Z by lia.
      apply Hloads. pose proof Hget as Hget'.
      apply get_ith_range in Hget'.
      rewrite get_ith_suffix by lia.
      rewrite <- Hget; f_equal; lia.
    + apply Z.divide_add_r; [easy|].
      rewrite align_word_chunk_size.
      apply Z.divide_factor_r.
  - intros [S1 [S2 [HS [HD [[Hperm1 [HS1 [Hwf1 [Hload1 Hbound1]]]]
                            [Hperm2 [HS2 [Hwf2 [Hload2 Hbound2]]]]]]]]].
    rewrite dom_mapsto_app, map_app, All_app, app_length, HS, HS1, HS2 in *.
    split_ands; try (sets||tauto||cbn in *; superlia).
    + unfold Mem.range_perm in *; intros o' Ho'.
      specialize (Hperm1 o'); specialize (Hperm2 o').
      match type of Hperm1 with ?t1 -> _ =>
      match type of Hperm2 with ?t2 -> _ =>
        assert (Hcases : t1 \/ t2) by superlia
      end end.
      destruct Hcases; eauto.
    + intros i v Hget.
      assert (Hcases : ((0 <= i < #|vs|) \/ (#|vs| <= i < #|vs| + #|ws|))%Z).
      { apply get_ith_range in Hget. rewrite app_length in Hget. lia. }
      destruct Hcases as [Hprefix|Hsuffix].
      * apply Hload1; rewrite <- Hget, get_ith_prefix by lia; auto.
      * replace (o + i*word_size)%Z with (o + #|vs|*word_size + (i-#|vs|)*word_size)%Z by lia.
        apply Hload2; rewrite <- Hget, get_ith_suffix by lia; auto.
Qed.

Lemma mapsto_cons S b o p v vs m :
  m |=_{S} ((b, o) ↦_{p} v :: vs) <->
  m |=_{S} ((b, o) ↦_{p} [v]) ⋆ ((b, o + word_size) ↦_{p} vs)%Z.
Proof. apply mapsto_app with (vs := [v]). Qed.

Lemma mapsto_store S b o p i v vs m m' :
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} ((b, o) ↦_{p} vs) ->
  m' |=_{S} ((b, o) ↦_{p} set_ith vs i v).
Proof.
  unfold mpred_denote_aux.
  intros Hwf_v Hbound Hstore [Hperm [HS [Hwf_vs [Hload Hbounds]]]].
  split_ands; try (cbn in *; superlia).
  - unfold Mem.range_perm in *; rewrite set_ith_len; intros o' Ho'.
    eapply Mem.perm_store_1; eauto.
  - rewrite HS; clear; revert i o; induction vs as [|v' vs IHvs]; [easy|intros i o].
    cbn; destruct (Z.eq_dec i 0) as [|Hne]; [subst|].
    + apply Ensemble_iff_In_iff; intros [b' o'].
      unfold In, dom_mapsto; cbn; lia.
    + rewrite dom_mapsto_cons.
      rewrite (dom_mapsto_cons _ _ _ (set_ith _ _ _)).
      now rewrite <- IHvs.
  - clear - Hwf_v Hwf_vs; revert i; induction vs as [|v' vs IHvs]; [easy|].
    intros i; cbn; destruct (Z.eq_dec i 0) as [|Hne]; [subst; now cbn in *|].
    cbn in *; split; [easy|].
    now apply IHvs.
  - intros i' v' Hget.
    destruct (Z.eq_dec i i') as [|Hne]; [subst|].
    + rewrite ith_gss in Hget by lia; inv Hget.
      rewrite <- (val_wf_load_result v') by auto.
      eapply Mem.load_store_same; eauto.
    + rewrite ith_gso in Hget by auto.
      specialize (Hload _ _ Hget).
      rewrite <- Hload; eapply Mem.load_store_other; eauto; superlia.
  - easy.
Qed.

Lemma mpred_unchanged_on S P m m' :
  Mem.unchanged_on (fun b o => S (b, o)) m m' ->
  m |=_{S} P ->
  m' |=_{S} P.
Proof.
  revert S; induction P as [[b o] p vs|P IHP Q IHQ|A F IHF|m''|Q]; cbn;
  intros S Hunchanged Hm.
  - destruct Hm as [Hperm[HS[?[Hload [??]]]]]; split_ands; auto.
    + destruct Hunchanged as [Hle Hperm' Haccess]; intros o' Ho'.
      apply Hperm'; auto.
      * rewrite Ensemble_iff_In_iff in HS; rewrite HS.
        unfold dom_mapsto, In; lia.
      * eapply Mem.perm_valid_block.
        apply Hperm; eauto.
    + intros i v Hget; eapply Mem.load_unchanged_on; eauto.
      intros o'; cbn; rewrite Ensemble_iff_In_iff in HS.
      specialize (HS (b, o')); rewrite HS; unfold In, dom_mapsto; superlia.
    + easy.
    + easy.
  - destruct Hm as [S1[S2[HS[?[??]]]]]; do 2 eexists; split_ands; eauto.
    + apply IHP; auto. 
      eapply Mem.unchanged_on_implies; eauto; cbn; intros; now apply (proj2 HS).
    + apply IHQ; auto.
      eapply Mem.unchanged_on_implies; eauto; cbn; intros; now apply (proj2 HS).
  - destruct Hm as [x Hx]; eexists; eauto.
  - destruct Hm as [H Hunchanged']; split; [auto|].
    eapply Mem.unchanged_on_trans; eauto.
  - destruct Hm as [Hm HQ]; split; auto.
    intros [b o] Hbo; pose proof Hbo as Hbo'; apply Hm in Hbo; unfold In, dom_mem in *.
    eapply Mem.perm_unchanged_on; eauto.
Qed.

Lemma dom_mapsto_Decidable b o vs :
  Decidable (dom_mapsto b o vs).
Proof.
  constructor; intros [b' o']; cbn.
  destruct (Pos.eq_dec b b'); [|now right].
  destruct (Z_le_dec o o'); [|now right].
  destruct (Z_lt_dec o' (o + #|vs|*word_size))%Z; [|now right].
  now left.
Qed.
Hint Resolve dom_mapsto_Decidable : DecidableDB.

Lemma mapsto_store_sepcon S P b o p i v vs m m' :
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} ((b, o) ↦_{p} vs) ⋆ P ->
  m' |=_{S} ((b, o) ↦_{p} set_ith vs i v) ⋆ P.
Proof.
  remember ((b, o) ↦_{p} vs) as bovs.
  remember ((b, o) ↦_{p} set_ith vs i v) as bovs'.
  cbn; subst bovs bovs'; intros Hwf Hrange Hstore.
  intros [S1 [S2 [HS [HD [Hbovs HP]]]]]; exists S1, S2; split_ands; auto.
  - eapply mapsto_store; eauto.
  - pose proof Hstore as Hunchanged.
    apply (Mem.store_unchanged_on (fun b o => S2 (b, o))) in Hunchanged.
    2:{ rewrite (Disjoint_pair_simpl S1 S2) in HD.
        intros o'; specialize (HD b o').
        intros Hin_S1 Hin_S2; contradiction HD.
        destruct Hbovs as [Hperm [HS1 _]].
        rewrite Ensemble_iff_In_iff in HS1.
        specialize (HS1 (b, o')); rewrite HS1.
        unfold dom_mapsto, In.
        intuition superlia. }
    eapply mpred_unchanged_on; eauto.
Qed.

Lemma sepcon_comm P Q S m :
  m |=_{S} P ⋆ Q <-> m |=_{S} Q ⋆ P.
Proof.
  cbn; split; intros [S1[S2[HS[HD[HP HQ]]]]]; exists S2, S1;
  rewrite HS; intuition (eauto||sets).
Qed.

Lemma unchanged_on_iff S1 S2 m m' :
  S1 <--> S2 ->
  Mem.unchanged_on (fun b o => S1 (b, o)) m m' <->
  Mem.unchanged_on (fun b o => S2 (b, o)) m m'.
Proof.
  intros H; split; intros Hunchanged; eapply Mem.unchanged_on_implies;
  eauto; cbn; intros; now apply H.
Qed.

Lemma mpred_Same_set P S1 S2 m :
  S1 <--> S2 ->
  m |=_{S1} P <-> m |=_{S2} P.
Proof.
  induction P as [[b o] vs|P IHP Q IHQ|A F IHF|m''|Q]; cbn.
  - intros ->; split; intros Hand; decompose [and] Hand; split_ands; sets.
  - intros H; split; intros Hand; decompose [ex and] Hand.
    + do 2 eexists; split_ands; eauto.
      now rewrite <- H.
    + do 2 eexists; split_ands; eauto; now rewrite H.
  - intros H; split; intros [x Hx]; exists x; now specialize (IHF x).
  - intros H. erewrite unchanged_on_iff; eauto. now rewrite H.
  - intros ->; tauto.
Qed.

Lemma dom_mem_empty : dom_mem Mem.empty <--> Empty_set _.
Proof.
  apply Ensemble_iff_In_iff; intros [b o].
  unfold dom_mem, Mem.perm; cbn.
  rewrite PMap.gi, In_Empty_set; now cbn.
Qed.

Lemma Sepcon_mempty P S m :
  m |=_{S} P ⋆ mempty <-> m |=_{S} P.
Proof.
  cbn. split; [intros [S1 [S2 [HS [HD [HP [HS2 Hsame]]]]]] |intros Hm].
  - rewrite dom_mem_empty, HS2 in *.
    eapply mpred_Same_set; [|apply HP].
    rewrite HS; sets.
  - exists S, (Empty_set _); split_ands; eauto; sets.
    + now rewrite dom_mem_empty.
    + constructor; try solve [inversion 1].
      unfold Coqlib.Ple; cbn; lia.
Qed.

Inductive is_frame : (mpred -> mpred) -> Prop :=
| is_frame_hole : is_frame (fun P => P)
| is_frame_sepcon1 F Q : is_frame F -> is_frame (fun P => F P ⋆ Q)
| is_frame_sepcon2 F P : is_frame F -> is_frame (fun Q => P ⋆ F Q)
(* These (redundant) cases make proof search possible *)
| is_frame_sepcon1' Q : is_frame (fun P => P ⋆ Q)
| is_frame_sepcon2' P : is_frame (fun Q => P ⋆ Q).
Hint Constructors is_frame : FrameDB.

Goal forall m Q, is_frame (fun P => (Q ⋆ P) ⋆ Mem m).
  intros; auto with FrameDB.
Abort.

Goal True.
  let x := constr:(S (S (S 3))) in
  match x with
  | S ?e =>
    lazymatch e with context F [3] => idtac F 3 end
  end.
Abort.

Lemma frame_cong' F P Q S m :
  is_frame F ->
  (forall S', m |=_{S'} P <-> m |=_{S'} Q) ->
  m |=_{S} F P <-> m |=_{S} F Q.
Proof.
  intros HF HPQ; revert S; induction HF; [auto|intros S..];
  split; intros [S1 [S2 [HS [HD [HP HQ]]]]]; do 2 eexists;
  intuition (try (rewrite <- IHHF + rewrite IHHF + rewrite HPQ + rewrite <- HPQ); eauto).
Qed.

Lemma frame_entail' F P Q S m :
  is_frame F ->
  (forall S', m |=_{S'} P -> m |=_{S'} Q) ->
  m |=_{S} F P -> m |=_{S} F Q.
Proof.
  intros HF HPQ; revert S; induction HF; [auto|intros S..];
  intros [S1 [S2 [HS [HD [HP HQ]]]]]; do 2 eexists;
  intuition (try (rewrite <- IHHF + rewrite IHHF + rewrite HPQ + rewrite <- HPQ); eauto).
Qed.

Definition mpred_equiv P Q := forall S m, m |=_{S} P <-> m |=_{S} Q.
Infix "<=>" := mpred_equiv (at level 79).

Ltac rewrite_equiv F H :=
  rewrite (frame_cong' F);
  [|eauto with FrameDB|intros; apply H].

Ltac rewrite_equiv_l F H :=
  rewrite <- (frame_cong' F);
  [|eauto with FrameDB|intros; apply H].

Lemma frame_swap_hole S F P Q m :
  is_frame F ->
  m |=_{S} F P ⋆ Q <-> m |=_{S} F Q ⋆ P.
Proof.
  intros HF; revert S; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros S.
  - apply sepcon_comm.
  - rewrite !sepcon_assoc.
    rewrite_equiv (fun H => F P ⋆ H) sepcon_comm.
    rewrite_equiv (fun H => F Q ⋆ H) sepcon_comm.
    rewrite <- !sepcon_assoc.
    rewrite_equiv (fun H => H ⋆ Q') IHF.
    now symmetry in IHF; rewrite_equiv (fun H => H ⋆ Q') IHF.
  - rewrite !sepcon_assoc.
    now rewrite_equiv (fun H => P' ⋆ H) IHF.
  - rewrite !sepcon_assoc.
    rewrite_equiv (fun H => P ⋆ H) sepcon_comm.
    now rewrite sepcon_comm, !sepcon_assoc.
  - rewrite !sepcon_assoc.
    now rewrite_equiv (fun H => P' ⋆ H) sepcon_comm.
Qed.

Lemma mpred_Ex {A} F (G : A -> _) S m :
  is_frame F ->
  m |=_{S} F (∃ x, G x) <-> exists x, m |=_{S} F (G x).
Proof.
  intros HF; revert S; induction HF; intros S.
  1: now cbn.
  1: rewrite frame_swap_hole by auto.
  1: erewrite MCUtils.iff_ex; [|intros x; apply frame_swap_hole; auto].
  2: rewrite sepcon_comm, frame_swap_hole by auto.
  2: erewrite MCUtils.iff_ex; [|intros x; apply sepcon_comm].
  2: erewrite MCUtils.iff_ex; [|intros x; apply frame_swap_hole; auto].
  all:
    try solve [cbn; split; intros Hexand; decompose [ex and] Hexand;
    (repeat match goal with |- exists _, _ => eexists end);
    split_ands; eauto].
Qed.

Ltac destruct_ex_ctx F x H :=
  rewrite (mpred_Ex F) in H; [|auto with FrameDB]; destruct H as [x H].
Ltac destruct_ex x H := destruct_ex_ctx (fun H : mpred => H) x H.

Ltac exists_ex_ctx F x :=
  rewrite (mpred_Ex F); [|auto with FrameDB]; exists x.
Ltac exists_ex x := exists_ex_ctx (fun H : mpred => H) x.

Ltac split_ex_ctx F :=
  rewrite (mpred_Ex F); [|auto with FrameDB]; unshelve eexists.
Ltac split_ex := split_ex_ctx (fun H : mpred => H).

Ltac rewrite_equiv_in F H Hin :=
  rewrite (frame_cong' F) in Hin;
  [|eauto with FrameDB|intros; apply H].

Lemma mpred_equiv_ex {A} (P Q : A -> _) :
  (forall x, P x <=> Q x) ->
  ∃ x, P x <=> ∃ x, Q x.
Proof.
  intros HPQ; split; intros Hm;
  destruct_ex x Hm;
  exists_ex x; now apply HPQ.
Qed.

Lemma mpred_ex_entail {A} (P : A -> _) x :
  P x |-- ∃ x, P x.
Proof. intros S m Hm; now exists_ex x. Qed.

Lemma frame_entail F P Q :
  is_frame F ->
  P |-- Q ->
  F P |-- F Q.
Proof.
  intros HF HPQ S m Hm.
  eapply frame_entail'; try eassumption.
  intros; now apply HPQ.
Qed.

Lemma mpred_ex_sepcon {A} P (Q : A -> _) :
  ∃ x, P ⋆ Q x <=> P ⋆ ∃ x, Q x.
Proof.
  split; intros Hm.
  - destruct_ex x Hm.
    eapply frame_entail; auto with FrameDB; [apply mpred_ex_entail|]; eauto.
  - cbn in Hm. destruct Hm as [S1 [S2 [HS [HD [HP [x HQ]]]]]].
    cbn; exists x; do 2 eexists; eauto.
Qed.

Lemma mpred_equiv_sym P Q :
  P <=> Q -> Q <=> P.
Proof.
  unfold "<=>"; intros HPQ; split; intros Hm.
  - now rewrite HPQ.
  - now rewrite <- HPQ.
Qed.

Lemma mpred_equiv_trans P Q R :
  P <=> Q -> Q <=> R -> P <=> R.
Proof.
  unfold "<=>"; intros HPQ HQR; split; intros Hm.
  - now rewrite <- HQR, <- HPQ.
  - now rewrite HPQ, HQR.
Qed.

Lemma frame_cong F P Q :
  is_frame F ->
  P <=> Q ->
  F P <=> F Q.
Proof.
  intros HF HPQ S m.
  apply frame_cong'; auto.
Qed.

Lemma mpred_aux_Included m S P :
  m |=_{S} P -> S \subset dom_mem m.
Proof.
  revert S; induction P as [[b o] p vs|P IHP Q IHQ|A F IHF|m''|Q]; cbn; intros S H.
  - destruct H as [Hperm [HS _]]; rewrite HS.
    intros [b' o'] [<- Hbo']; unfold dom_mapsto, dom_mem, In in *.
    apply Mem.perm_cur_max.
    eapply Mem.perm_implies; [apply Hperm|]; auto with mem.
  - destruct H as [S1 [S2 [HS [HD [HP HQ]]]]].
    specialize (IHP _ HP); specialize (IHQ _ HQ).
    rewrite HS; sets.
  - destruct H as [x Hm]; eauto.
  - destruct H as [HS Hsame]; rewrite HS.
    intros [b o]; unfold In, dom_mem; intros Hm''.
    eapply Mem.perm_unchanged_on; eauto.
    apply HS, Hm''.
  - tauto.
Qed.

Lemma entail_True P : P |-- Pure True.
Proof.
  intros S m Hm; cbn; split; auto.
  eapply mpred_aux_Included; eauto.
Qed.

Lemma mapsto_in_cons b o p v vs :
  (b, o) ↦_{p} v :: vs ⋆ Pure True |-- (b, o + word_size)%Z ↦_{p} vs ⋆ Pure True.
Proof.
  intros S m.
  rewrite_equiv (fun H => H ⋆ Pure True) mapsto_cons.
  rewrite sepcon_assoc.
  rewrite sepcon_comm.
  rewrite sepcon_assoc.
  apply frame_entail; auto with FrameDB.
  apply entail_True.
Qed.

Lemma frame_mem_ex F S P m :
  is_frame F ->
  m |=_{S} F P -> exists S' m',
  m' |=_{S'} P.
Proof.
  intros HF; revert S; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros S Hm;
    cbn in Hm; decompose [ex and] Hm; try eapply IHF; eauto.
Qed.

Lemma entail_trans P Q R :
  P |-- Q -> Q |-- R -> P |-- R.
Proof. unfold "|--"; eauto. Qed.

Lemma entail_trans' P Q R :
  Q |-- R -> P |-- Q ->  P |-- R.
Proof. unfold "|--"; eauto. Qed.

Lemma mapsto_unique F b o p vs vs' m P :
  is_frame F ->
  m |= F P ->
  P |-- ((b, o) ↦_{p} vs) ⋆ Pure True ->
  P |-- ((b, o) ↦_{p} vs') ⋆ Pure True ->
  #|vs| = #|vs'| ->
  vs = vs'.
Proof.
  intros HF Hm Hvs Hvs' Hlen.
  revert b o vs' Hvs Hvs' Hlen; induction vs as [|v vs IHvs]; intros b o vs' Hvs Hvs'.
  - destruct vs'; cbn; [auto|lia].
  - destruct vs' as [|v' vs']; [cbn; lia|]; intros Hlen; f_equal.
    + apply frame_mem_ex in Hm; auto.
      destruct Hm as [S[m' Hm]].
      specialize (Hvs _ _ Hm); specialize (Hvs' _ _ Hm).
      cbn in *; decompose [ex and] Hvs; decompose [ex and] Hvs'.
      now repeat match goal with H : forall (_ : Z), _ |- _ => try specialize (H 0%Z _ eq_refl); cbn in H end.
    + eapply entail_trans' in Hvs; [|apply mapsto_in_cons].
      eapply entail_trans' in Hvs'; [|apply mapsto_in_cons].
      eapply IHvs; eauto.
      cbn in *; lia.
Qed.

Lemma mpred_load S F b o p i v vs m :
  is_frame F ->
  get_ith vs i = Some v ->
  m |=_{S} F ((b, o) ↦_{p} vs) ->
  load m b (o + i*word_size) = Some v.
Proof.
  intros HF Hget; revert S; induction HF; intros S Hm;
  cbn in Hm; decompose [ex and] Hm; eauto.
Qed.

Lemma mpred_store S F b o p i v vs m m' :
  is_frame F ->
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} F ((b, o) ↦_{p} vs) ->
  m' |=_{S} F ((b, o) ↦_{p} set_ith vs i v).
Proof.
  intros HF Hwf Hrange Hstore Hm; destruct HF.
  - eapply mapsto_store; eauto.
  - rewrite frame_swap_hole in * by auto.
    rewrite sepcon_comm in *; eapply mapsto_store_sepcon; eauto.
  - rewrite sepcon_comm, frame_swap_hole in *; auto.
    rewrite sepcon_comm in *; eapply mapsto_store_sepcon; eauto.
  - eapply mapsto_store_sepcon; eauto.
  - rewrite sepcon_comm in *; eapply mapsto_store_sepcon; eauto.
Qed.

Definition increase_nextblock_to (b : block) (m : mem) :
  (b >= Mem.nextblock m)%positive -> mem.
Proof.
  destruct m; intros H; unshelve econstructor.
  - exact mem_contents. - exact mem_access. - exact b. - exact access_max.
  - abstract (intros b' o k Hge; change Coqlib.Plt with Pos.lt in *;
    cbn in H; apply nextblock_noaccess; lia).
  - exact contents_default.
Defined.

Definition dom_alloc (b : block) (lo hi : Z) : Ensemble (block * Z) :=
  fun '(b', o) => b' = b /\ (lo <= o < hi)%Z.

Definition alloc_alone (m : mem) (lo hi : Z) : mem.
Proof.
  refine (fst (Mem.alloc (increase_nextblock_to (Mem.nextblock m) Mem.empty _) lo hi)).
  abstract (cbn; lia).
Defined.

Transparent Mem.alloc.
Lemma dom_alloc_alone m lo hi :
  dom_mem (alloc_alone m lo hi) <--> dom_alloc (Mem.nextblock m) lo hi.
Proof.
  apply Ensemble_iff_In_iff; intros [b o].
  unfold dom_mem, Mem.perm, alloc_alone, Mem.alloc; cbn.
  destruct (Pos.eq_dec (Mem.nextblock m) b) as [|Hne]; [subst|].
  - rewrite PMap.gss.
    destruct (Coqlib.zle lo o); [|now cbn].
    destruct (Coqlib.zlt o hi); [|now cbn].
    assert (Horder : perm_order Freeable Nonempty <-> True) by (split; auto; constructor).
    cbn; now rewrite Horder.
  - now rewrite PMap.gso, PMap.gi by auto.
Qed.

Lemma alloc_alone_dom_disjoint m lo hi :
  Disjoint _ (dom_mem m) (dom_mem (alloc_alone m lo hi)).
Proof.
  unfold address; rewrite Disjoint_pair_simpl; intros b o.
  unfold dom_mem; intros [Hm Halone].
  destruct m; unfold Mem.perm, Mem.perm_order', Mem.alloc in *; cbn in *.
  destruct (Pos.eq_dec nextblock b) as [|Hne]; [subst|].
  - rewrite PMap.gss in *.
    destruct (Coqlib.zle lo o), (Coqlib.zlt o hi); cbn in Halone; auto.
    rewrite nextblock_noaccess in Hm; auto.
    unfold Coqlib.Plt; lia.
  - now rewrite PMap.gso, PMap.gi in Halone by auto.
Qed.

Lemma alloc_alone_perm m lo hi b o :
  Mem.perm (alloc_alone m lo hi) b o Max Nonempty <->
  (b = Mem.nextblock m /\ lo <= o < hi)%Z.
Proof.
  unfold Mem.perm, Mem.perm_order', "!!"; cbn.
  destruct (Pos.eq_dec b (Mem.nextblock m)) as [|Hne]; [subst|].
  - rewrite M.gss.
    destruct (Coqlib.zle lo o); cbn; [|lia].
    destruct (Coqlib.zlt o hi); cbn; [|lia].
    assert (Horder : perm_order Freeable Nonempty <-> True) by (split; auto; constructor).
    rewrite Horder; lia.
  - rewrite M.gso, M.gempty by auto; lia.
Qed.

Lemma alloc_alone_unchanged_on m lo hi :
  Mem.unchanged_on (fun b o => dom_mem (alloc_alone m lo hi) (b, o)) (alloc_alone m lo hi)
                   (fst (Mem.alloc m lo hi)).
Proof.
  constructor.
  - cbn; unfold Coqlib.Ple; lia.
  - unfold dom_mem; intros* Hperm Hvalid.
    rewrite alloc_alone_perm in Hperm.
    destruct Hperm; subst.
    unfold Mem.perm; cbn.
    rewrite !PMap.gss.
    destruct (Coqlib.zle lo ofs); [|now cbn].
    destruct (Coqlib.zlt ofs hi); [|now cbn].
    now cbn.
  - unfold dom_mem; intros* Hperm Hperm'.
    rewrite alloc_alone_perm in Hperm.
    destruct Hperm; subst; cbn.
    now rewrite !PMap.gss.
Qed.

Lemma alloc_alone_dom_mem m lo hi :
  dom_mem (fst (Mem.alloc m lo hi)) <-->
  dom_mem m :|: dom_mem (alloc_alone m lo hi).
Proof.
  apply Ensemble_iff_In_iff; intros [b o].
  rewrite In_or_Iff_Union; unfold In.
  unfold dom_mem, Mem.perm; cbn.
  destruct m as [c a next access noaccess default]; cbn.
  destruct (Pos.eq_dec next b) as [|Hne]; [subst|].
  - rewrite !PMap.gss.
    rewrite noaccess; [|unfold Coqlib.Plt; lia]; cbn.
    destruct (Coqlib.zle lo o); [|easy].
    destruct (Coqlib.zlt o hi); [|easy].
    now cbn.
  - rewrite !PMap.gso, !PMap.gi by auto.
    now cbn.
Qed.
Opaque Mem.alloc.

Lemma mpred_alloc' P m lo hi :
  m |= P -> fst (Mem.alloc m lo hi) |= P ⋆ Mem (alloc_alone m lo hi).
Proof.
  intros Hm; cbn.
  exists (dom_mem m), (dom_mem (alloc_alone m lo hi)); split_ands.
  - apply alloc_alone_dom_mem.
  - apply alloc_alone_dom_disjoint.
  - eapply mpred_unchanged_on; eauto.
    destruct (Mem.alloc m lo hi) eqn:Halloc.
    eapply Mem.alloc_unchanged_on; eauto.
  - sets.
  - apply alloc_alone_unchanged_on.
Qed.

Transparent Mem.free Mem.unchecked_free.
Lemma dom_mem_free m b lo hi m' :
  Mem.free m b lo hi = Some m' ->
  dom_mem m' <--> dom_mem m \\ dom_alloc b lo hi.
Proof.
  intros Hfree; apply Ensemble_iff_In_iff; intros [b' o'].
  unfold dom_mem; rewrite not_In_Setminus; unfold In.
  unfold Mem.free in Hfree.
  destruct (Mem.range_perm_dec _ _ _ _ _ _) as [Hfreeable|]; inv Hfree.
  destruct m; unfold Mem.perm; cbn in *.
  destruct (Pos.eq_dec b b') as [|Hne]; [subst|].
  - rewrite PMap.gss.
    destruct (Coqlib.zle lo o'); [|now cbn].
    destruct (Coqlib.zlt o' hi); [|now cbn].
    now cbn.
  - now rewrite PMap.gso by auto.
Qed.
Opaque Mem.free Mem.unchecked_free.

Transparent Mem.alloc.
Lemma mpred_free' P m b lo hi m_old m' :
  b = Mem.nextblock m_old ->
  m |= P ⋆ Mem (alloc_alone m_old lo hi) ->
  Mem.free m b lo hi = Some m' ->
  m' |= P.
Proof.
  intros Hnext_eq [S1 [S2 [HS [HD [HS1 [HS2 Hunchanged]]]]]] Hfree.
  assert (Hunchanged' : Mem.unchanged_on (fun b o => S1 (b, o)) m m').
  { eapply Mem.free_unchanged_on; eauto.
    intros i Hi Hbad. destruct HD as [HD].
    contradiction (HD (b, i)).
    constructor; auto.
    rewrite Ensemble_iff_In_iff in HS2.
    rewrite HS2; cbn.
    cbn; unfold Mem.perm, Mem.perm_order'; subst b.
    unfold alloc_alone, Mem.alloc; cbn.
    rewrite PMap.gss.
    destruct (Coqlib.zle lo i); [|lia].
    destruct (Coqlib.zlt i hi); [|lia].
    cbn; auto with mem. }
  assert (Hdom_m' : S1 <--> dom_mem m').
  { apply dom_mem_free in Hfree.
    rewrite Hfree, HS, HS2, dom_alloc_alone, Hnext_eq in *.
    rewrite Setminus_Union_Included; sets. }
  rewrite mpred_Same_set in HS1 by apply Hdom_m'.
  eapply mpred_unchanged_on; eauto.
  eapply unchanged_on_iff; [symmetry; apply Hdom_m'|auto].
Qed.
Opaque Mem.alloc.

Lemma mpred_Mem F P m m_inner :
  m_inner |= P ->
  m |= F (Mem m_inner) ->
  m |= F P.
Proof. Abort.

Definition allocd b lo hi :=
  ∃ m, Mem (alloc_alone m lo hi) WITH b = Mem.nextblock m.

Lemma mpred_alloc P m b lo hi m' :
  m |= P ->
  Mem.alloc m lo hi = (m', b) ->
  m' |= P ⋆ allocd b lo hi.
Proof.
  intros Hm Halloc; unfold allocd.
  apply mpred_Ex; eauto with FrameDB.
  exists m; apply mpred_Ex; eauto with FrameDB.
  pose proof Halloc as Hb.
  apply Mem.alloc_result in Hb; exists Hb.
  replace m' with (fst (Mem.alloc m lo hi))
    by (destruct (Mem.alloc m lo hi); now inv Halloc).
  now apply mpred_alloc'.
Qed.

Lemma mpred_free P m b lo hi m' :
  m |= P ⋆ allocd b lo hi ->
  Mem.free m b lo hi = Some m' ->
  m' |= P.
Proof.
  unfold allocd; intros Hm Hfree. 
  apply mpred_Ex in Hm; eauto with FrameDB; destruct Hm as [m_old Hm].
  apply mpred_Ex in Hm; eauto with FrameDB; destruct Hm as [Hb Hm].
  eapply mpred_free'; eauto.
Qed.

Definition vint (z : Z) : Values.val :=
  if Archi.ptr64
  then Vlong (Int64.repr z)
  else Values.Vint (Int.repr z).

(** The spine of the shadow stack contains a linked list of frame structs and root arrays.
    Each root array has a fixed size, large enough to fit all the live variables at each GC. *)
Record stack_frame_spine := mk_ss_frame
{ ss_frame : block * ptrofs;
  ss_root : block * ptrofs;
  ss_size : Z }.
Definition stack_spine := list stack_frame_spine.

Definition stack_top (ss : stack_spine) :=
  match ss with
  | [] => Vnullptr
  | {| ss_frame := (b, o) |} :: _ => Vptr b o
  end.

(** A frame of the shadow stack with spine [sp], next pointer [next], containing roots [cvs]. *)
Definition shadow_stack_frame (sp : stack_frame_spine) (cvs : list Values.val) (next : Values.val) :=
  let '{| ss_frame := (f_b, f_o); ss_root := (r_b, r_o); ss_size := n |} := sp in
  (f_b, O.unsigned f_o) ↦_{Freeable}
    [Vptr r_b (O.repr (O.unsigned r_o + #|cvs|*word_size));
     Vptr r_b r_o;
     next] ⋆
  (∃ suffix, (r_b, O.unsigned r_o) ↦_{Freeable} cvs ++ suffix
   WITH #|cvs ++ suffix| = n).

(** A shadow stack with roots [cvss]. *)
Fixpoint shadow_stack (ss : stack_spine) (cvss : list (list Values.val)) : mpred :=
  match ss, cvss with
  | [], [] => mempty
  | fr :: ss, cvs :: cvss =>
    shadow_stack_frame fr cvs (stack_top ss) ⋆ shadow_stack ss cvss
  | _, _ => Pure False
  end.

Notation "'match!' e1 'with' p 'in' e2" :=
  (match e1 with p => e2 | _ => False end)
  (at level 80, p pattern, e1 at next level, right associativity).

(** [has_shape P v cv] if nested constructor applications in v are well represented
    in (P, cv), and if function values correspond to pointers. *)
Fixpoint has_shape P v cv :=
  match v, cv with
  | Vint i, cv => cv = vint (rep_unboxed (Z.to_N i))
  | Vconstr c vs, cv =>
    match get_ctor_rep cenv c with
    | Ret (enum t) => cv = vint (rep_unboxed t)
    | Ret (boxed t a) =>
      match! cv with Vptr b o in
      exists cvs,
      P |-- ((b, O.unsigned o - word_size) ↦_{Readable} vint (rep_boxed t a) :: cvs) ⋆ Pure True /\
      Forall2' (has_shape P) vs cvs
    | _ => False
    end
  | Vfun ρ fds f, Vptr b o => True
  | _, _ => False
  end%Z.

(** [compatible_shape P P' v cv cv'] if
    - [has_shape P v cv],
    - [has_shape P' v cv'],
    - cv and cv' are exactly the same at function values *)
Fixpoint compatible_shape P P' v cv cv' :=
  match v, cv, cv' with
  | Vint i, cv, cv' => cv = vint (rep_unboxed (Z.to_N i)) /\ cv = cv'
  | Vconstr c vs, cv, cv' =>
    match get_ctor_rep cenv c with
    | Ret (enum t) => cv = vint (rep_unboxed t) /\ cv = cv'
    | Ret (boxed t a) =>
      match! cv with Vptr b o in
      match! cv' with Vptr b' o' in
      exists cvs cvs',
      #|cvs| = #|vs| /\
      P |-- ((b, O.unsigned o - word_size) ↦_{Readable} vint (rep_boxed t a) :: cvs) ⋆ Pure True /\
      P' |-- ((b', O.unsigned o' - word_size) ↦_{Readable} vint (rep_boxed t a) :: cvs') ⋆ Pure True /\
      Forall3 (compatible_shape P P') vs cvs cvs'
    | _ => False
    end
  | Vfun ρ fds f, Vptr b o, Vptr b' o' => b = b' /\ o = o'
  | _, _, _ => False
  end%Z.

Definition has_shapes P := Forall2 (Forall2 (has_shape P)).
Definition compatible_shapes P P' := Forall3 (Forall3 (compatible_shape P P')).

(** A mem is well-formed if it contains
    - A well-formed thread_info pointing to a nursery, args array, and shadow stack
    - A heap of values, part of which freely modified by GC, and part of which contains
      "outliers" (memory outside of the GC heap that's reachable from a root) *)
Definition valid_mem
           nursery_b talloc_o tlimit_o alloc_o limit_o
           tinfo_b tinfo_o
           args ss cvss nalloc values frame : mpred :=
  (∃ heap,
   (tinfo_b, O.unsigned tinfo_o) ↦_{Writable}
     [Vptr nursery_b talloc_o; Vptr nursery_b tlimit_o; heap] ++
     args ++ [stack_top ss; vint nalloc]
   WITH #|args| = max_args) ⋆
   (∃ free_space, (nursery_b, O.unsigned alloc_o) ↦_{Writable} free_space
    WITH (#|free_space|*word_size = O.unsigned limit_o - O.unsigned alloc_o /\ 
          #|free_space|*word_size <= O.max_signed))%Z ⋆
  shadow_stack ss cvss ⋆
  values ⋆
  frame.

Hypothesis garbage_collect_spec :
  forall tinfo_b tinfo_o vss ss cvss nalloc outliers values frame m,
  (** if m is a valid CertiCoq mem containing
      - thread_info struct with nalloc = # of bytes to make available,
      - shadow stack cvss representing L6 values vss, *)
  m |= ∃ nursery_b talloc_o tlimit_o alloc_o limit_o args,
       valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
                 tinfo_b tinfo_o args ss cvss nalloc values frame ->
  values |-- outliers ⋆ Pure True ->
  has_shapes values vss cvss ->
  (** then GC produces m', *)
  exists m' limit_o alloc_o cvss' values',
  Events.external_functions_sem
    "garbage_collect"
    (mksignature [ast_value] None cc_default) prog_genv
    [Vptr tinfo_b tinfo_o] m Events.E0 Vundef m' /\
  (** m' is a valid CertiCoq mem,
      the thread_info's location stays the same,
      the shadow stack's spine stays the same,
      the nursery contains limit-alloc >= nalloc words of free space,
      the shadow stack contains new roots cvss', *)
  m' |= ∃ nursery_b args nalloc,
        valid_mem nursery_b alloc_o limit_o alloc_o limit_o tinfo_b tinfo_o
                  args ss cvss' nalloc values' frame /\
  (O.unsigned limit_o - O.unsigned alloc_o >= nalloc*word_size)%Z /\
  values' |-- outliers ⋆ Pure True /\
  (** and the contents of the new shadow stack still represents vss *)
  compatible_shapes values values' vss cvss cvss'.

(** * Logical relation between λ-ANF_CC and Clight *)

Fixpoint closed_val (v : cps.val) :=
  match v with
  | Vconstr c vs => All (map closed_val vs)
  | Vfun ρ fds f => M.bempty ρ = true
  | Vint _ => True
  end.

(* TODO
Definition local_word b (v : Values.val) :=
  ∃ m m', Mem m'
  WITH Some m' = store (alloc_alone m 0 word_size) b 0 v
  WITH b = Mem.nextblock m.

Search Mem.store list.
Definition local_words b (v : list Values.val) :=
  ∃ m m', Mem m'
  WITH Some m' = store (alloc_alone m 0 word_size) b 0 v
  WITH b = Mem.nextblock m.
*)

Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

Hypothesis one_app_nonzero : forall f ft ys, to_nat (one (Eapp f ft ys)) > 0.

(** Bigstep evaluation of L6 terms *)
Definition bstep_res := fun '(ρ, e, cin) '(v, cout) =>
  bstep_fuel cenv ρ e cin (Res v) cout.
Infix "⇓cps" := bstep_res (at level 80).

(** The calling conventions for each fun_tag *)
Variable calling_convention : fun_tag -> option fun_ty_info.

Section ValueRelation.

Variable rel_val : forall (k : nat) (v : cps.val) (P : mpred) (cv : Values.val), Prop.

Definition rel_val_aux (k : nat) :=
  fix go (v : cps.val) (P : mpred) (cv : Values.val) : Prop :=
  match v, cv with
  | Vint v, cv => cv = vint (rep_unboxed (Z.to_N v))
  | Vconstr t vs, cv =>
    match get_ctor_rep cenv t with
    | Ret (enum t) => cv = vint (rep_unboxed t) /\ vs = []
    | Ret (boxed t a) =>
      match! cv with Vptr b o in
      exists cvs,
      P |-- ((b, O.unsigned o - word_size) ↦_{Readable} vint (rep_boxed t a) :: cvs) ⋆ Pure True /\
      Forall2' (fun v cv => go v P cv) vs cvs
    | _ => False
    end%Z
  | Vfun ρ fds f, Vptr b o =>
    (* match! M.bempty ρ with true in *)
    match! find_def f fds with Some (t, xs, e) in
    match! calling_convention t with Some (arity, indices) in
    match! Genv.find_funct prog_genv (Vptr b o) with Some fn in
    type_of_fundef fn =
      Tfunction (Tcons threadInf (value_tys (Nat.min n_param (N.to_nat arity)))) value
      cc_default /\
    forall j vs ρ_xvs cin cout vss v,
    forall cvs m tinfo_b tinfo_o,
    forall args ss cvss outliers values frame,
    j < k ->
    match k with
    | 0 => True
    | S k =>
      (** if vs are related to cvs at level j<k (written as k-(k-j) to convince
          Coq of well-foundedness) *)
      let j := k-(k-j) in
      Forall2 (fun v cv => rel_val j v values cv) vs cvs ->
      (** and calling the L6 function with arguments xs↦vs yields v in i<=j steps, *)
      (* set_lists xs vs (def_funs fds fds (M.empty _) (M.empty _)) = Some ρ_xvs -> *)
      set_lists xs vs (def_funs fds fds ρ ρ) = Some ρ_xvs ->
      to_nat cin <= j ->
      (ρ_xvs, e, cin) ⇓cps (v, cout) ->
      (** then the corresponding C call evaluates to (m', cv), *)
      Forall2 (fun cv i => get_ith args (Z.of_N i) = Some cv)
              (skipn n_param cvs) (skipn n_param indices) ->
      m |= ∃ nursery_b alloc_o limit_o nalloc,
           valid_mem nursery_b alloc_o limit_o alloc_o limit_o tinfo_b tinfo_o
                     args ss cvss nalloc values frame ->
      values |-- outliers ⋆ Pure True ->
      has_shapes values vss cvss ->
      exists m' cv cvss' values',
      eval_funcall prog_genv m fn (Vptr tinfo_b tinfo_o :: firstn n_param cvs) Events.E0 m' cv /\
      (** and m' is still a valid CertiCoq memory, *)
      m' |= ∃ nursery_b alloc_o limit_o args nalloc,
            valid_mem nursery_b alloc_o limit_o alloc_o limit_o tinfo_b tinfo_o
                      args ss cvss' nalloc values' frame /\
      values' |-- outliers ⋆ Pure True /\
      compatible_shapes values values' vss cvss cvss' /\
      (** and cv is related to v at level j-i *)
      rel_val (j - to_nat cin) v values' cv
    end
  | _, _ => False
  end.

End ValueRelation.

(** L6 values are related to (C value, mpred) pairs *)
Fixpoint rel_val (k : nat) := fun v '(P, cv) => 
  rel_val_aux (fun k v P cv => rel_val k v (P, cv)) k v P cv.
Notation "v '~ᵥ{' k '}' cv" := (rel_val k v cv) (at level 80).

Lemma rel_val_eqn k v P cv :
  rel_val k v (P, cv) = rel_val_aux (fun k v P cv => rel_val k v (P, cv)) k v P cv.
Proof. now destruct k. Qed.

Definition env_get : Clight.env * Clight.temp_env -> ident -> option Values.val :=
  fun '(env, tenv) x =>
  match tenv!x, env!x, Genv.find_symbol prog_genv x with
  | Some v, _, _ => Some v
  | None, Some (b, _), _
  | None, None, Some b => Some (Vptr b O.zero)
  | _, _, _ => None
  end.
Infix "!!!" := env_get (at level 60, no associativity).

Definition rel_env k := fun S ρ '(env, tenv, m) =>
  forall x, x \in S ->
  match! ρ!x with Some v in
  match! (env, tenv) !!! x with Some cv in
  v ~ᵥ{k} (m, cv).
Notation "ρ '~ₑ{' k ',' S '}' envm" := (rel_env k S ρ envm) (at level 80).

(** ** Antimonotonicity of the logical relation *)

(* TODO: hoist and maybe find better way to express this theorem *)
Lemma mapi_rel {A B} (R : B -> B -> Prop) op z (f g : _ -> A -> B) i (xs : list A) :
  forall (Hfg_ok : forall i x, List.In x xs -> R (f i x) (g i x))
    (HR_z_ok : R z z)
    (HR_op_ok : forall x y x' y', R x y -> R x' y' -> R (op x x') (op y y')),
  R (fold_right op z (mapi f i xs)) (fold_right op z (mapi g i xs)).
Proof.
  intros; revert i; induction xs as [|x xs IHxs]; cbn; [easy|]; intros i.
  apply HR_op_ok; [apply Hfg_ok; now left|].
  apply IHxs; intros i' x' Hin; apply Hfg_ok; now right.
Qed.

Fixpoint sizeof_val v :=
  match v with
  | Vconstr t vs => 1 + fold_right (fun v n => sizeof_val v + n) 0 vs
  | Vfun ρ fds f => 1
  | Vint _ => 0
  end.

Arguments Z.mul : simpl never.
Arguments Genv.find_funct : simpl never.
Lemma rel_val_antimon : forall j k v m cv,
  j <= k ->
  v ~ᵥ{k} (m, cv) ->
  v ~ᵥ{j} (m, cv).
Proof.
  intros j k; revert j.
  induction k as [k IHk] using lt_wf_ind.
  intros j v; revert j.
  remember (sizeof_val v) as sv eqn:Hsv; generalize dependent v.
  induction sv as [sv IHsv] using lt_wf_ind.
  intros v Hsv j m cv Hle.
  rewrite !rel_val_eqn; destruct v as [t vs|ρ fds f|i].
  - simpl; destruct (get_ctor_rep _ _) as [| [tag|tag arity]] eqn:Hrep; auto.
    destruct cv; auto.
    intros [cvs [Hm Hrel]]; exists cvs; split; [easy|].
    rewrite Forall2'_spec in *.
    clear Hm; generalize dependent sv.
    induction Hrel; intros sv IHsv Hsv; constructor.
    + rewrite <- rel_val_eqn in *. eapply IHsv; eauto. cbn in Hsv; lia.
    + eapply (IHHrel (sizeof_val (Vconstr t l))); eauto.
      intros; eapply IHsv; eauto. cbn in *; lia.
  - simpl; destruct cv; auto.
    (* destruct (M.bempty ρ); auto. *)
    destruct (find_def f fds) as [[[t xs] e] |] eqn:Hfind; auto.
    destruct (calling_convention t) as [[arity indices] |] eqn:Hindices; auto.
    destruct (Genv.find_funct _ _) as [fn|] eqn:Hfunct; auto.
    intros [Hty Hfuture_call]; split; [auto|]; intros*Hlt; destruct j; [easy|].
    intros Hvs_ok Hρ_xvs Hfuel Hbstep Hrest_args Hm.
    replace (j - (j - j0)) with j0 in * by lia.
    destruct k as [|k]; [lia|].
    specialize Hfuture_call with (j := j0).
    replace (k - (k - j0)) with j0 in Hfuture_call by lia.
    eapply Hfuture_call; eauto; lia.
  - auto.
Qed.

Lemma rel_env_antimon j k S ρ env tenv m :
  j <= k ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  ρ ~ₑ{j, S} (env, tenv, m).
Proof.
  intros Hle Hk x Hx; specialize (Hk x Hx).
  destruct (ρ ! x); [|easy]; lazy zeta in *.
  destruct ((env, tenv) !!! x); [|easy].
  eapply rel_val_antimon; eauto.
Qed.

Lemma rel_env_antimon_S k S1 S2 ρ env tenv m :
  S1 \subset S2 ->
  ρ ~ₑ{k, S2} (env, tenv, m) ->
  ρ ~ₑ{k, S1} (env, tenv, m).
Proof. intros Hle Hk x Hx; now apply Hk, Hle. Qed.

(** ** Lemmas about the environment relation *)

Lemma rel_env_gss k S x v cv ρ env tenv m :
  v ~ᵥ{k} (m, cv) ->
  ρ ~ₑ{k, S \\ [set x]} (env, tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (env, M.set x cv tenv, m).
Proof.
  intros Hv Hρ x' Hx'; unfold "!!!".
  destruct (M.elt_eq x x') as [|Hne]; [subst x'; now rewrite !M.gss|].
  rewrite !M.gso by auto.
  apply Hρ; constructor; [auto|now inversion 1].
Qed.

Lemma rel_env_gss_sing k x v cv ρ env tenv m :
  v ~ᵥ{k} (m, cv) ->
  M.set x v ρ ~ₑ{k, [set x]} (env, M.set x cv tenv, m).
Proof.
  intros Hv x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [|now inv Hx'].
  subst x'; unfold "!!!"; now rewrite !M.gss.
Qed.

Lemma rel_env_gso k S x v cv ρ env tenv m :
  ~ x \in S ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (env, M.set x cv tenv, m).
Proof.
  intros Hin Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [easy|].
  unfold "!!!"; rewrite !M.gso by auto. now apply Hρ.
Qed.

Lemma rel_env_union k S1 S2 ρ env tenv m :
  ρ ~ₑ{k, S1 :|: S2} (env, tenv, m) <->
  ρ ~ₑ{k, S1} (env, tenv, m) /\ ρ ~ₑ{k, S2} (env, tenv, m).
Proof.
  split; [intros HS12|intros [HS1 HS2]].
  - split; intros x Hx; now apply HS12.
  - intros x Hx; inv Hx; [apply HS1|apply HS2]; easy.
Qed.

Lemma rel_val_fun_mem k ρ fds f m m' cv :
  Vfun ρ fds f ~ᵥ{k} (m, cv) ->
  Vfun ρ fds f ~ᵥ{k} (m', cv).
Proof. rewrite !rel_val_eqn; intros H; exact H. Qed.

Fixpoint val_ind'' (P : cps.val -> Prop)
         (Hconstr : forall c vs, (forall v, List.In v vs -> P v) -> P (Vconstr c vs))
         (Hfun : forall ρ fds f, P (Vfun ρ fds f))
         (Hint : forall z, P (Vint z))
         v {struct v} : P v.
Proof.
  destruct v as [c vs|ρ fds f|z].
  - apply Hconstr.
    induction vs as [|v vs IHvs]; [inversion 1|].
    intros v' [Hin|Hin]; [subst v'|].
    + apply val_ind''; assumption. Guarded.
    + apply IHvs, Hin.
  - apply Hfun.
  - apply Hint.
Qed.

Lemma All_spec {A} (P : A -> Prop) xs :
  All (map P xs) <-> forall x, List.In x xs -> P x.
Proof.
  induction xs as [|x xs IHxs]; [now cbn|cbn].
  rewrite IHxs; intuition (eauto||tauto||congruence).
Qed.

Lemma rel_val_compatible_shape k F P P' m m' v cv cv' :
  is_frame F ->
  m |= F P ->
  v ~ᵥ{k} (P, cv) ->
  compatible_shape P P' v cv cv' ->
  m' |= F P' ->
  v ~ᵥ{k} (P', cv').
Proof.
  intros HF Hm Hv Hcompat Hm'.
  revert cv cv' Hv Hcompat; induction v as [c vs IHvs|ρ fds f|z] using val_ind'';
   intros cv cv' Hv Hcompat.
  - rewrite !rel_val_eqn in *; simpl in *.
    destruct (get_ctor_rep _ _) as [|rep]; auto.
    destruct rep as [t'|t' a]; auto; [intuition congruence|].
    destruct cv; auto; destruct cv'; auto.
    rename i into o, b0 into b', i0 into o'.
    destruct Hv as [cvs [Hvs Hvs_rel]].
    destruct Hcompat as [cvs_ [cvs' [Hlen [Hcvs_ [Hcvs' Hcompat]]]]].
    assert (Hcvs : vint (rep_boxed t' a) :: cvs_ = vint (rep_boxed t' a) :: cvs).
    { eapply mapsto_unique with (P := P); eauto.
      cbn; do 2 f_equal.
      rewrite Forall2'_spec in Hvs_rel; apply Forall2_length in Hvs_rel.
      cbn in *; lia. }
    inv Hcvs. exists cvs'; split; auto.
    rewrite Forall2'_spec in *.
    clear Hvs Hcvs_ Hlen Hcvs'.
    revert cvs' Hcompat; induction Hvs_rel; intros cvs' Hcompat.
    + destruct cvs'; inv Hcompat; constructor.
    + destruct cvs' as [|cv' cvs']; [inv Hcompat|constructor].
      * rewrite <- rel_val_eqn in *.
        eapply IHvs; eauto; [now left|].
        now cbn in Hcompat.
      * eapply IHHvs_rel; eauto; [|now inv Hcompat].
        intros; eapply IHvs; eauto; now right.
  - cbn in Hcompat. destruct cv; auto; destruct cv'; auto.
    destruct Hcompat as [<- <-]; eapply rel_val_fun_mem; eauto.
  - cbn in Hcompat; destruct Hcompat as [-> <-].
    rewrite !rel_val_eqn in *; apply Hv.
Qed.

(* TODO hoist *)
Lemma mpred_Mem_unchanged F m' S m :
  is_frame F ->
  m |=_{S} F (Mem m') ->
  Mem.unchanged_on (fun b o => dom_mem m' (b, o)) m' m.
Proof.
  inversion 1.
  { intros [Hm Hsame].
    eapply Mem.unchanged_on_implies; eauto.
    now intros; apply Hm. }
  1: rewrite frame_swap_hole by auto.
  2: rewrite sepcon_comm, frame_swap_hole by auto.
  all:
    cbn; intros Hexand; decompose [ex and] Hexand; clear Hexand;
    eapply Mem.unchanged_on_implies; eauto; intros;
    now match goal with H : _ <--> dom_mem _ |- _ => rewrite Ensemble_iff_In_iff in H; rewrite H end.
Qed.

Section TRANSLATE_BODY_CORRECT.

Context (locals : FVSet).

(** * Main theorem *)

Arguments rel_val : simpl never.
Arguments rel_env : simpl never.

Ltac normalize_occurs_free_in H :=
  eapply rel_env_antimon_S in H; [|normalize_occurs_free; apply Included_refl].

Definition postcond env tenv m stmt P :=
  exists tenv' m' out,
  exec_stmt prog_genv env tenv m stmt Events.E0 tenv' m' out /\
  P tenv' m' out.
Definition postcond' env tenv m stmt P :=
  exists tenv' m' cv,
  (env, tenv, m, stmt) ⇓ (tenv', m', cv) /\
  P tenv' m' cv.

Lemma postcond'_refl env tenv m stmt P :
  postcond' env tenv m stmt P -> postcond' env tenv m stmt P.
Proof. auto. Qed.

Lemma postcond'_spec env tenv m stmt P :
  postcond' env tenv m stmt P <->
  postcond env tenv m stmt
           (fun tenv' m' out =>
              match out with
              | Out_return (Some (cv, ty)) => P tenv' m' cv /\ ty = value
              | _ => False
              end).
Proof.
  split; intros [tenv' [m' [output [Hexec HP]]]]; exists tenv', m'.
  - exists (Out_return (Some (output, value))); split_ands; auto.
  - destruct output; auto; destruct o as [[output value'] |]; auto.
    destruct HP as [HP ->]; eauto.
Qed.

Lemma fwd_red env tenv m s env' tenv' m' s' P :
  (env, tenv, m, s) --> (env', tenv', m', s') ->
  postcond env' tenv' m' s' P ->
  postcond env tenv m s P.
Proof.
  intros Hred [tenv'' [m'' [cv [Hstep HP]]]].
  exists tenv'', m'', cv; split; auto.
Qed.

Ltac fwd H :=
  (eapply fwd_red; [eapply H|]) ||(apply postcond'_refl; rewrite postcond'_spec; eapply fwd_red; [eapply H|]).

(* TODO lemmas like forward_set, forward_assign, ...
   to step through generated code in proofs *)

(* TODO prove an induction scheme for values with IH like: Forall P vs -> P (Vconstr c vs) *)
(* TODO lemmas about has_shape and friends and subheaps;
   e.g. has_shape v m cv -> unchanged_on S m m' -> has_shape v m' cv *)

Lemma typeof_c_int i t : typeof (c_int i t) = t.
Proof. unfold c_int; now destruct Archi.ptr64. Qed.

Lemma eval_expr_int ge env tenv m i :
  eval_expr ge env tenv m (c_int i value) (vint i).
Proof. unfold c_int, vint; destruct Archi.ptr64; constructor. Qed.
Hint Resolve eval_expr_int : EvalDB.

Lemma sem_ptr_add ge b o i m :
  sem_add ge (Vptr b o) (tptr value) (vint i) value m =
  Some (Vptr b (O.repr (O.unsigned o + i*word_size)))%Z.
Proof.
  unfold value, tptr, vint, word_size, size_chunk, word_chunk.
  destruct Archi.ptr64 eqn:Harchi; cbn; do 2 f_equal.
  - unfold Ptrofs.add.
    unfold Ptrofs.mul.
    apply O.eqm_samerepr.
    apply O.eqm_add; [apply O.eqm_refl|].
    eapply O.eqm_trans; [apply O.eqm_sym, O.eqm_unsigned_repr|].
    rewrite Z.mul_comm.
    apply O.eqm_mult; [|apply O.eqm_refl].
    erewrite O.agree64_of_int_eq; [|now apply O.agree64_repr].
    apply O.eqm_sym, O.eqm_unsigned_repr.
  - unfold Ptrofs.add.
    unfold Ptrofs.mul.
    apply O.eqm_samerepr.
    apply O.eqm_add; [apply O.eqm_refl|].
    eapply O.eqm_trans; [apply O.eqm_sym, O.eqm_unsigned_repr|].
    rewrite Z.mul_comm.
    apply O.eqm_mult; [|apply O.eqm_refl].
    unfold O.of_intu, O.of_int.
    apply O.eqm_sym.
    eapply O.eqm_trans; [|apply O.eqm_unsigned_repr].
    rewrite <- O.eqm32 by auto.
    apply Int.eqm_unsigned_repr.
Qed.
Hint Resolve sem_ptr_add : EvalDB.

Lemma eval_ptr_add ge env tenv m i p b o :
  typeof p = tptr value ->
  eval_expr ge env tenv m p (Vptr b o) ->
  eval_expr ge env tenv m (p +' c_int i value) (Vptr b (O.repr (O.unsigned o + i*word_size))).
Proof.
  intros Hp Heval; econstructor; cbn; eauto with EvalDB.
  now rewrite typeof_c_int, Hp, sem_ptr_add.
Qed.
Hint Resolve eval_ptr_add : EvalDB.
Hint Constructors eval_expr eval_lvalue : EvalDB.

Lemma eval_ptr_add_cast ge env tenv m i p b o :
  typeof p = tptr value ->
  eval_expr ge env tenv m p (Vptr b o) ->
  eval_expr ge env tenv m (Ecast (p +' c_int i value) value) (Vptr b (O.repr (O.unsigned o + i*word_size))).
Proof. intros Hp Heval; econstructor; eauto with EvalDB. Qed.
Hint Resolve eval_ptr_add_cast : EvalDB.

Lemma eval_unfold env tenv m e v :
  eval_expr prog_genv env tenv m e v ->
  (env, tenv, m, e) ⇓ᵣ v.
Proof. auto. Qed.
Hint Resolve eval_unfold : EvalDB.

Lemma evall_unfold env tenv m e b o :
  eval_lvalue prog_genv env tenv m e b o ->
  (env, tenv, m, e) ⇓ₗ (b, o).
Proof. auto. Qed.
Hint Resolve evall_unfold : EvalDB.

Fixpoint NoDup' {A} (xs : list A) :=
  match xs with
  | [] => True
  | x :: xs => All (map (fun x' => x <> x') xs) /\ NoDup' xs
  end.

Lemma notin_spec {A} (x : A) xs : 
  All (map (fun x' => x <> x') xs) <-> ~ List.In x xs.
Proof.
  induction xs as [|x' xs IHxs]; [cbn; tauto|].
  cbn; rewrite IHxs.
  assert (x <> x' <-> x' <> x) by intuition congruence.
  tauto.
Qed.

Lemma NoDup'_spec {A} (xs : list A) :
  NoDup' xs <-> NoDup xs.
Proof.
  induction xs as [|x xs IHxs]; [split; constructor|].
  cbn; now rewrite NoDup_cons_iff, notin_spec.
Qed.

(* TODO delete *)
Fixpoint exp_bv_list e :=
  match e with
  | Econstr x t ys e' => x :: exp_bv_list e'
  | Ecase x cs => fold_right (@app _) [] (map (fun '(c, e) => exp_bv_list e) cs)
  | Eproj x t n v e' => x :: exp_bv_list e'
  | Eletapp x f t ys e' => x :: exp_bv_list e'
  | Efun fds e' => fds_bv_list fds ++ exp_bv_list e'
  | Eapp f t ys => []
  | Eprim x p ys e' => x :: exp_bv_list e'
  | Ehalt x => []
  end%list
with fds_bv_list fds :=
  match fds with
  | Fnil => []
  | Fcons f t ys e fds' => f :: ys ++ exp_bv_list e ++ fds_bv_list fds'
  end%list.

(* TODO delete *)
Lemma exp_bv_list_spec e :
  FromList (exp_bv_list e) <--> bound_var e
with fds_bv_list_spec fds :
  FromList (fds_bv_list fds) <--> bound_var_fundefs fds.
Proof.
  all: rename exp_bv_list_spec into IHe, fds_bv_list_spec into IHfds.
  - destruct e; try solve [cbn; normalize_bound_var; rewrite ?FromList_cons, ?IHe; sets].
    + induction l as [| [c e] ces IHces]; cbn; normalize_bound_var; [clear IHe IHfds; sets|].
      now rewrite FromList_app, IHe, IHces.
    + now cbn; rewrite FromList_app, IHe, IHfds; normalize_bound_var. Guarded.
  - destruct fds as [f t xs e fds|]; [|now cbn; normalize_bound_var].
    now cbn; normalize_bound_var; rewrite FromList_cons, !FromList_app, IHe, IHfds.
Qed.

Fixpoint exp_vars_list e :=
  match e with
  | Econstr x t ys e' => x :: ys ++ exp_vars_list e'
  | Ecase x cs => x :: fold_right (@app _) [] (map (fun '(c, e) => exp_vars_list e) cs)
  | Eproj x t n y e' => x :: y :: exp_vars_list e'
  | Eletapp x f t ys e' => x :: f :: ys ++ exp_vars_list e'
  | Efun fds e' => fds_vars_list fds ++ exp_vars_list e'
  | Eapp f t ys => f :: ys
  | Eprim x p ys e' => x :: ys ++ exp_vars_list e'
  | Ehalt x => [x]
  end%list
with fds_vars_list fds :=
  match fds with
  | Fnil => []
  | Fcons f t ys e fds' => f :: ys ++ exp_vars_list e ++ fds_vars_list fds'
  end%list.

Lemma exp_vars_list_spec e :
  FromList (exp_vars_list e) <--> used_vars e
with fds_vars_list_spec fds :
  FromList (fds_vars_list fds) <--> used_vars_fundefs fds.
Proof.
  all: rename exp_vars_list_spec into IHe, fds_vars_list_spec into IHfds.
  - destruct e;
      try solve [cbn; normalize_used_vars; rewrite ?FromList_cons, ?FromList_app, ?FromList_nil, ?IHe; sets].
    Guarded.
    induction l as [| [c e] ces IHces]; cbn; normalize_used_vars; [clear IHe IHfds; sets|].
    rewrite FromList_cons, FromList_app, Union_assoc, (Union_commut [set v]), <- Union_assoc.
    rewrite <- FromList_cons, IHces, IHe; sets. Guarded.
  - destruct fds as [f t xs e fds|]; [|now cbn; normalize_used_vars].
    now cbn; normalize_used_vars; rewrite FromList_cons, !FromList_app, IHe, IHfds, !Union_assoc.
Qed.

Hint Extern 1 ((M.set _ _ _) ! _ = Some _) => rewrite M.gso by easy : EvalDB.
Hint Resolve M.gss : EvalDB.

Lemma sem_cast_ptr b o m :
  sem_cast (Vptr b o) value (tptr value) m = Some (Vptr b o).
Proof. unfold sem_cast, value; cbn; destruct Archi.ptr64; now cbn. Qed.
Hint Resolve sem_cast_ptr : EvalDB.

Lemma sem_cast_ptr' b o ty m :
  sem_cast (Vptr b o) value (tptr ty) m = Some (Vptr b o).
Proof. unfold sem_cast, value; cbn; destruct Archi.ptr64; now cbn. Qed.
Hint Resolve sem_cast_ptr : EvalDB.
Hint Extern 1 (eval_expr _ _ _ _ (make_tag _) _) => unfold make_tag : EvalDB.

Lemma sem_cast_int_same i m :
  sem_cast (vint i) value value m = Some (vint i).
Proof. unfold sem_cast, value, vint; destruct Archi.ptr64; cbn; now destruct Archi.ptr64. Qed.
Hint Resolve sem_cast_int_same : EvalDB.

Lemma access_mode_value :
  access_mode value = By_value word_chunk.
Proof. unfold value, word_chunk; now destruct Archi.ptr64. Qed.
Hint Resolve access_mode_value : EvalDB.

Lemma repr_unsigned_addl e1 e2 :
  O.repr (O.unsigned (O.repr e1) + e2) = O.repr (e1 + e2).
Proof. apply O.eqm_samerepr; auto with ints. Qed.

Lemma sem_cast_ptr_same b o m :
  sem_cast (Vptr b o) value value m = Some (Vptr b o).
Proof. unfold sem_cast, value; destruct Archi.ptr64 eqn:Harchi; cbn; now rewrite Harchi. Qed.
Hint Resolve sem_cast_ptr_same : EvalDB.

Lemma sem_cast_ptr_ptr_same b o m :
  sem_cast (Vptr b o) (tptr value) (tptr value) m = Some (Vptr b o).
Proof. unfold sem_cast, tptr, value; destruct Archi.ptr64 eqn:Harchi; now cbn. Qed.
Hint Resolve sem_cast_ptr_ptr_same : EvalDB.

Definition val_defined_wf v :=
  if Archi.ptr64 then match v with Vlong _ | Vptr _ _ => True | _ => False end
  else match v with Values.Vint _ | Vptr _ _ => True | _ => False end.
Lemma val_defined_wf_wf v : val_defined_wf v -> val_wf v.
Proof. unfold val_wf, val_defined_wf; destruct Archi.ptr64, v; tauto. Qed.
Hint Resolve val_defined_wf_wf : EvalDB.

Lemma sem_cast_wf_same v m :
  val_defined_wf v -> sem_cast v value value m = Some v.
Proof. unfold val_defined_wf, sem_cast, value; destruct Archi.ptr64 eqn:Harchi; cbn; rewrite Harchi; destruct v; tauto. Qed.
Hint Resolve sem_cast_wf_same : EvalDB.

Hypothesis is_ptr_spec :
  forall m v,
  val_defined_wf v -> exists cv,
  Events.external_functions_sem "is_ptr"
    (mksignature [ast_value] None cc_default) prog_genv
    [v] m Events.E0 cv m /\
  (forall b o, v = Vptr b o -> cv = Vtrue) /\
  (forall i, v = vint i -> cv = Vfalse).

(* TODO hoist *)
Transparent Mem.store.
Lemma store_ex b o p i v vs m :
  perm_order p Writable ->
  m |= ((b, o) ↦_{p} vs) ⋆ Pure True ->
  (0 <= i < #|vs|)%Z -> exists m',
  store m b (o + i*word_size) v = Some m'.
Proof.
  intros Hperm Hm Hbound.
  unfold store, Mem.store; cbn.
  destruct (Mem.valid_access_dec _ _ _ _ _) as [|Hwat]; [eauto|].
  contradiction Hwat.
  cbn in Hm; decompose [ex and] Hm; clear Hm.
  unfold Mem.valid_access; split.
  - eapply Mem.range_perm_implies; eauto.
    match goal with
    | H : Mem.range_perm _ _ _ _ _ _ |- _ =>
      intros ??; eapply H; superlia
    end.
  - apply Z.divide_add_r; [easy|].
    rewrite align_word_chunk_size.
    apply Z.divide_factor_r.
Qed.
Opaque Mem.store.

(* TODO hoist *)
Lemma is_frame_comp F G :
  is_frame F ->
  is_frame G ->
  is_frame (fun h => F (G h)).
Proof. induction 1; eauto with FrameDB. Qed.
Hint Resolve is_frame_comp : FrameDB.

Lemma frame_stuff_hole F S P Q m :
  is_frame F ->
  m |=_{S} F P ⋆ Q <-> m |=_{S} F (P ⋆ Q).
Proof.
  intros HF; revert S; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros S.
  - easy.
  - rewrite sepcon_assoc.
    rewrite_equiv (fun H => F P ⋆ H) sepcon_comm.
    rewrite_equiv_l (fun H => H ⋆ Q') IHF.
    now rewrite sepcon_assoc.
  - rewrite_equiv_l (fun H => P' ⋆ H) IHF.
    now rewrite sepcon_assoc.
  - rewrite sepcon_assoc.
    rewrite_equiv (fun H => P ⋆ H) sepcon_comm.
    now rewrite sepcon_assoc.
  - now rewrite sepcon_assoc.
Qed.

(* TODO hoist *)
Lemma mpred_frame_in F P m :
  is_frame F ->
  m |= F P ->
  m |= P ⋆ Pure True.
Proof.
  intros HF; revert P; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros P; unfold "|=" in *.
  { intros H; exists (dom_mem m), (Empty_set _).
    split_ands; sets; eauto; cbn; sets. }
  - rewrite frame_stuff_hole by auto.
    intros Hm; apply IHF in Hm.
    rewrite sepcon_assoc in Hm; revert Hm.
    apply frame_entail; auto with FrameDB; apply entail_True.
  - rewrite sepcon_comm, frame_swap_hole by auto.
    rewrite sepcon_comm; apply frame_entail; auto with FrameDB; apply entail_True.
  - apply frame_entail; auto with FrameDB; apply entail_True.
  - rewrite sepcon_comm; apply frame_entail; auto with FrameDB; apply entail_True.
Qed.

(* TODO hoist *)
Lemma store_dom_mem b o v m m' :
  store m b o v = Some m' ->
  dom_mem m <--> dom_mem m'.
Proof.
  intros Hm; apply Ensemble_iff_In_iff; intros [b' o']; unfold In, dom_mem.
  split; intros Hperm.
  - eapply Mem.perm_store_1; eauto.
  - eapply Mem.perm_store_2; eauto.
Qed.

Lemma fwd_store F env tenv m offset ty a i e b o p v s vs P :
  is_frame F ->
  val_defined_wf v ->
  (env, tenv, m, a) ⇓ᵣ (Vptr b (O.repr (O.unsigned o + offset*word_size))) ->
  (env, tenv, m, e) ⇓ᵣ v ->
  typeof a = value \/ typeof a = tptr ty ->
  typeof e = value ->
  (0 <= offset <= 1)%Z ->
  (0 <= offset + i < #|vs|)%Z ->
  perm_order p Writable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall m',
    store m b (O.unsigned o + (offset + i)*word_size)%Z v = Some m' ->
    m' |= F ((b, O.unsigned o) ↦_{p} set_ith vs (offset + i) v)%Z ->
    postcond env tenv m' s P) ->
  postcond env tenv m (a.[i] :::= e.; s)%C P.
Proof.
  intros HF Hv Ha He Htypeof_a Htypeof_e Hoffset Hi Hperm Hm Hcont.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (v := v) in Hm_in; eauto.
  destruct Hm_in as [m' Hstore].
  pose proof Hstore as Hmpred.
  eapply mpred_store in Hmpred; eauto; [|auto with EvalDB].
  rewrite mpred_Same_set in Hmpred; [|eapply store_dom_mem; eauto].
  specialize (Hcont _ Hstore Hmpred).
  fwd Cred_assign.
  - constructor.
    apply eval_ptr_add; auto.
    econstructor; eauto with EvalDB.
    destruct Htypeof_a as [Hty|Hty]; rewrite Hty; eauto with EvalDB.
  - eauto with EvalDB.
  - rewrite Htypeof_e; eauto with EvalDB.
  - eapply assign_loc_value; [cbn; rewrite access_mode_value; reflexivity|].
    rewrite <- Hstore; unfold Mem.storev, store; f_equal.
    apply mpred_frame_in in Hmpred; [|auto].
    cbn in Hmpred; decompose [ex and] Hmpred; clear Hmpred.
    rewrite O.unsigned_repr; rewrite O.unsigned_repr; superlia.
  - apply Hcont.
Qed.

Lemma fwd_store' F env tenv m a i e ty b o p v s vs P :
  is_frame F ->
  val_defined_wf v ->
  (env, tenv, m, a) ⇓ᵣ (Vptr b o) ->
  (env, tenv, m, e) ⇓ᵣ v ->
  typeof a = value \/ typeof a = tptr ty ->
  typeof e = value ->
  (0 <= i < #|vs|)%Z ->
  perm_order p Writable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall m',
    store m b (O.unsigned o + i*word_size)%Z v = Some m' ->
    m' |= F ((b, O.unsigned o) ↦_{p} set_ith vs i v)%Z ->
    postcond env tenv m' s P) ->
  postcond env tenv m (a.[i] :::= e.; s)%C P.
Proof.
  intros; eapply fwd_store with (offset := 0%Z); eauto; [|lia].
  replace (O.unsigned o + 0*word_size)%Z with (O.unsigned o) by lia.
  now rewrite O.repr_unsigned.
Qed.

Lemma vint_wf i : val_defined_wf (vint i).
Proof. unfold val_defined_wf, vint; now destruct Archi.ptr64. Qed.
Hint Resolve vint_wf : EvalDB.

(* TODO hoist *)
Lemma skipn_len {A} n (xs : list A) :
  (0 <= n <= #|xs| -> #|skipn (Z.to_nat n) xs| = #|xs| - n)%Z.
Proof.
  remember (Z.to_nat n) as nat_n eqn:Hnat; generalize dependent n.
  revert xs; induction nat_n as [|nat_n IHnat]; intros xs n Hnat; [cbn; lia|].
  destruct xs as [|x xs]; [cbn; lia|].
  specialize (IHnat xs (Z.pred n)).
  cbn; intros Hn; rewrite IHnat; lia.
Qed.

(* TODO hoist *)
Lemma firstn_len {A} n (xs : list A) :
  (0 <= n <= #|xs| -> #|firstn (Z.to_nat n) xs| = n)%Z.
Proof.
  remember (Z.to_nat n) as nat_n eqn:Hnat; generalize dependent n.
  revert xs; induction nat_n as [|nat_n IHnat]; intros xs n Hnat; [cbn; lia|].
  destruct xs as [|x xs]; [cbn; lia|].
  specialize (IHnat xs (Z.pred n)).
  cbn; rewrite !Nat2Z.inj_succ; intros H; rewrite IHnat; lia.
Qed.

Lemma wordsize_mul_div_le n m : (n*word_size <= m -> n <= m/word_size)%Z.
Proof.
  intros H; apply Z_div_le with (c := word_size) in H; [|superlia].
  now rewrite Z_div_mult in H by superlia.
Qed.

Lemma wordsize_mul_div n m : (n*word_size = m -> n = m/word_size)%Z.
Proof.
  intros H; apply f_equal with (f := fun x => (x/word_size)%Z) in H.
  now rewrite Z_div_mult in H by superlia.
Qed.

Lemma mem_nursery_alloc n m nursery_b alloc_o limit_o
      tinfo_b tinfo_o ss cvss m_values frame :
  (0 <= n*word_size <= O.unsigned limit_o - O.unsigned alloc_o)%Z ->
  m |= ∃ args nalloc talloc_o tlimit_o,
       valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o tinfo_b tinfo_o
                 args ss cvss nalloc m_values frame ->
  m |= (∃ vs, (nursery_b, O.unsigned alloc_o) ↦_{Writable} vs WITH #|vs| = n) ⋆
       ∃ args nalloc talloc_o tlimit_o,
       valid_mem nursery_b talloc_o tlimit_o
                 (O.repr (O.unsigned alloc_o + n*word_size))%Z
                 limit_o tinfo_b tinfo_o
                 args ss cvss nalloc m_values frame.
Proof.
  intros Hbound Hm. unfold "|=" in *.
  destruct_ex args Hm; destruct_ex nalloc Hm.
  destruct_ex talloc_o Hm; destruct_ex tlimit_o Hm.
  unfold valid_mem in *.
  match goal with
  | Hm : _ |=_{_} ?P ⋆ _ ⋆ ?Q |- _ |=_{_} ?R ⋆ _ =>
    destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) free_space Hm;
    destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) Hfree_space Hm;
    exists_ex_ctx (fun H => R ⋆ H) args;
    exists_ex_ctx (fun H => R ⋆ H) nalloc;
    exists_ex_ctx (fun H => R ⋆ H) talloc_o;
    exists_ex_ctx (fun H => R ⋆ H) tlimit_o
  end.
  match goal with
  | |- _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
    exists_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R) (skipn (Z.to_nat n) free_space);
    split_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R)
  end.
  { pose proof Hfree_space as Hfree_space_old.
    destruct Hfree_space as [Hfree_space Hbound'].
    apply wordsize_mul_div in Hfree_space.
    destruct Hbound as [Hbound_lower Hbound].
    apply wordsize_mul_div_le in Hbound.
    rewrite skipn_len, Hfree_space by superlia.
    rewrite O.unsigned_repr.
    - unfold Z.sub. rewrite Z.opp_add_distr, Z.add_assoc.
      do 2 change (?x + - ?y)%Z with (x - y)%Z.
      rewrite <- !(proj1 Hfree_space_old).
      rewrite Z_div_mult by superlia.
      now rewrite Z.mul_sub_distr_r.
    - cbn in Hm; decompose [ex and] Hm; superlia. }
  match goal with
  | |- _ |=_{_} _ ⋆ ?P =>
    exists_ex_ctx (fun H => H ⋆ P) (firstn (Z.to_nat n) free_space);
    split_ex_ctx (fun H => H ⋆ P)
  end.
  { pose proof Hfree_space as Hfree_space_old.
    destruct Hfree_space as [Hfree_space Hbound'].
    apply wordsize_mul_div in Hfree_space.
    destruct Hbound as [Hbound_lower Hbound].
    apply wordsize_mul_div_le in Hbound.
    rewrite firstn_len by superlia. lia. }
  rewrite <- (firstn_skipn (Z.to_nat n) free_space) in Hm.
  match type of Hm with
  | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
    rewrite_equiv_in (fun H => P ⋆ H ⋆ Q) mapsto_app Hm;
    rewrite_equiv_in (fun H => P ⋆ H) sepcon_assoc Hm;
    rewrite <- sepcon_assoc in Hm
  end.
  match type of Hm with
  | _ |=_{_} (_ ⋆ _) ⋆ ?Q =>
    rewrite_equiv_in (fun H => H ⋆ Q) sepcon_comm Hm;
    rewrite sepcon_assoc in Hm
  end.
  replace #|firstn (Z.to_nat n) free_space| with n in *; [rewrite O.unsigned_repr; auto|].
  - cbn in Hm; decompose [ex and] Hm; clear Hm; superlia.
  - pose proof Hfree_space as Hfree_space_old.
    destruct Hfree_space as [Hfree_space Hbound'].
    apply wordsize_mul_div in Hfree_space.
    destruct Hbound as [Hbound_lower Hbound].
    apply wordsize_mul_div_le in Hbound.
    rewrite firstn_len; superlia.
Qed.

(* TODO hoist *)
Lemma mapsto_perm_order F p b o p' vs S m :
  is_frame F ->
  perm_order p p' ->
  m |=_{S} F ((b, o) ↦_{p} vs) ->
  m |=_{S} F ((b, o) ↦_{p'} vs).
Proof.
  intros HF Hperm Hm.
  eapply frame_entail'; try eassumption.
  clear - Hperm; cbn; intros S Hm; decompose [and] Hm; clear Hm; split_ands; auto.
  eapply Mem.range_perm_implies; eauto.
Qed.

Hypothesis global_local_disjoint : forall x v,
  Genv.find_symbol prog_genv x = Some v ->
  PS.mem x locals = false.

(** non-local variables in the fun_env must be in the global environment *)
Hypothesis fenv_inv : forall x description,
  fenv!x = Some description ->
  PS.mem x locals = false ->
  Genv.find_symbol prog_genv x <> None.

(** each calling convention in fenv is well-formed *)
Hypothesis fenv_cc_inv : forall x arity inds,
  fenv!x = Some (arity, inds) ->
  length inds = N.to_nat arity /\ NoDup (skipn n_param inds) /\
  Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) (skipn n_param inds).

(** calling conventions in fenv respect calling_convention for each call site in e *)
Definition fenv_respects_tags e :=
  forall C f t,
   (exists xs, e = C |[ Eapp f t xs ]|) \/
   (exists x ys e', e = C |[ Eletapp x f t ys e' ]|) ->
   fenv ! f = calling_convention t.

Definition fenv_respects_tags_ctx C e :
  fenv_respects_tags (C |[ e ]|) ->
  fenv_respects_tags e.
Proof.
  intros HCe D f t Hcall; apply (HCe (comp_ctx_f C D)).
  destruct Hcall as [[xs Htail] | [x [ys [e' Hnontail]]]]; [left|right].
  - exists xs; rewrite <- app_ctx_f_fuse, Htail; easy.
  - exists x, ys, e'; rewrite <- app_ctx_f_fuse, Hnontail; easy.
Qed.

(** fenv does not contain any of the parameters/local variables *)
Context
  (fenv_tinfo : fenv ! tinfo_id = None)
  (fenv_alloc : fenv ! alloc_id = None)
  (fenv_limit : fenv ! limit_id = None)
  (fenv_ret : fenv ! ret_id = None)
  (fenv_case : fenv ! case_id = None)
  (fenv_roots_temp : fenv ! roots_temp_id = None).

(** env only contains the frame struct and root array *)
Definition env_inv (env : Clight.env) :=
  forall x, x <> frame_id /\ x <> roots_id -> env!x = None.

Definition tenv_inv (tenv : Clight.temp_env) :=
  (** every non-case_id x in the temp environment corresponds to a well-defined value, and
      is either a local variable or one of {tinfo, alloc, limit, ret, case_id, roots_temp} *)
  (forall x cv, x <> case_id ->
           tenv!x = Some cv ->
           (PS.mem x locals = true
            \/ x = tinfo_id
            \/ x = alloc_id
            \/ x = limit_id
            \/ x = ret_id
            \/ x = roots_temp_id) /\
           val_defined_wf cv) /\
  (forall cv, tenv!case_id = Some cv -> cv = Vtrue \/ cv = Vfalse) /\
  (** every local variable is in tenv *)
  (forall x, PS.mem x locals = true -> tenv!x <> None).

Lemma env_get_wf env tenv x v :
  x <> case_id ->
  tenv_inv tenv ->
  (env, tenv) !!! x = Some v -> val_defined_wf v.
Proof.
  unfold "!!!"; destruct (tenv!x) eqn:Htenv_get.
  - intros Hne Htenv H; inv H. eapply Htenv; eauto.
  - destruct (env!x) as [[] |].
    + now inversion 3.
    + destruct (Genv.find_symbol _ _); now inversion 3.
Qed.
Hint Resolve env_get_wf : EvalDB.

Lemma sem_cast_fptr_val cv n m :
  val_defined_wf cv ->
  sem_cast cv (fun_ty n) value m = Some cv.
Proof.
  unfold val_defined_wf, value, fun_ty, sem_cast;
  destruct Archi.ptr64 eqn:Harchi; cbn; rewrite Harchi; destruct cv; easy.
Qed.
Hint Resolve sem_cast_fptr_val : EvalDB.

Hint Extern 1 (sem_cast _ (typeof (_ _)) _ _ = _) => simpl typeof : EvalDB.
Hint Constructors deref_loc : EvalDB.

Definition ρ_inv (ρ : eval.env) :=
  (** if x is in ρ and the global env, then it must be in fun_env
      and v must be a function *)
  (forall x v b,
   ρ ! x = Some v ->
   Genv.find_symbol prog_genv x = Some b ->
   fenv ! x <> None /\ exists ρ_f fds f, v = Vfun ρ_f fds f).

Lemma eval_make_var x ρ env tenv cv m :
  x <> case_id /\ x <> frame_id /\ x <> roots_id ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  ρ!x <> None ->
  (env, tenv) !!! x = Some cv ->
  eval_expr prog_genv env tenv m (make_var fenv locals x) cv.
Proof.
  intros Hx [Henv [Htenv Hρ]] Hρ_some Henv_some.
  (* destruct (_ ! _) as [v|] eqn:Hget_ρ; [|easy]. *)
  unfold make_var; unfold "!!!" in Henv_some.
  specialize (Henv x); rewrite Henv in * by tauto.
  destruct (fenv ! x) as [[arity locs] |] eqn:Hfenv.
  - destruct (tenv!x) eqn:Hget_tenv.
    + inv Henv_some.
      pose proof Hget_tenv as Hlocals_wf.
      apply Htenv in Hlocals_wf; try easy.
      destruct Hlocals_wf as [Hlocals Hwf].
      decompose [or] Hlocals; [|now subst x..].
      destruct (PS.mem x locals); [|easy].
      eauto with EvalDB.
    + destruct (Genv.find_symbol _ _) as [b|] eqn:Hgenv; [|easy].
      erewrite global_local_disjoint; eauto.
      inv Henv_some.
      econstructor.
      { econstructor.
        - eapply eval_Evar_global; try easy.
        - eauto with EvalDB. }
      eauto with EvalDB.
  - destruct (tenv!x) eqn:Hget_tenv; [inv Henv_some; eauto with EvalDB|].
    destruct (Genv.find_symbol prog_genv x) eqn:Hgenv; [|easy].
    destruct (ρ!x) eqn:Hρx; [|congruence].
    exfalso; eapply Hρ; eauto.
Qed.

Reserved Infix "!!!!" (at level 60, no associativity).
Fixpoint get_env_list envs xs :=
  match xs with
  | [] => Some []
  | x :: xs =>
    match envs !!! x, envs !!!! xs with
    | Some cv, Some cvs => Some (cv :: cvs)
    | _, _ => None
    end
  end
where "envs !!!! xs" := (get_env_list envs xs).

(* TODO hoist *)
Fixpoint overwrite_sublist {A} (xs : list A) i ys :=
  match ys with
  | [] => xs
  | y :: ys => set_ith (overwrite_sublist xs (i + 1) ys) i y
  end%Z.

(* TODO hoist *)
Lemma set_ith_range {A} (xs : list A) i y :
  ~ (0 <= i < #|xs|)%Z ->
  set_ith xs i y = xs.
Proof.
  revert i; induction xs as [|x xs IHxs]; [easy|intros* Hget].
  cbn; destruct (Z.eq_dec i 0) as [|Hne]; [subst; cbn in *; lia|].
  rewrite IHxs; auto; cbn in *; lia.
Qed.

(* TODO hoist *)
Lemma set_ith_prefix {A} (vs ws : list A) i v :
  (i < #|vs|)%Z ->
  (set_ith (vs ++ ws) i v = set_ith vs i v ++ ws)%list.
Proof.
  revert i; induction vs as [|v' vs IHvs]; intros i.
  - cbn in *; intros H.
    now rewrite set_ith_range by lia.
  - intros Hi; cbn; destruct (Z.eq_dec i 0) as [|Hne]; [now subst|].
    now rewrite IHvs by (cbn in *; superlia).
Qed.

(* TODO hoist *)
Lemma set_ith_suffix {A} (vs ws : list A) i w :
  (#|vs| <= i)%Z ->
  (set_ith (vs ++ ws) i w = vs ++ set_ith ws (i - #|vs|) w)%list.
Proof.
  revert i; induction vs as [|v vs IHvs]; intros i; cbn.
  - now replace (Z.of_nat 0 + i)%Z with i by lia.
  - destruct (Z.eq_dec i 0) as [|Hne]; [now subst|intros H].
    rewrite IHvs by lia.
    do 2 f_equal; f_equal; superlia.
Qed.

(* TODO hoist *)
Lemma get_ith_firstn_skipn {A} i xs (x : A) :
  get_ith xs i = Some x ->
  firstn (Z.to_nat 1) (skipn (Z.to_nat i) xs) = [x].
Proof.
  revert i; induction xs as [|x' xs IHxs]; intros i Hget; [inv Hget|].
  cbn in Hget; destruct (Coqlib.zeq i 0) as [|Hne]; [subst; inv Hget|].
  - now change (Z.to_nat 0) with 0; change (Z.to_nat 1) with 1.
  - replace (Z.to_nat i) with (S (Z.to_nat (Z.pred i))) by (apply get_ith_range in Hget; lia).
    cbn; rewrite IHxs; auto; superlia.
Qed.

(* TODO hoist *)
Lemma overwrite_sublist_spec {A} (xs : list A) i ys :
  (0 <= i <= #|xs| - #|ys|)%Z ->
  (overwrite_sublist xs i ys =
   firstn (Z.to_nat i) xs ++ ys ++ skipn (Z.to_nat (i + #|ys|)) xs)%list%Z.
Proof.
  revert dependent i; induction ys as [|y ys IHys]; intros i Hi; cbn.
  - replace (i + Z.of_nat 0)%Z with i by lia.
    now rewrite firstn_skipn.
  - rewrite IHys by (cbn in *; superlia).
    rewrite set_ith_prefix by (cbn in *; rewrite firstn_len by superlia; lia).
    replace (Z.to_nat (i + 1)) with (Z.to_nat i + Z.to_nat 1) by lia.
    rewrite MCList.firstn_add.
    rewrite set_ith_suffix by (rewrite firstn_len by superlia; lia).
    rewrite firstn_len by superlia.
    replace (i - i)%Z with 0%Z by lia.
    destruct (get_ith_in_range xs i) as [x Hget]; [cbn in *; lia|].
    erewrite get_ith_firstn_skipn; eauto; cbn.
    rewrite <- !app_assoc; cbn.
    do 4 f_equal; lia.
Qed.

Lemma typeof_make_var x : typeof (make_var fenv locals x) = value.
Proof. unfold make_var; destruct (fenv!x) as [[] |]; destruct (PS.mem x locals); now cbn. Qed.
Hint Resolve typeof_make_var : EvalDB.

Lemma env_invs_project1 env tenv ρ :
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ -> env_inv env.
Proof. easy. Qed.
Hint Resolve env_invs_project1 : InvDB.

Lemma env_invs_project2 env tenv ρ :
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ -> tenv_inv tenv.
Proof. easy. Qed.
Hint Resolve env_invs_project2 : InvDB.

Lemma env_invs_project3 env tenv ρ :
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ -> ρ_inv ρ.
Proof. easy. Qed.
Hint Resolve env_invs_project3 : InvDB.

(* TODO hoist *)
Lemma set_ith_commut {A} (xs : list A) i j x_i x_j :
  i <> j -> set_ith (set_ith xs i x_i) j x_j = set_ith (set_ith xs j x_j) i x_i.
Proof.
  revert i j; induction xs as [|x xs IHxs]; [now cbn|cbn]; intros i j.
  destruct (Z.eq_dec i 0), (Z.eq_dec j 0); cbn;
  destruct (Z.eq_dec i 0), (Z.eq_dec j 0); cbn; try lia; auto.
  intros Hne; f_equal.
  now rewrite IHxs by lia.
Qed.

(* TODO hoist *)
Lemma overwrite_sublist_set_ith_comm {A} xs i j (ys : list A) y :
  ~ (i <= j < j + #|ys|)%Z ->
  overwrite_sublist (set_ith xs j y) i ys = 
  set_ith (overwrite_sublist xs i ys) j y.
Proof.
  revert i; induction ys as [|y' ys IHys]; [now cbn|cbn; intros i Hbound].
  now rewrite IHys, set_ith_commut by lia.
Qed.

(* TODO hoist *)
Lemma overwrite_sublist_snoc {A} xs i (y : A) ys :
  overwrite_sublist (set_ith xs i y) (i + 1)%Z ys = 
  overwrite_sublist xs i (y :: ys).
Proof. cbn; now rewrite overwrite_sublist_set_ith_comm by lia. Qed.

Arguments "!!!" : simpl never.
Lemma fwd_stores F ρ env tenv m offset a i ty (ys : list cps.var) p b o s vs P :
  is_frame F ->
  (forall m P,
    m |= F P ->
   (env, tenv, m, a) ⇓ᵣ (Vptr b (O.repr (O.unsigned o + offset*word_size)))) ->
  typeof a = value \/ typeof a = tptr ty ->
  (0 <= offset <= 1 /\ 0 <= offset + #|ys| <= #|vs| /\ 0 <= offset + i <= #|vs| - #|ys|)%Z ->
  ~ List.In case_id ys ->
  ~ List.In frame_id ys ->
  ~ List.In roots_id ys ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  All (map (fun x => ρ!x <> None) ys) ->
  All (map (fun x => (env, tenv)!!!x <> None) ys) ->
  perm_order p Writable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall m' vs',
    (env, tenv) !!!! ys = Some vs' ->
    m' |= F ((b, O.unsigned o) ↦_{p} overwrite_sublist vs (offset + i) vs') ->
    postcond env tenv m' s P) ->
  postcond env tenv m (statements (mapi (fun i y => a.[i] :::= make_var fenv locals y) i ys).; s)%C P.
Proof.
  intros HF Ha Hty_a Hbounds Hcase Hframe Hroots Henvs Hρ Henv Hperm Hm Hsimpler.
  revert vs m i Hm Hbounds Hsimpler; induction ys as [|y ys IHys]; intros vs m i Hm Hbounds Hsimpler.
  { cbn. fwd Cred_skip. apply (Hsimpler m []); auto. }
  cbn in Hcase,Hframe,Hroots|-*; fwd Cred_seq_assoc.
  assert (Henv_x : exists cv, (env, tenv)!!!y = Some cv).
  { cbn in Henv. destruct ((env, tenv)!!!y) eqn:Hy; [eauto|intuition congruence]. }
  destruct Henv_x as [cv Hcv].
  eapply fwd_store with (F := fun H => F H).
  4:{ eapply eval_make_var; eauto; try easy.
      apply Hρ; now rewrite FromList_cons. }
  all: try eassumption; eauto with FrameDB InvDB EvalDB; try solve[lia|cbn in *; superlia].
  eapply env_get_wf; eauto; try easy.
  intros m' Hstore Hm'.
  eapply IHys; eauto; try now cbn in *.
  { cbn in *; superlia. }
  intros m'' vs' Hvs' Hm''.
  specialize (Hsimpler m'' (cv :: vs')).
  simpl overwrite_sublist in Hsimpler.
  rewrite Z.add_assoc, overwrite_sublist_snoc in Hm''.
  eapply Hsimpler; eauto.
  cbn. now rewrite Hcv, Hvs'.
Qed.

Lemma fwd_stores' F ρ env tenv m a i ty (ys : list cps.var) p b o s vs P :
  is_frame F ->
  (forall m P,
    m |= F P ->
   (env, tenv, m, a) ⇓ᵣ (Vptr b o)) ->
  typeof a = value \/ typeof a = tptr ty ->
  (0 <= #|ys| <= #|vs| /\ 0 <= i <= #|vs| - #|ys|)%Z ->
  ~ List.In case_id ys ->
  ~ List.In frame_id ys ->
  ~ List.In roots_id ys ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  All (map (fun x => ρ!x <> None) ys) ->
  All (map (fun x => (env, tenv)!!!x <> None) ys) ->
  perm_order p Writable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall m' vs',
    (env, tenv) !!!! ys = Some vs' ->
    m' |= F ((b, O.unsigned o) ↦_{p} overwrite_sublist vs i vs') ->
    postcond env tenv m' s P) ->
  postcond env tenv m (statements (mapi (fun i y => a.[i] :::= make_var fenv locals y) i ys).; s)%C P.
Proof.
  intros; eapply fwd_stores with (offset := 0%Z); eauto; try lia.
  intros. replace (O.unsigned o + 0*word_size)%Z with (O.unsigned o) by lia.
  now rewrite O.repr_unsigned.
Qed.

Lemma set_get_None {A} (m : M.t A) k v k' :
  (M.set k v m) ! k' = None ->
  m ! k' = None.
Proof. destruct (Pos.eq_dec k k'); [subst; rewrite M.gss|rewrite M.gso by auto]; easy. Qed.

Hypothesis NoDup_vars : NoDup [gc_id; isptr_id; tinfo_id; alloc_id; limit_id; frame_id; roots_id; ret_id; case_id; roots_temp_id].

Ltac solve_tenv_inv_set special_ident :=
  unfold tenv_inv; intros Hwf [Htenv1 [Htenv2 Htenv3]]; split_ands;
  [intros x cv Hcase Hget;
   destruct (Pos.eq_dec special_ident x) as [|Hne]; [subst x|];
   [rewrite M.gss in Hget; inv Hget; easy
   |rewrite M.gso in Hget; auto]
  |assert (special_ident <> case_id)
     by (intros ->; rewrite <- NoDup'_spec in NoDup_vars; cbn in NoDup_vars; easy);
   (rewrite M.gso by auto);
   apply Htenv2
  |intros* Hlocal Heq; eapply Htenv3; eauto; eapply set_get_None; eauto].

Lemma tenv_inv_set_alloc tenv v :
  val_defined_wf v ->
  tenv_inv tenv -> tenv_inv (M.set alloc_id v tenv).
Proof. solve_tenv_inv_set alloc_id. Qed.
Hint Resolve tenv_inv_set_alloc : InvDB.

Lemma tenv_inv_set_limit tenv v :
  val_defined_wf v ->
  tenv_inv tenv -> tenv_inv (M.set limit_id v tenv).
Proof. solve_tenv_inv_set limit_id. Qed.
Hint Resolve tenv_inv_set_limit : InvDB.

Lemma tenv_inv_set_ret tenv v :
  val_defined_wf v ->
  tenv_inv tenv -> tenv_inv (M.set ret_id v tenv).
Proof. solve_tenv_inv_set ret_id. Qed.
Hint Resolve tenv_inv_set_ret : InvDB.

Lemma tenv_inv_set_case tenv v :
  v = Vtrue \/ v = Vfalse ->
  tenv_inv tenv -> tenv_inv (M.set case_id v tenv).
Proof.
  intros Hv [Htenv1 [Htenv2 Htenv3]]; unfold tenv_inv; split_ands.
  - intros x cv Hcase Hget.
    destruct (Pos.eq_dec case_id x) as [|Hne]; [easy|].
    rewrite M.gso in Hget by auto.
    apply Htenv1; auto.
  - rewrite M.gss; auto. congruence.
  - intros* Hlocal Heq; eapply Htenv3; eauto; eapply set_get_None; eauto.
Qed.

Lemma tenv_inv_set_case_true tenv :
  tenv_inv tenv -> tenv_inv (M.set case_id Vtrue tenv).
Proof. now apply tenv_inv_set_case. Qed.
Hint Resolve tenv_inv_set_case_true : InvDB.

Lemma tenv_inv_set_case_false tenv :
  tenv_inv tenv -> tenv_inv (M.set case_id Vfalse tenv).
Proof. now apply tenv_inv_set_case. Qed.
Hint Resolve tenv_inv_set_case_false : InvDB.

Lemma tenv_inv_set_x x tenv v :
  val_defined_wf v ->
  x <> case_id ->
  x \in FromSet locals ->
  tenv_inv tenv -> tenv_inv (M.set x v tenv).
Proof.
  unfold tenv_inv; intros Hwf Hcase Hlocals [Htenv1 [Htenv2 Htenv3]]; split_ands.
  - intros x' cv Hcase' Hget; destruct (Pos.eq_dec x x') as [|Hne]; [subst x'|].
    + rewrite M.gss in Hget; inv Hget; split; [|auto].
      left. apply PS.mem_spec. eapply FromSet_sound; eauto; sets.
    + rewrite M.gso in Hget; auto.
  - destruct (Pos.eq_dec x case_id); [now subst|].
    rewrite M.gso by auto; apply Htenv2.
  - intros* Hlocal Hnone; eapply Htenv3; eauto; eapply set_get_None; eauto.
Qed.
Hint Resolve tenv_inv_set_x : InvDB.

Lemma env_rel_all_some ρ k S env xs :
  ρ ~ₑ{k, S} env ->
  FromList xs \subset S ->
  All (map (fun x => ρ!x <> None) xs).
Proof.
  intros Hrel Hxs.
  induction xs as [|x xs IHxs]; [easy|cbn].
  split; [|apply IHxs; eapply Included_trans; eauto; now right].
  destruct env as [[??]?].
  specialize (Hrel x).
  intros Heq; rewrite Heq in Hrel; apply Hrel.
  apply Hxs; now left.
Qed.
Hint Resolve env_rel_all_some : InvDB.

Lemma env_rel_all_some_tenv ρ k S env tenv m xs :
  ρ ~ₑ{k, S} (env, tenv, m) ->
  FromList xs \subset S ->
  All (map (fun x => (env, tenv)!!!x <> None) xs).
Proof.
  intros Hrel Hxs.
  induction xs as [|x xs IHxs]; [easy|cbn].
  split; [|apply IHxs; eapply Included_trans; eauto; now right].
  specialize (Hrel x).
  destruct (ρ!x).
  2:{ contradiction Hrel; apply Hxs; now left. }
  intros Heq; rewrite Heq in Hrel; apply Hrel.
  apply Hxs; now left.
Qed.
Hint Resolve env_rel_all_some_tenv : InvDB.

Lemma env_rel_all_some_tenv_set env tenv x v xs :
  All (map (fun x => (env, tenv) !!! x <> None) xs) ->
  All (map (fun x' => (env, M.set x v tenv) !!! x' <> None) xs).
Proof.
  intros Hxs; induction xs as [|x' xs IHxs]; [easy|].
  cbn; split; [|apply IHxs; now cbn in *].
  destruct Hxs as [Hx _]; clear - Hx; unfold "!!!" in *.
  destruct (Pos.eq_dec x x') as [|Hne]; [subst; now rewrite M.gss in *|].
  rewrite M.gso in *; auto.
Qed.
Hint Resolve env_rel_all_some_tenv_set : InvDB.

Lemma get_env_list_len envs ys vs : envs !!!! ys = Some vs -> #|ys| = #|vs|.
Proof.
  revert vs; induction ys; destruct vs; try (cbn; congruence).
  - cbn. destruct (envs !!! a), (envs !!!! ys); congruence.
  - cbn. destruct (envs !!! a); [|easy].
    destruct (envs !!!! ys); [|easy].
    intros H; inv H.
    specialize (IHys _ eq_refl).
    superlia.
Qed.

(* TODO hoist *)
Lemma rel_val_sepcon k P Q v cv :
  v ~ᵥ{k} (P, cv) ->
  v ~ᵥ{k} (P ⋆ Q, cv).
Proof.
  revert cv; induction v as [c vs IHvs|ρ fds f|z] using val_ind''; intros cv.
  - rewrite !rel_val_eqn; cbn; intros Hrel.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    destruct cv; auto; rename i into o.
    destruct Hrel as [cvs [HP Hcvs]].
    exists cvs; split.
    { eapply entail_trans.
      2:{ apply (frame_entail (fun H => _ ⋆ H)); [auto with FrameDB|].
          apply (entail_True (Q ⋆ Pure True)). }
      intros S m.
      match goal with
      | |- _ -> _ |=_{_} ?P ⋆ _ => rewrite_equiv (fun H => P ⋆ H) sepcon_comm
      end.
      rewrite <- sepcon_assoc.
      apply (frame_entail (fun H => H ⋆ Q)); auto with FrameDB. }
    rewrite Forall2'_spec in *.
    clear HP; induction Hcvs; constructor.
    + rewrite <- rel_val_eqn in *.
      apply IHvs; auto; now left.
    + rewrite <- rel_val_eqn in *.
      apply IHHcvs; intros; apply IHvs; auto; now right.
  - apply rel_val_fun_mem.
  - rewrite !rel_val_eqn; now cbn.
Qed.

(* TODO hoist *)
Lemma rel_env_sepcon k S ρ P Q env tenv :
  ρ ~ₑ{k, S} (env, tenv, P) ->
  ρ ~ₑ{k, S} (env, tenv, P ⋆ Q).
Proof.
  intros Hrel x Hx; specialize (Hrel x Hx).
  destruct (ρ!x); [|easy].
  destruct (_!!!_); [|easy].
  apply rel_val_sepcon; auto.
Qed.

(* TODO hoist *)
Lemma rel_val_entail k P Q v cv :
  P |-- Q ->
  v ~ᵥ{k} (Q, cv) ->
  v ~ᵥ{k} (P, cv).
Proof.
  intros HPQ; revert cv.
  induction v as [c vs IHvs|ρ fds f|z] using val_ind''; intros cv.
  - rewrite !rel_val_eqn; cbn; intros Hrel.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    destruct cv; auto; rename i into o.
    destruct Hrel as [cvs [HP Hcvs]].
    exists cvs; split.
    { eapply entail_trans; eauto. }
    rewrite Forall2'_spec in *.
    clear HP; induction Hcvs; constructor.
    + rewrite <- rel_val_eqn in *.
      apply IHvs; auto; now left.
    + rewrite <- rel_val_eqn in *.
      apply IHHcvs; intros; apply IHvs; auto; now right.
  - apply rel_val_fun_mem.
  - rewrite !rel_val_eqn; now cbn.
Qed.

Lemma valid_mem_sepcon_frame nursery_b talloc_o tlimit_o alloc_o limit_o
      tinfo_b tinfo_o args ss cvss nalloc values P frame :
  valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o tinfo_b tinfo_o
    args ss cvss nalloc values
    (P ⋆ frame)
  <=>
  P ⋆ valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o tinfo_b tinfo_o
    args ss cvss nalloc values
    frame.
Proof.
  unfold valid_mem.
  intros S m.
  rewrite (sepcon_comm P).
  match goal with 
  | |- _ <-> (_ |=_{_} (?P1 ⋆ ?P2 ⋆ ?P3 ⋆ ?P4 ⋆ _) ⋆ _) =>
    rewrite (frame_stuff_hole (fun H => P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ H)); auto with FrameDB;
    rewrite_equiv (fun H => P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ H) sepcon_comm
  end.
  reflexivity.
Qed.

Hypothesis prog_co_stack_frame : exists co,
  (prog_comp_env prog) ! stack_frame_id = Some co /\
  field_offset (prog_comp_env prog) next_fld (co_members co) = OK 0%Z /\
  field_offset (prog_comp_env prog) root_fld (co_members co) = OK word_size /\
  field_offset (prog_comp_env prog) prev_fld (co_members co) = OK (2*word_size)%Z.

(* TODO the following lemmas are very similar to each other;
   technically could refactor into a single lemma about struct accesses. *)

Lemma fwd_frame_next F env tenv m e ty frame_b old_next b o roots prev s P :
  is_frame F ->
  env ! frame_id = Some (frame_b, stack_frame) ->
  typeof e = value \/ typeof e = tptr ty ->
  (env, tenv, m, e) ⇓ᵣ Vptr b o ->
  m |= F ((frame_b, 0%Z) ↦_{Freeable} [old_next; roots; prev]) ->
  (forall m',
    m' |= F ((frame_b, 0%Z) ↦_{Freeable} [Vptr b o; roots; prev]) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (frame.next :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (Vptr b o) (typeof e) (typeof frame.next) m = Some (Vptr b o)).
  { destruct Htype as [Htype|Htype]; rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_stack_frame.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := 0%Z) (v := Vptr b o) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
  - apply Hsimpler; eauto.
    change [Vptr b o; roots; prev] with (set_ith [old_next; roots; prev] 0%Z (Vptr b o)).
    unfold "|=" in *.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    eapply mpred_store; eauto; [|cbn; lia].
    unfold val_wf; destruct Archi.ptr64; easy.
Qed.

Lemma fwd_frame_root F env tenv m e ty frame_b next old_root b o prev s P :
  is_frame F ->
  env ! frame_id = Some (frame_b, stack_frame) ->
  typeof e = value \/ typeof e = tptr ty  ->
  (env, tenv, m, e) ⇓ᵣ Vptr b o ->
  m |= F ((frame_b, 0%Z) ↦_{Freeable} [next; old_root; prev]) ->
  (forall m',
    m' |= F ((frame_b, 0%Z) ↦_{Freeable} [next; Vptr b o; prev]) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (frame.root :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (Vptr b o) (typeof e) (typeof frame.next) m = Some (Vptr b o)).
  { destruct Htype as [Htype|Htype]; rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_stack_frame.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := 1%Z) (v := Vptr b o) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
  - apply Hsimpler; eauto.
    change [next; Vptr b o; prev] with (set_ith [next; old_root; prev] 1%Z (Vptr b o)).
    unfold "|=" in *.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    eapply mpred_store; eauto; [|cbn; lia].
    unfold val_wf; destruct Archi.ptr64; easy.
Qed.

Lemma fwd_frame_prev F env tenv m e ty frame_b next root old_prev b o s P :
  is_frame F ->
  env ! frame_id = Some (frame_b, stack_frame) ->
  typeof e = value \/ typeof e = tptr ty  ->
  (env, tenv, m, e) ⇓ᵣ Vptr b o ->
  m |= F ((frame_b, 0%Z) ↦_{Freeable} [next; root; old_prev]) ->
  (forall m',
    m' |= F ((frame_b, 0%Z) ↦_{Freeable} [next; root; Vptr b o]) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (frame.prev :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (Vptr b o) (typeof e) (typeof frame.next) m = Some (Vptr b o)).
  { destruct Htype as [Htype|Htype]; rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_stack_frame.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := 2%Z) (v := Vptr b o) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
  - apply Hsimpler; eauto.
    change [next; root; Vptr b o] with (set_ith [next; root; old_prev] 2%Z (Vptr b o)).
    unfold "|=" in *.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    eapply mpred_store; eauto; [|cbn; lia].
    unfold val_wf; destruct Archi.ptr64; easy.
Qed.

(* TODO: real alignment may be slightly different *)
Hypothesis prog_co_thread_info : exists co,
  (prog_comp_env prog) ! thread_info_id = Some co /\
  field_offset (prog_comp_env prog) alloc_id (co_members co) = OK 0%Z /\
  field_offset (prog_comp_env prog) limit_id (co_members co) = OK word_size /\
  field_offset (prog_comp_env prog) args_id (co_members co) = OK (3*word_size)%Z /\
  field_offset (prog_comp_env prog) fp_id (co_members co) = OK ((3+max_args)*word_size)%Z /\
  field_offset (prog_comp_env prog) nalloc_id (co_members co) = OK ((4+max_args)*word_size)%Z.

Lemma Mptr_word : Mptr = word_chunk.
Proof. unfold Mptr, word_chunk; now destruct Archi.ptr64. Qed.

(* TODO hoist *)
Lemma mpred_mempty P :
  P ⋆ mempty <=> P.
Proof.
  intros S m; cbn; split.
  - intros [S1 [S2 [HS [HD [HP [HS2 Hunchanged]]]]]].
    rewrite dom_mem_empty in HS2; rewrite HS2 in HS.
    rewrite Union_Empty_set_neut_r in HS.
    eapply mpred_Same_set; eauto.
  - intros Hm; exists S, (Empty_set _); split_ands; sets.
    + rewrite dom_mem_empty; sets.
    + constructor.
      * unfold Mem.empty; cbn; unfold Coqlib.Ple; lia.
      * inversion 1.
      * inversion 1.
Qed.

(* TODO hoist *)
Lemma mpred_frame_ex {A} F (P : A -> _) :
  is_frame F ->
  F (∃ x, P x) <=> ∃ x, F (P x).
Proof.
  intros HF S m.
  rewrite mpred_Ex by auto.
  now rewrite <- (mpred_Ex (fun H => H)) by auto with FrameDB.
Qed.

Lemma val_defined_wf_int i : val_defined_wf (vint i).
Proof. unfold val_defined_wf, vint; now destruct Archi.ptr64. Qed.
Hint Resolve val_defined_wf_int : EvalDB.

Lemma val_defined_wf_ptr b o : val_defined_wf (Vptr b o).
Proof. unfold val_defined_wf; now destruct Archi.ptr64. Qed.
Hint Resolve val_defined_wf_ptr : EvalDB.

Lemma fwd_tinfo_alloc F env tenv m e ty tinfo_b tinfo_o alloc limit args fp nalloc b o s P :
  is_frame F ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  typeof e = value \/ typeof e = tptr ty ->
  (env, tenv, m, e) ⇓ᵣ Vptr b o ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m',
     m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [Vptr b o; limit; heap] ++ args ++ [fp; nalloc]
              WITH #|args| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (tinfo->alloc :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (Vptr b o) (typeof e) (typeof (tinfo->fp)) m = Some (Vptr b o)).
  { destruct Htype as [Htype|Htype]; rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_thread_info.
  unfold "|=" in *.
  destruct_ex_ctx F heap Hm.
  destruct_ex_ctx F Hargs_len Hm.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := 0%Z) (v := Vptr b o) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
      eauto with EvalDB.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
    unfold Ptrofs.add.
    rewrite Mptr_word.
    change (O.unsigned (O.repr 0)) with (0 * word_size)%Z.
    rewrite O.unsigned_repr
      by ((rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto);
          cbn in Hm; decompose [ex and] Hm; superlia).
    eauto.
  - apply Hsimpler; eauto.
    (rewrite mpred_Ex by auto); exists heap.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    exists_ex_ctx F Hargs_len.
    change ([Vptr b o; limit; heap] ++ args ++ [fp; nalloc])%list
      with (set_ith ([alloc; limit; heap] ++ args ++ [fp; nalloc]) 0%Z (Vptr b o))%list.
    eapply mpred_store; eauto with EvalDB; cbn; lia.
Qed.

Lemma fwd_tinfo_limit F env tenv m e ty tinfo_b tinfo_o alloc limit args fp nalloc b o s P :
  is_frame F ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  typeof e = value \/ typeof e = tptr ty ->
  (env, tenv, m, e) ⇓ᵣ Vptr b o ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m',
     m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; Vptr b o; heap] ++ args ++ [fp; nalloc]
              WITH #|args| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (tinfo->limit :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (Vptr b o) (typeof e) (typeof (tinfo->fp)) m = Some (Vptr b o)).
  { destruct Htype as [Htype|Htype]; rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_thread_info.
  unfold "|=" in *.
  destruct_ex_ctx F heap Hm.
  destruct_ex_ctx F Hargs_len Hm.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := 1%Z) (v := Vptr b o) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
      eauto with EvalDB.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
    unfold Ptrofs.add.
    rewrite Mptr_word.
    change (O.unsigned (O.repr word_size)) with (1 * word_size)%Z.
    rewrite O.unsigned_repr
      by ((rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto);
          cbn in Hm; decompose [ex and] Hm; superlia).
    eauto.
  - apply Hsimpler; eauto.
    (rewrite mpred_Ex by auto); exists heap.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    exists_ex_ctx F Hargs_len.
    change ([alloc; Vptr b o; heap] ++ args ++ [fp; nalloc])%list
      with (set_ith ([alloc; limit; heap] ++ args ++ [fp; nalloc]) 1%Z (Vptr b o))%list.
    eapply mpred_store; eauto with EvalDB; cbn; lia.
Qed.

Lemma fwd_tinfo_fp F env tenv m e ty tinfo_b tinfo_o alloc limit args fp nalloc v s P :
  is_frame F ->
  val_defined_wf v ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  typeof e = value \/ typeof e = tptr ty ->
  (env, tenv, m, e) ⇓ᵣ v ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m',
     m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [v; nalloc]
              WITH #|args| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (tinfo->fp :::= e.; s)%C P.
Proof.
  intros HF Hwf Henv Htype Heval Hm Hsimpler.
  assert (sem_cast v (typeof e) (typeof (tinfo->fp)) m = Some v).
  { destruct Htype as [Htype|Htype]; rewrite Htype;
      unfold val_defined_wf in Hwf; unfold value, tptr;
      destruct Archi.ptr64 eqn:Harchi; cbn; destruct v; try auto;
      unfold sem_cast; cbn; now rewrite Harchi. }
  decompose [ex and] prog_co_thread_info.
  unfold "|=" in *.
  destruct_ex_ctx F heap Hm.
  destruct_ex_ctx F Hargs_len Hm.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := (3+max_args)%Z) (v := v) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
      eauto with EvalDB.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
    unfold Ptrofs.add.
    rewrite Mptr_word.
    change (O.unsigned (O.repr ((3 + max_args)*word_size))) with ((3+max_args) * word_size)%Z.
    rewrite O.unsigned_repr.
    2:{
      rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto.
      cbn in Hm; decompose [ex and] Hm.
      rewrite app_length in *; superlia. }
    eauto.
  - apply Hsimpler; eauto.
    (rewrite mpred_Ex by auto); exists heap.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    exists_ex_ctx F Hargs_len.
    replace ([alloc; limit; heap] ++ args ++ [v; nalloc])%list
      with (set_ith ([alloc; limit; heap] ++ args ++ [fp; nalloc]) (3+max_args)%Z v)%list.
    + eapply mpred_store; eauto with EvalDB; cbn.
      rewrite app_length; cbn. superlia.
    + rewrite !set_ith_suffix by (cbn; lia).
      rewrite Hargs_len.
      replace (3 + _ - _ - _)%Z with 0%Z by (cbn; lia).
      reflexivity.
  - cbn; rewrite app_length; cbn; lia.
Qed.

Lemma fwd_tinfo_nalloc F env tenv m e tinfo_b tinfo_o alloc limit args fp nalloc i s P :
  is_frame F ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  typeof e = value ->
  (env, tenv, m, e) ⇓ᵣ vint i ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m',
     m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; vint i]
              WITH #|args| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (tinfo->nalloc :::= e.; s)%C P.
Proof.
  intros HF Henv Htype Heval Hm Hsimpler.
  assert (sem_cast (vint i) (typeof e) (typeof (tinfo->nalloc)) m = Some (vint i)).
  { rewrite Htype; eauto with EvalDB. }
  decompose [ex and] prog_co_thread_info.
  unfold "|=" in *.
  destruct_ex_ctx F heap Hm.
  destruct_ex_ctx F Hargs_len Hm.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; [|auto].
  eapply store_ex with (i := (4+max_args)%Z) (v := vint i) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn; eauto.
    econstructor; cbn.
    + constructor; eauto.
      eauto with EvalDB.
    + apply deref_loc_copy; now cbn.
  - econstructor; cbn; eauto.
    { reflexivity. }
    unfold Ptrofs.add.
    change (O.unsigned (O.repr ((4+max_args)*word_size))) with ((4+max_args) * word_size)%Z.
    rewrite O.unsigned_repr.
    2:{
      rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto.
      cbn in Hm; decompose [ex and] Hm.
      rewrite app_length in *.
      cbn in *; superlia. }
    eauto.
  - apply Hsimpler; eauto.
    (rewrite mpred_Ex by auto); exists heap.
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    exists_ex_ctx F Hargs_len.
    replace ([alloc; limit; heap] ++ args ++ [fp; vint i])%list
      with (set_ith ([alloc; limit; heap] ++ args ++ [fp; nalloc]) (4+max_args)%Z (vint i))%list.
    + eapply mpred_store; eauto with EvalDB; cbn.
      rewrite app_length; cbn. superlia.
    + rewrite !set_ith_suffix by (cbn; lia).
      rewrite Hargs_len.
      replace (4 + _ - _ - _)%Z with 1%Z by (cbn; lia).
      reflexivity.
  - cbn; rewrite app_length; cbn; lia.
Qed.

Lemma sem_cast_ptr_val_same v ty m :
  val_defined_wf v ->
  sem_cast v (tptr ty) value m = Some v.
Proof.
  unfold val_defined_wf, value, tptr, sem_cast; cbn;
  destruct Archi.ptr64 eqn:Harchi; cbn; rewrite Harchi; now destruct v.
Qed.
Hint Resolve sem_cast_ptr_val_same : EvalDB.

Lemma fwd_args_store F env tenv m e ty tinfo_b tinfo_o alloc limit args fp nalloc i v s P :
  is_frame F ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  typeof e = value \/ typeof e = tptr ty ->
  val_defined_wf v ->
  (0 <= i < max_args)%Z ->
  (env, tenv, m, e) ⇓ᵣ v ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m',
    m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ set_ith args i v ++ [fp; nalloc]
            WITH #|args| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (tinfo->args.[i] :::= e.; s)%C P.
Proof.
  intros HF Htinfo Hty Hwf Hbound Heval Hm Hsimpler.
  unfold "|=" in *; decompose [ex and] prog_co_thread_info.
  assert (sem_cast v (typeof e) (typeof (tinfo->args.[i])) m = Some v).
  { destruct Hty as [Hty|Hty]; rewrite Hty; cbn; eauto with EvalDB. }
  destruct_ex_ctx F heap Hm;
  destruct_ex_ctx F Hargs_len Hm.
  pose proof Hm as Hm_in.
  apply mpred_frame_in in Hm_in; auto with FrameDB.
  eapply store_ex with (i := (3+i)%Z) (v := v) in Hm_in; eauto; auto with mem; try (cbn; lia).
  destruct Hm_in as [m' Hstore].
  fwd Cred_assign; eauto with EvalDB.
  - econstructor; cbn.
    econstructor; cbn; eauto with EvalDB.
    econstructor.
    + econstructor; eauto with EvalDB.
      econstructor; eauto with EvalDB.
      reflexivity.
    + cbn; reflexivity.
  - econstructor; cbn; eauto with EvalDB.
    unfold Ptrofs.add.
    rewrite (O.unsigned_repr (_ * _)%Z)
      by (unfold O.max_unsigned, O.modulus, O.wordsize,
          Wordsize_Ptrofs.wordsize, two_power_nat;
          destruct Archi.ptr64; cbn; superlia).
    rewrite (O.unsigned_repr (_ + 3 * word_size)%Z).
    2:{ rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto.
        cbn in Hm; decompose [ex and] Hm; rewrite app_length in *; cbn in *;
        superlia. }
    rewrite O.unsigned_repr.
    2:{ rewrite <- (mpred_mempty _ (dom_mem m) m), frame_swap_hole in Hm by auto.
        cbn in Hm; decompose [ex and] Hm; rewrite app_length in *; cbn in *;
        superlia. }
    rewrite <- Z.add_assoc, <- Z.mul_add_distr_r.
    eauto.
  - apply Hsimpler; eauto.
    (rewrite mpred_Ex by auto); exists heap.
    rewrite <- set_ith_prefix by (cbn; lia).
    replace i with ((3 + i) - 3)%Z by lia.
    rewrite <- set_ith_suffix by (cbn; lia).
    rewrite mpred_Same_set in Hm; [|eapply store_dom_mem; eauto].
    exists_ex_ctx F Hargs_len.
    eapply mpred_store; eauto with EvalDB.
    cbn; rewrite app_length; cbn; lia.
  - cbn; rewrite app_length; cbn; lia.
Qed.

(* TODO hoist *)
Definition set_iths {A} (xs ys : list A) inds :=
  fold_right (fun '(y, i) xs => set_ith xs (Z.of_N i) y) xs (combine ys inds).
Lemma set_iths_eqn {A} (xs ys : list A) inds :
  fold_right (fun '(y, i) xs => set_ith xs (Z.of_N i) y) xs (combine ys inds) = set_iths xs ys inds.
Proof. easy. Qed.

(* TODO hoist *)
Lemma set_iths_len {A} (xs ys : list A) inds :
  #|set_iths xs ys inds| = #|xs|.
Proof.
  revert inds; induction ys as [|y ys IHys]; [easy|cbn]; intros inds.
  destruct inds; [easy|cbn].
  rewrite set_ith_len.
  unfold set_iths in IHys.
  now rewrite IHys.
Qed.

(* TODO hoist *)
Lemma Forall2_combine {A B} R (xs : list A) (ys : list B) :
  #|xs| = #|ys| ->
  Forall2 R xs ys <-> Forall (fun '(x, y) => R x y) (combine xs ys).
Proof.
  revert ys; induction xs as [|x xs IHxs]; destruct ys as [|y ys]; try solve [inversion 1].
  - intros Hlen; cbn; intuition eauto.
  - intros Hlen; split; intros H; inv H; cbn;
    constructor; auto;
      apply IHxs; auto; cbn in *; lia.
Qed.

(* TODO hoist *)
Lemma set_iths_spec {A} (xs ys : list A) inds :
  #|ys| = #|inds| ->
  NoDup inds ->
  Forall (fun i => 0 <= Z.of_N i < #|xs|)%Z inds ->
  Forall2 (fun y i => get_ith (set_iths xs ys inds) (Z.of_N i) = Some y) ys inds.
Proof.
  revert inds; induction ys as [|y ys IHys]; destruct inds as [|i inds];
    intros Hlen Hdup Hbounds; try solve [inv Hlen]; [constructor|].
  constructor.
  - cbn; rewrite ith_gss; auto.
    rewrite set_iths_eqn, set_iths_len.
    inv Hbounds; lia.
  - rewrite Forall2_combine by (cbn in *; lia).
    rewrite Forall_forall.
    intros [y' i'] Hin.
    cbn. rewrite ith_gso.
    2:{ intros Heq. apply in_combine_r in Hin. assert (i = i') by lia. now inv Hdup. }
    rewrite set_iths_eqn.
    specialize (IHys inds).
    rewrite Forall2_combine in IHys by (cbn in *; lia).
    rewrite (Forall_forall _ (combine _ _)) in IHys.
    inv Hdup; inv Hbounds. specialize IHys with (x := (y', i')); apply IHys; auto.
    cbn in *; lia.
Qed.

Lemma set_iths_set_ith_comm {A} (xs ys : list A) i inds y :
  ~ List.In i inds ->
  set_iths (set_ith xs (Z.of_N i) y) ys inds = set_ith (set_iths xs ys inds) (Z.of_N i) y.
Proof.
  revert inds; induction ys as [|y' ys IHys].
  - intros inds Hin; now cbn.
  - destruct inds as [|i' inds]; [now cbn|].
    intros Hin; cbn; rewrite !set_iths_eqn.
    rewrite IHys; [|intros Hin'; contradiction Hin; now right].
    rewrite set_ith_commut; auto.
    intros Heq; (assert (i = i') by lia); subst; contradiction Hin; now left.
Qed.

Lemma fwd_args_stores F ρ env tenv m tinfo_b tinfo_o alloc limit args fp nalloc s ys inds P :
  is_frame F ->
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  #|ys| = #|inds| ->
  NoDup inds ->
  Forall (fun i => 0 <= Z.of_N i < #|args|)%Z inds ->
  ~ List.In case_id ys ->
  ~ List.In frame_id ys ->
  ~ List.In roots_id ys ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  All (map (fun x => ρ!x <> None) ys) ->
  All (map (fun x => (env, tenv)!!!x <> None) ys) ->
  m |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ args ++ [fp; nalloc]
          WITH #|args| = max_args) ->
  (forall m' v_ys,
    (env, tenv) !!!! ys = Some v_ys ->
    m' |= F (∃ heap, (tinfo_b, O.unsigned tinfo_o) ↦_{Writable} [alloc; limit; heap] ++ set_iths args v_ys inds ++ [fp; nalloc]
            WITH #|set_iths args v_ys inds| = max_args) ->
    postcond env tenv m' s P) ->
  postcond env tenv m (statements (map (fun '(y, i) => tinfo->args.[Z.of_N i] :::= make_var fenv locals y) (combine ys inds)).; s)%C P.
Proof.
  intros HF Htinfo Hlen_eq Hnodup Hbounds Hcase Hframe Hroots Henvs Hρ Henv Hm Hsimpler.
  revert args inds Hlen_eq Hnodup m Hm Hbounds Hsimpler; induction ys as [|y ys IHys];
    intros args inds Hlen_eq Hnodup m Hm Hbounds Hsimpler.
  { cbn. fwd Cred_skip. apply (Hsimpler m []); auto. }
  destruct inds as [|i inds]; [now inv Hlen_eq|].
  cbn in Hcase,Hframe,Hroots|-*; fwd Cred_seq_assoc.
  assert (Henv_x : exists cv, (env, tenv)!!!y = Some cv).
  { cbn in Henv. destruct ((env, tenv)!!!y) eqn:Hy; [eauto|intuition congruence]. }
  destruct Henv_x as [cv Hcv].
  assert (#|args| = max_args).
  { unfold "|=" in *. destruct_ex_ctx F heap Hm; destruct_ex_ctx F Hargs Hm; auto. }
  eapply fwd_args_store with (ty := value) (F := F).
  6:{ eapply eval_make_var; eauto; try easy.
      apply Hρ; now rewrite FromList_cons. }
  all: try eassumption; eauto with FrameDB InvDB EvalDB; try solve[lia|inv Hbounds; cbn in *; superlia].
  { eapply env_get_wf; eauto. easy. }
  intros m' Hm'.
  eapply IHys with (args := set_ith args (Z.of_N i) cv); eauto; try (clear - Hρ Henv Hlen_eq; now cbn in * ).
  { now inv Hnodup. }
  { rewrite set_ith_len. apply Hm'. }
  { inv Hbounds. now rewrite set_ith_len. }
  intros m'' vs' Hvs' Hm''.
  specialize (Hsimpler m'' (cv :: vs')).
  unfold set_iths in Hsimpler; simpl fold_right in Hsimpler; rewrite set_iths_eqn in Hsimpler.
  rewrite set_iths_set_ith_comm in Hm'' by now inv Hnodup.
  eapply Hsimpler; eauto.
  cbn. now rewrite Hcv, Hvs'.
Qed.

Lemma skipn_combine {A B} n (xs : list A) (ys : list B) :
  skipn n (combine xs ys) = combine (skipn n xs) (skipn n ys).
Proof.
  revert xs ys; induction n as [|n IHn]; [easy|].
  destruct xs as [|x xs], ys as [|y ys]; cbn; try easy.
  now destruct (skipn n xs).
Qed.

Lemma exp_ind'' (P : exp -> Prop)
      (Hconstr : forall x c ys e, P e -> P (Econstr x c ys e))
      (Hcase : forall x ces (IHces : forall c e, List.In (c, e) ces -> P e), P (Ecase x ces))
      (Hproj : forall x t n y e, P e -> P (Eproj x t n y e))
      (Hletapp : forall x f t ys e, P e -> P (Eletapp x f t ys e))
      (Hfun : forall fds e, P e -> P (Efun fds e))
      (Happ : forall f t ys, P (Eapp f t ys))
      (Hprim : forall x p ys e, P e -> P (Eprim x p ys e))
      (Hhalt : forall x, P (Ehalt x))
  : forall e, P e.
Proof.
  fix IHe 1; intros [].
  - apply Hconstr, IHe.
  - apply Hcase; intros c' e' Hce'.
    induction l as [| [c e] ces IHces].
    + inversion Hce'.
    + destruct Hce' as [Hl|Hr].
      * inversion Hl; subst e'; apply IHe. Guarded.
      * eapply IHces, Hr.
  - apply Hproj, IHe.
  - apply Hletapp, IHe.
  - apply Hfun, IHe.
  - apply Happ.
  - apply Hprim, IHe.
  - apply Hhalt.
Qed.

Lemma fwd_call env tenv m m' a tyargs tyres cconv optid al s vargs f vf vres P :
  classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
  eval_expr prog_genv env tenv m a vf ->
  eval_exprlist prog_genv env tenv m al tyargs vargs ->
  Genv.find_funct prog_genv vf = Some f ->
  type_of_fundef f = Tfunction tyargs tyres cconv ->
  eval_funcall prog_genv m f vargs Events.E0 m' vres ->
  postcond env (set_opttemp optid vres tenv) m' s P ->
  postcond env tenv m (Scall optid a al.; s)%C P.
Proof.
  unfold postcond; intros Hclassify Heval Hevals Hfind Htype Hcall Hnext.
  destruct Hnext as [tenv' [m'' [cv [Hstep HP]]]].
  exists tenv', m'', cv; split; auto.
  unfold "⇓". change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto.
  econstructor; eauto.
Qed.

Lemma rel_val_in_ρ k S x ρ env tenv values :
  x \in S ->
  ρ ~ₑ{k, S} (env, tenv, values) ->
  exists v, ρ!x = Some v.
Proof.
  intros Hx Henv; specialize (Henv x Hx).
  destruct (ρ ! x); auto; eauto.
Qed.

Lemma rel_val_in_env k S x ρ env tenv values :
  x \in S ->
  ρ ~ₑ{k, S} (env, tenv, values) ->
  exists cv, (env, tenv) !!! x = Some cv.
Proof.
  intros Hx Henv; specialize (Henv x Hx).
  destruct (ρ ! x); auto.
  destruct (_ !!! _); eauto.
Qed.

Lemma rel_val_in_ρs k S xs ρ env tenv values :
  FromList xs \subset S ->
  ρ ~ₑ{k, S} (env, tenv, values) ->
  exists vs, get_list xs ρ = Some vs.
Proof.
  induction xs as [|x xs IHxs]; [now exists [] |intros Hsub Hrel].
  edestruct (rel_val_in_ρ k S x) as [v Hv]; try eassumption; eauto.
  { eapply Included_trans; sets; now left. }
  destruct IHxs as [vs Hvs]; auto; [eapply Included_trans; eauto; now right|].
  cbn; rewrite Hv, Hvs; eauto.
Qed.

Lemma rel_val_in_envs k S xs ρ env tenv values :
  FromList xs \subset S ->
  ρ ~ₑ{k, S} (env, tenv, values) ->
  exists cvs, (env, tenv) !!!! xs = Some cvs.
Proof.
  induction xs as [|x xs IHxs]; [now exists [] |intros Hsub Hrel].
  edestruct (rel_val_in_env k S x) as [cv Hcv]; try eassumption; eauto.
  { eapply Included_trans; sets; now left. }
  destruct IHxs as [cvs Hcvs]; auto; [eapply Included_trans; eauto; now right|].
  cbn; rewrite Hcv, Hcvs; eauto.
Qed.

Lemma rel_val_xs_related' k S xs vs cvs ρ env tenv values :
  FromList xs \subset S ->
  ρ ~ₑ{k, S} (env, tenv, values) ->
  get_list xs ρ = Some vs ->
  (env, tenv) !!!! xs = Some cvs ->
  Forall2 (fun v cv => v ~ᵥ{k} (values, cv)) vs cvs.
Proof.
  revert vs cvs; induction xs as [|x xs IHxs]; intros vs cvs Hsub Hrel Hget Hcget.
  - cbn in *; inv Hget; inv Hcget; constructor.
  - cbn in Hget; cbn in Hcget.
    destruct (ρ ! x) as [v|] eqn:Hρ; [|easy].
    destruct (get_list xs ρ) as [vs'|] eqn:Hρs; [|easy].
    destruct ((env, tenv) !!! x) as [cv|] eqn:Hc; [|easy].
    destruct ((env, tenv) !!!! xs) as [cvs'|] eqn:Hcs; [|easy].
    inv Hget; inv Hcget; constructor.
    + specialize (Hrel x); rewrite Hρ, Hc in Hrel; apply Hrel.
      eapply Included_trans; eauto; sets; now left.
    + apply IHxs; eauto.
      eapply Included_trans; eauto; now right.
Qed.

Lemma rel_val_x_related x k S ρ env tenv values :
  x \in S ->
  ρ ~ₑ{k, S} (env, tenv, values) -> exists v cv,
  ρ ! x = Some v /\
  (env, tenv) !!! x = Some cv /\
  v ~ᵥ{k} (values, cv).
Proof.
  intros Hin Hrel.
  edestruct (rel_val_in_ρ k S x) as [v Hv]; eauto.
  edestruct (rel_val_in_env k S x) as [cv Hcv]; eauto.
  do 2 eexists; split_ands; eauto.
  specialize (Hrel x Hin); now rewrite Hv, Hcv in Hrel.
Qed.

Lemma rel_val_xs_related xs k S ρ env tenv values :
  FromList xs \subset S ->
  ρ ~ₑ{k, S} (env, tenv, values) -> exists vs cvs,
  get_list xs ρ = Some vs /\
  (env, tenv) !!!! xs = Some cvs /\
  Forall2 (fun v cv => v ~ᵥ{k} (values, cv)) vs cvs.
Proof.
  intros Hsub Hrel.
  edestruct (rel_val_in_ρs k S xs) as [vs Hvs]; eauto.
  edestruct (rel_val_in_envs k S xs) as [cvs Hcvs]; eauto.
  do 2 eexists; split_ands; eauto.
  eapply rel_val_xs_related'; eauto.
Qed.

(* TODO: generalize the version in map_util to P : A -> B -> Prop and use that instead *)
Lemma set_lists_Forall2_get' {A} {B} (P : A -> B -> Prop)
      xs vs1 vs2 rho1 rho2 rho1' rho2' x :
  Forall2 P vs1 vs2 ->
  set_lists xs vs1 rho1 = Some rho1' ->
  set_lists xs vs2 rho2 = Some rho2' ->
  List.In x xs ->
  exists v1 v2,
    M.get x rho1' = Some v1 /\
    M.get x rho2' = Some v2 /\ P v1 v2.
Proof.
  revert rho1' rho2' vs1 vs2.
  induction xs; simpl; intros rho1' rho2' vs1 vs2 Hall Hset1 Hset2 Hin.
  - inv Hin.
  - destruct (Coqlib.peq a x); subst.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (set_lists xs vs1 rho1) eqn:Heq1;
        destruct (set_lists xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall.
      repeat eexists; try rewrite M.gss; eauto.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (set_lists xs vs1 rho1) eqn:Heq1;
        destruct (set_lists xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall. inv Hin; try congruence.
      edestruct IHxs as [v1 [v2 [Hget1 [Hget2 HP]]]]; eauto.
      repeat eexists; eauto; rewrite M.gso; eauto.
Qed.

Lemma set_related_lists_rel_val k S xs vs cvs ρ_old tenv_old ρ env tenv values :
  Forall2 (fun v cv => v ~ᵥ{k} (values, cv)) vs cvs ->
  set_lists xs vs ρ_old = Some ρ ->
  set_lists xs cvs tenv_old = Some tenv ->
  S \subset FromList xs ->
  ρ ~ₑ{k, S} (env, tenv, values).
Proof.
  intros Hforall Hset_ρ Hset_tenv Hsub x Hx.
  eapply Hsub in Hx; unfold In, FromList in Hx.
  edestruct @set_lists_Forall2_get' as [v [cv [Hv [Hcv Hrel]]]]; eauto; cbn in Hrel.
  rewrite Hv; unfold "!!!"; rewrite Hcv; assumption.
Qed.

Lemma tenv_inv_set_lists xs vs old_tenv tenv :
  Forall val_defined_wf vs ->
  tenv_inv old_tenv ->
  ~ List.In case_id xs ->
  FromList xs \subset FromSet locals ->
  set_lists xs vs old_tenv = Some tenv ->
  tenv_inv tenv.
Proof.
  intros Hwf Htenv Hcase Hsub Hset.
  generalize dependent vs; generalize dependent tenv;
    induction xs as [|x xs IHxs]; [now destruct vs; cbn|].
  destruct vs as [|v vs]; [easy|]; intros Hwf Hset.
  cbn in Hset; destruct (set_lists xs vs old_tenv) as [tenv'|] eqn:Htenv'; [|easy].
  inv Hwf; inv Hset; eapply tenv_inv_set_x; auto.
  { cbn in Hcase; easy. }
  { rewrite FromList_cons in Hsub; eapply Included_trans; eauto; sets. }
  eapply IHxs; eauto; sets.
  { cbn in Hcase; easy. }
  eapply Included_trans; eauto; sets; now right.
Qed.

(* TODO put in Ensembles.v *)
Lemma FromList_firstn {A} n (xs : list A) :
  FromList (firstn n xs) \subset FromList xs.
Proof.
  revert xs; induction n as [|n IHn]; [easy|intros xs].
  destruct xs as [|x xs]; [easy|cbn; rewrite !FromList_cons]; sets.
Qed.
Hint Resolve FromList_firstn : Ensembles_DB.
  
(* TODO put in Ensembles.v *)
Lemma FromList_skipn {A} n (xs : list A) :
  FromList (skipn n xs) \subset FromList xs.
Proof.
  revert xs; induction n as [|n IHn]; [easy|intros xs].
  destruct xs as [|x xs]; [easy|cbn; rewrite !FromList_cons]; sets.
Qed.
Hint Resolve FromList_skipn : Ensembles_DB.

Lemma some_inj {A} (x y : A) : Some x = Some y -> x = y. Proof. congruence. Qed.

(* TODO hoist *)
Hypothesis one_letapp_nonzero : forall x f ft ys e, to_nat (one (Eletapp x f ft ys e)) > 0.

(* TODO hoist *)
Lemma rel_val_has_shape k v P cv :
  v ~ᵥ{k} (P, cv) ->
  has_shape P v cv.
Proof.
  revert cv; induction v as [c vs IHvs|ρ fds f|z] using val_ind''; intros cv Hrel.
  - rewrite rel_val_eqn in Hrel; cbn in *.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; [easy|now cbn|].
    destruct cv; try easy.
    destruct Hrel as [cvs [Hcvs Hrel_cvs]].
    exists cvs; split; auto.
    rewrite Forall2'_spec in *.
    clear Hcvs.
    induction Hrel_cvs; [constructor|constructor].
    + rewrite <- rel_val_eqn in *; apply IHvs; eauto; now left.
    + apply IHHrel_cvs; auto.
      intros; apply IHvs; eauto; now right.
  - rewrite rel_val_eqn in Hrel; cbn in *.
    destruct cv; auto.
  - rewrite rel_val_eqn in Hrel; now cbn in *.
Qed.
Hint Resolve rel_val_has_shape : ShapeDB.

(* TODO hoist *)
Lemma rel_vals_has_shapes k vs P cvs :
  Forall2 (fun v cv => v ~ᵥ{k} (P, cv)) vs cvs ->
  has_shapes P [vs] [cvs].
Proof.
  intros Hrel; constructor; [|constructor].
  induction Hrel; constructor; auto.
  eapply rel_val_has_shape; eauto.
Qed.
Hint Resolve rel_vals_has_shapes : ShapeDB.

Lemma has_shapes_app P vss1 cvss1 vss2 cvss2 :
  has_shapes P vss1 cvss1 ->
  has_shapes P vss2 cvss2 ->
  (has_shapes P (vss1 ++ vss2) (cvss1 ++ cvss2))%list.
Proof.
  induction 1; cbn; auto.
  intros Hshapes; constructor; auto.
  now apply IHForall2.
Qed.

Lemma eval_tinfo_alloc env tenv m tinfo_b tinfo_o nursery_b talloc_o
      tlimit_o alloc_o limit_o ss cvss values frame :
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  m |= ∃ args nalloc,
       valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
                 tinfo_b tinfo_o args ss cvss nalloc values frame ->
  eval_expr prog_genv env tenv m (tinfo->alloc) (Vptr nursery_b talloc_o).
Proof.
  intros Htenv Hm.
  decompose [ex and] prog_co_thread_info.
  econstructor.
  - econstructor; eauto with EvalDB; reflexivity.
  - econstructor; cbn; eauto.
    unfold "|=" in *.
    destruct_ex args Hm.
    destruct_ex nalloc Hm.
    unfold valid_mem in Hm.
    match type of Hm with
    | _ |=_{_} _ ⋆ ?P =>
      destruct_ex_ctx (fun H => H ⋆ P) heap Hm;
      destruct_ex_ctx (fun H => H ⋆ P) Hargs Hm;
      eapply mpred_load with (F := fun H => H ⋆ P) (i := 0%Z) in Hm;
      eauto with FrameDB; cbn; try reflexivity
    end.
    unfold Ptrofs.add.
    change (O.unsigned (O.repr 0)) with 0%Z.
    rewrite Z.add_0_r.
    rewrite O.repr_unsigned.
    rewrite <- Hm; unfold load; f_equal; lia.
Qed.
Hint Resolve eval_tinfo_alloc : EvalDB.

Lemma eval_tinfo_limit env tenv m tinfo_b tinfo_o nursery_b talloc_o
      tlimit_o alloc_o limit_o ss cvss values frame :
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  m |= ∃ args nalloc,
       valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
                 tinfo_b tinfo_o args ss cvss nalloc values frame ->
  eval_expr prog_genv env tenv m (tinfo->limit) (Vptr nursery_b tlimit_o).
Proof.
  intros Htenv Hm.
  decompose [ex and] prog_co_thread_info.
  econstructor.
  - econstructor; eauto with EvalDB; reflexivity.
  - econstructor; cbn; eauto.
    unfold "|=" in *.
    destruct_ex args Hm.
    destruct_ex nalloc Hm.
    unfold valid_mem in Hm.
    match type of Hm with
    | _ |=_{_} _ ⋆ ?P =>
      destruct_ex_ctx (fun H => H ⋆ P) heap Hm;
      destruct_ex_ctx (fun H => H ⋆ P) Hargs Hm;
      pose proof Hm as Hm';
      eapply mpred_load with (F := fun H => H ⋆ P) (i := 1%Z) in Hm;
      eauto with FrameDB; cbn; try reflexivity
    end.
    unfold Ptrofs.add.
    change (O.unsigned (O.repr word_size)) with (1*word_size)%Z.
    rewrite <- Hm; unfold load; f_equal.
    rewrite O.unsigned_repr; auto.
    cbn in Hm'; decompose [ex and] Hm'; clear Hm'.
    rewrite app_length in *; cbn in *; superlia.
Qed.
Hint Resolve eval_tinfo_limit : EvalDB.

(* Hdis : Disjoint _ S1 S2 contradictory at x.
   Assumes Hdis already normalized *)
Ltac dis_bad Hdis x :=
  destruct Hdis as [Hdis]; contradiction (Hdis x);
  constructor; auto 10.

(* Assumes Hdis already normalized *)
Ltac vars_neq Hdis x y :=
  assert (x <> y) by (clear - Hdis; intros ?; subst y; dis_bad Hdis x).

Inductive normal_stmt s :=
  mk_normal_stmt :
    (forall env tenv m t tenv' m' o,
     exec_stmt prog_genv env tenv m s t tenv' m' o -> o = Out_normal) ->
    normal_stmt s.

Lemma normal_skip : normal_stmt Sskip.
Proof. constructor; intros env* H; now inv H. Qed.

Lemma normal_assign e1 e2 : normal_stmt (e1 :::= e2).
Proof. constructor; intros env* H; now inv H. Qed.

Lemma normal_set x e : normal_stmt (x ::= e).
Proof. constructor; intros env* H; now inv H. Qed.

Lemma normal_seq s1 s2 :
  normal_stmt s1 ->
  normal_stmt s2 ->
  normal_stmt (s1.; s2)%C.
Proof. intros [Hs1] [Hs2]; constructor; intros env* Hexec; inv Hexec; eauto. Qed.

Lemma normal_if e s1 s2 :
  normal_stmt s1 ->
  normal_stmt s2 ->
  normal_stmt (Sifthenelse e s1 s2).
Proof. intros [Hs1] [Hs2]; constructor; intros env* H; inv H; destruct b; eauto. Qed.

Lemma normal_call x f es : normal_stmt (Scall x f es).
Proof. constructor; intros env* H; now inv H. Qed.

Hint Resolve normal_skip normal_assign normal_set normal_seq normal_if normal_call : NormalDB.

Lemma normal_statements {A} f i (xs : list A) :
  (forall i x, normal_stmt (f i x)) ->
  normal_stmt (statements (mapi f i xs)).
Proof. intros Hfi; revert i; induction xs as [|x xs IHxs]; intros i; cbn; auto with NormalDB. Qed.

Lemma normal_create_space n pre post :
  normal_stmt pre ->
  normal_stmt post ->
  normal_stmt (create_space n pre post).
Proof. unfold create_space; auto 10 with NormalDB. Qed.

Hint Resolve normal_statements normal_create_space : NormalDB.

Lemma normal_coq_if1 {A} (b : {A} + {~ A}) s1 s2 :
  normal_stmt s1 ->
  normal_stmt s2 ->
  normal_stmt (if b then s1 else s2).
Proof. intros [Hs1] [Hs2]; now destruct b. Qed.
Hint Resolve normal_coq_if1 : NormalDB.

(* TODO hoist *)
Lemma normal_coq_if2 (b : bool) s1 s2 :
  normal_stmt s1 ->
  normal_stmt s2 ->
  normal_stmt (if b then s1 else s2).
Proof. intros [Hs1] [Hs2]; now destruct b. Qed.
Hint Resolve normal_coq_if2 : NormalDB.

Lemma fwd_seq P tenv m env s1 s2 Q :
  normal_stmt s1 ->
  postcond env tenv m s1 P ->
  (forall tenv' m', P tenv' m' Out_normal -> postcond env tenv' m' s2 Q) ->
  postcond env tenv m (s1.; s2)%C Q.
Proof.
  intros Hnormal [tenv' [m' [out [Hs1 HP]]]] Hmp.
  assert (out = Out_normal) by (eapply Hnormal; eauto); subst out.
  apply Hmp in HP; destruct HP as [tenv'' [m'' [out [Hs2 HQ]]]].
  exists tenv'', m'', out; split; auto.
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto.
Qed.

Lemma Forall3_last_two_len {A B C} (R : A -> B -> C -> Prop) xs : forall ys zs,
  Forall3 R xs ys zs -> #|ys| = #|zs|.
Proof.
  induction xs as [|x xs IHxs]; destruct ys as [|y ys], zs as [|z zs]; try easy.
  intros [HR Hforall]; specialize (IHxs _ _ Hforall).
  cbn in *; lia.
Qed.

(* TODO hoist *)
Lemma compatible_shape_refl P v cv :
  has_shape P v cv ->
  compatible_shape P P v cv cv.
Proof.
  revert cv; induction v as [c vs IHvs|ρ fds f|z] using val_ind''; intros cv Hshape.
  - cbn in *.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; try easy.
    destruct cv; try easy.
    destruct Hshape as [cvs [Hcvs Hshapes]].
    exists cvs, cvs; split_ands; auto.
    + rewrite Forall2'_spec in Hshapes.
      apply Forall2_length in Hshapes; cbn; now rewrite Hshapes.
    + rewrite Forall2'_spec in Hshapes; clear - IHvs Hshapes.
      induction Hshapes; constructor.
      * eapply IHvs; eauto; now left.
      * eapply IHHshapes; intros; eapply IHvs; eauto; now right.
  - cbn in *; destruct cv; auto.
  - now cbn in *.
Qed.
Hint Resolve compatible_shape_refl : ShapeDB.

(* TODO hoist *)
Lemma compatible_shapes_refl P vss cvss :
  has_shapes P vss cvss ->
  compatible_shapes P P vss cvss cvss.
Proof.
  induction 1 as [|vs cvs vss cvss Hvs Hvss IHvss]; constructor; eauto.
  induction Hvs; constructor; eauto.
  eapply compatible_shape_refl; eauto.
Qed.
Hint Resolve compatible_shapes_refl : ShapeDB.

(* TODO hoist *)
Lemma compatible_shape_trans F m P1 P2 P3 v cv1 cv2 cv3 :
  is_frame F ->
  m |= F P2 ->
  compatible_shape P1 P2 v cv1 cv2 ->
  compatible_shape P2 P3 v cv2 cv3 ->
  compatible_shape P1 P3 v cv1 cv3.
Proof.
  revert cv1 cv2 cv3; induction v as [c vs IHvs|ρ fds f|z] using val_ind'';
    intros cv1 cv2 cv3 HF Hm H12 H23.
  - cbn in *.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; try easy.
    destruct cv1, cv2, cv3; try easy.
    destruct H12 as [cvs1 [cvs2 [Hlen12 [Hcvs1 [Hcvs2 Hcvs12]]]]].
    destruct H23 as [cvs2' [cvs3 [Hlen23 [Hcvs2' [Hcvs3 Hcvs23]]]]].
    assert (cvs2 = cvs2').
    { eapply mapsto_unique in Hcvs2; eauto with FrameDB.
      - congruence.
      - assert (#|cvs1| = #|cvs2|) by now eapply Forall3_last_two_len.
        cbn in *; lia. }
    subst cvs2'; clear Hcvs2'.
    exists cvs1, cvs3; split_ands; eauto.
    clear - HF Hm IHvs Hcvs12 Hcvs23; revert cvs1 cvs2 cvs3 Hcvs12 Hcvs23.
    induction vs as [|v vs IHvs']; destruct cvs1 as [|cv1 cvs1], cvs2 as [|cv2 cvs2], cvs3 as [|cv3 cvs3]; try easy.
    intros [Hcv12 Hcvs12] [Hcv23 Hcvs23]; split.
    + eapply IHvs; eauto; now left.
    + eapply IHvs'; eauto; intros; eapply IHvs; eauto; now right.
  - cbn in *. destruct cv1, cv2, cv3; easy.
  - cbn in *. easy.
Qed.

(* TODO hoist *)
Lemma compatible_shapes_trans F m P1 P2 P3 vss : forall cvss1 cvss2 cvss3,
  is_frame F ->
  m |= F P2 ->
  compatible_shapes P1 P2 vss cvss1 cvss2 ->
  compatible_shapes P2 P3 vss cvss2 cvss3 ->
  compatible_shapes P1 P3 vss cvss1 cvss3.
Proof.
  induction vss as [|vs vss IHvss];
    destruct cvss1 as [|cvs1 cvss1];
    destruct cvss2 as [|cvs2 cvss2];
    destruct cvss3 as [|cvs3 cvss3]; try easy.
  intros HF Hm [Hvs12 Hvss12] [Hvs23 Hvss23]; constructor; eauto.
  clear - thread_info_id calling_convention HF Hm Hvs12 Hvs23; revert cvs1 cvs2 cvs3 Hvs12 Hvs23.
  induction vs as [|v vs IHvs]; destruct cvs1 as [|cv1 cvs1], cvs2 as [|cv2 cvs2], cvs3 as [|cv3 cvs3]; try easy.
  intros [Hv12 Hvs12] [Hv23 Hvs23]; constructor; eauto.
  eapply compatible_shape_trans; eauto.
Qed.

(* TODO hoist *)
Lemma compatible_shape_has_shape P1 P2 v cv1 cv2 :
  compatible_shape P1 P2 v cv1 cv2 ->
  has_shape P2 v cv2.
Proof.
  revert cv1 cv2; induction v as [c vs IHvs|ρ fds f|z] using val_ind'';
    intros cv1 cv2 Hcompat.
  - cbn in *.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; try easy.
    destruct cv1, cv2; try easy.
    destruct Hcompat as [cvs1 [cvs2 [Hlen12 [Hcvs1 [Hcvs2 Hcvs12]]]]].
    exists cvs2; split; auto.
    clear - IHvs Hcvs12; revert cvs1 cvs2 Hcvs12.
    induction vs as [|v vs IHvs']; destruct cvs1 as [|cv1 cvs1], cvs2 as [|cv2 cvs2]; try easy.
    intros [Hcv12 Hcvs12]; split.
    + eapply IHvs; eauto; now left.
    + eapply IHvs'; eauto; intros; eapply IHvs; eauto; now right.
  - cbn in *. destruct cv1, cv2; easy.
  - cbn in *. easy.
Qed.
Hint Resolve compatible_shape_has_shape : ShapeDB.

(* TODO hoist *)
Lemma compatible_shapes_has_shapes P1 P2 vss : forall cvss1 cvss2,
  compatible_shapes P1 P2 vss cvss1 cvss2 ->
  has_shapes P2 vss cvss2.
Proof.
  induction vss as [|vs vss IHvss];
    destruct cvss1 as [|cvs1 cvss1];
    destruct cvss2 as [|cvs2 cvss2]; try easy; try solve [constructor].
  intros [Hvs12 Hvss12]; eauto.
  constructor; [|eapply IHvss; eauto].
  clear - Hvs12; revert cvs1 cvs2 Hvs12.
  induction vs as [|v vs IHvs']; destruct cvs1 as [|cv1 cvs1], cvs2 as [|cv2 cvs2]; try easy.
  intros [Hv12 Hvs12]; constructor; eauto.
  eapply compatible_shape_has_shape; eauto.
Qed.
Hint Resolve compatible_shapes_has_shapes : ShapeDB.

(* TODO hoist *)
Lemma fwd_skip env tenv m (P : _ -> _ -> _ -> Prop) :
  P tenv m Out_normal -> postcond env tenv m Sskip P.
Proof. intros HP; exists tenv, m, Out_normal; split; auto; constructor. Qed.

Lemma valid_mem_fold S m nursery_b talloc_o tlimit_o alloc_o limit_o
      tinfo_b tinfo_o args ss cvss nalloc values frame :
  m |=_{S} valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
                     tinfo_b tinfo_o args ss cvss nalloc values frame ->
  m |=_{S} valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
                     tinfo_b tinfo_o args ss cvss nalloc values frame.
Proof. auto. Qed.

(* TODO hoist *)
Lemma sizeof_value ge : sizeof ge value = word_size.
Proof. now unfold value, word_size, size_chunk, word_chunk; cbn; destruct Archi.ptr64; cbn. Qed.

Lemma wordsize_divides_modulus : (word_size | O.modulus)%Z.
Proof.
  unfold word_size, size_chunk, word_chunk, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize;
    destruct Archi.ptr64.
  - exists (two_power_nat 61).
    rewrite !two_power_nat_S, !Coqlib.two_power_nat_O.
    lia.
  - exists (two_power_nat 30).
    rewrite !two_power_nat_S, !Coqlib.two_power_nat_O.
    lia.
Qed.

Lemma unsigned_repr_lt i j :
  (O.unsigned (O.repr i) < j)%Z ->
  (i <= O.max_unsigned)%Z ->
  (i < j)%Z.
Proof.
  intros Hrepr Hupper.
  assert (Hcases : ((i < 0) \/ (0 <= i))%Z) by lia.
  destruct Hcases as [Hneg|Hnneg].
  - pose proof O.unsigned_range (O.repr i) as Hj_nneg. lia.
  - rewrite O.unsigned_repr in Hrepr by lia. lia.
Qed.

Lemma mod_div_word_size_bounds :
  (0 < O.modulus/word_size < O.modulus)%Z.
Proof.
  unfold word_size, size_chunk, word_chunk, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize;
    destruct Archi.ptr64.
  - rewrite !two_power_nat_S, !Coqlib.two_power_nat_O.
    change 8%Z with (2*2*2)%Z.
    rewrite !Z.mul_assoc.
    rewrite <- !Zdiv_Zdiv by lia.
    rewrite Z.mul_1_r.
    rewrite !Z.div_mul by lia.
    lia.
  - rewrite !two_power_nat_S, !Coqlib.two_power_nat_O.
    change 4%Z with (2*2)%Z.
    rewrite !Z.mul_assoc.
    rewrite <- !Zdiv_Zdiv by lia.
    rewrite Z.mul_1_r.
    rewrite !Z.div_mul by lia.
    lia.
Qed.

Lemma word_size_lt_max_signed : (word_size < O.max_signed)%Z.
Proof.
  unfold word_size, size_chunk, word_chunk, O.max_signed, O.half_modulus,
  O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize;
    destruct Archi.ptr64; now cbv.
Qed.

Lemma eval_space_check' S env tenv m nursery_b limit_o alloc_o tlimit_o talloc_o
      tinfo_b tinfo_o args ss cvss nalloc values frame n :
  (0 <= n <= O.max_signed)%Z ->
  m |=_{S} valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
            tinfo_b tinfo_o args ss cvss nalloc values frame ->
  tenv ! limit_id = Some (Vptr nursery_b limit_o) ->
  tenv ! alloc_id = Some (Vptr nursery_b alloc_o) ->
  exists v,
  (env, tenv, m, limit -' alloc <' c_int n value) ⇓ᵣ v /\ exists b,
  bool_val v (typeof (limit -' alloc <' c_int n value)) m = Some b /\
  if b then (O.unsigned limit_o - O.unsigned alloc_o < n*word_size)%Z
  else (O.unsigned limit_o - O.unsigned alloc_o >= n*word_size)%Z.
Proof.
  intros Hn Hm Hlimit Halloc; destruct Archi.ptr64 eqn:Harchi.
  - eexists; split.
    + econstructor; eauto with EvalDB.
      * econstructor; eauto with EvalDB.
        cbn. destruct (eq_block _ _) as [_|wat]; [|easy].
        rewrite sizeof_value.
        destruct (Coqlib.zlt _ _) as [Hlt|wat]; [cbn; clear Hlt|easy].
        destruct (Coqlib.zle _ _) as [Hle|wat]; [cbn; clear Hle|].
        2:{ unfold O.max_signed, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize, two_power_nat in *;
            destruct Archi.ptr64; simpl in *; superlia. }
        reflexivity.
      * cbn; unfold tptr, value, c_int, vint; rewrite Harchi; cbn;
          unfold cmp_ptr; rewrite Harchi; cbn; unfold Vptrofs; rewrite Harchi; cbn; reflexivity.
    + cbn; unfold Val.of_bool.
      unfold Int64.ltu.
      destruct (Coqlib.zlt _ _) as [Hlt|Hge]; cbn; eexists; split; cbn; eauto.
      * unfold Int.eq. destruct (Coqlib.zeq _ _) as [Heq|Hne]; [inv Heq|]; cbn.
        unfold O.sub, O.divs in Hlt.
        change (O.signed (O.repr word_size)) with word_size in Hlt.
        rewrite O.to_int64_of_int64 in Hlt by assumption.
        rewrite <- O.agree64_repr in Hlt by auto.
        rewrite <- O.agree64_to_int in Hlt by auto.
        unfold valid_mem in Hm; cbn in Hm; decompose [ex and] Hm.
        rewrite O.signed_repr in Hlt by superlia.
        match goal with
        | H : (_ * _ = O.unsigned limit_o - O.unsigned alloc_o)%Z |- _ => rewrite <- H in *
        end.
        rewrite Z.quot_mul in Hlt by superlia.
        apply Z.mul_lt_mono_pos_r; [superlia|].
        rewrite !O.unsigned_repr in Hlt; auto; superlia.
      * unfold Int.eq. destruct (Coqlib.zeq _ _) as [Heq|Hne]; [|now contradiction Hne]; cbn.
        unfold O.sub, O.divs in Hge.
        change (O.signed (O.repr word_size)) with word_size in Hge.
        rewrite O.to_int64_of_int64 in Hge by assumption.
        rewrite <- O.agree64_repr in Hge by auto.
        rewrite <- O.agree64_to_int in Hge by auto.
        unfold valid_mem in Hm; cbn in Hm; decompose [ex and] Hm.
        rewrite O.signed_repr in Hge by superlia.
        match goal with
        | H : (_ * _ = O.unsigned limit_o - O.unsigned alloc_o)%Z |- _ => rewrite <- H in *
        end.
        rewrite Z.quot_mul in Hge by superlia.
        rewrite !O.unsigned_repr in Hge by superlia.
        apply Z.le_ge; apply Z.ge_le in Hge.
        apply Z.mul_le_mono_pos_r; [superlia|].
        auto.
  - eexists; split.
    + econstructor; eauto with EvalDB.
      * econstructor; eauto with EvalDB.
        cbn. destruct (eq_block _ _) as [_|wat]; [|easy].
        rewrite sizeof_value.
        destruct (Coqlib.zlt _ _) as [Hlt|wat]; [cbn; clear Hlt|easy].
        destruct (Coqlib.zle _ _) as [Hle|wat]; [cbn; clear Hle|].
        2:{ unfold O.max_signed, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize, two_power_nat in *;
            destruct Archi.ptr64; simpl in *; superlia. }
        reflexivity.
      * cbn; unfold tptr, value, c_int, vint; rewrite Harchi; cbn;
          unfold cmp_ptr; rewrite Harchi; cbn; unfold Vptrofs; rewrite Harchi; cbn; reflexivity.
    + cbn; unfold Val.of_bool.
      unfold Int.ltu.
      destruct (Coqlib.zlt _ _) as [Hlt|Hge]; cbn; eexists; split; cbn; eauto.
      * unfold Int.eq. destruct (Coqlib.zeq _ _) as [Heq|Hne]; [inv Heq|]; cbn.
        unfold Ptrofs.to_int in Hlt.
        rewrite <- !O.agree32_of_ints in Hlt by auto.
        unfold O.of_ints in Hlt.
        unfold O.divs, O.sub in Hlt.
        unfold valid_mem in Hm; cbn in Hm; decompose [ex and] Hm.
        match goal with
        | H : (_ * _ = O.unsigned limit_o - O.unsigned alloc_o)%Z |- _ => rewrite <- H in *
        end.
        apply Z.mul_lt_mono_pos_r; [superlia|].
        pose proof word_size_lt_max_signed.
        rewrite !O.signed_repr in Hlt by superlia.
        rewrite Z.quot_mul in Hlt by superlia.
        rewrite !O.agree32_repr in Hlt by auto.
        rewrite !Int.repr_signed in Hlt.
        rewrite !Int.repr_unsigned in Hlt.
        rewrite <- !O.agree32_repr in Hlt by auto.
        rewrite !O.unsigned_repr in Hlt by superlia.
        rewrite O.repr_unsigned in Hlt.
        unfold O.of_intu, O.of_int in Hlt.
        rewrite <- O.agree32_repr in Hlt by auto.
        rewrite O.repr_unsigned in Hlt.
        rewrite O.unsigned_repr in Hlt by superlia.
        superlia.
      * unfold Int.eq. destruct (Coqlib.zeq _ _) as [Heq|Hne]; [|now contradiction Hne]; cbn.
        unfold O.sub, O.divs in Hge.
        unfold valid_mem in Hm; cbn in Hm; decompose [ex and] Hm.
        match goal with
        | H : (_ * _ = O.unsigned limit_o - O.unsigned alloc_o)%Z |- _ => rewrite <- H in *
        end.
        apply Z.le_ge; apply Z.ge_le in Hge.
        apply Z.mul_le_mono_pos_r; [superlia|].
        rewrite !O.signed_repr in Hge by superlia.
        pose proof word_size_lt_max_signed.
        rewrite O.signed_repr in Hge by superlia.
        rewrite Z.quot_mul in Hge by superlia.
        rewrite <- !O.agree32_of_ints in Hge by auto.
        unfold O.to_int, O.of_ints in Hge.
        rewrite !O.agree32_repr in Hge by auto.
        rewrite !Int.repr_signed, !Int.repr_unsigned in Hge.
        rewrite <- !O.agree32_repr in Hge by auto.
        unfold O.of_intu, O.of_int in Hge.
        rewrite <- O.agree32_repr in Hge by auto.
        rewrite !O.repr_unsigned in Hge.
        rewrite !O.unsigned_repr in Hge by superlia.
        superlia.
Qed.

Lemma rel_val_wf k v P cv :
  v ~ᵥ{k} (P, cv) ->
  val_defined_wf cv.
Proof.
  destruct v; rewrite rel_val_eqn; cbn.
  - destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    + intros [H ?]; subst cv; auto with EvalDB.
    + destruct cv; auto with EvalDB.
  - destruct cv; auto with EvalDB.
  - intros ->; auto with EvalDB.
Qed.
Hint Resolve rel_val_wf : EvalDB.

Lemma shadow_stack_eqn m S s ss cvs cvss :
  m |=_{S} shadow_stack (s :: ss) (cvs :: cvss) <->
  m |=_{S} shadow_stack_frame s cvs (stack_top ss) ⋆ shadow_stack ss cvss.
Proof. reflexivity. Qed.

Ltac rewrite_equiv_in_l F H Hin :=
  rewrite <- (frame_cong' F) in Hin;
  [|eauto with FrameDB|intros; apply H].

Hypothesis prog_genv_has_gc : exists b,
  let sig := mksignature (ast_value :: nil) None cc_default in
  let ext_fn := EF_external "garbage_collect" sig in
  let fn := External ext_fn (Tcons threadInf Tnil) Tvoid cc_default in
  Genv.find_symbol prog_genv gc_id = Some b /\
  Genv.find_funct prog_genv (Vptr b O.zero) = Some fn.

Hypothesis prog_genv_has_isptr : exists b,
  let sig := mksignature (ast_value :: nil) None cc_default in
  let ext_fn := EF_external "is_ptr" sig in
  let fn := External ext_fn (Tcons value Tnil) bool_ty cc_default in
  Genv.find_symbol prog_genv isptr_id = Some b /\
  Genv.find_funct prog_genv (Vptr b O.zero) = Some fn.

Lemma has_shapes_snoc_top P v cv vs cvs vss cvss :
  has_shape P v cv ->
  has_shapes P (vs :: vss) (cvs :: cvss) ->
  has_shapes P ((vs ++ [v]) :: vss)%list ((cvs ++ [cv]) :: cvss)%list.
Proof.
  intros Hv Hvs.
  inv Hvs; constructor; auto.
  apply Forall2_app; auto.
Qed.

Lemma Forall3_len {A B C} (P : A -> B -> C -> Prop) xs ys zs :
  Forall3 P xs ys zs -> #|xs| = #|ys| /\ #|ys| = #|zs|.
Proof.
  revert ys zs; induction xs as [|x xs IHxs]; destruct ys as [|y ys], zs as [|z zs]; cbn; try lia.
  intros [HP Hforall]; specialize (IHxs ys zs Hforall); lia.
Qed.

Ltac bad_lengths_in H :=
  apply Forall3_len in H; cbn in H; rewrite ?app_length in H; cbn in H; lia.

Lemma Forall3_snoc {A B C} (P : A -> B -> C -> Prop) xs x ys y zs z :
  Forall3 P (xs ++ [x]) (ys ++ [y]) (zs ++ [z]) ->
  Forall3 P xs ys zs /\ P x y z.
Proof.
  revert ys zs; induction xs as [|x' xs IHxs].
  - intros [|y' ys] [|z' zs] H; try solve [bad_lengths_in H].
    now inv H.
  - intros [|y' ys] [|z' zs] H; try solve [bad_lengths_in H].
    destruct H as [Hxyz' H]; apply IHxs in H; cbn; easy.
Qed.

Lemma compatible_shapes_snoc_top P P' v cv cv' vs cvs cvs' vss cvss cvss' :
  (compatible_shapes P P' ((vs ++ [v]) :: vss) ((cvs ++ [cv]) :: cvss) ((cvs' ++ [cv']) :: cvss') ->
   compatible_shapes P P' (vs :: vss) (cvs :: cvss) (cvs' :: cvss') /\
   compatible_shape P P' v cv cv')%list.
Proof. intros [Hvs Hvss]; apply Forall3_snoc in Hvs; destruct Hvs as [Hvs Hv]; now cbn. Qed.

Lemma valid_mem_limit_alloc_nonneg S m nursery_b talloc_o tlimit_o alloc_o limit_o tinfo_b
      tinfo_o args ss cvss nalloc values frame :
  m |=_{S} valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o
    tinfo_b tinfo_o args ss cvss nalloc
    values frame ->
  (O.unsigned limit_o - O.unsigned alloc_o >= 0)%Z.
Proof.
  intros H; unfold valid_mem in H.
  match type of H with
  | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
    destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) free_space H;
    destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) Hfree_space H
  end.
  superlia.
Qed.

Lemma fwd_load F env tenv m a i x ty b o p s vs P :
  is_frame F ->
  (env, tenv, m, a) ⇓ᵣ (Vptr b o) ->
  typeof a = value \/ typeof a = tptr ty ->
  (0 <= i < #|vs|)%Z ->
  perm_order p Readable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall v,
    get_ith vs i = Some v ->
    postcond env (M.set x v tenv) m s P) ->
  postcond env tenv m (x ::= a.[i].; s)%C P.
Proof.
  intros HF Ha Hty Hbound Hperm Hm Hcont.
  apply get_ith_in_range in Hbound; destruct Hbound as [v Hv].
  fwd Cred_set.
  - econstructor.
    + econstructor; econstructor; eauto with EvalDB.
      econstructor; eauto with EvalDB.
      { destruct Hty as [Hty|Hty]; rewrite Hty; eauto with EvalDB. }
      cbn; eauto with EvalDB.
    + econstructor; eauto with EvalDB.
      apply mpred_frame_in in Hm; [|auto]; cbn in Hm; decompose [ex and] Hm.
      unfold Mem.loadv, load in *.
      rewrite O.unsigned_repr by superlia.
      eauto.
  - auto.
Qed.

Fixpoint add_to_env vs (tenv : Clight.temp_env) xs i :=
  match xs with
  | [] => Some tenv
  | x :: xs =>
    match get_ith vs i with
    | Some v => add_to_env vs (M.set x v tenv) xs (i + 1)%Z
    | None => None
    end
  end.

Lemma skipn_nil_len {A} n : forall xs : list A,
  skipn n xs = [] -> n >= length xs.
Proof.
  induction n as [|n IHn]; destruct xs as [|x xs]; cbn; try easy.
  intros H; specialize (IHn _ H); lia.
Qed.

Lemma skipn_len_le {A} n : forall xs : list A,
  length (skipn n xs) <= length xs - n.
Proof. induction n as [|n IHn]; destruct xs as [|x xs]; cbn; easy. Qed.

Lemma pos_list_in_dec : forall (x : positive) xs, {List.In x xs} + {~ List.In x xs}.
Proof.
  induction xs as [|x' xs IHxs]; [now right|].
  destruct (Pos.eq_dec x x') as [|Hne]; [subst x'; left; now left|].
  destruct IHxs as [Hin|Hno]; [left; now right|right; intros [->|Hwat]; easy].
Qed.

Lemma set_lists_snoc {A} xs vs x v (ρ ρ1 ρ2 : M.t A) :
  ~ List.In x xs ->
  set_lists xs vs (M.set x v ρ) = Some ρ1 ->
  set_lists (x :: xs) (v :: vs) ρ = Some ρ2 ->
  forall y, ρ1!y = ρ2!y.
Proof.
  cbn [set_lists].
  destruct (set_lists xs vs ρ) as [ρxv|] eqn:Hρxv; [|easy].
  intros Hnotin Hxvs_xv Hxv_xvs; inv Hxv_xvs; intros y.
  destruct (pos_list_in_dec y xs) as [Hyes|Hno].
  - assert (y <> x) by (intros ->; contradiction Hnotin).
    rewrite M.gso by auto.
    edestruct (set_lists_Forall2_get eq xs vs vs ρ (M.set x v ρ)) as [vx [vx' [Hvx [Hvx' Hvx_eq]]]];
      try eassumption; try apply Forall2_refl; congruence.
  - destruct (Pos.eq_dec x y) as [<-|Hne].
    + rewrite M.gss.
      erewrite <- set_lists_not_In with (rho' := ρ1); eauto.
      now rewrite M.gss.
    + rewrite M.gso by auto.
      erewrite <- set_lists_not_In with (rho := M.set x v ρ) (rho' := ρ1); eauto.
      erewrite <- set_lists_not_In with (rho := ρ) (rho' := ρxv); eauto.
      now rewrite M.gso by auto.
Qed.

Lemma add_to_env_set_lists vs xs : forall tenv i ρ,
  (0 <= i <= #|vs| - #|xs|)%Z ->
  NoDup xs ->
  add_to_env vs tenv xs i = Some ρ -> exists ρ',
  set_lists xs (firstn (Z.to_nat #|xs|) (skipn (Z.to_nat i) vs)) tenv = Some ρ' /\
  forall x, ρ!x = ρ'!x.
Proof.
  induction xs as [|x xs IHxs].
  - cbn; intros tenv i Hi.
    now rewrite Nat2Z.id; cbn.
  - intros tenv i ρ Hi.
    assert (Hget : (0 <= i < #|vs|)%Z) by (cbn in *; lia).
    apply get_ith_in_range in Hget.
    destruct Hget as [vi Hvi].
    cbn [add_to_env]. rewrite Hvi.
    intros Hdup Hadd; inv Hdup.
    edestruct IHxs as [ρ' [Hρ' Hρρ']]; try apply Hadd; try (cbn in *; superlia); auto.
    replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1) in * by lia.
    rewrite <- MCList.skipn_skipn in Hρ'.
    destruct (skipn (Z.to_nat i) vs) as [|vi' vis] eqn:Hskip_vs.
    { cbn; rewrite !firstn_nil; cbn.
      apply skipn_nil_len in Hskip_vs.
      cbn in *. superlia. }
    cbn [skipn] in Hρ'.
    pose proof skipn_len_le (Z.to_nat i) vs as Hskipn_len.
    replace (Z.to_nat #|x::xs|) with (1 + Z.to_nat #|xs|) by (cbn; lia).
    rewrite MCList.firstn_add; cbn [firstn skipn app].
    edestruct (set_lists_length3 tenv) as [ρ'' Hρ''].
    2: exists ρ''; split; eauto.
    + cbn. rewrite firstn_length_le.
      * cbn; now rewrite Nat2Z.id.
      * apply f_equal with (f := fun xs => #|xs|) in Hskip_vs.
        rewrite skipn_len in Hskip_vs by lia.
        cbn in *; superlia.
    + intros y; transitivity (ρ' ! y); auto.
      eapply set_lists_snoc; eauto.
      apply get_ith_firstn_skipn in Hvi.
      apply f_equal with (f := firstn (Z.to_nat 1)) in Hskip_vs.
      now rewrite Hvi in Hskip_vs; inv Hskip_vs.
Qed.

Lemma fwd_loads F P_tenv env tenv m a i xs ty b o p s vs P :
  is_frame F ->
  (forall tenv,
    P_tenv tenv ->
    (env, tenv, m, a) ⇓ᵣ (Vptr b o)) ->
  P_tenv tenv ->
  (forall tenv x v, List.In x xs -> P_tenv tenv -> P_tenv (M.set x v tenv)) ->
  typeof a = value \/ typeof a = tptr ty ->
  (0 <= #|xs| <= #|vs| /\ 0 <= i <= #|vs| - #|xs|)%Z ->
  perm_order p Readable ->
  m |= F ((b, O.unsigned o) ↦_{p} vs) ->
  (forall tenv',
    add_to_env vs tenv xs i = Some tenv' ->
    postcond env tenv' m s P) ->
  postcond env tenv m (statements (mapi (fun i x => x ::= a.[i]) i xs).; s)%C P.
Proof.
  intros HF Ha Htenv_base Htenv_ind Hty Hbounds Hperm Hm Hcont.
  revert tenv vs m i Ha Htenv_base Htenv_ind Hm Hbounds Hcont; induction xs as [|x xs IHxs];
  intros tenv vs m i Ha Htenv_base Htenv_ind Hm Hbounds Hcont.
  { cbn. fwd Cred_skip. apply Hcont; auto. }
  cbn. fwd Cred_seq_assoc.
  eapply fwd_load; eauto; try (cbn in *; superlia).
  intros vi Hget_vi.
  eapply IHxs; eauto.
  { apply Htenv_ind; auto; now left. }
  { intros; apply Htenv_ind; auto; now right. }
  { cbn in *; superlia. }
  intros tenv' Htenv'.
  apply Hcont; cbn; now rewrite Hget_vi.
Qed.

(* TODO hoist *)
Lemma mpred_ex_intro {A} S m F G (x : A) :
  is_frame F ->
  m |=_{S} F (G x) -> m |=_{S} F (∃ x, G x).
Proof.
  intros HF Hm.
  rewrite mpred_Ex by auto; now exists x.
Qed.

Ltac tempvars_neq_as H x y :=
  assert (H : x <> y)
  by (clear - thread_info_id calling_convention NoDup_vars;
     rewrite <- NoDup'_spec in NoDup_vars; now cbn in * ).

Ltac tempvars_neq x y :=
  assert (x <> y)
  by (clear - thread_info_id calling_convention NoDup_vars;
      rewrite <- NoDup'_spec in NoDup_vars; now cbn in * ).

(* TODO hoist *)
Lemma max_live_ctx C e n :
  max_live locals (C |[ e ]|) n -> max_live locals e n.
Proof.
  intros HCe D x f t ys e' ->.
  specialize (HCe (comp_ctx_f C D) x f t ys e').
  now rewrite app_ctx_f_fuse in HCe.
Qed.

(*
Print make_cases.
Print translate_body.
Lemma make_cases_unboxed_spec :
  cps_util.find_tag_nth ces c e n ->
  make_cases cenv (translate_body cenv fenv locals nenv) = Ret (boxed, unboxed, fvs, n) ->
 *)

(* TODO hoist *)
Lemma bind_assoc {A B C} m (j : A -> error B) (k : B -> error C) :
 (y <- (x <- m ;; j x) ;; k y) = (x <- m ;; y <- j x ;; k y).
Proof. destruct m; reflexivity. Qed.

Lemma fwd_switch env tenv m e i ls P :
  (0 <= i <= O.max_unsigned)%Z ->
  typeof e = value ->
  (env, tenv, m, e) ⇓ᵣ vint i ->
  postcond' env tenv m (seq_of_labeled_statement (select_switch i ls)) P ->
  postcond' env tenv m (Sswitch e ls) P.
Proof.
  intros Hbound Hty Heval [env' [tenv' [m' [Hrun HP]]]]; do 3 eexists; split; eauto.
  unfold "⇓"; change (Out_return ?v) with (outcome_switch (Out_return v)).
  econstructor; eauto.
  rewrite Hty.
  unfold vint, value; destruct Archi.ptr64 eqn:Harchi; cbn.
  - rewrite <- O.agree64_repr by auto. 
    rewrite O.unsigned_repr; auto; superlia.
  - rewrite <- O.agree32_repr by auto.
    rewrite O.unsigned_repr; auto; superlia.
Qed.

Hypothesis cenv_tags_representable : forall c,
  match get_ctor_rep cenv c with
  | Ret (enum t) => 0 <= rep_unboxed t <= O.max_unsigned
  | Ret (boxed t a) =>
    0 <= rep_boxed t a <= O.max_unsigned /\
    0 <= Z.of_N t < Zpower.two_power_pos 8 /\
    0 <= Z.of_N a < Zpower.two_power_nat (Ptrofs.wordsize - 10)
  | _ => True
  end%Z.

Hypothesis cenv_tags_inj : forall c c',
  c <> c' ->
  match get_ctor_rep cenv c, get_ctor_rep cenv c' with
  | Ret (enum t), Ret (enum t') => t <> t'
  | Ret (boxed t a), Ret (boxed t' a') => t <> t'
  | _, _ => True
  end.

Lemma max_signed_archi : O.max_signed = if Archi.ptr64 then Int64.max_signed else Int.max_signed.
Proof.
  unfold O.max_signed, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize.
  unfold Int64.max_signed, Int64.half_modulus, Int.max_signed, Int.half_modulus.
  unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  now destruct Archi.ptr64.
Qed.

Lemma max_unsigned_archi : O.max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.
Proof.
  unfold O.max_unsigned, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize.
  unfold Int64.max_unsigned, Int64.half_modulus, Int.max_unsigned, Int.half_modulus.
  unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  now destruct Archi.ptr64.
Qed.

Lemma concrete_int64_max_unsigned : Int64.max_unsigned = 18446744073709551615%Z. Proof. now cbv. Qed.
Lemma concrete_int64_max_signed : Int64.max_signed = 9223372036854775807%Z. Proof. now cbv. Qed.
Lemma concrete_int_max_unsigned : Int.max_unsigned = 4294967295%Z. Proof. now cbv. Qed.
Lemma concrete_int_max_signed : Int.max_signed = 2147483647%Z. Proof. now cbv. Qed.

Lemma eval_shiftr1 ge env tenv m e i :
  (0 <= i <= O.max_unsigned)%Z ->
  typeof e = value ->
  eval_expr ge env tenv m e (vint i) ->
  eval_expr ge env tenv m (e >>' c_int 1 value) (vint (Z.shiftr i 1)).
Proof.
  intros Hbound Hty He; econstructor; eauto with EvalDB.
  cbn; rewrite Hty, typeof_c_int.
  unfold vint, value; rewrite max_unsigned_archi in Hbound; destruct Archi.ptr64 eqn:Harchi; cbn.
  - unfold Int64.ltu.
    destruct (Coqlib.zlt _ _) as [Hok|Hwat].
    2:{ unfold Int64.iwordsize in *.
        rewrite <- !O.agree64_repr in Hwat by auto.
        unfold Int64.zwordsize, Int64.wordsize, Wordsize_64.wordsize in *.
        assert (Z.of_nat 64 <= O.max_signed)%Z.
        { unfold O.max_signed, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize; rewrite Harchi.
          unfold two_power_nat, Z.div; now cbv. }
        rewrite !O.unsigned_repr in Hwat by superlia.
        superlia. }
    do 2 f_equal.
    rewrite Int64.shru_div_two_p.
    pose proof concrete_int64_max_unsigned.
    rewrite !Int64.unsigned_repr by lia.
    rewrite <- O.Zshiftr_div_two_p by lia.
    reflexivity.
  - unfold Int.ltu.
    destruct (Coqlib.zlt _ _) as [Hok|Hwat].
    2:{ unfold Int.iwordsize in *.
        rewrite <- !O.agree32_repr in Hwat by auto.
        unfold Int.zwordsize, Int.wordsize, Wordsize_32.wordsize in *.
        assert (Z.of_nat 32 <= O.max_signed)%Z.
        { unfold O.max_signed, O.half_modulus, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize; rewrite Harchi.
          unfold two_power_nat, Z.div; now cbv. }
        rewrite !O.unsigned_repr in Hwat by superlia.
        superlia. }
    do 2 f_equal.
    rewrite Int.shru_div_two_p.
    pose proof Int.min_signed_neg.
    pose proof Int.max_signed_unsigned.
    pose proof concrete_int_max_unsigned.
    rewrite !Int.unsigned_repr by superlia.
    rewrite <- O.Zshiftr_div_two_p by lia.
    reflexivity.
Qed.

Lemma binarith_value :
  binarith_type (classify_binarith value value) = value.
Proof. unfold value; destruct Archi.ptr64 eqn:Harchi; cbn; easy. Qed.

Lemma eval_and255 ge env tenv m e i :
  (0 <= i <= O.max_unsigned)%Z ->
  typeof e = value ->
  eval_expr ge env tenv m e (vint i) ->
  eval_expr ge env tenv m (e &' c_int 255 value) (vint (Z.land i 255)).
Proof.
  intros Hbound Hty He; econstructor; eauto with EvalDB.
  cbn; rewrite Hty, typeof_c_int.
  unfold sem_and, sem_binarith; cbn.
  rewrite !binarith_value, !sem_cast_wf_same; auto with EvalDB.
  unfold vint, value; rewrite max_unsigned_archi in Hbound; destruct Archi.ptr64 eqn:Harchi; cbn.
  - do 2 f_equal.
    unfold Int64.and.
    pose proof Int64.min_signed_neg.
    pose proof Int64.max_signed_unsigned.
    rewrite Int64.unsigned_repr by superlia.
    rewrite Int64.unsigned_repr; auto.
    cbv; split; inversion 1.
  - do 2 f_equal.
    unfold Int.and.
    pose proof Int.min_signed_neg.
    pose proof Int.max_signed_unsigned.
    rewrite Int.unsigned_repr by superlia.
    rewrite Int.unsigned_repr; auto.
    cbv; split; inversion 1.
Qed.

Lemma env_gso env tenv x v y :
  x <> y ->
  (env, PTree.set x v tenv) !!! y = (env, tenv) !!! y.
Proof. now unfold "!!!"; intros H; rewrite M.gso by auto. Qed.

Lemma repr_unboxed_shiftr i:
  Z.shiftr (Z.shiftl i 1 + 1) 1 = i.
Proof.
  rewrite O.Zshiftl_mul_two_p by lia.
  unfold Z.shiftr. 
  simpl Z.shiftl.
  unfold Zpower.two_power_pos. simpl.
  rewrite Zdiv.Zdiv2_div. 
  replace (i * 2 + 1)%Z with (OrdersEx.Z_as_OT.b2z true + 2 * i)%Z by (simpl OrdersEx.Z_as_OT.b2z; lia).
  apply OrdersEx.Z_as_OT.add_b2z_double_div2.
Qed.

(* TODO hoist *)
Lemma postcond'_seq env tenv m s s_skipd P :
  postcond' env tenv m s P ->
  postcond' env tenv m (s.; s_skipd)%C P.
Proof.
  intros [env' [tenv' [m' [Heval HP]]]].
  exists env', tenv', m'; split; auto.
  constructor; eauto. easy.
Qed.

Theorem pos_testbit_nat_impossible:
  forall b,
  ~(forall d : nat, 0 <= d -> Pos.testbit_nat b d = false).
Proof.
  induction b; intro.
  - apply IHb; intros.
    assert ( 0 <= 0) by reflexivity.
    apply H in H1. inv H1.
  - apply IHb.
    intros.    
    simpl in H.    
    assert (0 <= S d) by lia.
    apply H in H1.
    auto.
  - assert (0 <= 0).
    reflexivity.
    apply H in H0. inv H0.    
Qed.

Theorem pland_split_nat:
  forall c a b,
  (forall d, d < c -> Pos.testbit_nat a d = false) -> 
  (forall d, c <= d -> Pos.testbit_nat b d = false) ->
                Pos.land a b = 0%N.
Proof.
  induction c; intros.
  - apply pos_testbit_nat_impossible in H0.
    inv H0.
  - destruct a.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by lia.
      apply H in H1.
      inv H1.
    + destruct b.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by lia.
        apply H in H2. auto.
        assert (S c <= S d) by lia.
        apply H0 in H2.
        simpl in H2. auto.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by lia.
        apply H in H2. auto.
        assert (S c <= S d) by lia.
        apply H0 in H2.
        simpl in H2. auto.
      * reflexivity.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by lia.
      apply H in H1.
      inv H1.
Qed.

Lemma repr_boxed_and t a :
  (0 <= Z.of_N t < Zpower.two_power_pos 8)%Z ->
  (0 <= Z.of_N a < Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z ->
  Z.land (rep_boxed t a) 255 = Z.of_N t.
Proof.
  intros Hbound_t Hbound_a.
  unfold rep_boxed.
  apply Z.bits_inj.
  unfold Z.eqf.
  intro.
  rewrite Z.land_spec.
  assert (Hcase_z:= Z.lt_ge_cases n 0%Z).
  destruct Hcase_z as [Hnz | Hnz].
  { (* testbit = false *)
    destruct n. exfalso; lia.
    exfalso. assert (0 < Z.pos p)%Z by apply Pos2Z.pos_is_pos. lia.
    reflexivity.
  }    
  assert (Hcase := Z.lt_ge_cases n 8%Z).
  destruct Hcase.
  - replace 255%Z with (Z.pred (2^8))%Z.
    rewrite <- Z.ones_equiv. 
    rewrite Z.ones_spec_low.
    rewrite Bool.andb_true_r.
    rewrite Z.add_nocarry_lxor.
    rewrite Z.lxor_spec.
    rewrite OrdersEx.Z_as_OT.shiftl_spec_low.
    rewrite Bool.xorb_false_l.
    reflexivity. lia.
    (* multiple cases depending of if one is 0 or not *)
    {
      destruct (Z.shiftl (Z.of_N a) 10) eqn:Ha.
      - reflexivity.
      - destruct (Z.of_N t) eqn:Hb.
        + reflexivity.
        + simpl.
          rewrite pland_split_nat with (c := 8). reflexivity.
          * intros.
            rewrite <- Ndigits.Ptestbit_Pbit.            
            destruct d. simpl.
            destruct (Z.of_N a). simpl in Ha.
            assert (0 < Z.pos p)%Z by apply Pos2Z.pos_is_pos. lia.
            simpl in Ha. inv Ha. reflexivity.
            inv Ha. 
            replace false with
                (Z.testbit (Z.pos p)  (Z.of_nat (S d))).
            reflexivity. 
            rewrite <- Ha.
            apply Z.shiftl_spec_low.
            apply Nat2Z.inj_lt in H0.
            simpl Z.of_nat in *. lia.
          * intros.
            rewrite Zpower.two_power_pos_nat in Hbound_t.
            rewrite <- Ndigits.Ptestbit_Pbit.            
            destruct d. exfalso; lia.
            replace false with
                (Z.testbit (Z.pos p0)  (Z.of_nat (S d))). reflexivity.
            eapply Int.Ztestbit_above.
            apply Hbound_t.
            apply Nat2Z.inj_le in H0.
            replace (Pos.to_nat 8) with 8.
            lia. reflexivity.
        + destruct t; inv Hb.
      - exfalso.
        destruct Hbound_a.
        rewrite <- Z.shiftl_nonneg with (n := 10%Z) in H0.
        rewrite Ha in H0.
        assert (Hnn := Zlt_neg_0 p). lia.
    }
    lia.
    simpl. reflexivity.
  - (* always false *)
    rewrite Bool.andb_false_intro2.
    symmetry.
    eapply Byte.Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct. 
    rewrite Zpower.two_power_pos_correct in *.
    unfold Z.pow_pos in H. simpl in *.
    lia.
    simpl. lia.
    eapply Byte.Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct. simpl. lia.
    simpl. lia.
Qed.

Lemma eval_load ge env tenv m nursery_b alloc_o limit_o tinfo_b tinfo_o ss cvss values frame b o t a cvs i e :
  typeof e = value ->
  eval_expr ge env tenv m e (Vptr b o) ->
  (-1 <= i < #|cvs|)%Z ->
  m |= ∃ (args : list Values.val) (nalloc : Z) (talloc_o tlimit_o : ptrofs),
     valid_mem nursery_b talloc_o tlimit_o alloc_o limit_o tinfo_b tinfo_o args ss cvss nalloc values frame ->
  values |-- (b, (O.unsigned o - word_size)%Z) ↦_{Readable} vint (rep_boxed t a) :: cvs ⋆ Pure True -> exists v,
  get_ith (vint (rep_boxed t a) :: cvs) (i + 1)%Z = Some v /\
  eval_expr ge env tenv m (e.[i]) v.
Proof.
  intros Hty Heval Hbound Hm Hvalues.
  edestruct (get_ith_in_range (vint (rep_boxed t a) :: cvs) (i + 1)%Z) as [v Hv].
  { cbn; superlia. }
  unfold "|=" in *.
  destruct_ex args Hm.
  destruct_ex nalloc Hm.
  destruct_ex talloc_o Hm.
  destruct_ex tlimit_o Hm.
  unfold valid_mem in Hm.
  match type of Hm with
  | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ _ ⋆ ?S =>
    eapply (frame_entail (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S)) in Hm;
      auto with FrameDB; eauto
  end.
  eexists; split; eauto.
  econstructor.
  - econstructor; eauto with EvalDB.
    econstructor; eauto with EvalDB.
    + econstructor; eauto with EvalDB.
      rewrite Hty; eauto with EvalDB.
    + cbn. eauto with EvalDB.
  - econstructor; [apply access_mode_value|].
    unfold Mem.loadv. rewrite O.unsigned_repr.
    2:{ cbn in Hm; decompose [ex and] Hm; clear Hm. superlia. }
    replace (O.unsigned o + i * word_size)%Z
      with ((O.unsigned o - word_size) + (i + 1)*word_size)%Z by lia.
    match type of Hm with
    | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ (_ ⋆ ?S) ⋆ ?T =>
      eapply (mpred_load _ (fun H => P ⋆ Q ⋆ R ⋆ (H ⋆ S) ⋆ T));
        auto with FrameDB; eauto
    end.
Qed.

Context (nenv : name_env).

Lemma mul_div_le n m k : (k > 0 -> n*k <= m -> n <= m/k)%Z.
Proof.
  intros Hpos H; apply Z_div_le with (c := k) in H; [|superlia].
  now rewrite Z_div_mult in H by superlia.
Qed.

Lemma mul_div_bound n m p k : (k > 0 -> n*k <= m <= p*k -> n <= m/k <= p)%Z.
Proof.
  intros Hpos [Hlo Hhi]; split; [apply mul_div_le; auto|].
  apply Z_div_le with (c := k) in Hhi; [|superlia].
  now rewrite Z_div_mult in Hhi by superlia.
Qed.

Lemma concrete_O_max_unsigned : O.max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.
Proof.
  unfold O.max_unsigned, O.modulus, O.wordsize, Wordsize_Ptrofs.wordsize; destruct Archi.ptr64;
    rewrite ?concrete_int64_max_unsigned; rewrite ?concrete_int_max_unsigned; reflexivity.
Qed.

Lemma fwd_case ces k ρ x vs env tenv cv m nursery_b alloc_o limit_o tinfo_b tinfo_o
      ss cvss values frame c e n_ce boxed_cases unboxed_cases fvs_cases n_cases P :
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  x <> case_id -> x <> frame_id -> x <> roots_id ->
  ρ ! x = Some (Vconstr c vs) ->
  (env, tenv) !!! x = Some cv ->
  Vconstr c vs ~ᵥ{k} (values, cv) ->
  m |= ∃ args nalloc talloc_o tlimit_o,
       valid_mem nursery_b talloc_o tlimit_o
                 alloc_o limit_o tinfo_b tinfo_o
                 args ss cvss nalloc values
                 frame ->
  cps_util.find_tag_nth ces c e n_ce ->
  make_cases cenv (translate_body cenv fenv locals nenv) ces = Ret (boxed_cases, unboxed_cases, fvs_cases, n_cases) ->
  (forall stm_e fvs_e n_e cv_isptr,
    cv_isptr = Vtrue \/ cv_isptr = Vfalse ->
    translate_body cenv fenv locals nenv e = Ret (stm_e, fvs_e, n_e) ->
    postcond' env (M.set case_id cv_isptr tenv) m stm_e P) ->
  postcond' env tenv m
           (Scall (Some case_id) isptr [make_var fenv locals x].;
            Sifthenelse
              (Etempvar case_id bool_ty)
              (Sswitch (make_var fenv locals x .[ -1] &' make_cint 255 value) boxed_cases)
              (Sswitch (make_var fenv locals x >>' make_cint 1 value) unboxed_cases))%C
           P.
Proof.
  intros Henvs Hcase Hframe Hroots Hvx Hcvx Hrel_x Hm Hfind Hmake Hcont.
  rewrite rel_val_eqn in Hrel_x; cbn in Hrel_x.
  pose proof cenv_tags_representable c as c_representable.
  destruct (get_ctor_rep _ _) as [| [t|t a]] eqn:Hrep; [destruct Hrel_x| |];
    rewrite ?Hrep in c_representable.
  - (** c is an unboxed constructor *)
    destruct Hrel_x as [-> ->]. rewrite postcond'_spec.
    (** Call is_ptr *)
    destruct prog_genv_has_isptr as [isptr_b [Hfind_isptr_symbol Hfind_isptr_funct]].
    pose proof is_ptr_spec as is_ptr_false.
    edestruct is_ptr_false with (v := vint (rep_unboxed t))
      as [cv_isptr [Hcv_isptr [_ Hcv_isptr_false]]]; auto with EvalDB.
    eapply fwd_call; try reflexivity; try eassumption; try reflexivity.
    { econstructor; [|eauto with EvalDB].
      tempvars_neq isptr_id frame_id.
      tempvars_neq isptr_id roots_id.
      eapply eval_Evar_global; eauto.
      eapply Henvs; auto. }
    { econstructor; [..|constructor].
      - eapply eval_make_var; eauto. split_ands; easy.
      - rewrite typeof_make_var. eauto with EvalDB. }
    { constructor. unfold Events.external_call. apply Hcv_isptr. }
    (assert (cv_isptr = Vfalse) by now eapply Hcv_isptr_false). subst cv_isptr.
    cbn [set_opttemp].
    fwd Cred_if'.
    { constructor; rewrite M.gss. reflexivity. }
    { cbn. rewrite Int.eq_true. reflexivity. }
    cbn [negb].
    rewrite <- postcond'_spec.
    unfold rep_unboxed in *.
    eapply fwd_switch; try reflexivity.
    2:{
      apply eval_shiftr1; eauto with EvalDB.
      eapply eval_make_var; eauto.
      - decompose [and] Henvs; split_ands; eauto with EvalDB InvDB.
      - congruence.
      - rewrite env_gso by auto. eauto. }
    { rewrite O.Zshiftr_div_two_p by lia.
      change (two_p 1) with 2%Z.
      apply mul_div_bound; lia. }
    rewrite repr_unboxed_shiftr.
    (** Search through ces for the right case *)
    revert n_ce Hfind boxed_cases unboxed_cases fvs_cases n_cases Hmake.
    induction ces as [| [c' e'] ces IHces]; [intros n_ce Hfind; inv Hfind|].
    intros n_ce Hfind boxed_cases unboxed_cases fvs_cases n_cases Hmake.
    cbn in Hmake.
    bind_step_in Hmake e'' He_taken.
    destruct e'' as [[stm_e_taken fvs_e_taken] n_e_taken].
    bind_step_in Hmake ces' Hces.
    destruct ces' as [[[boxed_cases' unboxed_cases'] fvs_ces'] n_ces'].
    destruct (get_ctor_rep _ c') as [| [t'|t' a']] eqn:Hrep'; [inv Hmake| |];
      rewrite !bind_ret in Hmake; inv Hmake.
    2:{ (** (c', e') is boxed *) inv Hfind; [congruence|]. eapply IHces; eauto. }
    inv Hfind.
    * (** c = c' *)
      assert (t = t') by congruence. subst t'.
      unfold select_switch, select_switch_case.
      destruct (Coqlib.zeq _ _) as [_|Hne]; [|lia].
      cbn [seq_of_labeled_statement].
      apply postcond'_seq.
      eapply Hcont; eauto.
    * (** c ≠ c' *)
      specialize (cenv_tags_inj c c'); rewrite Hrep, Hrep' in cenv_tags_inj.
      assert (t <> t') by auto.
      unfold select_switch, select_switch_case; fold select_switch_case.
      unfold select_switch_default; fold select_switch_default.
      destruct (Coqlib.zeq _ _) as [Heq|Hne]; [lia|].
      eapply IHces; eauto.
  - (** c is a boxed constructor *)
    rewrite postcond'_spec.
    destruct cv; try solve [destruct Hrel_x].
    rename b into cvx_b, i into cvx_o.
    destruct Hrel_x as [cvs [Hcvs Hrel_cvs]].
    (** Call is_ptr *)
    destruct prog_genv_has_isptr as [isptr_b [Hfind_isptr_symbol Hfind_isptr_funct]].
    pose proof is_ptr_spec as is_ptr_true.
    edestruct is_ptr_true with (v := Vptr cvx_b cvx_o)
      as [cv_isptr [Hcv_isptr [Hcv_isptr_true _]]]; auto with EvalDB.
    eapply fwd_call; try reflexivity; try eassumption; try reflexivity.
    { econstructor; [|eauto with EvalDB].
      tempvars_neq isptr_id frame_id.
      tempvars_neq isptr_id roots_id.
      eapply eval_Evar_global; eauto.
      eapply Henvs; auto. }
    { econstructor; [..|constructor].
      - eapply eval_make_var; eauto. split_ands; easy.
      - rewrite typeof_make_var. eauto with EvalDB. }
    { constructor. unfold Events.external_call. apply Hcv_isptr. }
    (assert (cv_isptr = Vtrue) by now eapply Hcv_isptr_true); subst cv_isptr.
    cbn [set_opttemp].
    fwd Cred_if'.
    { constructor; rewrite M.gss. reflexivity. }
    { cbn. rewrite Int.eq_false by easy. reflexivity. }
    cbn [negb].
    rewrite <- postcond'_spec.
    unfold rep_boxed in *.
    (** Evaluate the scrutinee *)
    edestruct eval_load
      with (e := make_var fenv locals x) (i := (-1)%Z)
           (tenv := PTree.set case_id Vtrue tenv)
      as [cv_tag [Hcv_tag Heval_cv_tag]]; try eassumption.
    { now rewrite typeof_make_var. }
    { eapply eval_make_var; eauto. split_ands; eauto with InvDB.
      - easy.
      - rewrite env_gso by auto. eassumption. }
    { lia. }
    replace (-1 + 1)%Z with 0%Z in Hcv_tag by lia.
    cbn in Hcv_tag; inv Hcv_tag.
    eapply fwd_switch; try reflexivity.
    2:{ apply eval_and255; eauto with EvalDB. unfold rep_boxed. lia. }
    { change 255%Z with (Z.ones 8).
      rewrite Z.land_ones by lia.
      assert (0 <= rep_boxed t a mod 2^8 < 2^8)%Z.
      { apply Z.mod_pos_bound. lia. }
      enough (2^8 < O.max_unsigned)%Z by lia.
      rewrite concrete_O_max_unsigned, concrete_int64_max_unsigned, concrete_int_max_unsigned;
        destruct Archi.ptr64; lia. }
    (** Search through ces for the right case *)
    revert n_ce Hfind boxed_cases unboxed_cases fvs_cases n_cases Hmake.
    induction ces as [| [c' e'] ces IHces]; [intros n_ce Hfind; inv Hfind|].
    intros n_ce Hfind boxed_cases unboxed_cases fvs_cases n_cases Hmake.
    cbn in Hmake.
    bind_step_in Hmake e'' He_taken.
    destruct e'' as [[stm_e_taken fvs_e_taken] n_e_taken].
    bind_step_in Hmake ces' Hces.
    destruct ces' as [[[boxed_cases' unboxed_cases'] fvs_ces'] n_ces'].
    destruct (get_ctor_rep _ c') as [| [t'|t' a']] eqn:Hrep'; [inv Hmake| |];
      rewrite !bind_ret in Hmake; inv Hmake.
    { (** (c', e') is unboxed *) inv Hfind; [congruence|]. eapply IHces; eauto. }
    inv Hfind.
    * (** c = c' *)
      assert (t = t') by congruence. subst t'.
      assert (a = a') by congruence. subst a'.
      rewrite repr_boxed_and by lia.
      unfold select_switch, select_switch_case.
      destruct (Coqlib.zeq _ _) as [_|Hne]; [|lia].
      cbn [seq_of_labeled_statement].
      apply postcond'_seq.
      eapply Hcont; eauto.
    * (** c ≠ c' *)
      specialize (cenv_tags_inj c c'); rewrite Hrep, Hrep' in cenv_tags_inj.
      assert (t <> t') by auto.
      rewrite repr_boxed_and in * by lia.
      unfold select_switch, select_switch_case; fold select_switch_case.
      unfold select_switch_default; fold select_switch_default.
      destruct (Coqlib.zeq _ _) as [Heq|Hne]; [lia|].
      eapply IHces; eauto.
Qed.

(* TODO hoist *)
Definition nthN_range {A} (xs : list A) n y : 
  nthN xs n = Some y -> (0 <= Z.of_N n < #|xs|)%Z.
Proof.
  revert n; induction xs as [|x xs IHxs]; [inversion 1|intros n].
  cbn [nthN]; destruct (N.eq_dec n 0) as [->|Hne]; [inversion 1; cbn; superlia|].
  destruct n; [easy|].
  intros H; specialize (IHxs _ H).
  cbn; superlia.
Qed.

(* TODO hoist *)
Lemma postcond_ret env tenv m e cv (P : _ -> _ -> _ -> Prop) :
  typeof e = value ->
  (env, tenv, m, e) ⇓ᵣ cv ->
  P tenv m cv ->
  postcond' env tenv m (Sreturn (Some e)) P.
Proof.
  intros Hty He HP; do 3 eexists; split_ands; eauto.
  unfold "⇓". rewrite <- Hty. constructor; auto.
Qed.

Lemma eval_exprlist_make_var xs env tenv ρ vs cvs m :
  ~ List.In case_id xs ->
  ~ List.In frame_id xs ->
  ~ List.In roots_id xs ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  get_list xs ρ = Some vs ->
  (env, tenv) !!!! xs = Some cvs ->
  eval_exprlist prog_genv env tenv m (map (make_var fenv locals) xs) (value_tys (length xs)) cvs.
Proof.
  revert vs cvs; induction xs as [|x xs IHxs]; intros vs cvs.
  - cbn; intros. assert (cvs = []) by congruence. subst cvs; constructor.
  - intros Hcase Hframe Hroots Henvs Hρ_get Henv_get; cbn.
    cbn in Hρ_get. destruct (ρ ! x) as [vx|] eqn:Hρ_x; [|easy].
    destruct (get_list xs ρ) as [vxs|] eqn:Hρ_xs; [|easy].
    inv Hρ_get.
    cbn in Henv_get.
    destruct ((env, tenv) !!! x) as [cv|] eqn:Henv_x; [|easy].
    destruct ((env, tenv) !!!! xs) as [cvs'|] eqn:Henv_xs; [|easy].
    inv Henv_get.
    cbn in *; econstructor.
    + eapply eval_make_var; eauto with EvalDB; try easy.
    + rewrite typeof_make_var. apply env_get_wf in Henv_x; try easy.
      eauto with EvalDB.
    + eapply IHxs; auto.
Qed.

Lemma not_In_skipn {A} n xs (x : A) :
  ~ List.In x xs ->
  ~ List.In x (skipn n xs).
Proof.
  revert xs; induction n as [|n IHn]; [auto|intros xs].
  destruct xs as [|x' xs]; [auto|cbn].
  intros; apply IHn; intros Hwat; auto.
Qed.
Hint Resolve not_In_skipn : EvalDB.

Lemma NoDup_skipn {A} n : forall (xs : list A),
  NoDup xs -> NoDup (skipn n xs).
Proof.
  induction n as [|n IHn]; [auto|].
  destruct xs as [|x xs]; [intros H; inv H; cbn; constructor|].
  intros H; inv H; cbn; now apply IHn.
Qed.
Hint Resolve NoDup_skipn : EvalDB.

(* TODO hoist *)
Lemma pure_True_dup :
  Pure True |-- Pure True ⋆ Pure True.
Proof.
  intros S m [HS _]; cbn; exists S, (Empty_set _); split_ands; eauto; sets.
Qed.

(* TODO hoist *)
Lemma compatible_shape_entail P Q P' v cv cv' :
  P |-- Q ⋆ Pure True ->
  compatible_shape Q P' v cv cv' ->
  compatible_shape P P' v cv cv'.
Proof.
  intros HPQ; revert cv cv'; induction v as [c vs IHvs|ρ fds f|z] using val_ind''; intros cv cv'.
  - cbn. destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    destruct cv, cv'; auto.
    intros [cvs [cvs' [Hlen [Hcvs [Hcvs' Hcvs_rel]]]]].
    exists cvs, cvs'; split_ands; auto.
    + eapply entail_trans; eauto.
      eapply entail_trans; [|eapply (frame_entail (fun H => _ ⋆ H)); [|apply (entail_True (Pure True ⋆ Pure True))]; auto with FrameDB].
      eapply entail_trans; [|intros S m Hm; rewrite <- sepcon_assoc; apply Hm].
      apply (frame_entail (fun H => H ⋆ Pure True)); auto with FrameDB.
    + clear - IHvs Hcvs_rel; revert cvs cvs' Hcvs_rel; induction vs as [|v vs IHvs']; auto.
      destruct cvs, cvs'; auto. intros Hcvs_rel; inv Hcvs_rel.
      constructor.
      * eapply IHvs; eauto; now left.
      * eapply IHvs'; eauto. intros; apply IHvs; auto. now right.
  - eauto.
  - eauto.
Qed.

(* TODO hoist *)
Lemma compatible_shapes_entail P Q P' vss : forall cvss cvss',
  P |-- Q ⋆ Pure True ->
  compatible_shapes Q P' vss cvss cvss' ->
  compatible_shapes P P' vss cvss cvss'.
Proof.
  induction vss as [|vs vss IHvss];
    destruct cvss as [|cvs cvss];
    destruct cvss' as [|cvs' cvss']; try easy.
  intros HPQ [Hcvs Hcvss]; constructor; eauto.
  revert cvs cvs' Hcvs; induction vs as [|v vs IHvs]; destruct cvs as [|cv cvs], cvs' as [|cv' cvs']; auto.
  intros [Hcv Hcvs]; constructor; auto.
  eapply compatible_shape_entail; eauto.
Qed.

(* TODO hoist *)
Lemma compatible_shapes_sepcon P Q P' vss cvss cvss' :
  compatible_shapes Q P' vss cvss cvss' ->
  compatible_shapes (P ⋆ Q) P' vss cvss cvss'.
Proof.
  intros; eapply compatible_shapes_entail; eauto.
  eapply entail_trans; [intros S m Hm; rewrite sepcon_comm in Hm; apply Hm|].
  apply (frame_entail (fun H => Q ⋆ H)); auto with FrameDB; apply entail_True.
Qed.
Hint Resolve compatible_shapes_sepcon : ShapeDB.

(* TODO hoist *)
Lemma frame_mem_ex' F S P m :
  is_frame F ->
  m |=_{S} F P -> exists S',
  m |=_{S'} P.
Proof.
  intros HF; revert S; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros S Hm;
    cbn in Hm; decompose [ex and] Hm; try eapply IHF; eauto.
Qed.

(* TODO hoist *)
Lemma mapsto_unique' F G b o p vs vs' m P Q :
  is_frame F -> is_frame G ->
  m |= F P ->
  m |= G (Q ⋆ P) ->
  P |-- ((b, o) ↦_{p} vs) ⋆ Pure True ->
  Q ⋆ P |-- ((b, o) ↦_{p} vs') ⋆ Pure True ->
  #|vs| = #|vs'| ->
  vs = vs'.
Proof.
  intros HF HG Hm Hm' Hvs Hvs' Hlen.
  revert b o vs' Hvs Hvs' Hlen; induction vs as [|v vs IHvs]; intros b o vs' Hvs Hvs'.
  - destruct vs'; cbn; [auto|lia].
  - destruct vs' as [|v' vs']; [cbn; lia|]; intros Hlen; f_equal.
    + apply frame_mem_ex' in Hm; auto.
      destruct Hm as [S Hm].
      eapply frame_mem_ex' in Hm'; auto.
      destruct Hm' as [S' Hm'].
      specialize (Hvs _ _ Hm).
      specialize (Hvs' _ _ Hm').
      cbn in *; decompose [ex and] Hvs; decompose [ex and] Hvs'.
      now repeat match goal with H : forall (_ : Z), _ |- _ => try specialize (H 0%Z _ eq_refl); cbn in H end.
    + eapply entail_trans' in Hvs; [|apply mapsto_in_cons].
      eapply entail_trans' in Hvs'; [|apply mapsto_in_cons].
      eapply IHvs; eauto.
      cbn in *; lia.
Qed.

Lemma has_shape_compatible_shape_restriction F G m Q P P' v : forall cv cv',
  is_frame F -> is_frame G ->
  m |= F P ->
  m |= G (Q ⋆ P) ->
  has_shape P v cv ->
  compatible_shape (Q ⋆ P) P' v cv cv' ->
  compatible_shape P P' v cv cv'.
Proof.
  induction v as [c vs IHvs|ρ fds f|z] using val_ind''.
  - cbn; destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    intros cv cv' HF HG HmF HmG; destruct cv, cv'; auto.
    intros [cvs [Hcvs Hshape]] [cvs_ [cvs' [Hlen [Hcvs_ [Hcvs' Hcompat]]]]].
    assert (#|vs| = #|cvs|) by (rewrite Forall2'_spec in Hshape; now apply Forall2_length in Hshape).
    assert (#|vs| = #|cvs_|) by now apply Forall3_len in Hcompat.
    assert (#|cvs| = #|cvs_|) by lia.
    assert (Heq : vint (rep_boxed t a) :: cvs = vint (rep_boxed t a) :: cvs_).
    { eapply (mapsto_unique' F G); eauto; cbn; try lia. }
    (assert (cvs = cvs_) by congruence); subst cvs_.
    exists cvs, cvs'; split_ands; auto.
    clear - HF HG HmF HmG Hshape IHvs Hcompat.
    revert cvs cvs' Hshape Hcompat; induction vs as [|v' vs IHvs']; auto.
    destruct cvs as [|cv cvs], cvs' as [|cv' cvs']; auto.
    intros [Hcv_shape Hcvs_shape] [Hcv_compat Hcvs_compat]; constructor.
    + eapply IHvs; eauto. now left.
    + eapply IHvs'; eauto. intros; eapply IHvs; eauto. now right.
  - auto.
  - auto.
Qed.

Lemma has_shapes_compatible_shapes_restriction F G m Q P P' vss : forall cvss cvss',
  is_frame F -> is_frame G ->
  m |= F P ->
  m |= G (Q ⋆ P) ->
  has_shapes P vss cvss ->
  compatible_shapes (Q ⋆ P) P' vss cvss cvss' ->
  compatible_shapes P P' vss cvss cvss'.
Proof.
  induction vss as [|vs vss IHvss];
    destruct cvss as [|cvs cvss];
    destruct cvss' as [|cvs' cvss']; try easy.
  intros HF HG HmF HmG Hshapes Hcompat.
  inv Hshapes; inv Hcompat; constructor; eauto.
  generalize dependent cvs; generalize dependent cvs'.
  induction vs as [|v vs IHvs]; destruct cvs as [|cv cvs], cvs' as [|cv' cvs']; auto.
  intros Hshape Hcompat; inv Hshape; inv Hcompat; constructor; auto.
  eapply has_shape_compatible_shape_restriction; try apply HmG; try apply HmF; eauto.
Qed.

(* To hide inequalities from lia *)
Definition neq' {A} (x y : A) := x <> y.
Arguments neq' : simpl never.

Definition max_allocs_representable e :=
  forall C e', e = C |[ e' ]| -> (0 <= max_allocs e' <= O.max_signed)%Z.

Lemma max_allocs_representable_ctx C e :
  max_allocs_representable (C |[ e ]|) ->
  max_allocs_representable e.
Proof.
  intros HCe D e' HDe'; specialize (HCe (comp_ctx_f C D) e').
  apply HCe; rewrite <- app_ctx_f_fuse; congruence.
Qed.

(* TODO hoist *)
Lemma rel_env_gso_r k S x cv ρ env tenv m :
  ~ x \in S ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  ρ ~ₑ{k, S} (env, M.set x cv tenv, m).
Proof.
  intros Hin Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [easy|].
  unfold "!!!"; rewrite !M.gso by auto. now apply Hρ.
Qed.

(* TODO hoist *)
Lemma rel_env_gso_l k S x v ρ env tenv m :
  ~ x \in S ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (env, tenv, m).
Proof.
  intros Hin Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [easy|].
  unfold "!!!"; rewrite !M.gso by auto. now apply Hρ.
Qed.

(* TODO hoist *)
Lemma firstn_prefix {A} n (xs ys : list A) :
  n <= length xs ->
  firstn n (xs ++ ys)%list = firstn n xs.
Proof.
  intros H; rewrite firstn_app.
  rewrite <- Nat.sub_0_le in H.
  rewrite H; cbn; rewrite app_nil_r. auto.
Qed.

(* TODO hoist *)
Lemma has_shape_wf P v cv :
  has_shape P v cv -> val_defined_wf cv.
Proof.
  destruct v; cbn.
  - destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    + intros H; subst; auto with EvalDB.
    + destruct cv; auto with EvalDB.
  - destruct cv; auto with EvalDB.
  - intros H; subst; auto with EvalDB.
Qed.

Lemma compatible_shape_wf1 P P' v cv cv' :
  compatible_shape P P' v cv cv' ->
  val_defined_wf cv.
Proof.
  destruct v; cbn.
  - destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    + intros [-> <-]; auto with EvalDB.
    + destruct cv, cv'; auto with EvalDB.
  - destruct cv; auto with EvalDB.
  - intros [-> <-]; auto with EvalDB.
Qed.

Lemma compatible_shape_wf2 P P' v cv cv' :
  compatible_shape P P' v cv cv' ->
  val_defined_wf cv'.
Proof.
  destruct v; cbn.
  - destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    + intros [-> <-]; auto with EvalDB.
    + destruct cv, cv'; auto with EvalDB.
  - destruct cv, cv'; auto with EvalDB.
  - intros [-> <-]; auto with EvalDB.
Qed.

Lemma Forall3_mp {A B C} (P Q : A -> B -> C -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q x y z) ->
  Forall3 P xs ys zs ->
  Forall3 Q xs ys zs.
Proof.
  intros HPQ; revert ys zs; induction xs as [|x xs IHxs];
    destruct ys as [|y ys], zs as [|z zs]; auto.
  intros [Hxyz Hxyzs]; constructor; auto.
Qed.

Lemma compatible_shape_mp (R : _ -> _ -> _ -> Prop) P P' vss cvss cvss' :
  (forall v cv cv', compatible_shape P P' v cv cv' -> R v cv cv') ->
  compatible_shapes P P' vss cvss cvss' ->
  Forall3 (Forall3 R) vss cvss cvss'.
Proof.
  intros HR Hcompat.
  eapply Forall3_mp; [|apply Hcompat].
  intros vs cvs cvs' Hcompat'; eapply Forall3_mp; [|apply Hcompat']; auto.
Qed.

Lemma Forall3_one {A B C} (P : A -> B -> C -> Prop) (Q : A -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q x) ->
  Forall3 P xs ys zs -> Forall Q xs.
Proof.
  revert ys zs; induction xs as [|x xs IHxs]; destruct ys as [|y ys], zs as [|z zs]; cbn; auto.
  intros HPQ [Hxyz Hxyzs]; constructor; eauto.
Qed.

Lemma Forall3_two {A B C} (P : A -> B -> C -> Prop) (Q : _ -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q y) ->
  Forall3 P xs ys zs -> Forall Q ys.
Proof.
  revert ys zs; induction xs as [|x xs IHxs]; destruct ys as [|y ys], zs as [|z zs]; cbn; auto.
  intros HPQ [Hxyz Hxyzs]; constructor; eauto.
Qed.

Lemma Forall3_three {A B C} (P : A -> B -> C -> Prop) (Q : _ -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q z) ->
  Forall3 P xs ys zs -> Forall Q zs.
Proof.
  revert ys zs; induction xs as [|x xs IHxs]; destruct ys as [|y ys], zs as [|z zs]; cbn; auto.
  intros HPQ [Hxyz Hxyzs]; constructor; eauto.
Qed.

Lemma compatible_shapes_wf1 P P' vss cvss cvss' :
  compatible_shapes P P' vss cvss cvss' ->
  Forall (Forall val_defined_wf) cvss.
Proof.
  intros Hcompat.
  assert (Forall3 (Forall3 (fun _ cv _ => val_defined_wf cv)) vss cvss cvss').
  { eapply compatible_shape_mp; eauto. apply compatible_shape_wf1. }
  eapply Forall3_two; eauto.
  intros; eapply Forall3_two; eauto; cbn; auto.
Qed.

Lemma compatible_shapes_wf2 P P' vss cvss cvss' :
  compatible_shapes P P' vss cvss cvss' ->
  Forall (Forall val_defined_wf) cvss'.
Proof.
  intros Hcompat.
  assert (Forall3 (Forall3 (fun _ _ cv' => val_defined_wf cv')) vss cvss cvss').
  { eapply compatible_shape_mp; eauto. apply compatible_shape_wf2. }
  eapply Forall3_three; eauto.
  intros; eapply Forall3_three; eauto; cbn; eauto.
Qed.

(* TODO hoist *)
Lemma set_lists_None : forall {A} x xs (vs : list A) ρ ρ',
  set_lists xs vs ρ = Some ρ' ->
  ρ' ! x = None ->
  ρ ! x = None.
Proof.
  clear; induction xs as [|x' xs IHxs].
  - destruct vs as [|v vs]; cbn; [inversion 1; subst; auto|inversion 1].
  - destruct vs as [|v vs]; cbn; [inversion 1|].
    intros* H; destruct (set_lists xs vs ρ) as [ρ''|] eqn:Hρ''; inv H.
    destruct (Pos.eq_dec x' x); [subst; now rewrite M.gss|rewrite M.gso by auto].
    intros; eapply IHxs; eauto.
Qed.

(* TODO hoist *)
Lemma Forall_All : forall {A} (P : A -> Prop) xs, Forall P xs <-> All (map P xs).
Proof.
  clear; induction xs as [|x xs IHxs].
  - split; constructor.
  - split; intros H; inv H; cbn; constructor; intuition auto.
Qed.

(* TODO hoist *)
Lemma set_lists_In : forall {A} x xs ys (y : A) ρ ρ',
  List.In x xs ->
  set_lists xs ys ρ = Some ρ' ->
  ρ' ! x = Some y ->
  List.In y ys.
Proof.
  clear; intros* Hx Hset Hget.
  revert ρ' ys Hset Hget; induction xs as [|x' xs IHxs]; [inv Hx|intros ρ'].
  destruct ys as [|y' ys]; cbn; try easy.
  destruct (set_lists xs ys ρ) as [ρ''|] eqn:Hρ''; try easy.
  intros H; inv H.
  destruct (Pos.eq_dec x x') as [|Hne]; [subst x'|].
  - rewrite M.gss. intros H; inv H; now left.
  - rewrite M.gso by auto; intros H; right; eapply IHxs; eauto.
    inv Hx; auto. congruence.
Qed.

(* TODO hoist *)
Lemma set_get_list_same : forall {A} (xs : list positive) (vs : list A) (ρ ρ' : M.t A) (x : positive),
  NoDup xs ->
  get_list xs ρ = Some vs ->
  set_lists xs vs ρ = Some ρ' ->
  List.In x xs ->
  ρ ! x = ρ' ! x.
Proof.
  clear; induction xs as [|x xs IHxs]; [easy|].
  destruct vs as [|v vs]; intros ρ ρ' x' HNoDup Hget Hset; try solve [inv Hset].
  inv HNoDup. cbn in *.
  destruct (ρ ! x) as [vx|] eqn:Hvx; [|easy].
  destruct (get_list xs ρ) as [vxs|] eqn:Hvxs; [inv Hget|easy].
  destruct (set_lists xs vs ρ) as [ρ''|] eqn:Hρ''; [inv Hset|easy].
  destruct (Pos.eq_dec x x'); [subst x'; rewrite M.gss; auto|].
  intros [Hwat|Hin]; [easy|].
  rewrite M.gso by auto.
  now erewrite IHxs by eauto.
Qed.

(* TODO hoist *)
Lemma PS_elements_NoDup : forall s, NoDup (PS.elements s).
Proof. intros; apply NoDupA_NoDup. apply PS.elements_spec2w. Qed.

(* TODO hoist *)
Lemma ρ_inv_set_local : forall x v ρ,
  PS.mem x locals = true ->
  ρ_inv ρ ->
  ρ_inv (M.set x v ρ).
Proof.
  clear - global_local_disjoint; intros x v ρ Hx Hρ x' v' b.
  destruct (Pos.eq_dec x x'); [subst|rewrite M.gso; auto; apply Hρ].
  rewrite M.gss. intros H; inv H.
  intros H.
  assert (PS.mem x' locals = false) by now eapply global_local_disjoint.
  congruence.
Qed.

(* TODO hoist and delete weaker version of this proof *)
Lemma rel_val_compatible_shape' : forall F G k P P' m m' v cv cv',
  is_frame F -> is_frame G ->
  m |= F P ->
  v ~ᵥ{k} (P, cv) ->
  compatible_shape P P' v cv cv' ->
  m' |= G P' ->
  v ~ᵥ{k} (P', cv').
Proof.
  clear; intros* HF HG Hm Hv Hcompat Hm'.
  revert cv cv' Hv Hcompat; induction v as [c vs IHvs|ρ fds f|z] using val_ind'';
   intros cv cv' Hv Hcompat.
  - rewrite !rel_val_eqn in *; simpl in *.
    destruct (get_ctor_rep _ _) as [|rep]; auto.
    destruct rep as [t'|t' a]; auto; [intuition congruence|].
    destruct cv; auto; destruct cv'; auto.
    rename i into o, b0 into b', i0 into o'.
    destruct Hv as [cvs [Hvs Hvs_rel]].
    destruct Hcompat as [cvs_ [cvs' [Hlen [Hcvs_ [Hcvs' Hcompat]]]]].
    assert (Hcvs : vint (rep_boxed t' a) :: cvs_ = vint (rep_boxed t' a) :: cvs).
    { eapply (mapsto_unique F) with (P := P); eauto.
      cbn; do 2 f_equal.
      rewrite Forall2'_spec in Hvs_rel; apply Forall2_length in Hvs_rel.
      cbn in *; lia. }
    inv Hcvs. exists cvs'; split; auto.
    rewrite Forall2'_spec in *.
    clear Hvs Hcvs_ Hlen Hcvs'.
    revert cvs' Hcompat; induction Hvs_rel; intros cvs' Hcompat.
    + destruct cvs'; inv Hcompat; constructor.
    + destruct cvs' as [|cv' cvs']; [inv Hcompat|constructor].
      * rewrite <- rel_val_eqn in *.
        eapply IHvs; eauto; [now left|].
        now cbn in Hcompat.
      * eapply IHHvs_rel; eauto; [|now inv Hcompat].
        intros; eapply IHvs; eauto; now right.
  - cbn in Hcompat. destruct cv; auto; destruct cv'; auto.
    destruct Hcompat as [<- <-]; eapply rel_val_fun_mem; eauto.
  - cbn in Hcompat; destruct Hcompat as [-> <-].
    rewrite !rel_val_eqn in *; apply Hv.
Qed.

(* TODO hoist *)
Lemma rel_val_compatible_shapes : forall F G k P P' m m' vs cvs cvs',
  is_frame F -> is_frame G ->
  m |= F P ->
  Forall2 (fun v cv => v ~ᵥ{k} (P, cv)) vs cvs ->
  Forall3 (compatible_shape P P') vs cvs cvs' ->
  m' |= G P' ->
  Forall2 (fun v cv => v ~ᵥ{k} (P', cv)) vs cvs'.
Proof.
  clear; intros* HF HG Hm Hvs Hcompat Hm'.
  revert cvs' Hcompat; induction Hvs; intros cvs' Hcompat.
  - destruct cvs'; inv Hcompat; constructor.
  - destruct cvs'; inv Hcompat; constructor; auto.
    eapply (rel_val_compatible_shape' F G k P P'); eauto.
Qed.

Print exp_ctx.
Inductive single_ctx_frame : exp_ctx -> Prop :=
| single_constr x c ys : single_ctx_frame (Econstr_c x c ys Hole_c)
| single_proj x t n y : single_ctx_frame (Eproj_c x t n y Hole_c)
| single_prim x p ys : single_ctx_frame (Eprim_c x p ys Hole_c)
| single_case x ces1 c ces2 : single_ctx_frame (Ecase_c x ces1 c Hole_c ces2)
| single_letapp x f t ys : single_ctx_frame (Eletapp_c x f t ys Hole_c).
Hint Constructors single_ctx_frame : CtxDB.

Lemma find_tag_Ecase_c x ces c e n :
  cps_util.find_tag_nth ces c e n ->
  exists ces1 ces2, Ecase x ces = (Ecase_c x ces1 c Hole_c ces2) |[ e ]|.
Proof.
  induction 1.
  - exists [], l. auto.
  - destruct IHfind_tag_nth as [ces1 [ces2 Hces12]].
    exists ((c, e) :: ces1), ces2.
    cbn in *; f_equal; f_equal. congruence.
Qed.

Lemma well_scoped_single_ctx C e :
  single_ctx_frame C ->
  well_scoped (C |[ e ]|) ->
  well_scoped e.
Proof. intros; eapply well_scoped_inv; eauto. Qed.
Hint Resolve well_scoped_single_ctx : CtxDB.

Lemma fenv_respects_tags_single_ctx C e :
  single_ctx_frame C ->
  fenv_respects_tags (C |[ e ]|) ->
  fenv_respects_tags e.
Proof. intros; eapply fenv_respects_tags_ctx; eauto. Qed.
Hint Resolve fenv_respects_tags_single_ctx : CtxDB.

Lemma max_allocs_representable_single_ctx C e :
  single_ctx_frame C ->
  max_allocs_representable (C |[ e ]|) ->
  max_allocs_representable e.
Proof. intros; eapply max_allocs_representable_ctx; eauto. Qed.
Hint Resolve max_allocs_representable_single_ctx : CtxDB.

Lemma max_live_single_ctx C e n :
  single_ctx_frame C ->
  max_live locals (C |[ e ]|) n ->
  max_live locals e n.
Proof. intros; eapply max_live_ctx; eauto. Qed.
Hint Resolve max_live_single_ctx : CtxDB.

Ltac solve_bound_var_locals :=
  match goal with
  | |- bound_var _ \subset FromSet locals => eapply Included_trans; [|eassumption]; normalize_bound_var; sets
  end.

Ltac solve_IH_obligations :=
  try (split_ands; match goal with H : env_inv _ /\ _ /\ _ |- _ =>
                                   destruct H as [Henv_inv [Htenv_inv Hρ_inv]]; auto with InvDB EvalDB end);
  try solve
    [assumption
    |solve_bound_var_locals
    |eauto 2 with CtxDB
    |try normalize_used_vars; eapply Disjoint_Included_r; [|eassumption]; sets
    |apply ρ_inv_set_local; auto;
     rewrite PS.mem_spec;
     eapply FromSet_sound; [apply Same_set_refl|];
     match goal with H : bound_var _ \subset FromSet locals |- _ => apply H end; auto
    |(repeat match goal with H : context [to_nat (plus _ _)] |- _ => rewrite to_nat_add in H end); lia
    |rewrite ?M.gso by easy; auto; now rewrite M.gss].

Instance mset_remove (S : Ensemble positive) x `{H : ToMSet S} : ToMSet (S \\ [set x]).
Proof. exists (PS.remove x mset); rewrite FromSet_remove; destruct H; sets. Qed.

(* TODO hoist *)
Lemma skipn_preserves_eq_len : forall {A B} n (xs : list A) (ys : list B),
  length xs = length ys -> length (skipn n xs) = length (skipn n ys).
Proof.
  clear; induction n as [|n IHn]; [auto|].
  destruct xs as [|x xs], ys as [|y ys]; try easy.
Qed.

(* TODO hoist *)
Lemma used_vars_ces_app ces1 ces2 :
  proto_util.used_vars_ces (ces1 ++ ces2)%list <-->
  proto_util.used_vars_ces ces1 :|: proto_util.used_vars_ces ces2.
Proof.
  induction ces1 as [| [c e] ces IHces].
  - cbn. sets.
  - cbn; rewrite IHces; sets.
Qed.

Lemma max_allocs_ces_eqn (ces : list (ctor_tag * exp)) acc :
  fold_left (fun allocs '(_, e) => Z.max (max_allocs e) allocs) ces acc =
  fold_left Z.max (map (fun '(c, e) => max_allocs e) ces) acc.
Proof.
  revert acc; induction ces as [| [c e] ces IHces].
  - cbn. auto.
  - cbn. intros; rewrite IHces. f_equal; lia.
Qed.

Lemma max_allocs_taken_branch ces1 : forall (c : ctor_tag) e ces2,
  (fold_left (fun allocs '(_, e) => Z.max (max_allocs e) allocs) (ces1 ++ (c, e) :: ces2) 0 >= max_allocs e)%Z.
Proof.
  intros.
  rewrite max_allocs_ces_eqn.
  rewrite fold_symmetric by lia.
  induction ces1 as [| [c' e'] ces1 IHces1]; cbn; lia.
Qed.

(* TODO hoist *)
Lemma nthN_get_ith : forall {A} (vs : list A) n, get_ith vs (Z.of_N n) = nthN vs n.
Proof.
  clear; induction vs as [|v vs IHvs]; [reflexivity|].
  cbn in *; intros n.
  destruct (Coqlib.zeq (Z.of_N n) 0) as [Heq|Hne].
  - destruct n; auto. lia.
  - destruct n; try lia. rewrite <- IHvs. f_equal; lia.
Qed.

(* TODO hoist *)
Lemma rel_env_sepcon' : forall k S ρ P Q env tenv,
  ρ ~ₑ{k, S} (env, tenv, P) ->
  ρ ~ₑ{k, S} (env, tenv, Q ⋆ P).
Proof.
  clear; intros* Hrel x Hx; specialize (Hrel x Hx).
  destruct (ρ!x); [|easy].
  destruct (_!!!_); [|easy].
  eapply rel_val_entail; [intros S' m Hm; rewrite sepcon_comm in Hm; apply Hm|].
  apply rel_val_sepcon; auto.
Qed.

(* TODO hoist *)
Lemma env_list_gso : forall (ys : list ident) (x : ident) (env : Clight.env) (tenv : temp_env) v,
           ~ List.In x ys -> (env, PTree.set x v tenv) !!!! ys = (env, tenv) !!!! ys.
Proof.
  clear; induction ys as [|y ys IHys]; [reflexivity|].
  intros* Hin; cbn in *.
  rewrite env_gso by (intros Heq; subst; contradiction Hin; now left).
  rewrite IHys by auto.
  auto.
Qed.

(* TODO hoist *)
Lemma has_shape_sepcon : forall v cv Q P,
  has_shape P v cv ->
  has_shape (Q ⋆ P) v cv.
Proof.
  clear; induction v as [c vs IHvs|ρ fds f|z] using val_ind''.
  - intros* H; cbn in *; destruct (get_ctor_rep _ _) as [| [t|t a]]; auto.
    destruct cv; auto.
    destruct H as [cvs [HP Hvs]].
    exists cvs; split.
    + eapply entail_trans.
      { intros S m Hm; rewrite sepcon_comm in Hm; apply Hm. }
      eapply entail_trans.
      { apply (frame_entail (fun H => H ⋆ Q)); auto with FrameDB; eauto. }
      intros S m Hm; rewrite sepcon_assoc in Hm.
      eapply frame_entail; auto with FrameDB; eauto; apply entail_True.
    + rewrite Forall2'_spec in *.
      clear HP. revert cvs Hvs; induction vs as [|v vs IHvs'].
      * destruct cvs as [|cv cvs]; auto. inversion 1.
      * destruct cvs as [|cv cvs]; auto. inversion 1. 
        intros Hforall; inv Hforall; constructor.
        -- apply IHvs; eauto; now left.
        -- apply IHvs'; auto. intros; apply IHvs; auto. now right.
  - easy.
  - easy.
Qed.

(* TODO hoist *)
Lemma has_shapes_sepcon : forall vss cvss Q P,
  has_shapes P vss cvss ->
  has_shapes (Q ⋆ P) vss cvss.
Proof.
  intros* H; unfold has_shapes in *.
  eapply Forall2_monotonic; [|apply H].
  intros* H'.
  eapply Forall2_monotonic; [|apply H'].
  intros; apply has_shape_sepcon; auto.
Qed.

Hint Extern 0 ((M.set ?x _ _) ! ?x = Some _) => rewrite M.gss; reflexivity : EvalDB.
Hint Extern 0 ((PTree.set ?x _ _) ! ?x = Some _) => rewrite M.gss; reflexivity : EvalDB.
Lemma translate_body_stm : forall e k,
  Disjoint _ (FromList [gc_id; tinfo_id; alloc_id; limit_id; frame_id; roots_id; ret_id; case_id; roots_temp_id]) (used_vars e) ->
  well_scoped e ->
  fenv_respects_tags e ->
  max_allocs_representable e ->
  (** if running e in environment ρ yields a value v in j <= k cost, *)
  forall ρ v cin cout vss,
  to_nat cin <= k ->
  (ρ, e, cin) ⇓cps (v, cout) ->
  (** and tenv+env contains bindings for alloc, limit, frame, roots, .. *)
  forall env tenv m,
  forall nursery_b tinfo_b tinfo_o alloc_o limit_o frame_b roots_b n_roots values,
  tenv ! tinfo_id = Some (Vptr tinfo_b tinfo_o) ->
  tenv ! alloc_id = Some (Vptr nursery_b alloc_o) ->
  tenv ! limit_id = Some (Vptr nursery_b limit_o) ->
  tenv ! roots_temp_id = Some (Vptr roots_b O.zero) ->
  env ! frame_id = Some (frame_b, stack_frame) ->
  max_live locals e (Z.to_nat n_roots) ->
  (max_allocs e * word_size <= O.unsigned limit_o - O.unsigned alloc_o)%Z ->
  (** and environments agree on the free variables of e
      and satisfy their respective invariants, *)
  bound_var e \subset FromSet locals ->
  env_inv env /\ tenv_inv tenv /\ ρ_inv ρ ->
  ρ ~ₑ{k, occurs_free e} (env, tenv, values) ->
  (** and m is a valid CertiCoq memory with shadow stack cvss related to vss, *)
  forall ss cvss outliers frame,
  val_defined_wf (stack_top ss) ->
  let frame :=
    (∃ next_o, (frame_b, 0%Z) ↦_{Freeable}
      [Vptr roots_b next_o; Vptr roots_b O.zero; stack_top ss]) ⋆
    (∃ cvs, (roots_b, 0%Z) ↦_{Freeable} cvs WITH #|cvs| = n_roots) ⋆
    frame
  in
  m |= ∃ args nalloc talloc_o tlimit_o,
       valid_mem nursery_b talloc_o tlimit_o
                 alloc_o limit_o tinfo_b tinfo_o
                 args ss cvss nalloc values
                 frame ->
  values |-- outliers ⋆ Pure True ->
  has_shapes values vss cvss ->
  match translate_body cenv fenv locals nenv e with
  | Ret (stmt, _, _) =>
    (** then running stmt yields a result (m', cv), *)
    exists tenv' m' cv,
    (env, tenv, m, stmt) ⇓ (tenv', m', cv) /\
    (** cv is related to v at level k-j, *)
    exists cvss' values',
    v ~ᵥ{k - to_nat cin} (values', cv) /\
    (** and m' is still a valid memory with shadow stack cvss' compatible with cvss *)
    m' |= ∃ nursery_b alloc_o limit_o args nalloc,
          valid_mem nursery_b alloc_o limit_o alloc_o limit_o tinfo_b tinfo_o
                    args ss cvss' nalloc values' frame /\
    values' |-- outliers ⋆ Pure True /\
    compatible_shapes values values' vss cvss cvss'
  | _ => True
  end.
Proof.
  intros e k Hdis; rewrite !FromList_cons in Hdis; revert e k Hdis.
  induction e using exp_ind''; lazy zeta;
    intros k Hdis Hscope Hftags Hmax_allocs*Hk Hbstep*Htinfo Halloc Hlimit Hroots
           Hframe Hlive Hallocs Hbv Henvs Henv_rel*Htop_wf Hm Hvalues Hshapes.
  - (** let x = Con c ys in e *)
    simpl. bind_step rep Hrep; destruct rep as [t|t a]; destruct ys as [|y ys]; try exact I; rewrite bind_ret.
    + (** Unboxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      fwd Cred_set; eauto with EvalDB.
      rewrite <- postcond'_spec.
      inv Hbstep; match goal with H : bstep _ _ _ _ _ _ |- _ => inv H end.
      normalize_used_vars.
      vars_neq Hdis x tinfo_id.
      vars_neq Hdis x alloc_id.
      vars_neq Hdis x limit_id.
      vars_neq Hdis x roots_temp_id.
      vars_neq Hdis x case_id.
      edestruct (IHe k) as [tenv_end [m_end [cv_end [Hend [cvss_end
       [values_end [Hrel_end [Hm_end [Hvalues_end Hcompat_end]]]]]]]]].
      6:{ eassumption. }
      17:{ eassumption. }
      19:{ exists tenv_end, m_end, cv_end; split; try eassumption.
           exists cvss_end, values_end; split_ands; eauto.
           rewrite to_nat_add; eapply rel_val_antimon; try eassumption. lia. }
      all: try solve_IH_obligations.
      apply rel_env_gss.
      * rewrite rel_val_eqn. cbn.
         rewrite Hrep. cbn in *. inv H8. split; reflexivity.
      * eapply rel_env_antimon_S; eauto. normalize_occurs_free; sets.
    + (** Boxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      normalize_used_vars. rewrite !FromList_cons in Hdis.
      repeat fwd Cred_seq_assoc.
      fwd Cred_set; [eauto with EvalDB|].
      vars_neq Hdis x alloc_id.
      fwd Cred_set; [eauto with EvalDB|].
      (** Grab some bytes from the nursery *)
      apply (mem_nursery_alloc (#|y::ys| + 1)%Z) in Hm.
      2:{ clear - Hallocs; cbn in *; superlia. }
      (** Store the tag *)
      unfold "|=" in *.
      match type of Hm with
      | _ |=_{_} _ ⋆ ?P =>
        destruct_ex_ctx (fun H => H ⋆ P) vs Hm;
        destruct_ex_ctx (fun H => H ⋆ P) Hvs Hm;
        destruct vs as [|tag_slot args_slots]; [cbn in Hvs; lia|];
        eapply (fwd_store (fun H => H ⋆ P)) with (ty := value)
      end.
      4:{ eauto with EvalDB. }
      all: eauto with FrameDB EvalDB; try lia; auto with mem.
      intros m' Hstore Hm'.
      replace (1 + -1)%Z with 0%Z in * by lia.
      rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.mul_1_l in *.
      simpl set_ith in Hm'; unfold "|=" in *.
      (** Store the arguments *)
      vars_neq Hdis x frame_id.
      vars_neq Hdis x roots_id.
      match type of Hm' with
      | _ |=_{_} _ ⋆ ?P =>
        eapply (fwd_stores (fun H => H ⋆ P)) with (ty := value); try eassumption;
        eauto with FrameDB; auto with mem
      end.
      { replace (O.unsigned alloc_o + word_size)%Z with (O.unsigned alloc_o + 1*word_size)%Z by lia.
        eauto with EvalDB. }
      { cbn in Hvs; cbn; lia. }
      { clear - Hdis; intros [Hin|Hin].
        - subst case_id; dis_bad Hdis y.
        - dis_bad Hdis case_id. }
      { clear - Hdis; intros [Hin|Hin].
        - subst frame_id; dis_bad Hdis y.
        - dis_bad Hdis frame_id. }
      { clear - Hdis; intros [Hin|Hin].
        - subst roots_id; dis_bad Hdis y.
        - dis_bad Hdis roots_id. }
      { normalize_bound_var_in_ctx.
        decompose [and] Henvs; split_ands; eauto with EvalDB InvDB Ensembles_DB.
        apply tenv_inv_set_alloc; auto with EvalDB.
        apply tenv_inv_set_x; auto with EvalDB.
        vars_neq Hdis x case_id. auto. }
      { eapply env_rel_all_some; eauto.
        normalize_occurs_free; rewrite !FromList_cons; sets. }
      { do 2 apply env_rel_all_some_tenv_set.
        eapply env_rel_all_some_tenv; eauto.
        normalize_occurs_free; rewrite !FromList_cons; sets. }
      intros m'' cv_skipn_ys Hcv_skipn_ys Hm''.
      rewrite overwrite_sublist_spec in Hm''.
      2:{ apply get_env_list_len in Hcv_skipn_ys.
          change cps.var with ident in *.
          clear - Hvs Hcv_skipn_ys.
          cbn in *; lia. }
      rewrite skipn_all2 in Hm''.
      2:{ apply get_env_list_len in Hcv_skipn_ys.
          clear - Hvs Hcv_skipn_ys; change cps.var with ident in *; cbn in *; lia. }
      rewrite app_nil_r in Hm''.
      simpl firstn in Hm''; simpl "++"%list in Hm''.
      (** Massage m'' until ready for IH *)
      unfold "|=" in *.
      match type of Hm'' with
      | _ |=_{_} ?P ⋆ _ =>
        destruct_ex_ctx (fun H => P ⋆ H) args Hm'';
        destruct_ex_ctx (fun H => P ⋆ H) nalloc Hm'';
        destruct_ex_ctx (fun H => P ⋆ H) talloc_o Hm'';
        destruct_ex_ctx (fun H => P ⋆ H) tlimit_o Hm''
      end.
      unfold valid_mem in Hm''. rewrite sepcon_comm in Hm''.
      match type of Hm'' with
      | _ |=_{_} (?P ⋆ ?Q ⋆ ?R ⋆ _ ⋆ ?S) ⋆ ?new_segment =>
        rewrite (frame_stuff_hole (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S)) in Hm''; auto with FrameDB;
        rewrite_equiv_in (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S) sepcon_comm Hm'';
        remember (values ⋆ new_segment) as values' eqn:Hvalues'
      end.
      apply valid_mem_fold in Hm''.
      (** Continue with e via IH *)
      vars_neq Hdis x tinfo_id.
      vars_neq Hdis x limit_id.
      vars_neq Hdis x roots_temp_id.
      vars_neq Hdis x case_id.
      tempvars_neq alloc_id limit_id.
      tempvars_neq tinfo_id alloc_id.
      tempvars_neq tinfo_id limit_id.
      tempvars_neq alloc_id roots_temp_id.
      tempvars_neq limit_id roots_temp_id.
      inv Hbstep; match goal with H : bstep _ _ _ _ _ _ |- _ => inv H end.
      edestruct (IHe k) as [tenv_end [m_end [cv_end [Hend [cvss_end
       [values_end [Hrel_end [Hm_end [Hvalues_end Hcompat_end]]]]]]]]].
      6:{ eassumption. }
      17:{ exists_ex args; exists_ex nalloc; exists_ex talloc_o; exists_ex tlimit_o.
           apply Hm''. }
      19:{ rewrite <- postcond'_spec.
           exists tenv_end, m_end, cv_end; split; try eassumption.
           exists cvss_end, values_end; split_ands; eauto.
           - rewrite to_nat_add; eapply rel_val_antimon; try eassumption.
             change (?x <> ?y) with (neq' x y) in *.
             lia.
           - unfold valid_mem in Hm''.
             match type of Hm'' with
             | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ (?S ⋆ _) ⋆ ?T =>
               eapply (has_shapes_compatible_shapes_restriction
                      (fun H => P ⋆ Q ⋆ R ⋆ (S ⋆ H) ⋆ T)
                      (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ T)); auto with FrameDB; eauto
             end. }
      all: try solve_IH_obligations.
      * rewrite O.unsigned_repr.
        2:{ change (?x <> ?y) with (neq' x y) in *.
            cbn in Hm''; decompose [ex and] Hm''. cbn in *; superlia. }
        cbn in *; superlia.
      * eapply rel_env_gso_r.
        { intros Hwat; destruct Hdis as [Hdis]; contradiction (Hdis alloc_id).
          constructor; auto 15. right; now right. }
        apply rel_env_gss.
        2:{ 
            apply rel_env_sepcon'.
            eapply rel_env_antimon_S; [|apply Henv_rel].
            normalize_occurs_free; sets. }
        rewrite rel_val_eqn; cbn. rewrite Hrep.
        edestruct (rel_val_xs_related (y :: ys)) as [vys [cvys [Hvys [Hcvys Hrelys]]]]; [|apply Henv_rel|].
        { normalize_occurs_free; sets. }
        assert (~ List.In alloc_id (y :: ys)).
        { intros Hin; destruct Hdis as [Hdis]; contradiction (Hdis alloc_id).
          constructor; auto 15. left; right. inv Hin; auto. }
        rewrite env_list_gso in Hcv_skipn_ys by auto.
        rewrite env_list_gso in Hcv_skipn_ys.
        2:{ intros Hin; destruct Hscope as [Huniq [Hdisj]].
            contradiction (Hdisj x); constructor; auto. }
        rewrite Hcv_skipn_ys in Hcvys. inv Hcvys.
        exists cvys; split_ands; auto.
        -- change (?x <> ?y) with (neq' x y) in *. 
           rewrite O.unsigned_repr.
           2:{ cbn in Hm''; decompose [ex and] Hm''; cbn in *; superlia. }
           replace (O.unsigned alloc_o + word_size - word_size)%Z with (O.unsigned alloc_o) by lia.
           eapply entail_trans.
           { intros Sarb marb Hmarb.
             eapply (mapsto_perm_order (fun H => H ⋆ values)) with (p' := Readable) in Hmarb;
               auto with FrameDB.
             apply Hmarb. auto with mem. }
           apply frame_entail; auto with FrameDB. apply entail_True.
        -- rewrite Forall2'_spec.
           rewrite H20 in Hvys; inv Hvys.
           eapply Forall2_monotonic; eauto.
           intros; rewrite <- rel_val_eqn.
           eapply rel_val_entail; [intros Sarb marb Hmarb; rewrite sepcon_comm in Hmarb; apply Hmarb|].
           apply rel_val_sepcon. auto.
      * eapply entail_trans.
        { eapply frame_entail; [auto with FrameDB|..]; eassumption. }
        intros Sa ma Hma.
        rewrite sepcon_comm in Hma.
        rewrite sepcon_assoc in Hma.
        eapply frame_entail; eauto with FrameDB.
        apply entail_True.
      * now apply has_shapes_sepcon.
  - (** case x of { ces } *)
    inv Hbstep. rename cin0 into cin, cout0 into cout. inv H.
    rename e into e_taken, t into c, vl into vs, H2 into Hx, H3 into HcaseConsistent, H5 into Hfind_tag, H9 into Hbstep.
    edestruct (rel_val_x_related x) as [vx [cvx [Hρx [Henvx Hrelx]]]]; try eassumption; sets.
    simpl. bind_step ces' Hces.
    destruct ces' as [[[boxed_cases unboxed_cases] fvs_ces] n_ces].
    rewrite proto_util.used_vars_Ecase in Hdis.
    vars_neq Hdis x case_id.
    vars_neq Hdis x frame_id.
    vars_neq Hdis x roots_id.
    tempvars_neq case_id tinfo_id.
    tempvars_neq case_id alloc_id.
    tempvars_neq case_id limit_id.
    tempvars_neq case_id roots_temp_id.
    edestruct (rel_val_x_related x) as [vx' [cvx' [Hvx' [Hcvx Hrel_cvx]]]]; try eassumption; sets.
    rewrite Hx in Hvx'; inv Hvx'.
    eapply fwd_case; try eassumption.
    intros stm_taken fvs_taken n_taken cv_isptr Hcv_isptr He_taken.
    (** Continue with taken branch via IH *)
    edestruct find_tag_Ecase_c with (x := x) as [ces1 [ces2 Hces12]]; eauto.
    rewrite Hces12 in *.
    specialize (IHces c e_taken) with (k := k); rewrite He_taken in IHces.
    edestruct IHces as [tenv_end [m_end [cv_end [Hend [cvss_end
     [values_end [Hrel_end [Hm_end [Hvalues_end Hcompat_end]]]]]]]]].
    7:{ eassumption. }
    18:{ eassumption. }
    20:{ exists tenv_end, m_end, cv_end; split; try eassumption.
         exists cvss_end, values_end; split_ands; eauto.
         rewrite to_nat_add; eapply rel_val_antimon; try eassumption.
         lia. }
    all: try solve_IH_obligations.
    { eapply cps_util.find_tag_nth_In_patterns; eauto. }
    + eapply Disjoint_Included_r; eauto.
      inv Hces12. rewrite used_vars_ces_app.
      cbn. sets.
    + cbn in Hallocs.
      pose proof max_allocs_taken_branch ces1 c e_taken ces2 as Hallocs_taken.
      superlia.
    + cbn in *; normalize_bound_var_in_ctx. eapply Included_trans; eauto.
      normalize_bound_var; sets.
    + destruct Hcv_isptr; subst cv_isptr; eauto with InvDB.
    + apply rel_env_gso_r.
      { intros Hwat; destruct Hdis as [Hdis]; contradiction (Hdis case_id).
        constructor; auto 10. inv Hces12. rewrite used_vars_ces_app.
        right; right. cbn. left. now right. }
      eapply rel_env_antimon_S; eauto.
      cbn; normalize_occurs_free. sets.
  - (** let x = Proj c n y in e *)
    simpl. bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
    inv Hbstep. rename cin0 into cin, cout0 into cout; inv H.
    rename t into c, v0 into v_n, H9 into Hy, H10 into Hv_n, H11 into Hbstep.
    edestruct (rel_val_x_related y) as [vy [cvy [Hvy [Hcvy Hrely]]]]; try eassumption; sets.
    rewrite Hy in Hvy; inv Hvy.
    rewrite rel_val_eqn in Hrely; cbn in Hrely.
    destruct (get_ctor_rep _ _) as [| [t|t a]]; [destruct Hrely| |].
    { destruct Hrely as [-> ->]. inv Hv_n. }
    destruct cvy; try solve [destruct Hrely].
    rename b into cvy_b, i into cvy_o.
    destruct Hrely as [cvs [Hcvs Hcvs_rel]].
    normalize_used_vars.
    vars_neq Hdis y case_id.
    vars_neq Hdis y frame_id.
    vars_neq Hdis y roots_id.
    edestruct eval_load with (i := Z.of_N n) as [vx [Hvx Heval_vx]]; try eassumption.
    2:{ eapply eval_make_var; eauto. easy. }
    { apply typeof_make_var. }
    { apply nthN_range in Hv_n.
      rewrite Forall2'_spec in Hcvs_rel.
      apply Forall2_length in Hcvs_rel.
      superlia. }
    fwd Cred_set; [eassumption|].
    rewrite <- postcond'_spec.
    vars_neq Hdis x tinfo_id.
    vars_neq Hdis x alloc_id.
    vars_neq Hdis x limit_id.
    vars_neq Hdis x case_id.
    vars_neq Hdis x roots_temp_id.
    edestruct (IHe k) as [tenv_end [m_end [cv_end [Hend [cvss_end
     [values_end [Hrel_end [Hm_end [Hvalues_end Hcompat_end]]]]]]]]].
    6:{ eassumption. }
    17:{ eassumption. }
    19:{ exists tenv_end, m_end, cv_end; split; try eassumption.
         exists cvss_end, values_end; split_ands; eauto.
         rewrite to_nat_add; eapply rel_val_antimon; try eassumption.
         change (?x <> ?y) with (neq' x y) in *.
         lia. }
    all: try solve_IH_obligations.
    + rewrite Forall2'_spec in Hcvs_rel.
      eapply Forall2_nthN in Hcvs_rel; eauto.
      destruct Hcvs_rel as [cv [Hcv Hrel]].
      rewrite <- nthN_get_ith in Hcv.
      cbn in Hvx. destruct (Coqlib.zeq (Z.of_N n + 1))%Z as [|Hne]; [lia|].
      replace (Z.pred (Z.of_N n + 1))%Z with (Z.of_N n) in Hvx by lia.
      rewrite Hvx in Hcv; inv Hcv.
      rewrite <- rel_val_eqn in Hrel.
      apply tenv_inv_set_x; auto with EvalDB.
      eapply rel_val_wf; eauto.
    + rewrite Forall2'_spec in Hcvs_rel.
      eapply Forall2_nthN in Hcvs_rel; eauto.
      destruct Hcvs_rel as [cv [Hcv Hrel]].
      rewrite <- nthN_get_ith in Hcv.
      cbn in Hvx. destruct (Coqlib.zeq (Z.of_N n + 1))%Z as [|Hne]; [lia|].
      replace (Z.pred (Z.of_N n + 1))%Z with (Z.of_N n) in Hvx by lia.
      rewrite Hvx in Hcv; inv Hcv.
      rewrite <- rel_val_eqn in Hrel.
      apply rel_env_gss; auto.
      eapply rel_env_antimon_S; eauto.
      normalize_occurs_free; sets.
  - (** let x = f ft ys in e *)
    simpl. bind_step e' He; destruct e' as [[stm_e live_after_call] n_e].
    pose proof translate_body_fvs locals nenv e as Hlive_after_call.
    rewrite He in Hlive_after_call.
    unfold make_fun_call.
    destruct (fenv ! f) as [[arity inds] |] eqn:Hf_cc; [|exact I].
    destruct (negb (_ =? _)%nat) eqn:Harity_match; [exact I|].
    rewrite bind_ret.
    rewrite used_vars_Eletapp in *. rewrite ?FromList_cons in Hdis.
    repeat fwd Cred_seq_assoc.
    (** Store variables live after call \ {x} in roots array *)
    unfold "|=" in *.
    destruct_ex args Hm.
    destruct_ex nalloc Hm.
    destruct_ex talloc_o Hm.
    destruct_ex tlimit_o Hm.
    apply valid_mem_sepcon_frame in Hm.
    rewrite (frame_cong' (fun H => _ ⋆ H)) in Hm; auto with FrameDB; [|intros; apply valid_mem_sepcon_frame].
    match type of Hm with
    | _ |=_{_} _ ⋆ ?P => destruct_ex_ctx (fun H => H ⋆ P) next_o Hm
    end.
    match type of Hm with
    | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
      destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) cvs Hm;
      destruct_ex_ctx (fun H => P ⋆ H ⋆ Q) Hcvs Hm
    end.
    pose (live_no_x_list := PS.elements (PS.remove x live_after_call)).
    assert (Hlive_no_x_list : FromList live_no_x_list
         <--> occurs_free e :&: FromSet locals \\ [set x]).
    { subst live_no_x_list.
      rewrite <- FromSet_elements.
      rewrite FromSet_remove.
      rewrite Hlive_after_call.
      sets. }
    assert (Hlive_after_call_len : PS.cardinal live_after_call <= PS.cardinal (PS.inter (exp_fv e) locals)).
    { assert (Hvs : occurs_free e :&: FromSet locals <--> FromSet live_after_call). { symmetry; auto. }
      assert (Hfvs_mset : {H : ToMSet (occurs_free e :&: FromSet locals)
                          | @mset _ H = live_after_call}).
      { exists (Build_ToMSet _ _ Hvs). reflexivity. }
      destruct Hfvs_mset as [Hmset <-].
      assert (Hrhs : occurs_free e :&: FromSet locals <--> FromSet (PS.inter (exp_fv e) locals)).
      { rewrite FromSet_intersection. rewrite exp_fv_correct. sets. }
      assert (Hrhs_mset : {H : ToMSet (occurs_free e :&: FromSet locals) | @mset _ H = PS.inter (exp_fv e) locals}).
      { exists (Build_ToMSet _ _ Hrhs). reflexivity. }
      destruct Hrhs_mset as [Hmset' <-].
      apply PS_elements_subset. sets. }
    assert (Hlive_no_x_len : length live_no_x_list <= PS.cardinal (PS.inter (exp_fv e) locals)).
    { subst live_no_x_list.
      rewrite <- PS.cardinal_spec.
      rewrite exp_fv_correct in Hlive_no_x_list.
      rewrite <- FromSet_intersection in Hlive_no_x_list.
      assert (Hvs : occurs_free e :&: FromSet locals \\ [set x] <--> FromSet (PS.remove x live_after_call)).
      { rewrite FromSet_remove. rewrite Hlive_after_call. sets. }
      assert (Hfvs_mset : {H : ToMSet (occurs_free e :&: FromSet locals \\ [set x])
                          | @mset _ H = PS.remove x live_after_call}).
      { exists (Build_ToMSet _ _ Hvs). reflexivity. }
      destruct Hfvs_mset as [Hmset <-].
      assert (Hrhs : occurs_free e :&: FromSet locals <--> FromSet (PS.inter (exp_fv e) locals)).
      { rewrite FromSet_intersection. rewrite exp_fv_correct. sets. }
      assert (Hrhs_mset : {H : ToMSet (occurs_free e :&: FromSet locals) | @mset _ H = PS.inter (exp_fv e) locals}).
      { exists (Build_ToMSet _ _ Hrhs). reflexivity. }
      destruct Hrhs_mset as [Hmset' <-].
      apply PS_elements_subset. sets. }
    assert (Hle_cvs : (#|PS.elements (PS.remove x live_after_call)| <= #|cvs|)%Z).
    { rewrite Hcvs. unfold max_live in Hlive.
      specialize (Hlive Hole_c _ _ _ _ _ eq_refl).
      subst live_no_x_list. lia. }
    match type of Hm with
    | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
      eapply (fwd_stores' (fun H => P ⋆ H ⋆ Q)) with (ty := value) (vs := cvs); try eassumption;
      auto with FrameDB; eauto with EvalDB; auto with mem
    end.
    { unfold PS.elt, cps.var, M.elt in *. lia. }
    { change (~ List.In ?x ?xs) with (~ x \in FromList xs).
      rewrite <- FromSet_elements, FromSet_remove.
      intros Hcase; inv Hcase.
      rewrite Hlive_after_call in H. inv H.
      destruct Hdis as [Hdis]; contradiction (Hdis case_id); constructor; auto 10.
      now do 3 right. }
    { change (~ List.In ?x ?xs) with (~ x \in FromList xs).
      rewrite <- FromSet_elements, FromSet_remove.
      intros Hcase; inv Hcase.
      rewrite Hlive_after_call in H. inv H.
      destruct Hdis as [Hdis]; contradiction (Hdis frame_id); constructor; auto 10.
      now do 3 right. }
    { change (~ List.In ?x ?xs) with (~ x \in FromList xs).
      rewrite <- FromSet_elements, FromSet_remove.
      intros Hcase; inv Hcase.
      rewrite Hlive_after_call in H. inv H.
      destruct Hdis as [Hdis]; contradiction (Hdis roots_id); constructor; auto 10.
      now do 3 right. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      rewrite <- FromSet_elements, FromSet_remove in Hx'.
      inv Hx'. rewrite Hlive_after_call in H; inv H.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      { normalize_occurs_free; right. constructor; auto. }
      easy. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      rewrite <- FromSet_elements, FromSet_remove in Hx'.
      inv Hx'. rewrite Hlive_after_call in H; inv H.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      { normalize_occurs_free; right. constructor; auto. }
      easy. }
    intros m_live_no_x cvs_live_no_x Hcvs_live_no_x Hm_live_no_x.
    rewrite overwrite_sublist_spec in Hm_live_no_x.
    2:{ apply get_env_list_len in Hcvs_live_no_x.
        clear - Hle_cvs Hcvs_live_no_x. superlia. }
    simpl firstn in Hm_live_no_x; simpl app in Hm_live_no_x.
    (** Set frame.next *)
    match type of Hm_live_no_x with
    |  _ |= _ ⋆ ?P =>
      eapply (fwd_frame_next (fun H => H ⋆ P)) with (ty := value); eauto with EvalDB FrameDB
    end.
    intros m_frame_no_x Hm_frame_no_x.
    (** Push frame onto shadow stack *)
    unfold valid_mem in Hm_frame_no_x; unfold "|=" in *.
    match type of Hm_frame_no_x with
    | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
      eapply (fwd_tinfo_fp (fun H => P ⋆ Q ⋆ H ⋆ R))
        with (ty := stack_frame) (v := Vptr frame_b _); eauto with EvalDB FrameDB
    end.
    intros m_frame_pushed Hm_frame_pushed; unfold "|=" in *.
    (** Some useful facts for later *)
    assert (Hcase_notin_ys : ~ List.In case_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis case_id).
      constructor; auto 10. }
    assert (Hframe_notin_ys : ~ List.In frame_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis frame_id).
      constructor; auto 10. }
    assert (Hroots_notin_ys : ~ List.In roots_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis roots_id).
      constructor; auto 10. }
    (** Store arguments n+1, .. in the args array at indices inds *)
    repeat fwd Cred_seq_assoc.
    rewrite skipn_combine.
    match type of Hm_frame_pushed with
    | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
      eapply (fwd_args_stores (fun H => P ⋆ Q ⋆ H ⋆ R)); eauto with EvalDB FrameDB
    end.
    { (* #|ys| = #|inds| *)
      do 2 f_equal; apply skipn_preserves_eq_len.
      specialize (fenv_cc_inv _ _ _ Hf_cc).
      rewrite Bool.negb_false_iff in Harity_match.
      apply beq_nat_true in Harity_match.
      lia. }
    { specialize (fenv_cc_inv _ _ _ Hf_cc); easy. }
    { specialize (fenv_cc_inv _ _ _ Hf_cc).
      eapply Forall_impl; try apply fenv_cc_inv; cbn.
      match type of Hm_frame_pushed with
      | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
        destruct_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R) args' Hm_frame_pushed;
        destruct_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R) Hlen_args Hm_frame_pushed
      end.
      lia. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      apply FromList_skipn in Hx'.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      { normalize_occurs_free; left; right. auto. }
      easy. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      apply FromList_skipn in Hx'.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      { normalize_occurs_free; left; right. auto. }
      intros Hwat. unfold temp_env in *. congruence. }
    intros m_args_stored cv_skipn_ys Hcv_skipn_ys Hm_args_stored; unfold "|=" in *.
    (** Update tinfo->alloc and tinfo->limit *)
    match type of Hm_args_stored with
    | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
      eapply (fwd_tinfo_alloc (fun H => P ⋆ Q ⋆ H ⋆ R)) with (ty := value);
      eauto with EvalDB FrameDB
    end.
    intros m_alloc_stored Hm_alloc_stored; unfold "|=" in *.
    match type of Hm_alloc_stored with
    | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
      eapply (fwd_tinfo_limit (fun H => P ⋆ Q ⋆ H ⋆ R)) with (ty := value);
      eauto with EvalDB FrameDB
    end.
    intros m_limit_stored Hm_limit_stored; unfold "|=" in *.
    (** The local frame struct is now a part of the shadow stack *)
    rewrite <- sepcon_assoc in Hm_limit_stored.
    match type of Hm_limit_stored with
    | _ |=_{_} ((?f_b, _) ↦_{_} [Vptr _ (O.repr (_ + ?len*_)); Vptr ?r_b ?r_o; ?next] ⋆
                (_, _) ↦_{_} (?cvs ++ ?suffix)) ⋆
               ?P =>
      (assert (Hlen_equal : len = #|cvs|) by now apply get_env_list_len in Hcvs_live_no_x);
      pose (frame_no_x := mk_ss_frame (f_b, O.zero) (r_b, r_o) #|cvs++suffix|);
      apply (frame_entail (fun H => H ⋆ P))
        with (Q := shadow_stack_frame frame_no_x cvs next)
        in Hm_limit_stored;
      auto with FrameDB
    end.
    2:{ cbn; intros S m_arbitrary.
      match goal with
      | |- _ |=_{_} _ ⋆ (_ ↦_{_} _ ++ ?suffix) -> _ |=_{_} ?P ⋆ _ =>
        intros Hm_arbitrary;
        exists_ex_ctx (fun H => P ⋆ H) suffix;
        split_ex_ctx (fun H => P ⋆ H); [reflexivity|]
      end.
      cbn in Hlen_equal; rewrite Hlen_equal in Hm_arbitrary; assumption. }
    rewrite sepcon_comm in Hm_limit_stored.
    match type of Hm_limit_stored with
    | _ |=_{_} (?P ⋆ ?Q ⋆ shadow_stack ?ss ?cvss ⋆ ?R) ⋆ shadow_stack_frame ?s ?cvs _ =>
      rewrite (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ R)) in Hm_limit_stored; auto with FrameDB;
      rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ R) sepcon_comm Hm_limit_stored;
      change (shadow_stack_frame _ _ _ ⋆ shadow_stack _ _) with (shadow_stack (s :: ss) (cvs :: cvss)) in *
    end.
    change (Vptr frame_b Ptrofs.zero) with (stack_top (frame_no_x :: ss)) in *.
    apply valid_mem_fold in Hm_limit_stored.
    (** The functions are related *)
    inv Hbstep. rename cin0 into cin, cout0 into cout; inv H.
    rename v0 into vx, cin1 into cin_call, cout1 into cout_call,
    cin2 into cin_cont, cout2 into cout_cont, fl into fds, rho' into ρ_f, rho'' into ρ_f_xvs,
    H5 into Hρ_f, H7 into Hρ_get_ys, H11 into Hfind_def, H12 into Hρ_f_xvs,
    H13 into Hbstep_call, H14 into Hbstep_cont.
    edestruct rel_val_x_related with (x := f) as [v_f [cv_f [Hv_f [Hcv_f Hrel_f]]]]; try eassumption.
    { normalize_occurs_free; sets. }
    (assert (v_f = Vfun ρ_f fds f') by congruence); subst v_f; clear Hρ_f.
    rewrite rel_val_eqn in Hrel_f; cbn [rel_val_aux] in Hrel_f.
    destruct cv_f; try solve [destruct Hrel_f]; rename b into f_b, i into f_o.
    rewrite Hfind_def in Hrel_f.
    (* destruct (M.bempty ρ_f) eqn:Hρ_f_empty; [|destruct Hrel_f]. *)
    pose proof Hf_cc as Hf_cc_tag.
    erewrite (Hftags Hole_c) in Hf_cc_tag; [|right; do 3 eexists; reflexivity].
    rewrite Hf_cc_tag in Hrel_f.
    destruct (Genv.find_funct _ _) as [fn|] eqn:Hfind_funct; [|destruct Hrel_f].
    (** The arguments are related *)
    edestruct rel_val_xs_related with (xs := firstn n_param ys)
      as [v_firstn_ys [cv_firstn_ys [Hv_firstn_ys [Hcv_firstn_ys Hrel_firstn_ys]]]]; eauto.
    { normalize_occurs_free; eapply Included_trans; sets. }
    edestruct rel_val_xs_related with (xs := skipn n_param ys)
      as [v_skipn_ys [cv_skipn_ys' [Hv_skipn_ys [Hcv_skipn_ys' Hrel_skipn_ys]]]]; eauto.
    { normalize_occurs_free; eapply Included_trans; sets. }
    assert (cv_skipn_ys' = cv_skipn_ys).
    { now apply some_inj; rewrite <- Hcv_skipn_ys, <- Hcv_skipn_ys'. }
    subst cv_skipn_ys'; clear Hcv_skipn_ys'.
    (** The args array contains (skipn n_param ys) at the right indices *)
    rewrite Bool.negb_false_iff, Nat.eqb_eq in Harity_match.
    destruct (fenv_cc_inv _ _ _ Hf_cc) as [Harity_eq [Hnodup_inds Hbounds_inds]].
    match goal with
    | H : context [set_iths ?args ?skipn_ys ?indices] |- _ =>
      (unshelve epose proof (set_iths_spec args skipn_ys indices _ _ _) as Hargs_in_right_places); auto
    end.
    { apply get_env_list_len in Hcv_skipn_ys.
      rewrite <- Hcv_skipn_ys.
      do 2 f_equal. apply skipn_preserves_eq_len. lia. }
    { (* #|args| = max_args *)
      specialize (fenv_cc_inv _ _ _ Hf_cc).
      eapply Forall_impl; try apply fenv_cc_inv; cbn.
      intros.
      match type of Hm_frame_pushed with
      | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
        destruct_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R) args' Hm_frame_pushed;
        destruct_ex_ctx (fun H => P ⋆ Q ⋆ H ⋆ R) Hlen_args Hm_frame_pushed
      end. lia. }
    (** The live variables \ {x} are related *)
    edestruct rel_val_xs_related with (xs := PS.elements (PS.remove x live_after_call))
      as [vs_live_no_x [cvs_live_no_x' [Hvs_live_no_x [Hcvs_live_no_x' Hrel_live_no_x]]]]; eauto.
    { rewrite <- FromSet_elements, FromSet_remove.
      apply Setminus_Included_Included_Union; normalize_occurs_free.
      rewrite Hlive_after_call.
      eapply Included_trans; [apply Included_Intersection_l|].
      rewrite <- !Union_assoc.
      apply Included_Union_preserv_r.
      apply Included_Union_preserv_r.
      sets. }
    assert (cvs_live_no_x' = cvs_live_no_x).
    { rewrite Hcvs_live_no_x in Hcvs_live_no_x'; now inv Hcvs_live_no_x'. }
    subst cvs_live_no_x'; clear Hcvs_live_no_x'.
    assert (Hshapes_frame_no_x : has_shapes values (vs_live_no_x :: vss) (cvs_live_no_x :: cvss)).
    { change (?x :: ?xs) with ([x] ++ xs)%list.
      apply has_shapes_app; [|apply Hshapes].
      eapply rel_vals_has_shapes; eauto. }
    (** Because the functions are related, the call will produce related results *)
    specialize (one_letapp_nonzero x f t ys e).
    destruct k as [|k]; [rewrite to_nat_add in Hk; lia|].
    unfold "|=" in Hrel_f.
    destruct Hrel_f as [Hty_f Hrel_f].
    specialize Hrel_f with (j := k) (cin := cin_call)
                           (cvs := (cv_firstn_ys ++ cv_skipn_ys)%list)
                           (cvss := cvs_live_no_x :: cvss)
                           (args := set_iths args cv_skipn_ys (skipn n_param inds)).
    replace (k - (k - k)) with k in Hrel_f by lia.
    edestruct Hrel_f as [m_call [cvx [cvss_call [values_call 
      [Heval_funcall [Hm_call [Hvalues_call [Hcompat_shapes Hrel_call]]]]]]]]; try eassumption.
    { lia. }
    { pose proof Hv_skipn_ys as Hv_ys.
      eapply get_list_app in Hv_ys; try apply Hv_firstn_ys.
      rewrite firstn_skipn, Hρ_get_ys in Hv_ys; inv Hv_ys.
      apply Forall2_app; eapply Forall2_monotonic; eauto; cbn;
        intros ? ? Hrel; eapply rel_val_antimon; try apply Hrel; lia. }
    { rewrite !to_nat_add in Hk. lia. }
    { rewrite skipn_app.
      destruct (dec_le (length ys) n_param) as [Hle|Hgt].
      - assert (Hskipn_inds : skipn n_param inds = []).
        { apply skipn_all2. superlia. }
        rewrite Hskipn_inds in *.
        rewrite skipn_all2 in Hv_skipn_ys by auto.
        inv Hv_skipn_ys.
        assert (length cv_firstn_ys <= length ys).
        { apply get_env_list_len in Hcv_firstn_ys.
          assert (length (firstn n_param ys) <= length ys).
          { rewrite firstn_length. lia. }
          superlia. }
        rewrite skipn_all2 with (n := n_param) by superlia.
        destruct cv_skipn_ys; [|inv Hargs_in_right_places].
        rewrite skipn_nil.
        constructor.
      - apply get_env_list_len in Hcv_firstn_ys.
        rewrite firstn_length_le in Hcv_firstn_ys by superlia.
        rewrite skipn_all2 with (n := n_param) (l := cv_firstn_ys) by lia.
        replace (n_param - length cv_firstn_ys) with 0 by lia.
        cbn. auto. }
    { exists_ex nursery_b. exists_ex alloc_o. exists_ex limit_o. exists_ex nalloc.
      apply Hm_limit_stored. }
    (** Make the call *)
    eapply fwd_call; try eassumption.
    { cbn. do 3 f_equal. lia. }
    { econstructor.
      - eapply eval_make_var; eauto.
        + vars_neq Hdis f frame_id.
          vars_neq Hdis f roots_id.
          now split.
        + intros Hnone; congruence.
      - rewrite typeof_make_var.
        change (Tpointer ?t noattr) with (tptr t).
        now rewrite sem_cast_ptr'. }
    { econstructor; eauto with EvalDB.
      destruct (dec_le (length ys) n_param) as [Hle|Hgt].
      - rewrite firstn_all2 in Hcv_firstn_ys by lia.
        rewrite (@firstn_all2 ident n_param ys) by superlia.
        rewrite (@skipn_all2 ident n_param ys) in Hcv_skipn_ys by superlia.
        inv Hcv_skipn_ys. rewrite app_nil_r.
        pose proof Hcv_firstn_ys as Hcv_firstn_ys_old.
        apply get_env_list_len in Hcv_firstn_ys.
        rewrite (@firstn_all2 Values.val n_param cv_firstn_ys) by superlia.
        replace (Nat.min n_param (N.to_nat arity)) with (length ys) by superlia.
        eapply eval_exprlist_make_var; eauto.
      - pose proof Hcv_firstn_ys as Hcv_firstn_ys_old.
        apply get_env_list_len in Hcv_firstn_ys.
        assert (n_param < length ys) by lia.
        assert (n_param = length (firstn n_param ys)).
        { rewrite firstn_length. lia. }
        rewrite firstn_prefix by superlia.
        replace (Nat.min n_param (N.to_nat arity)) with (length (firstn n_param ys)) by superlia.
        assert (In_firstn : forall {A} (x : A) n xs,
          ~ List.In x xs ->
          ~ List.In x (firstn n xs)).
        { clear; induction n as [|n IHn]; destruct xs as [|x' xs]; try easy.
          cbn; intros Hnotin; cbn; intros [Hl|Hr]; subst; auto. eapply IHn; eauto.
          rewrite firstn_firstn. replace (Nat.min n n) with n by lia. auto. }
        eapply eval_exprlist_make_var; eauto.
        rewrite firstn_all2 with (l := cv_firstn_ys) by superlia.
        auto. }
    cbn [set_opttemp].
    (** Retrieve new alloc and limit *)
    destruct_ex nursery_b_call Hm_call.
    destruct_ex alloc_o_call Hm_call.
    destruct_ex limit_o_call Hm_call.
    fwd Cred_set.
    { eapply eval_tinfo_alloc; eauto.
      vars_neq Hdis x tinfo_id.
      rewrite M.gso; auto. }
    fwd Cred_set.
    { eapply eval_tinfo_limit; eauto.
      vars_neq Hdis x alloc_id.
      vars_neq Hdis x tinfo_id.
      rewrite !M.gso; auto.
      rewrite <- NoDup'_spec in NoDup_vars.
      clear - NoDup_vars; cbn in *; easy. }
    repeat fwd Cred_seq_assoc.
    (** Step through outer if-then-else *)
    destruct cvss_call as [|cvs_live_no_x_call cvss_call]; [destruct Hcompat_shapes|].
    match goal with
    | |- postcond _ ?tenv_call' _ _ _ =>
      pose (tenv_call := tenv_call');
      change tenv_call' with tenv_call
    end.
    assert (Halloc_ne_limit : alloc_id <> limit_id).
    { rewrite <- NoDup'_spec in NoDup_vars.
      clear - NoDup_vars; cbn in *; easy. }
    eapply fwd_seq with (P := fun tenv_gc m_gc _ =>
      (** after the if-then-else,
          - the new tenv contains a binding (x ↦ cvx_gc),
          - and the new mem contains a possibly-GC'd heap values_gc + enough free space for max_allocs,
          - and the shapes vss post-GC are compatible with their shapes pre-GC 
          - and the shape of x is comaptible with its shape pre-GC if x is live after the call *)
      exists cvx_gc values_gc nursery_b_gc alloc_o_gc limit_o_gc cvs_gc cvss_gc maybe_x,
      tenv_gc ! x = Some cvx_gc /\
      tenv_gc ! limit_id = Some (Vptr nursery_b_gc limit_o_gc) /\
      tenv_gc ! alloc_id = Some (Vptr nursery_b_gc alloc_o_gc) /\
      (forall x', x' <> x -> x' <> limit_id -> x' <> alloc_id -> tenv_gc ! x' = tenv_call ! x') /\
      m_gc |= ∃ talloc_o_gc tlimit_o_gc args nalloc,
              valid_mem nursery_b_gc talloc_o_gc tlimit_o_gc alloc_o_gc limit_o_gc
                        tinfo_b tinfo_o args (frame_no_x :: ss) ((cvs_gc ++ maybe_x) :: cvss_gc)%list
                        nalloc values_gc frame /\
      values_gc |-- outliers ⋆ Pure True /\
      (max_allocs e * word_size <= O.unsigned limit_o_gc - O.unsigned alloc_o_gc)%Z /\
      (if PS.mem x live_after_call
       then compatible_shape values_call values_gc vx cvx cvx_gc
       else val_defined_wf cvx_gc) /\
      compatible_shapes values_call values_gc (vs_live_no_x :: vss)
                        (cvs_live_no_x_call :: cvss_call)
                        (cvs_gc :: cvss_gc)
    ); [auto 10 with NormalDB|..].
    { destruct (Z.eq_dec _ _) as [Hno_allocs|Hyes_allocs].
      { apply fwd_skip.
        exists cvx, values_call, nursery_b_call, alloc_o_call, limit_o_call, cvs_live_no_x_call, cvss_call, [].
        split_ands; auto; try solve [eauto with ShapeDB].
        - subst tenv_call.
          vars_neq Hdis x limit_id.
          vars_neq Hdis x alloc_id.
          rewrite !M.gso by auto.
          now rewrite M.gss.
        - subst tenv_call. now rewrite M.gss.
        - subst tenv_call. rewrite M.gso by auto. now rewrite M.gss.
        - unfold "|=".
          exists_ex alloc_o_call; exists_ex limit_o_call.
          rewrite app_nil_r.
          assumption.
        - destruct_ex args' Hm_call; destruct_ex nalloc' Hm_call.
          apply valid_mem_limit_alloc_nonneg in Hm_call; lia.
        - destruct (PS.mem _ _); eauto with ShapeDB EvalDB. }
      assert (Hcall_preserves_len : #|PS.elements (PS.remove x live_after_call)| = #|cvs_live_no_x_call|).
      { rewrite Hlen_equal.
        destruct Hcompat_shapes as [Hframe_compat Hstack_compat].
        apply Forall3_len in Hframe_compat; lia. }
      (** Step through inner if-then-else *)
      destruct (PS.mem x live_after_call) eqn:Hx_live_after_call.
      - (** x live after call *)
        unfold create_space.
        pose proof Hm_call as Hm_call'.
        destruct_ex args' Hm_call'; destruct_ex nalloc' Hm_call'.
        edestruct eval_space_check' with (env := env) (n := max_allocs e) (tenv := tenv_call)
          as [cmp_v [Hcmp_v [cmp_b [Heval_cmp_b Hcmp_b]]]]; try apply Hm_call'.
        { now apply (Hmax_allocs (Eletapp_c x f t ys Hole_c)). }
        { subst tenv_call; now rewrite M.gss. }
        { subst tenv_call. rewrite M.gso by auto. now rewrite M.gss. }
        fwd Cred_if'; eauto.
        destruct cmp_b.
        2:{ (** Enough space in nursery; no need to GC *)
          apply fwd_skip.
          exists cvx, values_call, nursery_b_call, alloc_o_call, limit_o_call, cvs_live_no_x_call, cvss_call, [].
          split_ands; auto; try solve [eauto with ShapeDB].
          - subst tenv_call.
            vars_neq Hdis x limit_id.
            vars_neq Hdis x alloc_id.
            rewrite !M.gso by auto.
            now rewrite M.gss.
          - subst tenv_call. now rewrite M.gss.
          - subst tenv_call. rewrite M.gso by auto. now rewrite M.gss.
          - unfold "|=".
            exists_ex alloc_o_call; exists_ex limit_o_call.
            rewrite app_nil_r.
            assumption.
          - destruct_ex args'' Hm_call; destruct_ex nalloc'' Hm_call.
            apply valid_mem_limit_alloc_nonneg in Hm_call; lia. }
        repeat fwd Cred_seq_assoc.
        (** Store x in the roots array *)
        unfold valid_mem in Hm_call.
        destruct_ex args_call Hm_call.
        destruct_ex nalloc_call Hm_call.
        unfold shadow_stack in Hm_call; fold shadow_stack in Hm_call.
        match type of Hm_call with
        | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?R =>
          rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ R) sepcon_comm Hm_call;
          rewrite <- (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ R)) in Hm_call;
          rewrite sepcon_comm in Hm_call; auto with FrameDB
        end.
        simpl shadow_stack_frame in Hm_call.
        vars_neq Hdis x limit_id.
        vars_neq Hdis x alloc_id.
        vars_neq Hdis x frame_id.
        vars_neq Hdis x roots_id.
        vars_neq Hdis roots_temp_id x.
        tempvars_neq_as Hroots_temp_ne_alloc roots_temp_id alloc_id.
        tempvars_neq_as Hroots_temp_ne_limit roots_temp_id limit_id.
        assert (length cvs >= PS.cardinal (PS.inter (exp_fv e) locals)).
        { specialize (Hlive Hole_c _ _ _ _ _ eq_refl).
          rewrite Nat2Z.id in Hlive. auto. }
        assert (length cvs_live_no_x = length live_no_x_list).
        { change (?x <> ?y) with (neq' x y) in *.
          subst live_no_x_list; lia. }
        assert (PS.cardinal live_after_call > length live_no_x_list).
        { subst live_no_x_list.
          rewrite <- PS.cardinal_spec.
          assert (Hadd_rem_eq : PS.Equal live_after_call (PS.add x (PS.remove x live_after_call))).
          { apply Same_set_From_set.
            rewrite Hlive_after_call, FromSet_add, FromSet_remove, Hlive_after_call.
            assert (Hx_locals : [set x] <--> [set x] :&: FromSet locals).
            { split; sets. apply Included_Intersection_l. }
            eapply Same_set_trans.
            2:{ apply Same_set_Union_compat; [symmetry; apply Hx_locals|apply Same_set_refl]. }
            rewrite <- Intersection_extract_Setminus.
            rewrite <- Intersection_Union_distr.
            apply Same_set_Intersection_compat; sets.
            apply Union_Setminus_Same_set; auto with Decidable_DB.
            apply PS.mem_spec in Hx_live_after_call.
            eapply FromSet_complete in Hx_live_after_call; [|symmetry; eauto].
            inv Hx_live_after_call; sets. }
          apply Proper_carinal in Hadd_rem_eq.
          rewrite Hadd_rem_eq.
          change (?x <> ?y) with (neq' x y) in *.
          rewrite <- PS_cardinal_add; [lia|].
          rewrite PS.remove_spec. easy. }
        match type of Hm_call with
        | _ |=_{_} (?P ⋆ _) ⋆ ?Q =>
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) suffix Hm_call;
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) Hsuffix Hm_call;
          eapply (fwd_store' (fun H => (P ⋆ H) ⋆ Q)) with (ty := value) (v := cvx); subst tenv_call;
          auto with FrameDB mem; eauto 7 with EvalDB
        end.
        { rewrite Hlen_equal, Hsuffix.
          (* x is live after the call, so |cvs| ≥ |live| = |live\x| + 1 *)
          split; try lia.
          rewrite app_length.
          rewrite skipn_length, Z.add_0_l.
          change (?x <> ?y) with (neq' x y) in *.
          superlia. }
        intros m_store_x Hstore_x Hm_store_x; unfold "|=" in *.
        (** Since x is live after call, suffix (the remaining slots on the shadow stack frame) must be nonempty *)
        destruct suffix as [|overwritten_by_x suffix].
        { rewrite app_nil_r, Z.add_0_l, Nat2Z.id in Hsuffix.
          assert (length cvs_live_no_x = length live_no_x_list).
          { apply get_env_list_len in Hcvs_live_no_x. auto. }
          destruct (skipn (length cvs_live_no_x) cvs) as [|cv' cvs'] eqn:Hskipn.
          { apply skipn_nil_len in Hskipn.
            change (?x <> ?y) with (neq' x y) in *. lia. }
          change (?x <> ?y) with (neq' x y) in *.
          rewrite app_length in Hsuffix; cbn in Hsuffix.
          destruct Hcompat_shapes as [Hframe_compat Hstack_compat].
          apply Forall3_len in Hframe_compat; lia. }
        rewrite set_ith_suffix in Hm_store_x by (clear - Hcall_preserves_len; lia).
        rewrite Hcall_preserves_len, Z.sub_diag in Hm_store_x.
        simpl set_ith in Hm_store_x.
        change (?xs ++ ?y :: suffix)%list with (xs ++ [y] ++ suffix)%list in Hm_store_x.
        rewrite app_assoc in Hm_store_x.
        (** Update bounds of shadow stack frame *)
        match type of Hm_store_x with
        | _ |=_{_} (_ ⋆ ?P) ⋆ ?Q =>
          eapply (fwd_frame_next (fun H => (H ⋆ P) ⋆ Q)) with (ty := value);
          auto with FrameDB; eauto 8 with EvalDB
        end.
        intros m_new_frame Hm_new_frame; unfold "|=" in *.
        (** Set tinfo->nalloc *)
        vars_neq Hdis tinfo_id x.
        tempvars_neq tinfo_id alloc_id.
        tempvars_neq tinfo_id limit_id.
        match type of Hm_new_frame with
        | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
          eapply (fwd_tinfo_nalloc (fun H => P ⋆ H ⋆ Q));
          eauto with FrameDB EvalDB
        end.
        intros m_pre_gc Hm_pre_gc; unfold "|=" in *.
        (** Rearrange memory to match GC spec *)
        match type of Hm_pre_gc with
        | _ |=_{_} ((?f_b, _) ↦_{_} [Vptr _ (O.repr (_ + ?len*_)); Vptr ?r_b ?r_o; ?next] ⋆
                    (_, _) ↦_{_} (?cvs ++ ?suffix)) ⋆
                   ?P =>
          pose (new_frame := mk_ss_frame (f_b, O.zero) (r_b, r_o) #|cvs++suffix|);
          apply (frame_entail (fun H => H ⋆ P))
            with (Q := shadow_stack_frame new_frame cvs next)
            in Hm_pre_gc;
          auto with FrameDB
        end.
        2:{ cbn; intros S m_arbitrary.
          match goal with
          | |- _ |=_{_} _ ⋆ (_ ↦_{_} _ ++ ?suffix) -> _ |=_{_} ?P ⋆ _ =>
            intros Hm_arbitrary;
            exists_ex_ctx (fun H => P ⋆ H) suffix;
            split_ex_ctx (fun H => P ⋆ H); [reflexivity|]
          end.
          assert (Hlens_eq : (1 + #|PS.elements (PS.remove x live_after_call)| =
                             #|cvs_live_no_x_call ++ [cvx] |)%Z).
          { rewrite app_length; cbn.
            cbn in Hcall_preserves_len; rewrite Hcall_preserves_len.
            lia. }
          cbn in Hlens_eq; rewrite Hlens_eq in Hm_arbitrary. assumption. }
        rewrite sepcon_comm in Hm_pre_gc.
        match type of Hm_pre_gc with
        | _ |=_{_} (?P ⋆ ?Q ⋆ _ ⋆ ?R) ⋆ _ =>
          rewrite (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ R)) in Hm_pre_gc; auto with FrameDB;
          rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ R) sepcon_comm Hm_pre_gc;
          rewrite_equiv_in_l (fun H => P ⋆ Q ⋆ H ⋆ R) shadow_stack_eqn Hm_pre_gc
        end.
        change (stack_top (frame_no_x :: ss)) with (stack_top (new_frame :: ss)) in Hm_pre_gc.
        apply valid_mem_fold in Hm_pre_gc.
        (** Invoke GC *)
        destruct prog_genv_has_gc as [gc_b [Hfind_gc_symbol Hfind_gc_funct]].
        edestruct garbage_collect_spec as [m_gc [limit_o_gc [alloc_o_gc [cvss_gc [values_gc 
           [Hgc_sem [Hm_gc [Halloc_gc [Hvalues_gc Hcompat_gc]]]]]]]]].
        { exists_ex nursery_b_call; exists_ex alloc_o_call; exists_ex limit_o_call.
          exists_ex alloc_o_call; exists_ex limit_o_call; exists_ex args_call; apply Hm_pre_gc. }
        { eassumption. }
        { apply has_shapes_snoc_top; eauto with ShapeDB. }
        eapply fwd_call; try eassumption; try reflexivity.
        { econstructor; [|eauto with EvalDB].
          tempvars_neq gc_id frame_id.
          tempvars_neq gc_id roots_id.
          eapply eval_Evar_global; eauto.
          eapply Henvs; auto. }
        { econstructor; [eauto with EvalDB| |constructor].
          cbn. reflexivity. }
        { constructor; unfold Events.external_call. eassumption. }
        cbn [set_opttemp].
        (** Retrieve new alloc and limit from tinfo *)
        destruct_ex nursery_b_gc Hm_gc.
        fwd Cred_set.
        { eapply eval_tinfo_alloc; eauto.
          vars_neq Hdis x tinfo_id.
          rewrite !M.gso; auto. }
        fwd Cred_set. { eapply eval_tinfo_limit; eauto. rewrite !M.gso; auto. }
        (** Retrieve x from the roots array *)
        destruct_ex args_gc Hm_gc; destruct_ex nalloc_gc Hm_gc.
        destruct cvss_gc as [|cvs_gc' cvss_gc]; [destruct Hcompat_gc|].
        destruct (destruct_last cvs_gc') as [->| [cvs_gc [cvx_gc ->]]].
        { destruct Hcompat_gc as [Hcompat_gc _].
          destruct vs_live_no_x, cvs_live_no_x_call; destruct Hcompat_gc. }
        apply compatible_shapes_snoc_top in Hcompat_gc.
        destruct Hcompat_gc as [Hcompat_gc Hcompat_cvx_gc].
        pose proof Hm_gc as Hm_gc_folded.
        unfold valid_mem in Hm_gc; unfold shadow_stack in Hm_gc; fold shadow_stack in Hm_gc.
        match type of Hm_gc with
        | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?S =>
          rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ S) sepcon_comm Hm_gc;
          rewrite <- (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ S)) in Hm_gc; auto with FrameDB;
          rewrite sepcon_comm in Hm_gc
        end.
        unfold shadow_stack_frame, new_frame in Hm_gc.
        match type of Hm_gc with
        | _ |=_{_} (?P ⋆ _) ⋆ ?Q =>
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) suffix_gc Hm_gc;
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) Hsuffix_gc Hm_gc
        end.
        assert (Hlen_cvs_gc : #|PS.elements (PS.remove x live_after_call)| = #|cvs_gc|).
        { (* |cvs_gc| = |vs_live_no_x| by Hcompat_gc
             = |live\x| by Hvs_live_no_x *)
          destruct Hcompat_gc as [Hframe_compat Hstack_compat].
          apply Forall3_len in Hframe_compat.
          apply get_list_length_eq in Hvs_live_no_x.
          change (?x <> ?y) with (neq' x y) in *; lia. }
        fwd Cred_set'.
        { econstructor.
          - econstructor. econstructor; eauto 10 with EvalDB.
            cbn [sem_binary_operation]; eauto with EvalDB.
          - econstructor. cbn. eauto with EvalDB.
            unfold Mem.loadv. rewrite O.unsigned_repr.
            match type of Hm_gc with
            | _|=_{_} (?P ⋆ _) ⋆ ?Q =>
              eapply (mpred_load _ (fun H => (P ⋆ H) ⋆ Q)); auto with FrameDB; eauto
            end.
            + rewrite get_ith_prefix, get_ith_suffix
                by (clear - Hlen_cvs_gc; cbn in *; rewrite ?app_length in *; cbn in *; lia).
              rewrite Hlen_cvs_gc, Z.sub_diag; reflexivity.
            + rewrite Hlen_cvs_gc; clear - Hm_gc; cbn in Hm_gc; decompose [ex and] Hm_gc.
              rewrite ?app_length in *; cbn in *.
              rewrite O.unsigned_zero; superlia. }
        apply fwd_skip.
        exists cvx_gc, values_gc, nursery_b_gc, alloc_o_gc, limit_o_gc, cvs_gc, cvss_gc, [cvx_gc].
        split_ands; auto.
        + now rewrite M.gss.
        + rewrite M.gso by auto. now rewrite M.gss.
        + rewrite !M.gso by auto. now rewrite M.gss.
        + intros x' Hx'_x Hx'_limit Hx'_alloc.
          now rewrite !M.gso by auto.
        + exists_ex alloc_o_gc; exists_ex limit_o_gc;
            exists_ex args_gc; exists_ex nalloc_gc.
          replace frame_no_x with new_frame; [apply Hm_gc_folded|].
          subst new_frame frame_no_x; f_equal; auto.
          cbn. rewrite <- Hsuffix. rewrite !app_length; cbn. superlia.
        + superlia.
      - (** x not live after call *)
        unfold create_space.
        pose proof Hm_call as Hm_call'.
        destruct_ex args' Hm_call'; destruct_ex nalloc' Hm_call'.
        edestruct eval_space_check' with (env := env) (n := max_allocs e) (tenv := tenv_call)
          as [cmp_v [Hcmp_v [cmp_b [Heval_cmp_b Hcmp_b]]]]; try apply Hm_call'.
        { now apply (Hmax_allocs (Eletapp_c x f t ys Hole_c)). }
        { subst tenv_call; now rewrite M.gss. }
        { subst tenv_call. rewrite M.gso by auto. now rewrite M.gss. }
        fwd Cred_if'; eauto.
        destruct cmp_b.
        2:{ (** Enough space in nursery; no need to GC *)
          apply fwd_skip.
          exists cvx, values_call, nursery_b_call, alloc_o_call, limit_o_call, cvs_live_no_x_call, cvss_call, [].
          split_ands; auto; try solve [eauto with ShapeDB].
          - subst tenv_call.
            vars_neq Hdis x limit_id.
            vars_neq Hdis x alloc_id.
            rewrite !M.gso by auto.
            now rewrite M.gss.
          - subst tenv_call. now rewrite M.gss.
          - subst tenv_call. rewrite !M.gso by auto. now rewrite M.gss.
          - unfold "|=".
            exists_ex alloc_o_call; exists_ex limit_o_call.
            rewrite app_nil_r. assumption.
          - lia.
          - eauto with EvalDB. }
        repeat fwd Cred_seq_assoc.
        fwd Cred_skip.
        (** Set tinfo->nalloc *)
        vars_neq Hdis tinfo_id x.
        tempvars_neq tinfo_id alloc_id.
        tempvars_neq tinfo_id limit_id.
        unfold valid_mem in Hm_call'; subst tenv_call.
        unfold shadow_stack in Hm_call'; fold shadow_stack in Hm_call'.
        match type of Hm_call' with
        | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?S =>
          rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ S) sepcon_comm Hm_call';
          rewrite <- (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ S)) in Hm_call'; auto with FrameDB;
          rewrite sepcon_comm in Hm_call'
        end.
        unfold shadow_stack_frame, frame_no_x in Hm_call'.
        match type of Hm_call' with
        | _ |=_{_} (?P ⋆ _) ⋆ ?Q =>
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) suffix_gc Hm_call';
          destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) Hsuffix_gc Hm_call'
        end.
        match type of Hm_call' with
        | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
          eapply (fwd_tinfo_nalloc (fun H => P ⋆ H ⋆ Q));
          eauto with FrameDB EvalDB
        end.
        intros m_pre_gc Hm_pre_gc; unfold "|=" in *.
        (** Rearrange memory to match GC spec *)
        match type of Hm_pre_gc with
        | _ |=_{_} ((?f_b, _) ↦_{_} [Vptr _ (O.repr (_ + ?len*_)); Vptr ?r_b ?r_o; ?next] ⋆
                    (_, _) ↦_{_} (?cvs ++ ?suffix)) ⋆
                   ?P =>
          pose (new_frame := mk_ss_frame (f_b, O.zero) (r_b, r_o) #|cvs++suffix|);
          apply (frame_entail (fun H => H ⋆ P))
            with (Q := shadow_stack_frame new_frame cvs next)
            in Hm_pre_gc;
          auto with FrameDB
        end.
        2:{ cbn; intros S m_arbitrary.
          match goal with
          | |- _ |=_{_} _ ⋆ (_ ↦_{_} _ ++ ?suffix) -> _ |=_{_} ?P ⋆ _ =>
            intros Hm_arbitrary;
            exists_ex_ctx (fun H => P ⋆ H) suffix;
            split_ex_ctx (fun H => P ⋆ H); [reflexivity|]
          end.
          apply Hm_arbitrary. }
        rewrite sepcon_comm in Hm_pre_gc.
        match type of Hm_pre_gc with
        | _ |=_{_} (?P ⋆ ?Q ⋆ _ ⋆ ?R) ⋆ _ =>
          rewrite (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ R)) in Hm_pre_gc; auto with FrameDB;
          rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ R) sepcon_comm Hm_pre_gc;
          rewrite_equiv_in_l (fun H => P ⋆ Q ⋆ H ⋆ R) shadow_stack_eqn Hm_pre_gc
        end.
        fold frame_no_x in Hm_pre_gc.
        change (stack_top (frame_no_x :: ss)) with (stack_top (new_frame :: ss)) in Hm_pre_gc.
        apply valid_mem_fold in Hm_pre_gc.
        (** Invoke GC *)
        destruct prog_genv_has_gc as [gc_b [Hfind_gc_symbol Hfind_gc_funct]].
        edestruct garbage_collect_spec as [m_gc [limit_o_gc [alloc_o_gc [cvss_gc [values_gc 
           [Hgc_sem [Hm_gc [Halloc_gc [Hvalues_gc Hcompat_gc]]]]]]]]].
        { exists_ex nursery_b_call; exists_ex alloc_o_call; exists_ex limit_o_call.
          exists_ex alloc_o_call; exists_ex limit_o_call; exists_ex args'.
          apply Hm_pre_gc. }
        { eassumption. }
        { eauto with ShapeDB. }
        eapply fwd_call; try eassumption; try reflexivity.
        { econstructor; [|eauto with EvalDB].
          tempvars_neq gc_id frame_id.
          tempvars_neq gc_id roots_id.
          eapply eval_Evar_global; eauto.
          eapply Henvs; auto. }
        { econstructor; [eauto with EvalDB| |constructor].
          cbn. reflexivity. }
        { constructor; unfold Events.external_call. eassumption. }
        cbn [set_opttemp].
        (** Retrieve new alloc and limit from tinfo *)
        destruct_ex nursery_b_gc Hm_gc.
        fwd Cred_set.
        { eapply eval_tinfo_alloc; eauto.
          vars_neq Hdis x tinfo_id.
          rewrite !M.gso; auto. }
        fwd Cred_set. { eapply eval_tinfo_limit; eauto. rewrite !M.gso; auto. }
        destruct_ex args_gc Hm_gc; destruct_ex nalloc_gc Hm_gc.
        destruct cvss_gc as [|cvs_gc cvss_gc]; [destruct Hcompat_gc|].
        apply fwd_skip.
        exists cvx, values_gc, nursery_b_gc, alloc_o_gc, limit_o_gc, cvs_gc, cvss_gc, [].
        split_ands; auto.
        + vars_neq Hdis x limit_id. vars_neq Hdis x alloc_id.
          rewrite !M.gso by auto. now rewrite M.gss.
        + now rewrite M.gss.
        + rewrite M.gso by auto. now rewrite M.gss.
        + intros; now rewrite !M.gso by auto.
        + exists_ex alloc_o_gc; exists_ex limit_o_gc;
            exists_ex args_gc; exists_ex nalloc_gc.
          rewrite app_nil_r.
          replace frame_no_x with new_frame; [apply Hm_gc|].
          subst new_frame frame_no_x; f_equal; auto.
        + superlia.
        + eauto with EvalDB. }
    intros tenv_gc m_gc [cvx_gc [values_gc [nursery_b_gc [alloc_o_gc [limit_o_gc
      [cvs_gc [cvss_gc [maybe_x [Htenv_gc_x [Htenv_gc_limit [Htenv_gc_alloc 
      [Htenv_gc [Hm_gc [Hvalues_gc [Hfree_space [Hcvx_compat Hcvs_compat]]]]]]]]]]]]]]]].
    (** Retrieve |live\x| from the roots array *)
    unfold "|=" in *.
    destruct_ex talloc_o_gc Hm_gc.
    destruct_ex tlimit_o_gc Hm_gc.
    destruct_ex args_gc Hm_gc.
    destruct_ex nalloc_gc Hm_gc.
    unfold valid_mem, shadow_stack in Hm_gc; fold shadow_stack in Hm_gc.
    match type of Hm_gc with
    | _ |=_{_} ?P ⋆ ?Q ⋆ _ ⋆ ?S =>
      rewrite_equiv_in (fun H => P ⋆ Q ⋆ H ⋆ S) sepcon_comm Hm_gc;
      rewrite <- (frame_stuff_hole (fun H => P ⋆ Q ⋆ H ⋆ S)) in Hm_gc; auto with FrameDB;
      rewrite sepcon_comm in Hm_gc
    end.
    unfold shadow_stack_frame, frame_no_x in Hm_gc.
    match type of Hm_gc with
    | _ |=_{_} (?P ⋆ _) ⋆ ?Q =>
      destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) suffix_gc Hm_gc;
      destruct_ex_ctx (fun H => (P ⋆ H) ⋆ Q) Hsuffix_gc Hm_gc
    end.
    assert (Hlen_cvs_gc : #|cvs_gc| = #|vs_live_no_x|).
    { destruct Hcvs_compat as [Hcvs_compat Hcvss_compat].
      apply Forall3_len in Hcvs_compat. lia. }
    assert (Hlen_vs_live_no_x : #|vs_live_no_x| = #|live_no_x_list|).
    { apply get_list_length_eq in Hvs_live_no_x. subst live_no_x_list. auto. }
    match type of Hm_gc with
    | _ |=_{_} (?P ⋆ _) ⋆ ?Q =>
      eapply (fwd_loads (fun H => (P ⋆ H) ⋆ Q))
        with (P_tenv := fun tenv => tenv!roots_temp_id = Some (Vptr roots_b O.zero))
             (ty := value); auto with FrameDB mem; try apply Hm_gc
    end.
    { eauto with EvalDB. }
    { vars_neq Hdis roots_temp_id x.
      tempvars_neq_as Hroots_temp_ne_alloc roots_temp_id alloc_id.
      tempvars_neq_as Hroots_temp_ne_limit roots_temp_id limit_id.
      rewrite Htenv_gc; auto.
      subst tenv_call; rewrite !M.gso by auto; auto. }
    { intros ? x_in_live; intros.
      assert (x_in_live <> roots_temp_id).
      { intros Hwat; subst x_in_live; destruct Hdis as [Hdis].
        contradiction (Hdis roots_temp_id); constructor; auto 10.
        (* roots_temp_id ∈ |live\x| ==> roots_temp_id ∈ FV(e) ⊆ used_vars e *)
        change (List.In ?x ?xs) with (x \in FromList xs) in H.
        rewrite <- FromSet_elements in H.
        rewrite FromSet_remove in H.
        rewrite Hlive_after_call in H.
        inv H. inv H1. right; right; now right. }
      now rewrite M.gso by auto. }
    { change (?x <> ?y) with (neq' x y) in *. superlia. }
    intros tenv_roots Htenv_roots.
    apply add_to_env_set_lists in Htenv_roots.
    2:{ change (?x <> ?y) with (neq' x y) in *. superlia. }
    2:{ apply PS_elements_NoDup. }
    destruct Htenv_roots as [tenv_roots' [Htenv_roots Htenv_roots']].
    change (Z.to_nat 0) with 0 in Htenv_roots; cbn [skipn] in Htenv_roots.
    (** Pop frame from shadow stack *)
    match type of Hm_gc with
    | _ |=_{_} ?P ⋆ _ ⋆ ?Q =>
      eapply (fwd_tinfo_fp (fun H => P ⋆ H ⋆ Q)) with (v := stack_top ss);
       auto with FrameDB; try apply Hm_gc
    end.
    { (* tenv_roots ! tinfo_id = tenv_roots' ! tinfo_id
         = tenv_gc ! tinfo_id (b/c tinfo_id ∉ |live\x|),
         = tenv_call ! tinfo_id (b/c tinfo_id ∉ {limit, alloc}),
         = tenv ! tinfo_id (b/c tinfo_id ∉ {limit, alloc}),
         = Some (Vptr tinfo_b tinfo_b) *)
      rewrite Htenv_roots'.
      assert (Hnotin_new : ~ List.In tinfo_id live_no_x_list).
      { change (~ tinfo_id \in FromList live_no_x_list).
        subst live_no_x_list.
        rewrite <- FromSet_elements.
        rewrite FromSet_remove, Hlive_after_call.
        intros H; inv H. inv H0.
        destruct Hdis as [Hdis]; contradiction (Hdis tinfo_id).
        constructor; auto 10. right; right; now right. }
      erewrite <- set_lists_not_In; try apply Hnotin_new; try apply Htenv_roots.
      tempvars_neq tinfo_id limit_id.
      tempvars_neq tinfo_id alloc_id.
      vars_neq Hdis tinfo_id x.
      rewrite Htenv_gc by auto.
      subst tenv_call; rewrite !M.gso by auto. auto. }
    { right; reflexivity. }
    { decompose [ex and] prog_co_stack_frame.
      econstructor.
      - econstructor; eauto with EvalDB. reflexivity.
      - econstructor; eauto.
        + reflexivity.
        + unfold Ptrofs.add.
          change (O.unsigned (O.repr (2 * word_size))) with (2 * word_size)%Z.
          unfold Mem.loadv.
          rewrite Mptr_word.
          rewrite O.unsigned_repr.
          2:{ cbn in Hm_gc; decompose [ex and] Hm_gc; clear Hm_gc. superlia. }
          match type of Hm_gc with
          | _ |=_{_} (_ ⋆ ?P) ⋆ ?Q =>
            eapply (mpred_load _ (fun H => (H ⋆ P) ⋆ Q));
              auto with FrameDB; try apply Hm_gc
          end.
          reflexivity. }
    intros m_pop Hm_pop.
    (** Massage m_pop until it's ready for IH *)
    unfold "|=" in Hm_pop.
    match type of Hm_pop with
    | _ |=_{_} ((?bo ↦_{?p} [Vptr ?roots_b ?next; ?root; ?prev]) ⋆ ?P) ⋆ ?Q =>
      eapply mpred_ex_intro
        with (F := fun H => (H ⋆ P) ⋆ Q) (G := fun H => bo ↦_{p} [Vptr roots_b H; root; prev])
        in Hm_pop;
      auto with FrameDB
    end.
    assert (Hroots_len_same : #|(cvs_gc ++ maybe_x) ++ suffix_gc| = #|cvs|).
    { rewrite Z.add_0_l, Nat2Z.id in Hsuffix_gc.
      assert (#|cvs_live_no_x ++ skipn (length cvs_live_no_x) cvs| = #|cvs|).
      { rewrite app_length, skipn_length; lia. }
      change (?x <> ?y) with (neq' x y) in *; superlia. }
    match type of Hm_pop with
    | _ |=_{_} (?P ⋆ (?bo ↦_{?p} ?cvs')) ⋆ ?Q =>
      eapply mpred_ex_intro
        with (F := fun H => (P ⋆ H) ⋆ Q) (G := fun H => bo ↦_{p} cvs')
             (x0 := Hroots_len_same)
        in Hm_pop;
      auto with FrameDB
    end.
    match type of Hm_pop with
    | _ |=_{_} (?P ⋆ (?bo ↦_{?p} ?cvs' WITH #|?cvs'| = #|cvs|)) ⋆ ?Q =>
      eapply mpred_ex_intro
        with (F := fun H => (P ⋆ H) ⋆ Q) (G := fun H => bo ↦_{p} H WITH #|H| = #|cvs|)
        in Hm_pop;
      auto with FrameDB
    end.
    rewrite sepcon_comm in Hm_pop.
    change (O.unsigned O.zero) with 0%Z in Hm_pop.
    match type of Hm_pop with
    | _ |=_{_} (?P ⋆ ?Q ⋆ ?R ⋆ ?S ⋆ _) ⋆ _ =>
      rewrite (frame_stuff_hole (fun H => P ⋆ Q ⋆ R ⋆ S ⋆ H)) in Hm_pop;
      auto with FrameDB;
      rewrite_equiv_in (fun H => P ⋆ Q ⋆ R ⋆ S ⋆ H) sepcon_comm Hm_pop;
      rewrite_equiv_in (fun H => P ⋆ Q ⋆ R ⋆ S ⋆ H) sepcon_assoc Hm_pop
    end.
    apply valid_mem_fold in Hm_pop.
    rewrite <- postcond'_spec.
    (** Collect some useful facts before invoke IH *)
    rewrite !firstn_prefix in Htenv_roots by (subst live_no_x_list; superlia).
    rewrite firstn_all2 in Htenv_roots by (subst live_no_x_list; superlia).
    assert (Hinv_tenv_roots : tenv_inv tenv_roots).
    { unfold tenv_inv; split_ands.
      - intros x' cvx' Hx'_case Hx_roots.
        rewrite Htenv_roots' in Hx_roots.
        destruct (pos_list_in_dec x' live_no_x_list) as [Hyes|Hno].
        + assert (Hcvx'_in_cvs_gc : List.In cvx' cvs_gc).
          { eapply set_lists_In; eauto. }
          apply compatible_shapes_wf2 in Hcvs_compat.
          rewrite Forall_All in Hcvs_compat.
          destruct Hcvs_compat as [Hcv_compat Hcvs_compat].
          rewrite Forall_forall in Hcv_compat.
          split; [|now apply Hcv_compat].
          left. rewrite PS.mem_spec.
          eapply FromSet_sound; [apply Same_set_refl|].
          apply Hlive_no_x_list in Hyes.
          inv Hyes. now inv H.
        + erewrite <- set_lists_not_In in Hx_roots; eauto.
          destruct (Pos.eq_dec x' alloc_id).
          { subst x'; split; [clear; easy|].
            rewrite Htenv_gc_alloc in Hx_roots; inv Hx_roots; auto with EvalDB. }
          destruct (Pos.eq_dec x' limit_id).
          { subst x'; split; [clear; easy|].
            rewrite Htenv_gc_limit in Hx_roots; inv Hx_roots; auto with EvalDB. }
          destruct (Pos.eq_dec x' x).
          { subst x'; split.
            - left. rewrite PS.mem_spec.
              eapply FromSet_sound; [apply Same_set_refl|].
              apply Hbv; sets.
            - rewrite Htenv_gc_x in Hx_roots. inv Hx_roots.
              destruct (PS.mem x live_after_call); auto.
              eapply compatible_shape_wf2; eauto. }
          rewrite Htenv_gc in Hx_roots by auto.
          subst tenv_call. rewrite !M.gso in Hx_roots by auto.
          apply Henvs; auto.
      - intros cv Hcv. rewrite Htenv_roots' in Hcv.
        erewrite <- set_lists_not_In in Hcv; eauto.
        2:{ change (~ List.In ?x ?xs) with (~ x \in FromList xs).
            subst live_no_x_list; rewrite Hlive_no_x_list.
            intros Hcase; inv Hcase. inv H.
            destruct Hdis as [Hdis]; contradiction (Hdis case_id).
            constructor; auto 10.
            right; right; right; auto. }
        vars_neq Hdis x case_id.
        tempvars_neq alloc_id case_id.
        tempvars_neq limit_id case_id.
        rewrite Htenv_gc in Hcv by auto.
        subst tenv_call; rewrite !M.gso in Hcv by auto.
        apply Henvs; auto.
      - intros x' Hx'. intros Hnone.
        rewrite Htenv_roots' in Hnone.
        eapply set_lists_None in Hnone; eauto.
        destruct (Pos.eq_dec x' x); [subst; congruence|].
        destruct (Pos.eq_dec x' alloc_id); [subst; congruence|].
        destruct (Pos.eq_dec x' limit_id); [subst; congruence|].
        rewrite Htenv_gc in Hnone by auto.
        subst tenv_call; rewrite !M.gso in Hnone by auto.
        destruct Henvs as [_ [[_ [_ Henvs]] _]].
        eapply Henvs; eauto. }
    assert (Hstacks_compat : 
              compatible_shapes values values_gc
                                (vs_live_no_x :: vss)
                                (cvs_live_no_x :: cvss)
                                (cvs_gc :: cvss_gc)).
    { destruct_ex args_call Hm_call; destruct_ex nalloc_call Hm_call.
      unfold valid_mem in Hm_call.
      match type of Hm_call with
      | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ _ ⋆ ?S =>
        eapply (compatible_shapes_trans (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S));
          [..|apply Hcvs_compat]; try eassumption; auto with FrameDB
      end. }
    assert (Hframe_rel : Forall2 (fun v cv => v ~ᵥ{S k} (values_gc, cv)) vs_live_no_x cvs_gc).
    { destruct Hstacks_compat as [Hframe_compat Hstacks_compat].
      unfold valid_mem in Hm_pop, Hm.
      match type of Hm with
      | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ ?S ⋆ ?T ⋆ _ ⋆ ?U =>
        match type of Hm_pop with
        | _ |=_{_} ?V ⋆ ?W ⋆ ?X ⋆ _ ⋆ ?Y =>
          eapply (rel_val_compatible_shapes
                    (fun H => P ⋆ Q ⋆ R ⋆ S ⋆ T ⋆ H ⋆ U)
                    (fun H => V ⋆ W ⋆ X ⋆ H ⋆ Y));
            auto 10 with FrameDB; eauto
        end
      end. }
    assert (Henv_rel_no_x : ρ ~ₑ{ S k, occurs_free e \\ [set x]} (env, tenv_roots, values_gc)).
    { intros x' Hx'. inv Hx'. rename H into Hx'_fve, H0 into Hx_x'.
      assert (x <> x') by (intros ?; subst; now contradiction Hx_x').
      destruct (Decidable_FromSet locals) as [Hdec_locals].
      destruct (Hdec_locals x') as [Hyes|Hno].
      - assert (Hx'_live_no_x : List.In x' live_no_x_list).
        { change (x' \in FromList live_no_x_list).
          rewrite Hlive_no_x_list. constructor; auto. }
        edestruct (set_lists_Forall2_get (@eq Values.val)) with (x := x')
          as [cv [cv' [Hcv [Hcv' Hcv_eq]]]]; try apply Htenv_roots.
        { apply Forall2_refl; auto. }
        { apply Hx'_live_no_x. }
        subst cv'; clear Hcv'.
        pose proof Hx'_live_no_x as Hx'_live_no_x_old.
        eapply set_lists_In in Hx'_live_no_x; eauto.
        unfold "!!!". rewrite Htenv_roots', Hcv.
        edestruct rel_val_in_ρ with (x := x') as [v' Hv']; [|apply Henv_rel|].
        { normalize_occurs_free. right; constructor; auto. }
        rewrite Hv'.
        edestruct (set_lists_length3 ρ live_no_x_list vs_live_no_x) as [ρ' Hρ'].
        { eapply get_list_length_eq; eauto. }
        erewrite set_get_list_same in Hv'; try apply Hρ'; subst live_no_x_list; auto;
          try apply PS_elements_NoDup.
        edestruct (@set_lists_Forall2_get' cps.val Values.val)
          with (x := x')
          as [v'' [cv'' [Hv'' [Hcv'' Hv_rel]]]];
          try apply Hframe_rel; try apply Hρ'; try apply Htenv_roots; auto.
        rewrite Hv' in Hv''; inv Hv''. rewrite Hcv in Hcv''; inv Hcv''.
        auto.
      - unfold "!!!". rewrite Htenv_roots'.
        assert (Hx'_live_no_x : ~ List.In x' live_no_x_list).
        { change (~ x' \in FromList live_no_x_list).
          rewrite Hlive_no_x_list. intros wat; inv wat.
          inv H0. contradiction. }
        erewrite <- set_lists_not_In with (rho' := tenv_roots'); eauto.
        assert (x' <> alloc_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis alloc_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> limit_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis limit_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> frame_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis frame_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> roots_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis roots_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> case_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis case_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> ret_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis ret_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> roots_temp_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis roots_temp_id).
          constructor; auto 10; right; right; now right. }
        assert (x' <> tinfo_id).
        { intros ->. destruct Hdis as [Hdis]; contradiction (Hdis tinfo_id).
          constructor; auto 10; right; right; now right. }
        rewrite Htenv_gc by auto.
        subst tenv_call. rewrite !M.gso by auto.
        specialize (Henv_rel x').
        destruct (ρ ! x') as [vx'|] eqn:Hvx'; [|destruct Henv_rel; normalize_occurs_free; right; constructor; auto].
        unfold "!!!" in Henv_rel.
        destruct (tenv ! x') as [tenv_cvx'|] eqn:Htenv_cvx'.
        { destruct Henvs as [_ [[Henvs _] _]].
          specialize (Henvs x' tenv_cvx').
          assert (wat : PS.mem x' locals = true).
          { destruct Henvs; auto. tauto. }
          exfalso; apply Hno.
          rewrite PS.mem_spec in wat.
          rewrite <- PS.elements_spec1 in wat.
          apply InA_In in wat. apply wat. }
        assert (Henv_none : env ! x' = None).
        { rewrite (proj1 Henvs); split_ands; auto. }
        rewrite Henv_none in *.
        destruct Henvs as [_ [_ Henvs]].
        specialize (Henvs x' vx').
        destruct (Genv.find_symbol prog_genv x') as [bx'|] eqn:Hgenv_x';
          [|destruct Henv_rel; normalize_occurs_free; right; constructor; auto].
        specialize (Henvs _ Hvx' eq_refl).
        destruct Henvs as [Hfenv [ρ_f' [fds' [f'' ->]]]].
        eapply rel_val_fun_mem; eauto. }
    (** Continue as e, via IH *)
    edestruct (IHe (k - to_nat cin_call)) as [tenv_end [m_end [cv_end [Hend [cvss_end
     [values_end [Hrel_end [Hm_end [Hvalues_end Hcompat_end]]]]]]]]].
    6:{ eassumption. }
    17:{
      exists_ex args_gc; exists_ex nalloc_gc; exists_ex talloc_o_gc; exists_ex tlimit_o_gc.
      apply Hm_pop. }
    19:{ exists tenv_end, m_end, cv_end; split; eauto.
         exists cvss_end, values_end; split_ands; eauto.
         - eapply rel_val_antimon; [|eauto].
           rewrite !to_nat_add in *. lia.
         - destruct Hstacks_compat as [Hframe_compat Hstacks_compat].
           unfold valid_mem in Hm_pop.
           match type of Hm_pop with
           | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ _ ⋆ ?S =>
             eapply (compatible_shapes_trans (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S));
               [..|apply Hcompat_end]; try assumption; try apply Hm_pop;
                 auto with FrameDB
           end. }
    all: try solve_IH_obligations.
    6:{ destruct Hcvs_compat as [Hcvs_compat Hcvss_compat].
        eauto with ShapeDB. }
    5:{ destruct (PS.mem x live_after_call) eqn:Hx_live.
         - rewrite PS.mem_spec in Hx_live.
           symmetry in Hlive_after_call.
           eapply FromSet_complete in Hx_live; eauto.
           destruct Hx_live as [x Hx_fvs Hx_locals].
           eapply rel_env_antimon_S; [apply Included_Union_Setminus with (s2 := [set x]); auto with Decidable_DB|].
           rewrite rel_env_union; split.
           { apply rel_env_gso_l; auto.
             - intros wat; inv wat. now contradiction H0.
             - eapply rel_env_antimon; try eassumption. lia. }
           intros x' Hx'. assert (x = x') by now inv Hx'. subst x'.
           rewrite M.gss. unfold "!!!". rewrite Htenv_roots'.
           erewrite <- set_lists_not_In; eauto.
           2:{ change (~ x \in FromSet (PS.remove x live_after_call)).
               rewrite FromSet_remove. intros Hwat. inv Hwat. now contradiction H0. }
           rewrite Htenv_gc_x.
           destruct_ex args_call Hm_call; destruct_ex nalloc_call Hm_call.
           unfold valid_mem in Hm_call.
           unfold valid_mem in Hm_pop.
           match type of Hm_call with
           | _ |=_{_} ?P ⋆ ?Q ⋆ ?R ⋆ _ ⋆ ?S =>
             match type of Hm_pop with
             | _ |=_{_} ?T ⋆ ?U ⋆ ?V ⋆ _ ⋆ ?W =>
               eapply (rel_val_compatible_shape'
                         (fun H => P ⋆ Q ⋆ R ⋆ H ⋆ S)
                         (fun H => T ⋆ U ⋆ V ⋆ H ⋆ W)); auto with FrameDB; eauto
             end
           end.
         - assert (Hx_live' : ~ PS.In x live_after_call).
           { intros Hx; rewrite <- PS.mem_spec in Hx. easy. }
           assert (Hx_live_set : ~ x \in occurs_free e :&: FromSet locals).
           { intros Hx. apply Hx_live'.
             symmetry in Hlive_after_call.
             eapply FromSet_sound; eauto. }
           assert (Hx_in_locals : x \in FromSet locals).
           { apply Hbv; sets. }
           assert (Hx_not_in_fvs : ~ x \in occurs_free e).
           { intros Hx; apply Hx_live_set; constructor; auto. }
           eapply rel_env_antimon_S;
             [apply Included_Setminus;
              [apply Disjoint_Singleton_r; eassumption|apply Included_refl] |].
           eapply rel_env_gso_l; [intros Hx; now inv Hx|].
           eapply rel_env_antimon; try eassumption. lia. }
    + rewrite Htenv_roots'.
      assert (~ List.In tinfo_id live_no_x_list).
      { change (~ tinfo_id \in FromList live_no_x_list).
        subst live_no_x_list.
        rewrite <- FromSet_elements.
        rewrite FromSet_remove, Hlive_after_call.
        intros Hwat; inv Hwat. inv H.
        destruct Hdis as [Hdis]; contradiction (Hdis tinfo_id).
        constructor; auto. right; right; now right. }
      erewrite <- set_lists_not_In; try apply Htenv_roots; auto.
      tempvars_neq tinfo_id limit_id.
      tempvars_neq tinfo_id alloc_id.
      vars_neq Hdis x tinfo_id.
      rewrite Htenv_gc by auto.
      subst tenv_call; rewrite !M.gso by auto. auto.
    + rewrite Htenv_roots'.
      assert (~ List.In alloc_id live_no_x_list).
      { change (~ alloc_id \in FromList live_no_x_list).
        subst live_no_x_list.
        rewrite <- FromSet_elements.
        rewrite FromSet_remove, Hlive_after_call.
        intros Hwat; inv Hwat. inv H.
        destruct Hdis as [Hdis]; contradiction (Hdis alloc_id).
        constructor; auto. right; right; now right. }
      erewrite <- set_lists_not_In; try apply Htenv_roots; auto.
    + rewrite Htenv_roots'.
      assert (~ List.In limit_id live_no_x_list).
      { change (~ limit_id \in FromList live_no_x_list).
        subst live_no_x_list.
        rewrite <- FromSet_elements.
        rewrite FromSet_remove, Hlive_after_call.
        intros Hwat; inv Hwat. inv H.
        destruct Hdis as [Hdis]; contradiction (Hdis limit_id).
        constructor; auto. right; right; now right. }
      erewrite <- set_lists_not_In; try apply Htenv_roots; auto.
    + rewrite Htenv_roots'.
      assert (~ List.In roots_temp_id live_no_x_list).
      { change (~ roots_temp_id \in FromList live_no_x_list).
        subst live_no_x_list.
        rewrite <- FromSet_elements.
        rewrite FromSet_remove, Hlive_after_call.
        intros Hwat; inv Hwat. inv H.
        destruct Hdis as [Hdis]; contradiction (Hdis roots_temp_id).
        constructor; auto 10. right; right; now right. }
      erewrite <- set_lists_not_In; try apply Htenv_roots; auto.
      tempvars_neq roots_temp_id limit_id.
      tempvars_neq roots_temp_id alloc_id.
      vars_neq Hdis x roots_temp_id.
      rewrite Htenv_gc by auto.
      subst tenv_call; rewrite !M.gso by auto. auto.
  - (** let rec fds in e *) exact I.
  - (** f ft ys *)
    cbn [translate_body]. unfold make_fun_call.
    destruct (fenv ! f) as [[arity inds] |] eqn:Hf_cc; [|exact I].
    destruct (negb (_ =? _)%nat) eqn:Harity_match; [exact I|].
    rewrite bind_ret.
    normalize_used_vars.
    repeat fwd Cred_seq_assoc.
    (** Some useful facts for later *)
    assert (Hcase_notin_ys : ~ List.In case_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis case_id).
      constructor; auto 10. }
    assert (Hframe_notin_ys : ~ List.In frame_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis frame_id).
      constructor; auto 10. }
    assert (Hroots_notin_ys : ~ List.In roots_id ys).
    { intros wat; destruct Hdis as [Hdis]; contradiction (Hdis roots_id).
      constructor; auto 10. }
    (** Store arguments n+1, .. in the args array at indices inds *)
    unfold "|=" in *.
    destruct_ex args Hm.
    destruct_ex nalloc Hm.
    destruct_ex talloc_o Hm.
    destruct_ex tlimit_o Hm.
    rewrite skipn_combine.
    unfold valid_mem in Hm.
    match type of Hm with
    | _ |=_{_} _ ⋆ ?P =>
      eapply (fwd_args_stores (fun H => H ⋆ P)); eauto with EvalDB FrameDB
    end.
    { (* #|ys| = #|inds| *)
      do 2 f_equal; apply skipn_preserves_eq_len.
      specialize (fenv_cc_inv _ _ _ Hf_cc).
      rewrite Bool.negb_false_iff in Harity_match.
      apply beq_nat_true in Harity_match.
      lia. }
    { specialize (fenv_cc_inv _ _ _ Hf_cc); easy. }
    { specialize (fenv_cc_inv _ _ _ Hf_cc).
      eapply Forall_impl; try apply fenv_cc_inv; cbn.
      match type of Hm with
      | _ |=_{_} _ ⋆ ?P =>
        destruct_ex_ctx (fun H => H ⋆ P) args' Hm;
        destruct_ex_ctx (fun H => H ⋆ P) Hlen_args Hm
      end.
      lia. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      apply FromList_skipn in Hx'.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      easy. }
    { rewrite All_spec; intros x' Hx'.
      change (List.In ?x ?xs) with (x \in FromList xs) in Hx'.
      apply FromList_skipn in Hx'.
      edestruct (rel_val_x_related x') as [vx' [cvx' [Hvx' [Hcvx' Hrelx']]]]; [|apply Henv_rel|]; eauto.
      intros Hwat. unfold temp_env in *. congruence. }
    intros m_args_stored cv_skipn_ys Hcv_skipn_ys Hm_args_stored; unfold "|=" in *.
    (** Update tinfo->alloc and tinfo->limit *)
    match type of Hm_args_stored with
    | _ |=_{_} _ ⋆ ?P =>
      eapply (fwd_tinfo_alloc (fun H => H ⋆ P)) with (ty := value);
      eauto with EvalDB FrameDB
    end.
    intros m_alloc_stored Hm_alloc_stored; unfold "|=" in *.
    match type of Hm_alloc_stored with
    | _ |=_{_} _ ⋆ ?P =>
      eapply (fwd_tinfo_limit (fun H => H ⋆ P)) with (ty := value);
      eauto with EvalDB FrameDB
    end.
    intros m_limit_stored Hm_limit_stored; unfold "|=" in *.
    apply valid_mem_fold in Hm_limit_stored.
    (** The functions are related *)
    inv Hbstep. rename cin0 into cin, cout0 into cout; inv H.
    rename fl into fds, rho' into ρ_f, rho'' into ρ_f_xvs, H3 into Hρ_f,
    H4 into Hρ_get_ys, H6 into Hfind_def, H10 into Hρ_f_xvs, H11 into Hbstep.
    edestruct rel_val_x_related with (x := f) as [v_f [cv_f [Hv_f [Hcv_f Hrel_f]]]]; try eassumption.
    { normalize_occurs_free; sets. }
    (assert (v_f = Vfun ρ_f fds f') by congruence); subst v_f; clear Hρ_f.
    rewrite rel_val_eqn in Hrel_f; cbn [rel_val_aux] in Hrel_f.
    destruct cv_f; try solve [destruct Hrel_f]; rename b into f_b, i into f_o.
    rewrite Hfind_def in Hrel_f.
    (* destruct (M.bempty ρ_f) eqn:Hρ_f_empty; [|destruct Hrel_f]. *)
    pose proof Hf_cc as Hf_cc_tag.
    erewrite (Hftags Hole_c) in Hf_cc_tag; [|left; do 2 eexists; reflexivity].
    rewrite Hf_cc_tag in Hrel_f.
    destruct (Genv.find_funct _ _) as [fn|] eqn:Hfind_funct; [|destruct Hrel_f].
    (** The arguments are related *)
    edestruct rel_val_xs_related with (xs := firstn n_param ys)
      as [v_firstn_ys [cv_firstn_ys [Hv_firstn_ys [Hcv_firstn_ys Hrel_firstn_ys]]]]; eauto.
    { normalize_occurs_free; eapply Included_trans; sets. }
    edestruct rel_val_xs_related with (xs := skipn n_param ys)
      as [v_skipn_ys [cv_skipn_ys' [Hv_skipn_ys [Hcv_skipn_ys' Hrel_skipn_ys]]]]; eauto.
    { normalize_occurs_free; eapply Included_trans; sets. }
    assert (cv_skipn_ys' = cv_skipn_ys).
    { now apply some_inj; rewrite <- Hcv_skipn_ys, <- Hcv_skipn_ys'. }
    subst cv_skipn_ys'; clear Hcv_skipn_ys'.
    (** The args array contains (skipn n_param ys) at the right indices *)
    rewrite Bool.negb_false_iff, Nat.eqb_eq in Harity_match.
    destruct (fenv_cc_inv _ _ _ Hf_cc) as [Harity_eq [Hnodup_inds Hbounds_inds]].
    match goal with
    | H : context [set_iths ?args ?skipn_ys ?indices] |- _ =>
      (unshelve epose proof (set_iths_spec args skipn_ys indices _ _ _) as Hargs_in_right_places); auto
    end.
    { apply get_env_list_len in Hcv_skipn_ys.
      rewrite <- Hcv_skipn_ys.
      do 2 f_equal. apply skipn_preserves_eq_len. lia. }
    { (* #|args| = max_args *)
      specialize (fenv_cc_inv _ _ _ Hf_cc).
      eapply Forall_impl; try apply fenv_cc_inv; cbn.
      intros.
      match type of Hm with
      | _ |=_{_} _ ⋆ ?P =>
        destruct_ex_ctx (fun H => H ⋆ P) args' Hm;
        destruct_ex_ctx (fun H => H ⋆ P) Hlen_args Hm
      end. lia. }
    (** Because the functions are related, the call will produce related results *)
    specialize (one_app_nonzero f t ys).
    destruct k as [|k]; [rewrite to_nat_add in Hk; lia|].
    unfold "|=" in Hrel_f.
    destruct Hrel_f as [Hty_f Hrel_f].
    specialize Hrel_f with (j := k) (cin := cin)
                           (cvs := (cv_firstn_ys ++ cv_skipn_ys)%list)
                           (cvss := cvss)
                           (args := set_iths args cv_skipn_ys (skipn n_param inds)).
    replace (k - (k - k)) with k in Hrel_f by lia.
    edestruct Hrel_f as [m_call [cvx [cvss_call [values_call 
      [Heval_funcall [Hm_call [Hvalues_call [Hcompat_shapes Hrel_call]]]]]]]]; try eassumption.
    { lia. }
    { pose proof Hv_skipn_ys as Hv_ys.
      eapply get_list_app in Hv_ys; try apply Hv_firstn_ys.
      rewrite firstn_skipn, Hρ_get_ys in Hv_ys; inv Hv_ys.
      apply Forall2_app; eapply Forall2_monotonic; eauto; cbn;
        intros ? ? Hrel; eapply rel_val_antimon; try apply Hrel; lia. }
    { rewrite !to_nat_add in Hk. lia. }
    { rewrite skipn_app.
      destruct (dec_le (length ys) n_param) as [Hle|Hgt].
      - assert (Hskipn_inds : skipn n_param inds = []).
        { apply skipn_all2. superlia. }
        rewrite Hskipn_inds in *.
        rewrite skipn_all2 in Hv_skipn_ys by auto.
        inv Hv_skipn_ys.
        assert (length cv_firstn_ys <= length ys).
        { apply get_env_list_len in Hcv_firstn_ys.
          assert (length (firstn n_param ys) <= length ys).
          { rewrite firstn_length. lia. }
          superlia. }
        rewrite skipn_all2 with (n := n_param) by superlia.
        destruct cv_skipn_ys; [|inv Hargs_in_right_places].
        rewrite skipn_nil.
        constructor.
      - apply get_env_list_len in Hcv_firstn_ys.
        rewrite firstn_length_le in Hcv_firstn_ys by superlia.
        rewrite skipn_all2 with (n := n_param) (l := cv_firstn_ys) by lia.
        replace (n_param - length cv_firstn_ys) with 0 by lia.
        cbn. auto. }
    { exists_ex nursery_b. exists_ex alloc_o. exists_ex limit_o. exists_ex nalloc.
      apply Hm_limit_stored. }
    (** Make the call *)
    eapply fwd_call; try eassumption.
    { cbn. do 3 f_equal. lia. }
    { econstructor.
      - eapply eval_make_var; eauto.
        + vars_neq Hdis f frame_id.
          vars_neq Hdis f roots_id.
          now split.
        + intros Hnone; congruence.
      - rewrite typeof_make_var.
        change (Tpointer ?t noattr) with (tptr t).
        now rewrite sem_cast_ptr'. }
    { econstructor; eauto with EvalDB.
      destruct (dec_le (length ys) n_param) as [Hle|Hgt].
      - rewrite firstn_all2 in Hcv_firstn_ys by lia.
        rewrite (@firstn_all2 ident n_param ys) by superlia.
        rewrite (@skipn_all2 ident n_param ys) in Hcv_skipn_ys by superlia.
        inv Hcv_skipn_ys. rewrite app_nil_r.
        pose proof Hcv_firstn_ys as Hcv_firstn_ys_old.
        apply get_env_list_len in Hcv_firstn_ys.
        rewrite (@firstn_all2 Values.val n_param cv_firstn_ys) by superlia.
        replace (Nat.min n_param (N.to_nat arity)) with (length ys) by superlia.
        eapply eval_exprlist_make_var; eauto.
      - pose proof Hcv_firstn_ys as Hcv_firstn_ys_old.
        apply get_env_list_len in Hcv_firstn_ys.
        assert (n_param < length ys) by lia.
        assert (n_param = length (firstn n_param ys)).
        { rewrite firstn_length. lia. }
        rewrite firstn_prefix by superlia.
        replace (Nat.min n_param (N.to_nat arity)) with (length (firstn n_param ys)) by superlia.
        assert (In_firstn : forall {A} (x : A) n xs,
          ~ List.In x xs ->
          ~ List.In x (firstn n xs)).
        { clear; induction n as [|n IHn]; destruct xs as [|x' xs]; try easy.
          cbn; intros Hnotin; cbn; intros [Hl|Hr]; subst; auto. eapply IHn; eauto.
          rewrite firstn_firstn. replace (Nat.min n n) with n by lia. auto. }
        eapply eval_exprlist_make_var; eauto.
        rewrite firstn_all2 with (l := cv_firstn_ys) by superlia.
        auto. }
    cbn [set_opttemp].
    rewrite <- postcond'_spec.
    eapply postcond_ret; eauto with EvalDB.
    exists cvss_call, values_call; split_ands; auto.
    eapply rel_val_antimon; try eassumption.
    rewrite !to_nat_add; lia.
  - (** let x = Prim p ys in e *) now inv Hbstep.
  - (** halt x *)
    cbn [translate_body]; repeat fwd Cred_seq_assoc.
    unfold "|=" in *.
    destruct_ex args Hm.
    destruct_ex nalloc Hm.
    destruct_ex talloc_o Hm.
    destruct_ex tlimit_o Hm.
    unfold valid_mem in Hm.
    match type of Hm with
    | _ |=_{_} _ ⋆ ?P =>
      eapply (fwd_tinfo_alloc (fun H => H ⋆ P)) with (ty := value) in Hm;
        eauto with FrameDB EvalDB
    end.
    intros m_alloc Hm_alloc; unfold "|=" in *.
    match type of Hm_alloc with
    | _ |=_{_} _ ⋆ ?P =>
      eapply (fwd_tinfo_limit (fun H => H ⋆ P)) with (ty := value) in Hm_alloc;
        eauto with FrameDB EvalDB
    end.
    intros m_limit Hm_limit; unfold "|=" in *.
    apply valid_mem_fold in Hm_limit.
    rewrite <- postcond'_spec.
    edestruct (rel_val_x_related x) as [vx [cvx [Hvx [Hcvx Hrelx]]]]; try eassumption; sets.
    inv Hbstep; inv H. rename H4 into Hx.
    rewrite Hx in Hvx; inv Hvx.
    normalize_used_vars.
    vars_neq Hdis x case_id.
    vars_neq Hdis x frame_id.
    vars_neq Hdis x roots_id.
    eapply postcond_ret; eauto with EvalDB.
    { eapply eval_make_var; eauto. easy. }
    exists cvss, values; split_ands; auto with ShapeDB.
    + eapply rel_val_antimon; try eassumption. rewrite to_nat_add; lia.
    + exists_ex nursery_b; exists_ex alloc_o; exists_ex limit_o.
      exists_ex args. exists_ex nalloc. apply Hm_limit.
Qed.

End TRANSLATE_BODY_CORRECT.

(* TODO will probably need something like this to prove translate_fundefs correct *)
Lemma ρ_inv_set_lists xs vs ρ_current ρ_fds ρ_fds_xvs :
  ρ_inv ρ_current ->
  ρ_inv ρ_fds ->
  get_list xs ρ_current = Some vs ->
  set_lists xs vs ρ_fds = Some ρ_fds_xvs ->
  ρ_inv ρ_fds_xvs.
Proof. Abort.

End PROOF.

End CODEGEN.

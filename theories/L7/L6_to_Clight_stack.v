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
        compcert.cfrontend.ClightBigstep
        Coq.Relations.Relations
        Coq.Sets.Ensembles
        Lia
        L6.eval L6.algebra L6.Ensembles_util L6.ctx.

Module O := Ptrofs.

Section CODEGEN.

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
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    (* Unboxed: no allocation necessary *)
    | [] => max_allocs e'
    (* Boxed: allocate 1 word for header + |vs| words for arguments *)
    | _ => S (length vs) + max_allocs e'
    end
  | Ecase x cs => fold_left (fun allocs '(_, e) => max (max_allocs e) allocs) cs 0
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => 0
  | Efun fds e' => 0 (* unreachable (we are compiling hoisted terms) *)
  | Eapp x t vs => 0
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
  end.

(** * Clight abbreviations *)

(** typedef intnat value; (See values.h, config.h)

    NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition value :=
  if Archi.ptr64
  then Tlong Signed noattr
  else Tint I32 Signed noattr.
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
      uintnat nalloc;
    };

    Zoe: nalloc is the number of allocations until the next GC call so that GC can perform a test. 
    Note that it will be coerced to UL from ULL. That should be safe for the values we're using but 
    consider changing it too. *)
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
Definition tinfo := Etempvar tinfo_id threadInf.
Definition tinfd := Ederef tinfo threadStructInf.
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
Definition roots := Etempvar roots_id (tptr value).
Definition frame := Evar frame_id stack_frame.
Notation "frame.next" := (Efield frame next_fld (tptr value)).
Notation "frame.root" := (Efield frame root_fld (tptr value)).
Notation "frame.prev" := (Efield frame prev_fld (tptr stack_frame)).
Definition stack_decl size : list (ident * type) :=
  (frame_id, stack_frame) ::
  (roots_id, roots_ty size) :: nil.

(** Each generated function body also declares the following local variables:
      value *alloc;
      value *limit; *)
Definition alloc := Etempvar alloc_id (tptr value).
Definition limit := Etempvar limit_id (tptr value).

(* Variable (isptr_id : ident). (* ident for the is_ptr external function *) *)

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

(** Each function declares a local variable
      value ret;
    for storing the results of tail calls. *)
Variable (ret_id : ident).

(** fun_ty n = value(struct thread_info *ti, value, .. min(n_param, n) times)
    prim_ty n = value(value, .. n times) *)
Definition value_tys (n : nat) : typelist := Nat.iter n (Tcons value) Tnil.
Definition fun_ty (n : nat) := Tfunction (Tcons threadInf (value_tys (min n_param n))) value cc_default.
Definition prim_ty (n : nat) := Tfunction (value_tys n) value cc_default.

Notation "'var' x" := (Etempvar x value) (at level 20).
Notation "a '+'' b" := (Ebinop Oadd a b (tptr value)) (at level 30).
Notation "a '-'' b" := (Ebinop Osub a b (tptr value)) (at level 30).
Notation "a '<'' b" := (Ebinop Olt a b type_bool) (at level 40).
Notation "a '>>'' b" := (Ebinop Oshr a b value) (at level 30).
Notation "a '&'' b" := (Ebinop Oand a b value) (at level 30).
Notation "a '=='' b" := (Ebinop Oeq a b type_bool) (at level 40).
Notation " p ';' q " := (Ssequence p q) (at level 100, format " p ';' '//' q ").
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
  match r with
  | enum t => c_int (rep_unboxed t) value
  | boxed t a => c_int (rep_boxed t a) value
  end%Z.

(** To use variables in Clight expressions, need variable name and its type.
    Variables that refer to functions must have type
      void(struct thread_info *ti, val, ..)
                                   ------- n times
    where n = min(n_param, arity of the function).

    All other variables just have type val. 

    make_var x =
      Ecast (Evar x suitable-fn-type) value if x is a toplevel function
      Etempvar x value otherwise *)
Definition make_var (x : ident) :=
  match M.get x fenv with
  | Some (_, locs) => Ecast (Evar x (fun_ty (length locs))) value
  | None => var x
  end.

Section Body.

Context
  (locals : FVSet) (* The set of local variables including definitions and arguments *)
  (nenv : M.t BasicAst.name).

Definition make_fun_call (destination : ident) f ys :=
  match M.get f fenv with 
  | Some (arity, inds) =>
    let arity := N.to_nat arity in
    if negb (length ys =? arity)%nat then
      Err ("make_fun_call: arity mismatch: " ++ pretty_fun_name f nenv)%string
    else
      ret (statements
             (map (fun '(y, i) => tinfo->args.[Z.of_N i] :::= make_var y)
                  (skipn n_param (combine ys inds)))%bool;
           tinfo->alloc :::= alloc;
           tinfo->limit :::= limit;
           Scall (Some destination)
                 (Ecast (make_var f) (Tpointer (fun_ty (min arity n_param)) noattr))
                 (tinfo :: map make_var (firstn n_param ys)))
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
      match p with
      | boxed t a => ret (LScons (Some (Z.of_N t)) (prog; Sbreak) ls, ls', fvs, n)
      | enum t => ret (ls, LScons (Some (Z.of_N t)) (prog; Sbreak) ls', fvs, n)
      end
    end.

(** Use limit and alloc to check whether nursery contains n words of free space.
    If not, run pre, invoke GC, then run post. *)
Definition create_space (n : nat) pre post : statement :=
  let n := c_int (Z.of_nat n) value in 
  Sifthenelse
    (limit -' alloc <' n)
    (pre;
     tinfo->alloc :::= alloc;
     tinfo->limit :::= limit;
     tinfo->nalloc :::= n;
     Scall None gc (tinfo :: nil);
     alloc_id ::= tinfo->alloc;
     limit_id ::= tinfo->limit;
     post)
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
      match rep with
      | enum t => ret (x ::= make_tag rep)
      | boxed t a =>
        ret (x ::= Ecast (alloc +' c_int 1 value) value;
             alloc_id ::= alloc +' c_int (Z.of_N (a + 1)) value;
             (var x).[-1] :::= make_tag rep;
             statements (mapi (fun i y => (var x).[i] :::= make_var y) 0 ys))
      end ;;
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((stm_constr; stm_e), add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (** [[Ecase x cs]] = 
        if (isptr(x)) { switch on x[-1]&255 over boxed cases } 
        else { switch on x>>1 over unboxed cases } *)
  | Ecase x cs =>
    '(boxed_cases, unboxed_cases, fvs_cs, n_cs) <- make_cases translate_body cs ;;
    ret (Sifthenelse
          (var x &' make_cint 1 value ==' make_cint 0 value)
          (Sswitch ((var x).[-1] &' make_cint 255 value) boxed_cases)
          (Sswitch (var x >>' make_cint 1 value) unboxed_cases),
         add_local_fv fvs_cs x, n_cs)
  (** [[let x = f(y, ..) in e]] =
        store local variables live after call (= locals∩(FV(e)\x)) in roots array
        push frame onto shadow stack
        x = call f (may GC)
        retreieve new limit, alloc from tinfo
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
      statements (mapi (fun i x => roots.[i] :::= var x) 0 live_minus_x_list);
      frame.next :::= roots +' c_int n_live_minus_x value;
      tinfo->fp :::= &frame;
      call;
      alloc_id ::= tinfo->alloc;
      limit_id ::= tinfo->limit;
      match max_allocs e with 0 => Sskip | S _ as allocs =>
        if PS.mem x live_after_call then
          create_space allocs
            (roots.[n_live_minus_x] :::= var x;
             frame.next :::= roots +' c_int (1 + n_live_minus_x) value)
            (x ::= roots.[n_live_minus_x])
        else
          create_space allocs Sskip Sskip
      end;
      retrieve_roots live_minus_x_list;
      tinfo->fp :::= frame.prev;
      stm_e
    in
    ret (stm, add_local_fvs live_minus_x (f :: ys),
         N.max n_e (N.of_nat (PS.cardinal live_after_call)))
  (** [[let x = y.n in e]] = (x = y[n]; [[e]]) *)
  | Eproj x t n y e =>
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((x ::= (var y).[Z.of_N n]; stm_e), add_local_fv (PS.remove x fvs_e) y, n_e)
  | Efun fnd e => Err "translate_body: nested function detected"
  (** [[f(ys)]] =
        ret_temp = call f with arguments ys;
        return ret_temp *)
  | Eapp f t ys =>
    call <- make_fun_call ret_id f ys ;;
    ret ((call; Sreturn (Some (var ret_id))), add_local_fvs PS.empty (f :: ys), 0)%N
  (** [[let x = p(ys) in e]] = (x = p(ys); [[e]]) *)
  | Eprim x p ys e =>    
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((Scall (Some x) (Evar p (prim_ty (length ys))) (map make_var ys);
          stm_e),
         add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (** [[halt x]] = (store alloc and limit in tinfo; return x) *)
  | Ehalt x =>
    ret ((tinfo->alloc :::= alloc;
          tinfo->limit :::= limit;
          Sreturn (Some (var x))),
         add_local_fv PS.empty x, 0)%N
  end.

End Body.

Definition definition := (ident * globdef Clight.fundef type)%type.

Definition make_fun (size : Z) (xs locals : list ident) (body : statement) : function :=
  let make_decls := map (fun x => (x, value)) in
  mkfunction value cc_default
             ((tinfo_id, threadInf) :: make_decls (firstn n_param xs))
             (make_decls (skipn n_param xs ++ locals) ++ stack_decl size ++
              (alloc_id, tptr value) :: (limit_id, tptr value) :: (ret_id, value) :: [])%list
             nil
             body.

Definition init_shadow_stack_frame :=
  frame.next :::= roots;
  frame.root :::= roots;
  frame.prev :::= tinfo->fp.

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
      let body :=
        alloc_id ::= tinfo->alloc;
        limit_id ::= tinfo->limit;
        statements (map (fun '(x, i) => x ::= tinfo->args.[Z.of_N i]) (skipn n_param (combine xs locs)));
        init_shadow_stack_frame;
        match allocs with 0 => Sskip | S _ as allocs =>
          create_space allocs
            (statements (mapi (fun i x => roots.[i] :::= var x) 0 live_xs_list);
             frame.next :::= roots +' c_int (Z.of_N n_live_xs) value;
             tinfo->fp :::= &frame)
            (statements (mapi (fun i x => x ::= roots.[i]) 0 live_xs_list);
             tinfo->fp :::= frame.prev)
        end;
        body
      in
      let stack_slots :=
        match allocs with
        | 0 => Z.of_N stack_slots
        | S _ => Z.of_N (N.max n_live_xs stack_slots)
        end
      in
      ret ((f, Gfun (Internal (make_fun stack_slots xs locals body))) :: defs)
    end
  end.

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
  let locals := PS.elements (exp_bv e) in
  funs <- translate_fundefs fds nenv ;;
  '(body, _, slots) <- translate_body (union_list PS.empty locals) nenv e ;;
  let body :=
    alloc_id ::= tinfo->alloc;
    limit_id ::= tinfo->limit;
    init_shadow_stack_frame;
    match max_allocs e with 0 => Sskip | S _ as allocs =>
      create_space (max_allocs e) Sskip Sskip
    end;
    body
  in
  let locals :=
    (map (fun x => (x, value)) locals ++
     stack_decl (Z.of_N slots) ++ 
     (alloc_id, tptr value) :: 
     (limit_id, tptr value) :: 
     (ret_id, value) :: 
     [])%list
  in
  let fn := mkfunction value cc_default ((tinfo_id, threadInf) :: nil) locals nil body in
  ret ((body_id, Gfun (Internal fn)) :: funs).

End CODEGEN.

(* TODO: Why are these numbers OK? *)
Definition make_tinfo_id := 20%positive.
Definition export_id := 21%positive.

Variable (main_id : ident).
Definition inf_vars :=
  (* (isptr_id, nNamed "is_ptr") :: *)
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
    let gc_fn := EF_external "gc" (mksignature (ast_value :: nil) None cc_default) in
    (* let is_ptr_fn := EF_external "is_ptr" (mksignature (ast_value :: nil) None cc_default) in *)
    (gc_id, Gfun (External gc_fn (Tcons threadInf Tnil) Tvoid cc_default)) ::
    (* (isptr_id, Gfun (External is_ptr_fn (Tcons value Tnil) type_bool cc_default)) :: *)
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

Notation "'#|' xs '|'" := (Z.of_nat (length xs)).

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

Definition union_with {A} (f : A -> A -> A) (m1 m2 : PMap.t A) :=
  (f (fst m1) (fst m2),
   PTree.combine
     (fun v1 v2 =>
        match v1, v2 with
        | Some v1, Some v2 => Some (f v1 v2)
        | Some v, None | None, Some v => Some v
        | None, None => None
        end)
     (snd m1) (snd m2)).

Lemma union_with_spec {A} (f : A -> A -> A) m1 m2 x :
  (union_with f m1 m2) !! x =
  match PTree.get x (snd m1), PTree.get x (snd m2) with
  | Some v1, Some v2 => f v1 v2
  | Some v, None | None, Some v => v
  | None, None => f (fst m1) (fst m2)
  end.
Proof.
  unfold union_with, "!!"; cbn.
  rewrite PTree.gcombine by auto.
  now destruct (PTree.get x (snd m1)), (PTree.get x (snd m2)).
Qed.
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
    destruct rep as [t|t a]; rewrite bind_ret;
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

Fixpoint translate_body_n_slots locals nenv e {struct e} :
  match translate_body cenv fenv locals nenv e with
  | Ret (_, _, n_slots) =>
    forall C x f t ys e', e = C |[ Eletapp x f t ys e' ]| ->
    N.to_nat n_slots >= PS.cardinal (PS.inter (exp_fv e') locals)
  | _ => True
  end.
Proof.
  rename translate_body_n_slots into IHe; destruct e.
  - cbn. bind_step rep Hrep.
    destruct rep as [t|t a]; rewrite bind_ret;
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

(** ** "Reductions" in machine state *)

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
  forall tenv' m' v,
  (env2, tenv2, m2, stmt2) ⇓ (tenv', m', v) ->
  (env1, tenv1, m1, stmt1) ⇓ (tenv', m', v).
Infix "-->" := Clight_state_red (at level 80).

Lemma Cred_trans s1 s2 s3 :
  s1 --> s2 -> s2 --> s3 -> s1 --> s3.
Proof. destruct s1 as [[[??]?]?], s2 as [[[??]?]?], s3 as [[[??]?]?]; cbn; eauto. Qed.

Lemma Cred_seq_assoc env tenv m s1 s2 s3 :
  (env, tenv, m, ((s1; s2); s3)) --> (env, tenv, m, (s1; (s2; s3))).
Proof.
  intros tenv' m' v H; unfold "⇓" in *; inv H.
  - inv H10.
    + rewrite <- Events.Eapp_assoc. do 2 (eapply exec_Sseq_1; eauto).
    + constructor; [|easy]. eapply exec_Sseq_1; eauto.
  - now do 2 (constructor; [|easy]).
Qed.

Lemma Cred_skip env tenv m s :
  (env, tenv, m, (Sskip; s)) --> (env, tenv, m, s).
Proof.
  intros tenv' m' v H; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; [constructor|eauto].
Qed.

Lemma Cred_set env tenv m x a v s :
  (env, tenv, m, a) ⇓ᵣ v ->
  (env, tenv, m, (x ::= a; s)) --> (env, M.set x v tenv, m, s).
Proof.
  intros; intros ??? Hexec; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto; econstructor; eauto.
Qed.

Lemma Cred_assign env tenv m a1 a2 v_pre v b o m' s :
  (env, tenv, m, a1) ⇓ₗ (b, o) ->
  (env, tenv, m, a2) ⇓ᵣ v_pre ->
  sem_cast v_pre (typeof a2) (typeof a1) m = Some v ->
  assign_loc prog_genv (typeof a1) m b o v m' ->
  (env, tenv, m, (a1 :::= a2; s)) --> (env, tenv, m', s).
Proof.
  intros; intros ??? Hexec; unfold "⇓".
  change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; eauto; econstructor; eauto.
Qed.

Lemma Cred_if env tenv m a v b s1 s2 s :
  (env, tenv, m, a) ⇓ᵣ v ->
  bool_val v (typeof a) m = Some b ->
  (env, tenv, m, (Sifthenelse a s1 s2; s)) -->
  (env, tenv, m, ((if b then s1 else s2); s)).
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
| Mapsto (bo : address) (vs : list Values.val)
| Sepcon (P Q : mpred)
| Exists {A} (F : A -> mpred)
| Mem (m : mem).
Infix "↦" := Mapsto (at level 77).
Infix "⋆" := Sepcon (at level 78, right associativity).
Notation "'∃' x .. y , p" :=
  (Exists (fun x => .. (Exists (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition dom_mem (m : mem) : Ensemble address :=
  fun '(b, o) => Mem.perm m b o Max Nonempty.

Definition dom_mapsto (b : block) (o : Z) (vs : list Values.val) :=
  fun '(b', o') => b = b' /\ (o <= o' < o + #|vs|*word_size)%Z.

Reserved Notation "m |=_{ S } P" (at level 79).
Fixpoint mpred_denote_aux (P : mpred) (S : Ensemble address) (m : mem) : Prop :=
  match P with
  | (b, o) ↦ vs =>
    S <--> dom_mapsto b o vs /\
    All (map val_wf vs) /\
    (forall i v, get_ith vs i = Some v -> load m b (o + i*word_size) = Some v) /\
    (o >= 0)%Z /\ (o + #|vs|*word_size < O.modulus)%Z (* all addresses are representable *)
  | P ⋆ Q =>
    exists S1 S2, 
    S <--> S1 :|: S2 /\
    Disjoint _ S1 S2 /\
    m |=_{S1} P /\
    m |=_{S2} Q
  | Exists _ F => exists x, m |=_{S} F x
  | Mem m' => S <--> dom_mem m' /\ Mem.unchanged_on (fun b o => S (b, o)) m' m
  end
where "m |=_{ S } P" := (mpred_denote_aux P S m).

Definition mpred_denote (P : mpred) (m : mem) : Prop := m |=_{dom_mem m} P.
Notation "m |= P" := (mpred_denote P m) (at level 79).

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

Ltac superlia :=
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
  change (size_chunk word_chunk) with word_size in *;
  rewrite ?Z.mul_add_distr_l, ?Z.mul_add_distr_r in *;
  (pose proof concretize_word_size);
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

(* TODO hoist *)
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

(* TODO hoist *)
Lemma get_ith_suffix {A} (vs ws : list A) i :
  (#|vs| <= i)%Z ->
  get_ith (vs ++ ws) i = get_ith ws (i - #|vs|).
Proof.
  revert i; induction vs as [|v vs IHvs]; intros i; cbn.
  - now replace (Z.of_nat 0 + i)%Z with i by lia.
  - destruct (Coqlib.zeq i 0) as [|Hne]; [now subst|intros H].
    rewrite IHvs; [|lia]; f_equal; lia.
Qed.

Lemma mapsto_app S b o vs ws m :
  m |=_{S} ((b, o) ↦ vs ++ ws)%list <->
  m |=_{S} ((b, o) ↦ vs) ⋆ ((b, o + #|vs|*word_size) ↦ ws)%Z.
Proof.
  unfold mpred_denote_aux; split.
  - intros [Hdom [Hwf [Hloads Hbounds]]].
    rewrite dom_mapsto_app, map_app, All_app, app_length in *.
    do 2 eexists; split; [eassumption|].
    split_ands; try (sets||tauto||cbn in *; superlia).
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
  - intros [S1 [S2 [HS [HD [[HS1 [Hwf1 [Hload1 Hbound1]]] [HS2 [Hwf2 [Hload2 Hbound2]]]]]]]].
    rewrite dom_mapsto_app, map_app, All_app, app_length, HS, HS1, HS2 in *.
    split_ands; try (sets||tauto||cbn in *; superlia).
    intros i v Hget.
    assert (Hcases : ((0 <= i < #|vs|) \/ (#|vs| <= i < #|vs| + #|ws|))%Z).
    { apply get_ith_range in Hget. rewrite app_length in Hget. lia. }
    destruct Hcases as [Hprefix|Hsuffix].
    + apply Hload1; rewrite <- Hget, get_ith_prefix by lia; auto.
    + replace (o + i*word_size)%Z with (o + #|vs|*word_size + (i-#|vs|)*word_size)%Z by lia.
      apply Hload2; rewrite <- Hget, get_ith_suffix by lia; auto.
Qed.

Lemma mapsto_cons S b o v vs m :
  m |=_{S} ((b, o) ↦ v :: vs) <->
  m |=_{S} ((b, o) ↦ [v]) ⋆ ((b, o + word_size) ↦ vs)%Z.
Proof. apply mapsto_app with (vs := [v]). Qed.

Lemma mapsto_store S b o i v vs m m' :
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} ((b, o) ↦ vs) ->
  m' |=_{S} ((b, o) ↦ set_ith vs i v).
Proof.
  unfold mpred_denote_aux.
  intros Hwf_v Hbound Hstore [HS [Hwf_vs [Hload Hbounds]]].
  split_ands; try (cbn in *; superlia).
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
Qed.

Lemma mpred_unchanged_on S P m m' :
  Mem.unchanged_on (fun b o => S (b, o)) m m' ->
  m |=_{S} P ->
  m' |=_{S} P.
Proof.
  revert S; induction P as [[b o] vs|P IHP Q IHQ|A F IHF|m'']; cbn;
  intros S Hunchanged Hm.
  - destruct Hm as [?[?[Hload [??]]]]; split_ands; auto.
    intros i v Hget; eapply Mem.load_unchanged_on; eauto.
    intros o'; cbn; rewrite Ensemble_iff_In_iff in H.
    specialize (H (b, o')); rewrite H; unfold In, dom_mapsto; superlia.
  - destruct Hm as [S1[S2[HS[?[??]]]]]; do 2 eexists; split_ands; eauto.
    + apply IHP; auto. 
      eapply Mem.unchanged_on_implies; eauto; cbn; intros; now apply (proj2 HS).
    + apply IHQ; auto.
      eapply Mem.unchanged_on_implies; eauto; cbn; intros; now apply (proj2 HS).
  - destruct Hm as [x Hx]; eexists; eauto.
  - destruct Hm as [H Hunchanged']; split; [auto|].
    eapply Mem.unchanged_on_trans; eauto.
Qed.

Lemma mapsto_store_sepcon S P b o i v vs m m' :
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} ((b, o) ↦ vs) ⋆ P ->
  m' |=_{S} ((b, o) ↦ set_ith vs i v) ⋆ P.
Proof.
  remember ((b, o) ↦ vs) as bovs.
  remember ((b, o) ↦ set_ith vs i v) as bovs'.
  cbn; subst bovs bovs'; intros Hwf Hrange Hstore.
  intros [S1 [S2 [HS [HD [Hbovs HP]]]]]; exists S1, S2; split_ands; auto.
  - eapply mapsto_store; eauto.
  - pose proof Hstore as Hunchanged.
    apply (Mem.store_unchanged_on (fun b o => S2 (b, o))) in Hunchanged.
    2:{ rewrite (Disjoint_pair_simpl S1 S2) in HD.
        intros o'; specialize (HD b o').
        intros Hin_S1 Hin_S2; contradiction HD.
        destruct Hbovs as [HS1 _].
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

Inductive is_frame : (mpred -> mpred) -> Prop :=
| is_frame_hole : is_frame (fun P => P)
| is_frame_sepcon1 F Q : is_frame F -> is_frame (fun P => F P ⋆ Q)
| is_frame_sepcon2 F P : is_frame F -> is_frame (fun Q => F P ⋆ Q)
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

Lemma frame_cong F P Q S m :
  is_frame F ->
  (forall S', m |=_{S'} P <-> m |=_{S'} Q) ->
  m |=_{S} F P <-> m |=_{S} F Q.
Proof.
  intros HF HPQ; revert S; induction HF; [auto|intros S..];
  split; intros [S1 [S2 [HS [HD [HP HQ]]]]]; do 2 eexists;
  intuition (try (rewrite <- IHHF + rewrite IHHF + rewrite HPQ + rewrite <- HPQ); eauto).
Qed.

Ltac rewrite_entailment F H :=
  rewrite (frame_cong F);
  [|eauto with FrameDB|intros; apply H].

Lemma frame_swap_hole S F P Q m :
  is_frame F ->
  m |=_{S} F P ⋆ Q <-> m |=_{S} F Q ⋆ P.
Proof.
  intros HF; revert S; induction HF as [|F Q' HF IHF|F P' HF IHF|Q'|P']; intros S.
  - apply sepcon_comm.
  - rewrite !sepcon_assoc.
    rewrite_entailment (fun H => F P ⋆ H) sepcon_comm.
    rewrite_entailment (fun H => F Q ⋆ H) sepcon_comm.
    rewrite <- !sepcon_assoc.
    rewrite_entailment (fun H => H ⋆ Q') IHF.
    now symmetry in IHF; rewrite_entailment (fun H => H ⋆ Q') IHF.
  - rewrite !sepcon_assoc.
    now rewrite_entailment (fun H => F P' ⋆ H) sepcon_comm.
  - rewrite !sepcon_assoc.
    rewrite_entailment (fun H => P ⋆ H) sepcon_comm.
    now rewrite sepcon_comm, !sepcon_assoc.
  - rewrite !sepcon_assoc.
    now rewrite_entailment (fun H => P' ⋆ H) sepcon_comm.
Qed.

Lemma mpred_load S F b o i v vs m :
  is_frame F ->
  get_ith vs i = Some v ->
  m |=_{S} F ((b, o) ↦ vs) ->
  load m b (o + i*word_size) = Some v.
Proof.
  intros HF Hget; revert S; induction HF; intros S Hm;
  cbn in Hm; decompose [ex and] Hm; eauto.
Qed.

Lemma mpred_store S F b o i v vs m m' :
  is_frame F ->
  val_wf v ->
  (0 <= i < #|vs|)%Z ->
  store m b (o + i*word_size) v = Some m' ->
  m |=_{S} F ((b, o) ↦ vs) ->
  m' |=_{S} F ((b, o) ↦ set_ith vs i v).
Proof.
  intros HF Hwf Hrange Hstore Hm; destruct HF.
  - eapply mapsto_store; eauto.
  - rewrite frame_swap_hole in * by auto.
    rewrite sepcon_comm in *; eapply mapsto_store_sepcon; eauto.
  - rewrite sepcon_comm in *; eapply mapsto_store_sepcon; eauto.
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

Lemma mpred_alloc P m lo hi :
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
  induction P as [[b o] vs|P IHP Q IHQ|A F IHF|m'']; cbn.
  - intros ->; split; intros Hand; decompose [and] Hand; split_ands; sets.
  - intros H; split; intros Hand; decompose [ex and] Hand.
    + do 2 eexists; split_ands; eauto.
      now rewrite <- H.
    + do 2 eexists; split_ands; eauto; now rewrite H.
  - intros H; split; intros [x Hx]; exists x; now specialize (IHF x).
  - intros H. erewrite unchanged_on_iff; eauto. now rewrite H.
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
Lemma mpred_free P m b lo hi m_old m' :
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

Definition vint (z : Z) : Values.val :=
  if Archi.ptr64
  then Vlong (Int64.repr z)
  else Values.Vint (Int.repr z).

Lemma mpred_Mem F P m m_inner :
  m_inner |= P ->
  m |= F (Mem m_inner) ->
  m |= F P.
Proof. Abort.

Lemma mpred_Ex {A} F (G : A -> _) S m :
  is_frame F ->
  m |=_{S} F (∃ x, G x) <-> exists x, m |=_{S} F (G x).
Proof.
  destruct 1.
  1: now cbn.
  1: rewrite frame_swap_hole by auto.
  1: erewrite MCUtils.iff_ex; [|intros x; apply frame_swap_hole; auto].
  all:
    cbn; split; intros Hexand; decompose [ex and] Hexand;
    (repeat match goal with |- exists _, _ => eexists end);
    split_ands; eauto.
Qed.

(*
tenv ! alloc_id = Vptr nursery_b alloc_o ->
tenv ! limit_id = Vptr nursery_b limit_o ->
tenv ! tinfo_id = Vptr tinfo_b tinfo_o ->
tenv ! frame_id = Vptr frame_b frame_o ->
tenv ! roots_id = Vptr roots_b roots_o ->
tenv ! args_id = Vptr args_b args_o ->
(#|free_space| = (O.unsigned limit_o - O.unsigned alloc_o)/word_size)%Z ->
nalloc = TODO ->
is_shadow_stack shadow_stack rootss ->
m ⊨
  ((nursery_b, alloc_o) ↦ free_space) ::
  ((tinfo_b, tinfo_o) ↦
     (tinfo_alloc :: 
      tinfo_limit :: 
      Vptr heap_b heap_o ::
      Vptr args_b args_o :: 
      Vptr fp_b fp_o :: 
      vint nalloc :: [])) ::
  ((frame_b, frame_o) ↦ (frame_next :: (roots_b, roots_o) :: (fp_b, fp_o) :: [])) ::
  ((roots_b, roots_o) ↦ roots) ::
  ((args_b, args_o) ↦ args) ::
  stack ++
  shadow_stack ++
 * stuff allocated on nursery (writable)
 * gc_heap (readable)
 * gc_aux (nonempty)
 * c managed heap (readable)
 * frame m' (TODO)
*)
(** The Clight machine state looks as follows at function entry:
      temporary environment
        tinfo_id ↦ (tinfo_b, tinfo_o)
        frame_id ↦ (frame_b, frame_o)
        alloc_id ↦ (nursery_b, alloc_o)
        limit_id ↦ (nursery_b, limit_o)
        args_id ↦ (args_b, args_o)
        roots_id ↦ (roots_b, roots_o)
      memory
        (tinfo_b, tinfo_b) ↦ [_, _, _, (args_b, args_o), (fp_b, fp_o), nalloc]
        (nursery_b, alloc_o) ↦ [_ × (limit_o - alloc_o)]
        (roots_b, roots_o) ↦ [_ × size]
        (frame_b, frame_o) ↦ [_, _, _]
        (args_b, args_o) ↦ [_ × max_args]
    where
      nalloc ≥ max_allocs(L6 term to execute)
      size ≥ |FV(e)| for all subterms (let y = f(xs) in e) of the L6 term to execute
    (Assuming that parameters have all been stored in temporary variables and that
     alloc/limit/etc have been fetched from tinfo)

    During execution, the free space (nursery_b, [alloc_o, limit_o)) may shrink and
    the temporary environment accumulates bindings for intermediate values.

    Before calling a function f,
    - tinfo is updated with the new alloc and limit
    - values live across the call are pushed onto the shadow stack
    - (skin n_param arguments) are stored in the args array at the indices specified by
      f's calling convention
    Now the state looks like (only relevant changes shown):
      temp
        ‥ bindings for intermediate values ‥
      mem
        (tinfo_b, tinfo_b) ↦ [(nursery_b, alloc_o), (nursery_b, limit_o), _, (args_b, args_o), (frame_b, frame_o), nalloc]
        (roots_b, roots_o) ↦ [pushed Coq values ‥]
        (frame_b, frame_o) ↦ [(roots_b, roots_o + |pushed Coq values|), (roots_b, roots_o), (fp_b, fp_o)]
        (args_b, args_o) ↦ [‥ (skipn n_param ys) at indices specified by calling convention ‥]

    After calling f(ys):
      mem
        (tinfo_b, tinfo_b) ↦ [(nursery_b, alloc_o), (nursery_b, limit_o), _, (args_b, args_o), (frame_b, frame_o), nalloc]
        (roots_b, roots_o) ↦ [pushed Coq values' ‥]
        (frame_b, frame_o) ↦ [(roots_b, roots_o + |pushed Coq values'|), (roots_b, roots_o), (fp_b, fp_o)]
        (args_b, args_o) ↦ [‥ f(ys) at index 1 ‥]
      where
        pushed Coq values' still represents the Coq values pushed before the call, but may have moved by GC
    
    After garbage collection and popping everything back out:
      mem
        (tinfo_b, tinfo_b) ↦ [(nursery_b, alloc_o), (nursery_b, limit_o), _, (args_b, args_o), (fp_b, fp_o), nalloc]
        (nursery_b, alloc_o) ↦ [_ × (limit_o - alloc_o)]
        (roots_b, roots_o) ↦ [_ × size]
        (frame_b, frame_o) ↦ [_, _, _]
        (args_b, args_o) ↦ [_ × max_args]

    At each step, each of the segments listed under "mem" are mutually disjoint, and also disjoint from the CertiCoq heap.
*)

Notation "P 'where' Q" := (∃ (_ : Q), P) (at level 100).
Definition mpure (P : Prop) : mpred := ∃ m, Mem m where P.

Definition stack_top (frame_addrs : list (block * ptrofs)) :=
  match frame_addrs with
  | [] => Vnullptr
  | (b, o) :: _ => Vptr b o
  end.

(** A shadow stack at addresses frame_addrs containing root arrays at addresses
    root_addrs, containing values cvss. The addresses of each frame and root array
    are made explicit so we can require that they be preserved across function calls
    and GC. The values inside each root array are made explicit so we can relate them
    to CertiCoq values. *)
Fixpoint shadow_stack
         (frame_addrs root_addrs : list (block * ptrofs))
         (cvss : list (list Values.val)) : mpred :=
  match frame_addrs, root_addrs, cvss with
  | [], [], [] => mpure True
  | (f_b, f_o) :: frame_addrs, (r_b, r_o) :: root_addrs, rs :: cvss =>
    (f_b, O.unsigned f_o) ↦
      Vptr r_b (O.repr (O.unsigned r_o + #|rs|*word_size)) ::
      Vptr r_b r_o :: stack_top frame_addrs :: [] ⋆
    (r_b, O.unsigned r_o) ↦ rs ⋆
    shadow_stack frame_addrs root_addrs cvss
  | _, _, _ => mpure False
  end.

(** A store is well-formed if it contains
    - A well-formed thread_info pointing to a nursery, args array, and shadow stack
    - A CertiCoq heap that can be freely modified by GC *)
Definition valid_mem tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs cvss : mpred :=
  ∃ nursery_b alloc_o,
  (∃ limit_o heap nalloc,
   (tinfo_b, O.unsigned tinfo_o) ↦
   (Vptr nursery_b alloc_o :: Vptr nursery_b limit_o :: heap ::
    Vptr args_b args_o :: stack_top frame_addrs :: nalloc :: [])) ⋆
  (∃ free_space, (nursery_b, O.unsigned alloc_o) ↦ free_space) ⋆
  ((args_b, O.unsigned args_o) ↦ args) ⋆
  (shadow_stack frame_addrs root_addrs cvss) ⋆
  (∃ gc_heap, Mem gc_heap).

(* The state during the execution of an L6 program *)

Axiom garbage_collect_spec : True (* TODO*).

Notation "'match!' e1 'with' p 'in' e2" :=
  (match e1 with p => e2 | _ => False end)
  (at level 80, p pattern, e1 at next level, right associativity).

(** * Logical relation between λ-ANF and Clight *)

Fixpoint closed_val (v : cps.val) :=
  match v with
  | Vconstr c vs => fold_right (fun v P => closed_val v /\ P) True vs
  | Vfun ρ fds f => M.bempty ρ = true
  | Vint _ => True
  end.

Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

Context (one_app_nonzero : forall f ft ys, to_nat (one (Eapp f ft ys)) > 0).

(** Bigstep evaluation of L6 terms *)
Definition bstep_res := fun '(ρ, e, cin) '(v, cout) =>
  bstep_fuel cenv ρ e cin (Res v) cout.
Infix "⇓cps" := bstep_res (at level 80).

Section CycleBreakers.

Context (rel_val : forall (k : nat) (v : cps.val) (m : Memory.mem) (cv : Values.val), Prop).

Definition rel_shadow_stack k vss m cvss :=
  Forall2 (Forall2 (fun v cv => rel_val k v m cv)) vss cvss.

Definition rel_exp' k (ρ : env) (e : cps.exp) env tenv m stmt : Prop :=
  forall v cin cout tinfo_b tinfo_o args_b args_o frame_addrs root_addrs vss frame,
  (** if running e in environment ρ yields a value v in j <= k cost, *)
  to_nat cin <= k ->
  (ρ, e, cin) ⇓cps (v, cout) ->
  (** and m is a valid CertiCoq memory with shadow stack cvss related to vss at level k, *)
  m |=
    (∃ args cvss, valid_mem tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs cvss
     (* TODO: is this OK? Seems like it breaks monotonicity.

        If not OK, could do the following:
        Define a relation has_shape relating L6 values to Clight values:
          has_shape m (Vint i) (vint ci) <-> i = ci
          has_shape m (Vconstr c vs) (Vptr b o) <->
            m contains cvs at (b, o) /\ Forall2 (has_shape m) vs cvs
          has_shape m (Vfun rho fds f) (Vptr b o) <-> True
        Define compatible_shapes relating L6 values two different Clight value-mem pairs:
          compatible_shapes m m' (Vint i) (vint ci) (vint ci') <-> i = ci = ci'
          compatible_shapes m m' (Vconstr c vs) (Vptr b o) (Vptr b' o') <->
            m contains cvs at (b, o) /\ Forall2 (has_shape m) vs cvs /\
            m' contains cvs' at (b', o') /\ Forall2 (has_shape m') vs cvs' /\
            Forall3 (compatible_shapes m m') vs cvs cvs'
          compatible_shapes m m' (Vfun rho fds f) (Vptr b o) (Vptr b' o') <->
            (b, o) = (b', o')

        Then, in here and in the axiomatization of the GC, only require
          has_shape m vss cvss
        and ensure
          compatible_shapes m m' vss cvss cvss'.
        
        Separately, prove that compatible_shapes respects the value relation; i.e.
          Forall2 (λ v cv ⇒ rel_val k v m cv) vss cvss ->
          compatible_shapes vss cvss cvss' ->
          Forall2 (λ v cv ⇒ rel_val k v m cv) vss cvss'. *)
     where rel_shadow_stack k vss m cvss) ⋆
    frame ->
  (** then running stmt yields a result (m', cv), *)
  exists tenv' m' cv,
  (env, tenv, m, stmt) ⇓ (tenv', m', cv) /\
  (** m' is still a valid CertiCoq memory containing a shadow stack related to vss at level k, *)
  m' |=
    (∃ args cvss, valid_mem tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs cvss
     where rel_shadow_stack k vss m' cvss) ⋆
    frame /\
  (** and cv is related to v at level k-j *)
  rel_val (k - to_nat cin) v m' cv.

Definition rel_val_aux (k : nat) :=
  fix go (v : cps.val) (m : Memory.mem) (cv : Values.val) : Prop :=
  match v, cv with
  | Vint v, cv => cv = vint (rep_unboxed (Z.to_N v))
  | Vconstr t vs, cv =>
    match get_ctor_rep cenv t with
    | Ret (enum t) => cv = vint (rep_unboxed t)
    | Ret (boxed t a) =>
      match! cv with Vptr b o in
      load m b (O.unsigned o + (-1)*word_size) = Some (vint (rep_boxed t a)) /\
      let arg_ok i v :=
        match! load m b (O.unsigned o + i*word_size) with Some cv in
        go v m cv
      in All (mapi arg_ok 0 vs)
    | _ => False
    end
  | Vfun ρ fds f, Vptr b o =>
    o = O.zero /\
    match! find_def f fds with Some (t, xs, e) in
    match! fenv ! f with Some (arity, indices) in
    Genv.find_symbol prog_genv f = Some b /\
    match! Genv.find_funct prog_genv (Vptr b o) with Some fn in
    forall j vs ρ_xvs cin cout,
    forall cvs m tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs vss frame,
    j < k ->
    match k with
    | 0 => True
    | S k =>
      (** if vs are related to cvs at level j<k (written as k-(k-j) to convince
          Coq of well-foundedness) *)
      let j := k-(k-j) in
      Forall2 (fun v cv => rel_val j v m cv) vs cvs ->
      (** and calling the L6 function with arguments xs↦vs yields v in i<=j steps, *)
      set_lists xs vs (def_funs fds fds ρ ρ) = Some ρ_xvs ->
      to_nat cin <= j ->
      (ρ_xvs, e, cin) ⇓cps (v, cout) ->
      (** then the corresponding C call evaluates to (m', cv), *)
      let arg_ok i cv := load m args_b (O.unsigned args_o + Z.of_N i * word_size) = Some cv in
      Forall2 arg_ok (skipn n_param indices) (skipn n_param cvs) ->
      m |=
        (∃ cvss, valid_mem tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs cvss
         where rel_shadow_stack j vss m cvss) ⋆
        frame ->
      exists m' cv,
      eval_funcall prog_genv m fn (Vptr tinfo_b tinfo_o :: firstn n_param cvs) Events.E0 m' cv /\
      (** and m' is a valid mem, the addresses of the args array and each frame and root array in
          the shadow stack are preserved across the call, the shadow stack is related to its L6
          counterpart at level j, and the result cv is related to v at level (j - i) *)
      m' |=
        (∃ args cvss, valid_mem tinfo_b tinfo_o args_b args_o args frame_addrs root_addrs cvss
         where rel_shadow_stack j vss m' cvss) ⋆
        frame /\
      rel_val (j - to_nat cin) v m' cv
    end
  | _, _ => False
  end.

End CycleBreakers.

(** L6 values are related to (C value, heap) pairs *)
Fixpoint rel_val (k : nat) := fun v '(m, cv) => 
  rel_val_aux (fun k v m cv => rel_val k v (m, cv)) k v m cv.
Notation "v '~ᵥ{' k '}' cv" := (rel_val k v cv) (at level 80).

(** L6 (environment, term) pairs are related to Clight (environment, heap, statement) triples *)
Definition rel_exp (k : nat) := fun '(ρ, e) '(env, tenv, m, stmt) => 
  rel_exp' (fun k v m cv => rel_val k v (m, cv)) k ρ e env tenv m stmt.
Notation "e '~{' k '}' ce" := (rel_exp k e ce) (at level 80).

(** L6 environments are related to (temp environment, heap) pairs wrt a set of identifiers S.

    Note: we require all identifiers in ρ to be in the temp environment only.
    The local environment env is used by the bigstep semantics to hold values for function parameters.
    TODO To move these values into tenv, the code generator loads each parameter into a temporary on
    function entry.

    The reason env shows up at all, in rel_exp, is to support linking with hand-written C code.
    Someone may want to prove that their C code implements an L6 function; the extra env parameter
    will let them do that without having to rewrite their C code to put all function parameters
    into temporaries before using them. *)
Definition rel_env k := fun S ρ '(tenv, m) =>
  forall x, x \in S ->
  match! ρ!x with Some v in
  match! tenv!x with Some cv in
  v ~ᵥ{k} (m, cv).
Notation "ρ '~ₑ{' k ',' S '}' tenv" := (rel_env k S ρ tenv) (at level 80).
Notation "ρ '~ₑ{' k '}' tenv" := (rel_env k (fun _ => True) ρ tenv) (at level 80).

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
Lemma rel_val_eqn k v m cv :
  rel_val k v (m, cv) = rel_val_aux (fun k v m cv => rel_val k v (m, cv)) k v m cv.
Proof. now destruct k. Qed.

Arguments Z.mul : simpl never.
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
  rewrite !rel_val_eqn; destruct v as [t [|v vs] |ρ fds f|i].
  - auto.
  - cbn; destruct (get_ctor_rep _ _) as [| [tag|tag arity]] eqn:Hrep; auto.
    destruct cv; auto.
    intros [Hload Hforall]; split; [easy|].
    change (_ /\ All (mapi ?f 1 _)) with (All (mapi f 0 (v :: vs))) in *.
    pose proof @mapi_rel val Prop (fun P Q => P -> Q) and True as mapi_rel.
    specialize mapi_rel with (i := 0%Z) (xs := v :: vs).
    match goal with _ : All (mapi ?f' _ _) |- _ => specialize mapi_rel with (f := f') end.
    match goal with |- All (mapi ?g' _ _) => specialize mapi_rel with (g := g') end.
    apply mapi_rel; clear mapi_rel; [|tauto..].
    intros i' x Hin.
    destruct (load m b (O.unsigned i + i' * word_size))%Z; [|tauto].
    rewrite <- !rel_val_eqn; eapply IHsv; auto.
    subst sv; destruct Hin as [[] |Hin]; [cbn; lia|clear - Hin].
    induction vs as [|v' vs IHvs]; [easy|].
    destruct Hin as [[] |Hin]; [cbn; lia|cbn in *; specialize (IHvs Hin); lia].
  - simpl; destruct cv; auto.
    destruct (find_def f fds) as [[[f' xs] e] |] eqn:Hfind; auto.
    destruct (fenv ! f) as [[arity indices] |] eqn:Hindices; auto.
    intros [Hi_zero Hrest]; split; [easy|]; revert Hrest.
    intros [Hfind_symbol Hrest]; split; [easy|]; revert Hrest.
    admit. (* TODO *) (*
    match goal with |- context [if ?e1 then ?e2 else ?e3] =>
      change (if e1 then e2 else e3) with (Genv.find_funct prog_genv (Vptr b i));
      destruct (Genv.find_funct prog_genv (Vptr b i)) as [[fn|] |] eqn:Hfind_funct; auto
    end.
    intros Hfuture_call; intros*; intros Hlt; destruct j; [easy|].
    intros Hvs_firstn_ok Hcvs_firstn_ok Hvs_rest_ok Hcvs_rest_ok Hvs_related.
    intros Hextend_ρ Hextend_args Hextend_locals Hentry.
    replace (j - (j - j0)) with j0 in * by lia.
    destruct k as [|k]; [lia|].
    specialize Hfuture_call with (j := j0).
    replace (k - (k - j0)) with j0 in Hfuture_call by lia.
    eapply Hfuture_call; eauto; lia. *)
  - auto.
Admitted.

(*
Lemma rel_exp_antimon j k ρ e env tenv m stmt :
  j <= k ->
  (ρ, e) ~{k} (env, tenv, m, stmt) ->
  (ρ, e) ~{j} (env, tenv, m, stmt).
Proof.
  intros Hle Hk v; intros* Hcost Hbstep Hm.
  unfold rel_exp, rel_exp' in Hk.
  edestruct Hk as [tenv' [m' [cv H]]]; try apply Hm.
  edestruct Hk as [tenv' [m' [cv [Hsteps Hres]]]]; eauto; [lia|].
  exists tenv', m', cv; split; [eauto|].
  eapply rel_val_antimon; [|eassumption]; lia.
Qed.

Lemma rel_env_antimon j k S ρ tenv m :
  j <= k ->
  ρ ~ₑ{k, S} (tenv, m) ->
  ρ ~ₑ{j, S} (tenv, m).
Proof.
  intros Hle Hk x Hx; specialize (Hk x Hx).
  destruct (ρ ! x); [|easy].
  destruct (tenv ! x); [eapply rel_val_antimon; eauto|easy].
Qed.

Lemma rel_env_antimon_S k S1 S2 ρ tenv m :
  S1 \subset S2 ->
  ρ ~ₑ{k, S2} (tenv, m) ->
  ρ ~ₑ{k, S1} (tenv, m).
Proof. intros Hle Hk x Hx; now apply Hk, Hle. Qed.

(** ** Lemmas about the environment relation *)

Lemma rel_env_gss k S x v cv ρ tenv m :
  x \in S ->
  v ~ᵥ{k} (m, cv) ->
  ρ ~ₑ{k, S \\ [set x]} (tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (M.set x cv tenv, m).
Proof.
  intros Hin Hv Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [subst x'; now rewrite !M.gss|].
  rewrite !M.gso by auto.
  apply Hρ; constructor; [auto|now inversion 1].
Qed.

Lemma rel_env_gss_sing k x v cv ρ tenv m :
  v ~ᵥ{k} (m, cv) ->
  M.set x v ρ ~ₑ{k, [set x]} (M.set x cv tenv, m).
Proof.
  intros Hv x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [|now inv Hx'].
  subst x'; now rewrite !M.gss.
Qed.

Lemma rel_env_gso k S x v cv ρ tenv m :
  ~ x \in S ->
  ρ ~ₑ{k, S} (tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (M.set x cv tenv, m).
Proof.
  intros Hin Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [easy|].
  rewrite !M.gso by auto. now apply Hρ.
Qed.

Lemma rel_env_union k S1 S2 ρ tenv m :
  ρ ~ₑ{k, S1 :|: S2} (tenv, m) <->
  ρ ~ₑ{k, S1} (tenv, m) /\ ρ ~ₑ{k, S2} (tenv, m).
Proof.
  split; [intros HS12|intros [HS1 HS2]].
  - split; intros x Hx; now apply HS12.
  - intros x Hx; inv Hx; [apply HS1|apply HS2]; easy.
Qed.

(** ** λ-ANF reductions preserve relatedness *)

Ltac solve_rel_exp_reduction :=
  unfold rel_exp, rel_exp'; intros Hweaker v cin cout Hk Hbstep;
  inv Hbstep; match goal with | H : bstep _ _ _ _ _ _ |- _ => inv H end;
  rewrite to_nat_add in *;
  edestruct Hweaker as [tenv' [m' [cv [Hstep Hresult]]]]; [idtac..|eassumption|]; [idtac..|lia|]; eauto;
  do 3 eexists; split; eauto;
  eapply rel_val_antimon; [|eauto]; lia.

Lemma rel_exp_constr k ρ x c ys e env tenv m stmt :
  (forall vs,
    get_list ys ρ = Some vs ->
    (M.set x (Vconstr c vs) ρ, e) ~{k} (env, tenv, m, stmt)) ->
  (ρ, Econstr x c ys e) ~{k} (env, tenv, m, stmt).
Proof. solve_rel_exp_reduction. Qed.

Lemma rel_exp_proj k ρ x c n y e env tenv m stmt :
  (forall vs v,
    ρ!y = Some (Vconstr c vs) ->
    nthN vs n = Some v ->
    (M.set x v ρ, e) ~{k} (env, tenv, m, stmt)) ->
  (ρ, Eproj x c n y e) ~{k} (env, tenv, m, stmt).
Proof. solve_rel_exp_reduction. Qed.

Lemma rel_exp_case k ρ x ces env tenv m stmt :
  (forall c vs n e,
    ρ!x = Some (Vconstr c vs) ->
    cps_util.caseConsistent cenv ces c ->
    cps_util.find_tag_nth ces c e n ->
    (ρ, e) ~{k} (env, tenv, m, stmt)) ->
  (ρ, Ecase x ces) ~{k} (env, tenv, m, stmt).
Proof. solve_rel_exp_reduction. Qed.

Lemma rel_exp_app k ρ f t ys env tenv m stmt :
  (forall k_f ρ_f fds f' vs xs e ρ_f_xvs,
    k = S k_f ->
    ρ!f = Some (Vfun ρ_f fds f') ->
    get_list ys ρ = Some vs ->
    find_def f' fds = Some (t, xs, e) ->
    set_lists xs vs (def_funs fds fds ρ_f ρ_f) = Some ρ_f_xvs ->
    (ρ_f_xvs, e) ~{k_f} (env, tenv, m, stmt)) ->
  (ρ, Eapp f t ys) ~{k} (env, tenv, m, stmt).
Proof.
  intros Hsimpler v cin cout Hk Heval; inv Heval; inv H.
  rewrite to_nat_add in *; specialize (one_app_nonzero f t ys).
  assert (to_nat cin0 <= k - 1) by lia.
  assert (Hk_f : exists k_f, k = S k_f) by (destruct k as [|k]; [|exists k]; lia).
  destruct Hk_f as [k_f Heq].
  edestruct Hsimpler as [tenv' [m' [cv [Heval' Hresult]]]]; eauto; try lia.
  exists tenv', m', cv; split; [auto|].
  eapply rel_val_antimon; [|eauto]; lia.
Qed.

Lemma rel_exp_prim k ρ x p ys e env tenv m stmt :
  (ρ, Eprim x p ys e) ~{k} (env, tenv, m, stmt).
Proof. intros v cin cout Hk Hrun; inv Hrun; inv H. Qed.

(** ** Clight reductions preserve relatedness *)

Lemma rel_exp_Cred env' tenv' m' stmt' k ρ e env tenv m stmt :
  (env, tenv, m, stmt) --> (env', tenv', m', stmt') ->
  (ρ, e) ~{k} (env', tenv', m', stmt') ->
  (ρ, e) ~{k} (env, tenv, m, stmt).
Proof.
  unfold rel_exp; intros Hsimple_step Hrel v cin cout Hk Hbstep.
  edestruct Hrel as [tenv'' [m'' [cv [Hstep2_after Hres]]]]; eauto.
  (do 3 eexists); eauto.
Qed.

(** Fully right-associate all [;]s *)
Ltac norm_seq := repeat progress (eapply rel_exp_Cred; [apply Cred_seq_assoc|]).

(** Step from _ ~{k} (env, tenv, m, s) to _ ~{k} (env, tenv', m', s')
    using [lemma : (env, tenv, m, s) --> (env, tenv', m', s')] *)
Ltac Cstep lemma := eapply rel_exp_Cred; [eapply lemma|].

(** * Main theorem *)

Arguments rel_val : simpl never.
Arguments rel_exp : simpl never.
Arguments rel_env : simpl never.

Ltac normalize_occurs_free_in H :=
  eapply rel_env_antimon_S in H; [|normalize_occurs_free; apply Included_refl].

Lemma translate_body_stm locals nenv k : forall e,
  match translate_body cenv fenv locals nenv e with
  | Ret (stmt, _, _) => forall ρ env tenv m,
    ρ ~ₑ{k, occurs_free e} (tenv, m) ->
    (* TODO: extra assumptions *)
    (ρ, e) ~{k} (env, tenv, m, stmt)
  | _ => True
  end.
Proof.
  (* TODO: induction on step index by not be necessary *)
  induction k as [k IHk] using lt_wf_ind; fix IHe 1; destruct e.
  - (* let x = Con c ys in e *)
    rename v into x, l into ys; cbn.
    bind_step rep Hrep; destruct rep as [t|t a]; rewrite bind_ret.
    + (* Unboxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      intros ρ env tenv m Hρ.
      apply rel_exp_constr; intros vs Hget.
      Cstep Cred_set; [constructor|].
      specialize (IHe e); rewrite He in IHe; apply IHe. Guarded.
      eapply rel_env_antimon_S; [apply (Included_Union_Setminus _ [set x]); sets|].
      normalize_occurs_free_in Hρ.
      rewrite rel_env_union in Hρ; destruct Hρ as [_ Hρ].
      rewrite rel_env_union; split; [apply rel_env_gso; [intros Hin; now inv Hin|auto] |].
      apply rel_env_gss_sing; rewrite rel_val_eqn; cbn; now rewrite Hrep.
    + (* Boxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      intros ρ env tenv m Hρ.
      apply rel_exp_constr; intros vs Hget.
      norm_seq; Cstep Cred_set.
      { admit. }
      Cstep Cred_set.
      { admit. }
      Cstep Cred_assign.
      (* TODO:
           Want assumption like
             state_ok env tenv m
           containing all the invariants we need the state to satisfy during execution
           - limit..alloc is disjoint from the rest of the heap and writable
           - alloc = tinfo->alloc
           - limit = tinfo->limit
           - tinfo contains shadow stack
           - etc
           Then can prove lemmas of the form
             state_ok env tenv m
             --------------------------------------
             ∃ b o, (env, tenv, a) ⇓ᵣ (b, o) /\ ...
           to solve the obligations needed to step through each statement. *)
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      admit.
  - (* case x of { ces } *)
    rename v into x, l into ces; cbn.
    bind_step ces' Hces; destruct ces' as [[[boxed_cases unboxed_cases] fvs_cs] n_cs].
    intros* Hρ; Cstep Cred_if'.
    { admit. }
    { admit. }
    revert boxed_cases unboxed_cases fvs_cs n_cs Hces ρ env tenv m Hρ.
    induction ces as [| [c e] ces IHces]; intros*; [inv Hces; intros; now apply rel_exp_case|].
    apply rel_exp_case; intros c' vs n e_taken Hx Hconsistent Hfind_tag.
    rename Hces into Hceces; cbn in Hceces. 
    bind_step_in Hceces e' He; destruct e' as [[stm_e fvs_e] n_e].
    bind_step_in Hceces ces' Hces; destruct ces' as [[[boxed_cases' unboxed_cases'] fvs_ces] n_ces].
    bind_step_in Hceces rep Hrep; destruct rep as [t|t a]; inv Hceces.
    + (* New case arm is unboxed *)
      (* If e = e_taken, IHe gives e ~ stm_e.
         Otherwise, switch body is equivalent to unboxed_cases', and can use IHces. *)
      admit.
    + (* New case arm is boxed *)
      (* Same idea as in previous subcase *) admit.
  - (* let x = Proj c n y in e *)
    rename v into x, v0 into y; cbn.
    bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
    intros* Hρ; apply rel_exp_proj; intros* Hy Hproj.
    Cstep Cred_set.
    { admit. }
    specialize (IHe e); rewrite He in IHe; apply IHe. Guarded.
    eapply rel_env_antimon_S; [apply (Included_Union_Setminus _ [set x]); sets|].
    normalize_occurs_free_in Hρ.
    rewrite rel_env_union in Hρ; destruct Hρ as [_ Hρ].
    rewrite rel_env_union; split; [apply rel_env_gso; [intros Hin; now inv Hin|auto] |].
    apply rel_env_gss_sing.
    admit.
  - (* let x = f ft ys in e *)
    rename v into x, v0 into f, f into ft, l into ys; cbn.
    bind_step e' He; destruct e' as [[stm_e live_after_call] n_e].
    bind_step call Hcall; intros* Hρ.
    norm_seq.
    admit.
    (* idea: we get from the call that the values in the shadow stack are preserved.
       (that is, if stack represents vs before call then stack still represents vs after call.)
       this includes all of the variables live after the call (except x, which isn't defined yet)
       we then push x onto the shadow stack, and maybe call gc.
       gc spec will say that all the values on the shadow stack are preserved.
       this includes, again, all the variables live after the call.
       thus ρ is still related to the heap wrt fvs(e) and we can instantiate IHe accordingly *)
  - (* let rec fds in e *) exact I.
  - (* f ft ys *)
    rename v into f, f into ft, l into ys; cbn.
    bind_step call Hcall; intros* Hρ.
    apply rel_exp_app; intros* -> Hfun Hget_ys Hfind_def Hset_lists.
    (* TODO: lemma about make_fun_call *)
    admit.
  - (* let x = Prim p ys in e *)
    rename v into x, l into ys; cbn.
    bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
    intros* Hρ; apply rel_exp_prim.
  - (* halt x *)
    rename v into x; cbn; intros* Hρ.
    norm_seq; Cstep Cred_assign.
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    Cstep Cred_assign.
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    (* TODO: lemma rel_exp_halt
                ρ(x) ~ᵥ{k} (m, args[1])
         ---------------------------------------
         (ρ, Ehalt x) ~{k} (env, tenv, m, Sskip) *)
    admit.
Abort.
*)

End PROOF.

End CODEGEN.

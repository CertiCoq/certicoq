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

Section CODEGEN.

Definition mapi {A B} (f : N -> A -> B) :=
  fix go (n : N) (xs : list A) : list B :=
    match xs with
    | [] => []
    | x :: xs => f n x :: go (n + 1)%N xs
    end.

(* We only translate hoisted terms *)
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

(* The number of parameters to be passed as C function parameters *)
Variable (n_param : nat).

(* The size of the args array. No function can take more than max_args parameters. *)
Definition max_args := 1024%Z.

(* fun_env holds mappings
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
    compute_fun_env' (M.set f (N.of_nat (length ys), mapi (fun n _ => n) 0 ys) fenv) e'
  | Efun fds e' =>
    let fenv := compute_fun_env_fundefs fds fenv in
    compute_fun_env' fenv e'
  | Eapp f t ys => M.set f (N.of_nat (length ys), mapi (fun n _ => n) 0 ys) fenv
  | Eprim x p ys e' => compute_fun_env' fenv e'
  | Ehalt x => fenv
  end
with compute_fun_env_fundefs fds fenv : fun_env :=
  match fds with
  | Fnil => fenv
  | Fcons f t ys e fds' =>
    let fenv := M.set f (N.of_nat (length ys), mapi (fun n _ => n) 0 ys) fenv in
    let fenv := compute_fun_env' fenv e in
    compute_fun_env_fundefs fds' fenv
  end.
Definition compute_fun_env : hoisted_exp -> fun_env :=
  fun '(fds, e) => compute_fun_env' (M.empty _) (Efun fds e).

(* Max number of words allocated by e up to the next function call.
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

(* typedef intnat value; (See values.h, config.h)

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

(* struct thread_info {
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

(* struct stack_frame {
     value *next;
     value *root;
     struct stack_frame *prev;
   }; *)
Context (stack_frame_id next_fld root_fld prev_fld : ident).
Notation stack_frame := (Tstruct stack_frame_id noattr).

(* Declarations for the above structs, in abstract syntax *)
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

(* Each generated function takes a (struct thread_info *tinfo) as argument *)
Context (tinfo_id : ident).
Definition tinfo := Etempvar tinfo_id threadInf.
Definition tinfd := Ederef tinfo threadStructInf.
Notation "tinfo->alloc" := (Efield tinfd alloc_id (tptr value)).
Notation "tinfo->limit" := (Efield tinfd limit_id (tptr value)).
Notation "tinfo->args" := (Efield tinfd args_id (Tarray value max_args noattr)).
Notation "tinfo->fp" := (Efield tinfd fp_id (tptr stack_frame)).
Notation "tinfo->nalloc" := (Efield tinfd nalloc_id value).

(* Each generated function body declares the following local variables:
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

(* Each generated function body also declares the following local variables:
     value *alloc;
     value *limit; *)
Definition alloc := Etempvar alloc_id (tptr value).
Definition limit := Etempvar limit_id (tptr value).

(* Variable (isptr_id : ident). (* ident for the is_ptr external function *) *)

(* void garbage_collect(struct thread_info *tinfo);
   struct thread_info *make_tinfo(void);
   value *export(struct thread_info *ti); *)
Variable (gc_id : ident).
Definition gc := Evar gc_id (Tfunction (Tcons threadInf Tnil) Tvoid cc_default).
Definition make_tinfo_ty := Tfunction Tnil threadInf cc_default.
Definition export_ty := Tfunction (Tcons threadInf Tnil) (tptr value) cc_default.
Variable (body_id : ident).

Variable (builtin_unreachable_id : ident).
Definition builtin_unreachable : statement :=
  let f := Evar builtin_unreachable_id (Tfunction Tnil Tvoid cc_default) in
  Scall None f nil.

(* fun_ty n = void(struct thread_info *ti, value, .. min(n_param, n) times)
   prim_ty n = value(value, .. n times) *)
Definition value_tys (n : nat) : typelist := Nat.iter n (Tcons value) Tnil.
Definition fun_ty (n : nat) := Tfunction (Tcons threadInf (value_tys (min n_param n))) Tvoid cc_default.
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
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| enum : N -> ctor_rep
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)
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

(* To use variables in Clight expressions, need variable name and its type.
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
  (* if f is a function with arity |locs|, then x has function type *)
  | Some (_, locs) => Ecast (Evar x (fun_ty (length locs))) value
  (* otherwise, x is just a regular variable *)
  | None => var x
  end.

Section Body.

Context
  (locals : FVSet) (* The set of local variables including definitions and arguments *)
  (nenv : M.t BasicAst.name).

Definition make_fun_call (tail_position : bool) f ys :=
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
           Scall None
                 (Ecast (make_var f) (Tpointer (fun_ty (min arity n_param)) noattr))
                 (tinfo :: map make_var (firstn n_param ys));
           match tail_position with true => Sskip | false =>
             alloc_id ::= tinfo->alloc;
             limit_id ::= tinfo->limit
           end)
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

(* Use limit and alloc to check whether the nursery contains n words of free space.
   If not, invoke GC. *)
Definition create_space (n : nat) : statement :=
  let n := c_int (Z.of_nat n) value in 
  Sifthenelse
    (limit -' alloc <' n)
    (tinfo->alloc :::= alloc;
     tinfo->limit :::= limit;
     tinfo->nalloc :::= n;
     Scall None gc (tinfo :: nil);
     alloc_id ::= tinfo->alloc;
     limit_id ::= tinfo->limit)
    Sskip.

(* fvs ∪ ({x} ∩ locals) *)
Definition add_local_fv fvs x := if PS.mem x locals then PS.add x fvs else fvs.
Definition add_local_fvs fvs xs := fold_left add_local_fv xs fvs.

(* Returns (C code for e, FV(e) ∩ locals, number of stack slots needed) 
   Number of stack slots needed = 
     max(|FV(e')∩locals| for each Eletapp x f t ys e' we encounter in e) *)
Fixpoint translate_body (e : exp) {struct e} : error (statement * FVSet * N) :=
  match e with
  (* [[let x = Con c ys in e]] =
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
             statements (mapi (fun n y => (var x).[Z.of_N n] :::= make_var y) 0 ys))
      end ;;
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((stm_constr; stm_e), add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (* [[Ecase x cs]] = 
       if (isptr(x)) { switch on x[-1]&255 over boxed cases } 
       else { switch on x>>1 over unboxed cases } *)
  | Ecase x cs =>
    '(boxed_cases, unboxed_cases, fvs_cs, n_cs) <- make_cases translate_body cs ;;
    ret (Sifthenelse
          (var x &' make_cint 1 value ==' make_cint 0 value)
          (Sswitch ((var x).[-1] &' make_cint 255 value) boxed_cases)
          (Sswitch (var x >>' make_cint 1 value) unboxed_cases),
         add_local_fv fvs_cs x, n_cs)
  (* [[let x = f(y, ..) in e]] =
       push local variables live after call (= locals∩(FV(e)\x)) onto frame
       push frame onto shadow stack
       call f (may GC)
       x = args[1]
       if max_allocs(e) > 0,
         if x is live after the call (<-> x ∈ locals∩FV(e)), push it onto frame
         use GC to create max_allocs(e) words of free space on the heap
         if x was pushed, pop x out of frame (in case it was moved by GC)
       pop locals out of frame (in case they were moved by GC)
       pop frame from shadow stack
       [[e]] *)
  | Eletapp x f t ys e =>
    '(stm_e, live_after_call, n_e) <- translate_body e ;;
    let live_minus_x := PS.remove x live_after_call in
    let live_minus_x_list := PS.elements live_minus_x in
    let n_live_minus_x := Z.of_nat (length live_minus_x_list) in
    call <- make_fun_call false f ys ;;
    let retrieve_roots xs := statements (mapi (fun n x => x ::= roots.[Z.of_N n]) 0 xs) in
    let stm :=
      statements (mapi (fun n x => roots.[Z.of_N n] :::= var x) 0 live_minus_x_list);
      frame.next :::= roots +' c_int n_live_minus_x value;
      tinfo->fp :::= &frame;
      call;
      x ::= tinfo->args.[1];
      match max_allocs e with 0 => Sskip | S _ as allocs =>
        let x_live := PS.mem x live_after_call in
        match x_live with false => Sskip | true =>
          roots.[n_live_minus_x] :::= var x;
          frame.next :::= roots +' c_int (1 + n_live_minus_x) value
        end;
        create_space allocs;
        if x_live then x ::= roots.[n_live_minus_x] else Sskip
      end;
      retrieve_roots live_minus_x_list;
      tinfo->fp :::= frame.prev;
      stm_e
    in
    ret (stm, add_local_fvs live_minus_x (f :: ys),
         N.max n_e (N.of_nat (PS.cardinal live_after_call)))
  (* [[let x = y.n in e]] = (x = y[n]; [[e]]) *)
  | Eproj x t n y e =>
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((x ::= (var y).[Z.of_N n]; stm_e), add_local_fv (PS.remove x fvs_e) y, n_e)
  | Efun fnd e => Err "translate_body: nested function detected"
  (* [[f(ys)]] = call f *)
  | Eapp f t ys =>
    call <- make_fun_call true f ys ;;
    ret (call, add_local_fvs PS.empty (f :: ys), 0)%N
  (* [[let x = p(ys) in e]] = (x = p(ys); [[e]]) *)
  | Eprim x p ys e =>    
    '(stm_e, fvs_e, n_e) <- translate_body e ;;
    ret ((Scall (Some x) (Evar p (prim_ty (length ys))) (map make_var ys);
          stm_e),
         add_local_fvs (PS.remove x fvs_e) ys, n_e)
  (* [[halt x]] = (args[1] = x; store alloc and limit in tinfo) *)
  | Ehalt x =>
    ret ((tinfo->args.[1] :::= make_var x;
          tinfo->alloc :::= alloc;
          tinfo->limit :::= limit),
         add_local_fv PS.empty x, 0)%N
  end.

End Body.

Definition definition := (ident * globdef Clight.fundef type)%type.

Definition make_fun (size : Z) (xs locals : list ident) (body : statement) : function :=
  let make_decls := map (fun x => (x, value)) in
  mkfunction Tvoid cc_default
             ((tinfo_id, threadInf) :: make_decls (firstn n_param xs))
             (make_decls (skipn n_param xs ++ locals) ++ stack_decl size ++
              (alloc_id, tptr value) :: (limit_id, tptr value) :: (args_id, tptr value) :: nil)%list
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
      (* [[f(xs.., ys..) = e]] (where |xs| = n_param) =
           void f(thread struct_info *tinfo, value x, ..) {
             alloc = tinfo->alloc;
             limit = tinfo->limit;
             args = tinfo->args;
             For n_param <= i < |xs|+|ys|,
               y_i = args[locs_i];
             initialize shadow stack frame
             if max_allocs(e) > 0,
               push locals live in e onto frame
               push frame onto shadow stack
               use GC to create max_allocs(e) words of free space on the heap
               pop locals out of frame
               pop frame from shadow stack
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
        args_id ::= tinfo->args;
        statements (map (fun '(x, i) => x ::= tinfo->args.[Z.of_N i]) (skipn n_param (combine xs locs)));
        init_shadow_stack_frame;
        match allocs with 0 => Sskip | S _ as allocs =>
          statements (mapi (fun n x => roots.[Z.of_N n] :::= var x) 0 live_xs_list);
          frame.next :::= roots +' c_int (Z.of_N n_live_xs) value;
          tinfo->fp :::= &frame;
          create_space allocs;
          statements (mapi (fun n x => x ::= roots.[Z.of_N n]) 0 live_xs_list);
          tinfo->fp :::= frame.prev
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

(* [[let rec fds in e]] =
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
       return tinfo->args[1];
     } *)
Definition translate_program (fds_e : hoisted_exp) (nenv : name_env) : error (list definition) :=
  let '(fds, e) := fds_e in
  let locals := PS.elements (exp_bv e) in
  funs <- translate_fundefs fds nenv ;;
  '(body, _, slots) <- translate_body (union_list PS.empty locals) nenv e ;;
  let body :=
    alloc_id ::= tinfo->alloc;
    limit_id ::= tinfo->limit;
    args_id ::= tinfo->args;
    init_shadow_stack_frame;
    match max_allocs e with 0 => Sskip | S _ as allocs =>
      create_space (max_allocs e)
    end;
    body;
    Sreturn (Some (tinfo->args.[1]))
  in
  let locals :=
    (map (fun x => (x, value)) locals ++
     stack_decl (Z.of_N slots) ++ 
     (alloc_id, tptr value) :: 
     (limit_id, tptr value) :: 
     (args_id, tptr value) :: 
     nil)%list
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
  (builtin_unreachable_id, nNamed "__builtin_unreachable") :: nil.

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
  let ext_fn := EF_external "body" (signature_of_type param_tys Tvoid cc_default) in
  (body_id, Gfun (External ext_fn param_tys Tvoid cc_default)).

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

Variable (pr : prims).
Variable (cenv : ctor_env).
Variable (fenv : fun_env).

(* The C program produced by the code generator *)
Variable (prog : program).

(* Its global environment *)
Let prog_genv : genv := globalenv prog.

Definition make_vint (z : Z) : Values.val :=
  if Archi.ptr64
  then Vlong (Int64.repr z)
  else Values.Vint (Int.repr z).

Fixpoint closed_val (v : cps.val) :=
  match v with
  | Vconstr c vs => fold_right (fun v P => closed_val v /\ P) True vs
  | Vfun ρ fds f => M.bempty ρ = true
  | Vint _ => True
  end.

Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
Definition int_size := size_chunk int_chunk.
Definition header_offset o := Ptrofs.unsigned (Ptrofs.sub o (Ptrofs.repr int_size)).
Definition index_offset o i := Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (int_size * i))).

(** * Tools for reasoning about Clight *)

(* Bigstep evaluation of statements: unlike exec_stmt,
   - Force the trace to be empty
   - Force outcome to be Out_normal (i.e., statement can't exit early
     via return/break/continue) *)
Definition texec := fun '(env, tenv, m, stmt) '(tenv', m') =>
  exec_stmt prog_genv env tenv m stmt Events.E0 tenv' m' Out_normal.
Infix "⇓" := texec (at level 80, no associativity).

(* Similar notations for bigstep evaluation of l- and r-values *)
Definition eval_expr_operator := fun '(env, tenv, m, e) v =>
  eval_expr prog_genv env tenv m e v.
Definition eval_lvalue_operator := fun '(env, tenv, m, e) '(b, o) =>
  eval_lvalue prog_genv env tenv m e b o.
Infix "⇓ᵣ" := eval_expr_operator (at level 80).
Infix "⇓ₗ" := eval_lvalue_operator (at level 80).

(** ** "Reductions" in machine state *)

(* (env1, tenv1, m1, stmt1) "reduces to" (env2, tenv2, m2, stmt2) if every terminating
   execution starting from (env2, tenv2, m2, stmt2) can be used to construct an execution
   starting from (env1, tenv1, m1, stmt1) *)
Definition Clight_state_red := fun '(env1, tenv1, m1, stmt1) '(env2, tenv2, m2, stmt2) =>
  forall tenv' m',
  (env2, tenv2, m2, stmt2) ⇓ (tenv', m') ->
  (env1, tenv1, m1, stmt1) ⇓ (tenv', m').
Infix "-->" := Clight_state_red (at level 80).

Lemma Cred_trans s1 s2 s3 :
  s1 --> s2 -> s2 --> s3 -> s1 --> s3.
Proof. destruct s1 as [[[??]?]?], s2 as [[[??]?]?], s3 as [[[??]?]?]; cbn; eauto. Qed.

Lemma Cred_seq_assoc s1 s2 s3 env tenv m :
  (env, tenv, m, ((s1; s2); s3)) --> (env, tenv, m, (s1; (s2; s3))).
Proof.
  intros tenv' m' Hs123; inv Hs123; [|contradiction].
  inv H9; [|contradiction].
  unfold "⇓"; rewrite <- H4, <- Events.Eapp_assoc; repeat (eapply exec_Sseq_1; eauto).
Qed.

Lemma Cred_skip env tenv m s :
  (env, tenv, m, (Sskip; s)) --> (env, tenv, m, s).
Proof.
  intros tenv' m' Hexec.
  unfold "⇓"; change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; [constructor|eauto].
Qed.

Lemma Cred_set env tenv m x a v s :
  (env, tenv, m, a) ⇓ᵣ v ->
  (env, tenv, m, (x ::= a; s)) --> (env, M.set x v tenv, m, s).
Proof.
  intros Heval tenv' m' Hexec.
  unfold "⇓"; change Events.E0 with (Events.Eapp Events.E0 Events.E0).
  eapply exec_Sseq_1; [now constructor|eauto].
Qed.

Lemma Cred_if env tenv m a v b s1 s2 s :
  (env, tenv, m, a) ⇓ᵣ v ->
  bool_val v (typeof a) m = Some b ->
  (env, tenv, m, (Sifthenelse a s1 s2; s)) -->
  (env, tenv, m, ((if b then s1 else s2); s)).
Proof.
  intros Heval Hbool tenv' m' Hexec.
  unfold "⇓" in *; inv Hexec; [|easy].
  eapply exec_Sseq_1; [econstructor|]; eauto.
Qed.

(** ** Address spaces *)

Definition addrs := Ensemble (block * Z).
Definition Addrs m : addrs := fun '(b, o) => exists chunk v, Mem.load chunk m b o = Some v.

(** * Logical relation between λ-ANF and Clight *)

Notation "'match!' e1 'with' p 'in' e2" :=
  (match e1 with p => e2 | _ => False end)
  (at level 80, p pattern, e1 at next level, right associativity).

Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

(* Bigstep evaluation of L6 terms *)
Definition bstep_res := fun '(ρ, e, cin) '(v, cout) =>
  bstep_fuel cenv ρ e cin (Res v) cout.
Infix "⇓cps" := bstep_res (at level 80).

Section CycleBreakers.

Context (rel_val : forall (k : nat) (v : cps.val) (m : Memory.mem) (cv : Values.val), Prop).

Definition rel_exp' k (ρ : env) (e : cps.exp) env tenv m stmt : Prop :=
  forall v (cin : fuel) (cout : trace),
  (* if running e in environment ρ yields a value v in j <= k cost, *)
  to_nat cin <= k ->
  (ρ, e, cin) ⇓cps (v, cout) ->
  exists tenv' m',
  (* then running stmt down to Sskip yields args[1] related to v at level k-j *)
  (env, tenv, m, stmt) ⇓ (tenv', m') /\
  match! tenv' ! args_id with Some (Vptr b o) in
  match! Mem.load int_chunk m' b (index_offset o 1) with Some cv' in
  rel_val (k - to_nat cin) v m' cv'.

Definition Forall' := fold_right and True.
Definition rel_val_aux (k : nat) :=
  fix go (v : cps.val) (m : Memory.mem) (cv : Values.val) : Prop :=
  match v, cv with
  | Vint v, cv => cv = make_vint (rep_unboxed (Z.to_N v))
  | Vconstr t [], cv =>
    match! get_ctor_rep cenv t with Ret (enum t) in
    cv = make_vint (rep_unboxed t)
  | Vconstr t vs, Vptr b o =>
    match! get_ctor_rep cenv t with Ret (boxed t a) in
    Mem.load int_chunk m b (header_offset o) = Some (make_vint (rep_boxed t a)) /\
    let arg_ok i v :=
      (* TODO: do we only ever load memory in int_chunk chunks? if so, can define as helper function *)
      match! Mem.load int_chunk m b (index_offset o (Z.of_N i)) with Some cv in
      go v m cv
    in Forall' (mapi arg_ok 0 vs)
  | Vfun ρ fds f, Vptr b o =>
    o = Ptrofs.zero /\
    match! find_def f fds with Some (t, xs, e) in
    match! fenv ! f with Some (arity, indices) in
    Genv.find_symbol prog_genv f = Some b /\
    match! Genv.find_funct prog_genv (Vptr b o) with Some (Internal fn) in
    forall j vs m cvs ρ_xvs env tenv m_cvs_firstn args_b args_o,
    j < k ->
    match k with
    | 0 => True
    | S k =>
      (* suppose that f is called with arguments vs and fn with arguments cvs, and that vs
         and cvs are related at level j<k (written as k-(k-j) to convince Coq of well-foundedness). *)
      let j := k-(k-j) in
      Forall2 (fun v cv => rel_val j v m cv) vs cvs ->
      (* if extend ρ with xs↦vs... *)
      set_lists xs vs (def_funs fds fds ρ ρ) = Some ρ_xvs ->
      (* and extend the C configuration with xs↦cvs... *)
      tenv ! args_id = Some (Vptr args_b args_o) ->
      let arg_ok cv i := Mem.load int_chunk m args_b (index_offset args_o (Z.of_N i)) = Some cv in
      Forall2 arg_ok (skipn n_param cvs) (skipn n_param indices) ->
      function_entry1 prog_genv fn (firstn n_param cvs) m env tenv m_cvs_firstn ->
      (* then e is related to the body of fn at level j *)
      rel_exp' j ρ e env tenv m_cvs_firstn (fn_body fn)
    end
  | _, _ => False
  end.

End CycleBreakers.

(* L6 values are related to (C value, heap) pairs *)
Fixpoint rel_val (k : nat) := fun v '(m, cv) => 
  rel_val_aux (fun k v m cv => rel_val k v (m, cv)) k v m cv.
Notation "v '~ᵥ{' k '}' cv" := (rel_val k v cv) (at level 80).

(* L6 (environment, term) pairs are related to Clight (environment, heap, statement) triples *)
Definition rel_exp (k : nat) := fun '(ρ, e) '(env, tenv, m, stmt) => 
  rel_exp' (fun k v m cv => rel_val k v (m, cv)) k ρ e env tenv m stmt.
Notation "e '~{' k '}' ce" := (rel_exp k e ce) (at level 80).

(* L6 environments are related to (environment, heap) pairs wrt a set of identifiers S *)
Definition rel_env k := fun S ρ '(env, tenv, m) =>
  forall x, x \in S ->
  match! ρ!x with Some v in
  match tenv!x with
  | Some v' => v ~ᵥ{k} (m, v')
  | None =>
    match! env!x : option (_ * type) with Some (b, _) in
    v ~ᵥ{k} (m, Vptr b Ptrofs.zero)
  end.
Notation "ρ '~ₑ{' k ',' S '}' cρ" := (rel_env k S ρ cρ) (at level 80).
Notation "ρ '~ₑ{' k '}' cρ" := (rel_env k (fun _ => True) ρ cρ) (at level 80).

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
  - cbn; destruct cv; auto; destruct (get_ctor_rep _ _) as [| [|tag arity]] eqn:Hrep; auto.
    intros [Hload Hforall]; split; [easy|].
    change (_ /\ Forall' (mapi ?f 1 _)) with (Forall' (mapi f 0 (v :: vs))) in *.
    pose proof @mapi_rel val Prop (fun P Q => P -> Q) and True as mapi_rel.
    specialize mapi_rel with (i := 0%N) (xs := v :: vs).
    match goal with _ : Forall' (mapi ?f' _ _) |- _ => specialize mapi_rel with (f := f') end.
    match goal with |- Forall' (mapi ?g' _ _) => specialize mapi_rel with (g := g') end.
    apply mapi_rel; clear mapi_rel; [|tauto..].
    intros i' x Hin.
    destruct (Mem.load _ m b (index_offset i (Z.of_N i'))); [|tauto].
    rewrite <- !rel_val_eqn; eapply IHsv; auto.
    subst sv; destruct Hin as [[] |Hin]; [cbn; lia|clear - Hin].
    induction vs as [|v' vs IHvs]; [easy|].
    destruct Hin as [[] |Hin]; [cbn; lia|cbn in *; specialize (IHvs Hin); lia].
  - simpl; destruct cv; auto.
    destruct (find_def f fds) as [[[f' xs] e] |] eqn:Hfind; auto.
    destruct (fenv ! f) as [[arity indices] |] eqn:Hindices; auto.
    intros [Hi_zero Hrest]; split; [easy|]; revert Hrest.
    intros [Hfind_symbol Hrest]; split; [easy|]; revert Hrest.
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
    eapply Hfuture_call; eauto; lia.
  - auto.
Qed.

Lemma rel_exp_antimon j k ρ e env tenv m stmt :
  j <= k ->
  (ρ, e) ~{k} (env, tenv, m, stmt) ->
  (ρ, e) ~{j} (env, tenv, m, stmt).
Proof.
  intros Hle Hk v cin cout Hcost Hbstep.
  edestruct Hk as [tenv' [m' [Hsteps Hres]]]; eauto; [lia|].
  exists tenv', m'; split; [eauto|].
  destruct (tenv' ! args_id) as [[] |]; try contradiction.
  destruct (Mem.load _ _ _ _); try contradiction.
  eapply rel_val_antimon; [|eassumption]; lia.
Qed.

Lemma rel_env_antimon j k S ρ env tenv m :
  j <= k ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  ρ ~ₑ{j, S} (env, tenv, m).
Proof.
  intros Hle Hk x Hx; specialize (Hk x Hx).
  destruct (ρ ! x); [|easy].
  destruct (tenv ! x); [eapply rel_val_antimon; eauto|].
  destruct (env ! x) as [[] |]; [|easy].
  eapply rel_val_antimon; eauto.
Qed.

Lemma rel_env_antimon_S k S1 S2 ρ env tenv m :
  S1 \subset S2 ->
  ρ ~ₑ{k, S2} (env, tenv, m) ->
  ρ ~ₑ{k, S1} (env, tenv, m).
Proof. intros Hle Hk x Hx; now apply Hk, Hle. Qed.

(** ** Lemmas about the environment relation *)

Lemma rel_env_gss k S x v cv ρ env tenv m :
  x \in S ->
  v ~ᵥ{k} (m, cv) ->
  ρ ~ₑ{k, S \\ [set x]} (env, tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (env, M.set x cv tenv, m).
Proof.
  intros Hin Hv Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [subst x'; now rewrite !M.gss|].
  rewrite !M.gso by auto.
  apply Hρ; constructor; [auto|now inversion 1].
Qed.

Lemma rel_env_gss_sing k x v cv ρ env tenv m :
  v ~ᵥ{k} (m, cv) ->
  M.set x v ρ ~ₑ{k, [set x]} (env, M.set x cv tenv, m).
Proof.
  intros Hv x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [|now inv Hx'].
  subst x'; now rewrite !M.gss.
Qed.

Lemma rel_env_gso k S x v cv ρ env tenv m :
  ~ x \in S ->
  ρ ~ₑ{k, S} (env, tenv, m) ->
  M.set x v ρ ~ₑ{k, S} (env, M.set x cv tenv, m).
Proof.
  intros Hin Hρ x' Hx'.
  destruct (M.elt_eq x x') as [Heq|Hne]; [easy|].
  rewrite !M.gso by auto. now apply Hρ.
Qed.

Lemma rel_env_union k S1 S2 ρ env tenv m :
  ρ ~ₑ{k, S1 :|: S2} (env, tenv, m) <->
  ρ ~ₑ{k, S1} (env, tenv, m) /\ ρ ~ₑ{k, S2} (env, tenv, m).
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
  edestruct Hweaker as [tenv' [m' [Hstep Hresult]]]; [idtac..|eassumption|]; [idtac..|lia|]; eauto;
  do 2 eexists; split; eauto;
  destruct (tenv' ! args_id) as [[] |]; eauto;
  destruct (Mem.load _ _ _ _); eauto;
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
  (forall ρ_f fds f' vs xs e ρ_f_xvs,
    ρ!f = Some (Vfun ρ_f fds f') ->
    get_list ys ρ = Some vs ->
    find_def f' fds = Some (t, xs, e) ->
    set_lists xs vs (def_funs fds fds ρ_f ρ_f) = Some ρ_f_xvs ->
    (ρ_f_xvs, e) ~{k} (env, tenv, m, stmt)) ->
  (ρ, Eapp f t ys) ~{k} (env, tenv, m, stmt).
Proof. solve_rel_exp_reduction. Qed.

(** ** Clight reductions preserve relatedness *)

Lemma rel_exp_Cred env' tenv' m' stmt' k ρ e env tenv m stmt :
  (env, tenv, m, stmt) --> (env', tenv', m', stmt') ->
  (ρ, e) ~{k} (env', tenv', m', stmt') ->
  (ρ, e) ~{k} (env, tenv, m, stmt).
Proof.
  unfold rel_exp; intros Hsimple_step Hrel v cin cout Hk Hbstep.
  edestruct Hrel as [tenv'' [m'' [Hstep2_after Hres]]]; eauto.
Qed.

(* TODO: basically, want one rule for each C code fragment corresponding to an L6 reduction step *)

(** * Relating λ-ANF calls to Clight calls *)

(*

Lemma rel_exp_letapp_compat k ρ x f t ys e env tenv m stmt :
  (forall ρ_f fds f' vs xs e ρ_f_xvs v,
    ρ!f = Some (Vfun ρ_f fds f') ->
    get_list ys ρ = Some vs ->
    find_def f' fds = Some (t, xs, e_f) ->
    set_lists xs vs (def_funs fds fds ρ_f ρ_f) = Some ρ_f_xvs ->
    (ρ_f_xvs, e_f, cin) ⇓f (v, cout) ->
    (M.set x v ρ, e_f) ~{k} (env, tenv, m, stmt)) ->
  (ρ, Eletapp x f t ys e) ~{k} (env, tenv, m, stmt).
Proof. solve_rel_exp_reduction. Qed.

*)

(** * Main theorem *)

Lemma bind_ret {A B} x (f : A -> error B) : (x <- Ret x ;; f x) = f x.
Proof. reflexivity. Qed.

Arguments Monad.bind : simpl never.
Arguments add_local_fvs : simpl never.
Arguments exp_fv : simpl never.
Arguments PS.cardinal : simpl never.
Arguments rel_val : simpl never.
Arguments rel_exp : simpl never.
Arguments rel_env : simpl never.

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
    eapply FromSet_complete; eauto with Ensembles_DB.
  - assert (~ PS.In x locals) by (intros Hin'; now rewrite <- PS.mem_spec in Hin').
    assert (~ x \in FromSet locals) by (intros Hin'; now eapply FromSet_sound in Hin').
    rewrite Intersection_Disjoint; eauto with Ensembles_DB.
Qed.

Lemma add_local_fvs_ok locals fvs xs :
  FromSet (add_local_fvs locals fvs xs) <--> FromSet fvs :|: (FromList xs :&: FromSet locals).
Proof.
  revert fvs; induction xs as [|x xs IHxs]; intros fvs.
  - cbn; rewrite FromList_nil, Intersection_Empty_set_abs_l; eauto with Ensembles_DB.
  - unfold add_local_fvs in *; cbn; rewrite IHxs, add_local_fv_ok, FromList_cons.
    rewrite Intersection_Union_distr; eauto with Ensembles_DB.
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
    apply Same_set_Union_compat; eauto with Ensembles_DB;
    rewrite IHe, Intersection_extract_Setminus; eauto with Ensembles_DB.
  - cbn. bind_step cases Hcases; destruct cases as [[[??] fvs_cs] ?].
    rewrite add_local_fv_ok.
    revert dependent n; revert l0 l1 fvs_cs;
    induction l as [| [c e] ces IHces]; intros l0 l1 fvs_cs n Hcases; cbn in *.
    + inv Hcases; rewrite FromSet_empty; normalize_occurs_free; eauto with Ensembles_DB.
    + bind_step_in Hcases e' He'; destruct e' as [[? fvs_e] ?].
      bind_step_in Hcases ces' Hces'; destruct ces' as [[[??]fvs_ces]?].
      specialize (IHces _ _ _ _ eq_refl).
      bind_step_in Hcases rep Hrep.
      assert (fvs_cs = PS.union fvs_e fvs_ces) by (now destruct rep); subst.
      specialize (IHe locals nenv e); rewrite He' in IHe.
      normalize_occurs_free; rewrite FromSet_union, <- Union_assoc, IHces, IHe, !Intersection_Union_distr.
      split; repeat apply Union_Included; eauto with Ensembles_DB.
      eapply Included_trans; [|apply Included_Union_r].
      apply Included_Intersection_compat; eauto with Ensembles_DB.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    normalize_occurs_free; rewrite add_local_fv_ok, FromSet_remove, IHe.
    rewrite !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; eauto with Ensembles_DB.
    now rewrite Intersection_extract_Setminus.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    bind_step call Hcall; normalize_occurs_free.
    specialize (IHe locals nenv e); rewrite He in IHe.
    rewrite add_local_fvs_ok, FromSet_remove, IHe, FromList_cons, !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; eauto with Ensembles_DB.
    now rewrite Intersection_extract_Setminus.
  - exact I.
  - cbn. bind_step call Hcall. normalize_occurs_free.
    rewrite add_local_fvs_ok, FromList_cons, !Intersection_Union_distr, Union_commut, FromSet_empty.
    split; repeat apply Union_Included; eauto with Ensembles_DB.
  - cbn. bind_step e' He; destruct e' as [[? fvs_e]?].
    specialize (IHe locals nenv e); rewrite He in IHe.
    normalize_occurs_free; rewrite add_local_fvs_ok, FromSet_remove, IHe.
    rewrite !Intersection_Union_distr, Union_commut.
    apply Same_set_Union_compat; eauto with Ensembles_DB.
    now rewrite Intersection_extract_Setminus.
  - cbn. normalize_occurs_free; rewrite add_local_fv_ok, FromSet_empty; eauto with Ensembles_DB.
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

Lemma translate_body_stm locals nenv k : forall e,
  match translate_body cenv fenv locals nenv e with
  | Ret (stmt, _, _) => forall ρ env tenv m,
    ρ ~ₑ{k, occurs_free e} (env, tenv, m) ->
    (* TODO: extra assumptions *)
    (ρ, e) ~{k} (env, tenv, m, stmt)
  | _ => True
  end.
Proof.
  induction k as [k IHk] using lt_wf_ind; fix IHe 1; destruct e.
  - (* Econstr *)
    cbn. bind_step rep Hrep. destruct rep as [t|t a]; rewrite bind_ret.
    + (* Unboxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      intros ρ env tenv m Hρ.
      apply rel_exp_constr; intros vs Hget.
      eapply rel_exp_Cred; [apply Cred_set; now constructor|].
      specialize (IHe e); rewrite He in IHe; apply IHe. Guarded.
      eapply rel_env_antimon_S.
      { apply (Included_Union_Setminus _ [set v]); eauto with Decidable_DB. }
      rewrite rel_env_union; split; [|apply rel_env_gss_sing; auto].
      { eapply rel_env_antimon_S in Hρ; [|normalize_occurs_free; apply Included_refl].
        rewrite rel_env_union in Hρ; destruct Hρ as [_ Hρ].
        apply rel_env_gso; [intros Hin; now inv Hin|auto]. }
      rewrite rel_val_eqn; cbn.
      destruct vs. 2:{ admit. (* TODO: l can't be empty *) }
      now rewrite Hrep.
    + (* Boxed *)
      bind_step e' He; destruct e' as [[stm_e fvs_e] n_e].
      intros ρ env tenv m Hρ.
      apply rel_exp_constr; intros vs Hget.
      repeat progress (eapply rel_exp_Cred; [apply Cred_seq_assoc|]).
      eapply rel_exp_Cred; [apply Cred_set|].
      { admit. }
      admit.
Abort.

End PROOF.

End CODEGEN.

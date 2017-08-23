(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Animating the CompCert Clight semantics *)

Require Import String.
Require Import Axioms.
Require Import Classical.
Require Import Coqlib.
Require Import certiClasses.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require compcert.cfrontend.Cexec.  
Require Import Clight.
Require Import compcert.lib.Maps.


Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.
Import ListNotations.

Module M := Maps.PTree.







Fixpoint show_positive' (p:positive) (acc:string) : string :=
  match p with
  | xI p' =>  show_positive' p' (append "1" acc)
  | xO p' => show_positive' p' (append "0" acc)
  | xH => append "1" acc
  end.

Definition show_positive (p:positive) : string :=
    show_positive' p "". 


(* Variables are shown using "x" as a prefix if their original name is not known*)
Definition show_var (x:positive) nenv :=
  match M.get x nenv with
    | Some (Ast.nNamed s) => (s++("_")++(show_positive x))%string
    | _ => ("x" ++ (show_positive x))%string
  end.


Definition print_errcode (on: option (M.t Ast.name)) (e:errcode): string :=
  match e  with
  | MSG err => err
  | POS p => show_positive p
  | CTX id => match on with
              | None => append "ctx_noEnv" (show_positive id)
              | Some nenv => (show_var id nenv)
              end
  end.



(* Returns the concatenation of all error codes in errs. 
s is passed for when I figure out how to pretty-print id from the state *)
Fixpoint print_error (errs:errmsg) (os:option (M.t Ast.name)): string :=
  let errstr := map (print_errcode os) errs in
  fold_left append errstr "". 


(** * Events, volatile memory accesses, and external functions. *)

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition offset_val (ofs: Z) (v: val) : res val :=
  match v with
  | Vptr b z => OK (Vptr b (Int.add z (Int.repr ofs)))
  | _ => Error [MSG "Expected a pointer"]
 end.

Definition force_ptr (v: val) : res val :=
          match v with
          | Vptr l ofs => OK v 
          | _ => Error [MSG "Expected a pointer"]
         end.

Definition force_opt {A} (v: option A) msg : res A :=
  match v with Some x => OK x | None => Error msg end.

Notation " 'check' A , msg ; B" := (if A then B else Error msg)
  (at level 200, A at level 100, msg at level 100, B at level 200)
  : error_monad_scope.

Section GENV.

Variable ge: genv.

Section EXPR.
Variable ve: env.
Variable le: temp_env.
Variable m: mem.

Definition compos id : res composite :=
 match ge.(genv_cenv) ! id with
 | Some x => OK x
 | None => Error [MSG "Identifier "; CTX id; MSG " is not a struct or union"]
 end.


Definition geterr {A} id (rho: PTree.tree A) : res A :=
 match PTree.get  id rho with
 | Some x => OK x
 | None => Error [MSG "Variable "; CTX id; MSG " not in scope"]
 end.

Definition eval_field  (ty: type) (fld: ident) (v: val) : res (block*int) :=
  match v with
  | Vptr l ofs => 
    ( match ty with
             | Tstruct id att =>
                do co <- compos id;
                do delta <- field_offset ge.(genv_cenv) fld (co_members co);
                OK (l, (Int.add ofs (Int.repr delta)))
             | Tunion id att =>
                do co <- compos id;
                  OK (l, ofs)
             | _ => Error [MSG "Expected a struct or union"]
      end)
  | _ => Error [MSG "Unexpected field access on a non-pointer"]
  end.

Definition eval_var (id:ident) (ty: type) : res (block * int) :=
            match PTree.get  id ve with
            | Some (b,ty') =>
                   check (type_eq ty ty') , [MSG "Type-check failure in eval_var"];
                   OK (b, Int.zero)
            | None =>
                   match Genv.find_symbol ge id  with
                   | Some b => OK (b, Int.zero)
                   | None => Error [MSG "Variable "; CTX id; MSG " not in scope"]
                   end
             end.

(* Return the val at loc (b,ofs) in memory *)
Fixpoint deref_loc (ty:type) (b:block) (ofs:int): res val :=
  match access_mode ty with
  | By_value chunk =>
    match Mem.loadv chunk m (Vptr b ofs) with
    | Some v => OK v
    | None => Error [MSG "Deref_loc failed, no value:chunk found in mem at loc"]
    end
  | By_reference =>
    OK (Vptr b ofs)
  | By_copy =>
    OK (Vptr b ofs)
  | _ => Error [MSG "Deref_loc failed, Access mode unknown"]
  end.

Fixpoint eval_expr (a0: expr) : res val :=
 match a0 with
 | Econst_int i ty => OK (Vint i)
 | Econst_long i ty => OK (Vlong i)
 | Econst_float f ty => OK (Vfloat f)
 | Econst_single f ty => OK (Vsingle f)
 | Etempvar id ty => 
        force_opt (PTree.get id le) [MSG "Tempvar "; CTX id; MSG " not in scope"]
 | Eaddrof a ty =>
   do (l, ofs) <- eval_lvalue a;
     OK (Vptr l ofs)
 | Eunop op a ty =>
     do v <- eval_expr a;
     force_opt (sem_unary_operation op v (typeof a) m)
             [MSG "Unary operation failed"]
 | Ebinop op a1 a2 ty =>
     do v1 <- eval_expr a1;
     do v2 <- eval_expr a2;
     force_opt (sem_binary_operation ge.(genv_cenv) op 
                       v1 (typeof a1) v2 (typeof a2) m)
             [MSG "Binary operation failed"]
 | Ecast a ty =>
     do v <- eval_expr a; 
     force_opt (sem_cast v (typeof a) ty m)
             [MSG "Cast failed"]
 | Esizeof t ty => OK (Vint (Int.repr (sizeof ge.(genv_cenv) t)))
 | Ealignof t ty => OK (Vint (Int.repr (alignof ge.(genv_cenv) t)))
 (* lvalue! *)
 | Evar id ty =>
   do (l, ofs) <- eval_var id ty;
     deref_loc (typeof a0) l ofs
 | Ederef a ty =>
   (match eval_expr a with 
    | OK (Vptr l ofs) => deref_loc (typeof a0) l ofs
    | _ => Error [MSG "Unexpected non-pointer being deref"] (* typecheck should ensure isptr *)end)
 | Efield a i ty =>
   do v <- eval_expr a;
   do (l, ofs) <- eval_field (typeof a) i v;
   deref_loc (typeof a0) l ofs
 end
 with eval_lvalue (a0: expr) : res (block*int) :=
 match a0 with
 | Evar id ty => eval_var id ty
 | Ederef a ty =>
   (match eval_expr a with 
    | OK (Vptr l ofs) => OK (l, ofs)
    | _ => Error [MSG "Unexpected non-pointer being deref"] (* typecheck should ensure isptr *)end)
 | Efield a i ty =>
     do v <- eval_expr a;
     eval_field (typeof a) i v
 | _  => Error [MSG "Unexpected r-expression in eval_lvalue"]
 end.

Fixpoint eval_exprlist  (tl0: typelist) (al0: list expr) : res (list val) :=
 match tl0, al0 with
 | Tcons ty tyl, a :: al => do v <- eval_expr (Ecast a ty); do vl <- eval_exprlist tyl al; OK(v::vl)
 | Tnil, nil => OK nil
 | _, _ => Error [MSG "eval_exprlist"]
 end.

End EXPR.


Definition do_ef_malloc
       (vargs: list val) (m: mem) : res (val * mem) :=
  match vargs with
  | Vint n :: nil =>
      let (m', b) := Mem.alloc m (-4) (Int.unsigned n) in
      do m'' <- force_opt (Mem.store Mint32 m' b (-4) (Vint n)) [MSG "malloc store failed"];
      OK (Vptr b Int.zero, m'')
  | _ => Error [MSG "malloc bad args"]
  end.




(* Test if a value is a pointer or an int 
  Returns true if Vptr, false is Vint odd (valid?), Error otherwise *)
Definition do_ef_is_ptr (vargs:list val) (m:mem) : res (val * mem) :=
  match vargs with
  | [Vint n] =>
    if Int.eq (Int.modu n (Int.repr 2)) (Int.repr 0) then Error [MSG "Expected odd int"] else OK (Vint (Int.repr 0), m)
  | [Vptr b off] => OK (Vint (Int.repr 1), m)
  | _ => Error [MSG "Not an int nor a pointer or more than one arguments"]
  end.

(* 
First argument is a pointer to the number of blocks to allocate (unsigned int32)
second arg is pointer to tinfo

Mem_alloc n blocks , updates alloc and limit in tinfo, returns void *)


Definition do_ef_gcmalloc
       (vargs: list val) (m: mem) : res (val * mem) :=
  match vargs with
  | Vptr bnum onum ::Vptr bsrc osrc :: nil =>
    ( match deref_loc m  (Tint I32 Unsigned noattr) bnum onum with
      | OK (Vint n) =>        
        let (m', b) := Mem.alloc m 0 ((Int.unsigned n)* 4) in
        let balloc := bsrc in
        let blimit := bsrc in
        let oalloc := osrc in
        let olimit := Int.repr ((Int.unsigned osrc) + size_chunk Mint32) in
             do m'' <- force_opt (Mem.store Mint32 m' balloc (Int.unsigned oalloc) (Vptr b (Int.repr 0))) [MSG "malloc store failed"];
               do m''' <- force_opt (Mem.store Mint32 m'' blimit (Int.unsigned olimit) (Vptr b (Int.repr ((Int.unsigned n)* 4)))) [MSG "malloc store failed"];
               OK (Vundef, m''')
(*           | _ , _ => Error [MSG "gcmalloc: alloc or limit ptr corrupted"]
           end) *)
      | _ => Error [MSG "gcmalloc first arg wasn't a pointer to an int"] 
      end)
      
  | _ => Error [MSG "gcmalloc bad args"]
  end.

Definition do_ef_free
       (vargs: list val) (m: mem) : res (val * mem) :=
  match vargs with
  | Vptr b lo :: nil =>
      do vsz <- force_opt (Mem.load Mint32 m b (Int.unsigned lo - 4)) [MSG "free: load failed"];
      match vsz with
      | Vint sz =>
          check (zlt 0 (Int.unsigned sz)), [MSG "free: header corrupted"];
          do m' <- force_opt (Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz)) [MSG "free failed"];
          OK (Vundef, m')
      | _ => Error [MSG "free: header corrupted"]
      end
  | _ => Error [MSG "free: bad args"]
  end.

Definition do_ef_memcpy (sz al: Z) (vargs: list val) (m: mem) : res (val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      check (Cexec.memcpy_check_args sz al bdst (Int.unsigned odst) bsrc (Int.unsigned osrc)), [MSG "memcpy check_args"];
        do bytes <- force_opt (Mem.loadbytes m bsrc (Int.unsigned osrc) sz) [MSG "memcpy loadbytes"];
        do m' <- force_opt (Mem.storebytes m bdst (Int.unsigned odst) bytes) [MSG "memcpy storebytes"];
        OK (Vundef, m')
  | _ => Error [MSG "memcpy bad args"]
  end.


Definition do_external (ef: external_function) (vargs: list val) (m: mem): res (val * mem) :=
  match ef with
  | EF_external name sg =>
    (* gc is the AST name used by L6_to_Clight, garbage_collect the PP name added in allInstance *)
    if UsefulTypes.string_eq_bool name "gc" then
      do_ef_gcmalloc vargs m
    else
      if UsefulTypes.string_eq_bool name "is_ptr" then
        do_ef_is_ptr vargs m
      else      
      Error [MSG "called external function "; MSG name]
  | EF_builtin name sg => Error [MSG "called builtin function "; MSG name]
  | EF_runtime name sg => Error [MSG "called runtime function "; MSG name]
  | EF_vload chunk => Error [MSG "volatile load "]
  | EF_vstore chunk => Error [MSG "volatile load "]
  | EF_malloc => do_ef_malloc vargs m
  | EF_free => do_ef_free vargs m
  | EF_memcpy sz al => do_ef_memcpy sz al vargs m
  | EF_annot text targs => Error [MSG "annot "; MSG text]
  | EF_annot_val text targ => Error [MSG "annot_val "; MSG text]
  | EF_inline_asm text sg clob => Error [MSG "inline_asm "; MSG text]
  | EF_debug kind text targs => Error [MSG "debug "; CTX kind; CTX text]
  end.

Definition assign_copy_ok (ty: type) (b: block) (ofs: int) (b': block) (ofs': int) : Prop :=
  (alignof_blockcopy ge ty | Int.unsigned ofs') /\ (alignof_blockcopy ge ty | Int.unsigned ofs) /\
  (b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
           \/ Int.unsigned ofs' + sizeof ge ty <= Int.unsigned ofs
           \/ Int.unsigned ofs + sizeof ge ty <= Int.unsigned ofs').

Remark check_assign_copy:
  forall (ty: type) (b: block) (ofs: int) (b': block) (ofs': int),
  { assign_copy_ok ty b ofs b' ofs' } + {~ assign_copy_ok ty b ofs b' ofs' }.
Proof with try (right; intuition omega).
  intros. unfold assign_copy_ok.
  assert (alignof_blockcopy ge ty > 0) by apply alignof_blockcopy_pos.
  destruct (Zdivide_dec (alignof_blockcopy ge ty) (Int.unsigned ofs')); auto...
  destruct (Zdivide_dec (alignof_blockcopy ge ty) (Int.unsigned ofs)); auto...
  assert (Y: {b' <> b \/
              Int.unsigned ofs' = Int.unsigned ofs \/
              Int.unsigned ofs' + sizeof ge ty <= Int.unsigned ofs \/
              Int.unsigned ofs + sizeof ge ty <= Int.unsigned ofs'} +
           {~(b' <> b \/
              Int.unsigned ofs' = Int.unsigned ofs \/
              Int.unsigned ofs' + sizeof ge ty <= Int.unsigned ofs \/
              Int.unsigned ofs + sizeof ge ty <= Int.unsigned ofs')}).
  destruct (eq_block b' b); auto.
  destruct (zeq (Int.unsigned ofs') (Int.unsigned ofs)); auto.
  destruct (zle (Int.unsigned ofs' + sizeof ge ty) (Int.unsigned ofs)); auto.
  destruct (zle (Int.unsigned ofs + sizeof ge ty) (Int.unsigned ofs')); auto.
  right; intuition omega.
  destruct Y... left; intuition omega.
Defined.

Definition do_assign_loc (ty: type) (m: mem) (vp v: val): res mem :=
 match vp with
 | Vptr b ofs =>
  match access_mode ty with
  | By_value chunk =>
      match type_is_volatile ty with
      | false => force_opt (Mem.storev chunk m (Vptr b ofs) v) [MSG "storev failed"]
      | true => Error [MSG "Volatile store at block "; POS b]
      end
  | By_copy =>
      match v with
      | Vptr b' ofs' =>
            check (check_assign_copy ty b ofs b' ofs') , [MSG "check_assign_copy failed"];
            do bytes <- force_opt (Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ge ty)) [MSG "loadbytes failed"];
            force_opt (Mem.storebytes m b (Int.unsigned ofs) bytes) [MSG "storebytes failed"]
      | _ => Error [MSG "mem copy at not-a-pointer"]
      end
  | _ => Error [MSG "illegal access_mode for assignment"]
  end
  | _ => Error [MSG "lhs of assignment not a pointer"]
 end.

Fixpoint alloc_variables (e: env) (m: mem) (vars: list (ident*type)) : res (env*mem) :=
  match vars with
  | nil => OK (e,m)
  | (id,ty)::vars' => 
        let (m1,b1) := Mem.alloc m 0 (sizeof ge ty) in
        let e' := PTree.set id (b1,ty) e in
        alloc_variables e' m1 vars'
  end.



Definition function_entry  (f: function) (vargs: list val) (m: mem) : res (env*temp_env*mem) :=
     (* list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) -> *)
      do (e,m') <- alloc_variables empty_env m f.(fn_vars);
      do le <- force_opt (bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)))
                            [MSG "bind_parameter_temps"];
      OK (e,le,m').      


(* Executation version of Clight.step where parameters are temporary variables *)
Fixpoint step (s: state) : res state :=
match s with
| State f (Sassign a1 a2) k e le m =>
     do (l, ofs) <- eval_lvalue e le m a1;
     do v2 <- eval_expr e le m (Ecast a2 (typeof a1));
     do m' <- do_assign_loc (typeof a1) m (Vptr l ofs) v2;
     OK (State f Sskip k e le m')
| State f (Sset id a) k e le m =>
     do v <- eval_expr e le m a;
     OK (State f Sskip k e (PTree.set id v le) m)
| State f (Scall optid a al) k e le m =>
    match classify_fun (typeof a) with
    | fun_case_f tyargs tyres cconv =>
       do vf <- eval_expr e le m a;
       do vargs <- eval_exprlist e le m tyargs al;
       do fd <- force_opt (Genv.find_funct ge vf) [MSG "Scall Genv.find_funct"];
       check (type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv)) , [MSG "Scall type_of_function"];
       OK (Callstate fd vargs (Kcall optid f e le k) m)
    | _ => Error [MSG "Scall classify_fun"]
    end
| State f (Sbuiltin optid ef tyargs al) k e le m =>
    do vl <- eval_exprlist e le m tyargs al;
    do (vres,m') <- do_external ef vl m;
    OK (State f Sskip k e (set_opttemp optid vres le) m')
| State f (Ssequence s1 s2) k e le m =>
     OK (State f s1 (Kseq s2 k) e le m)
| State f Sskip (Kseq s k) e le m =>
    OK (State f s k e le m)
| State f Scontinue (Kseq s k) e le m =>
    OK (State f Scontinue k e le m)
| State f Sbreak (Kseq s k) e le m =>
    OK (State f Sbreak k e le m)
| State f (Sifthenelse a s1 s2) k e le m =>
    do v1 <- eval_expr e le m a;
    do b <- force_opt (bool_val v1 (typeof a) m) [MSG "Sifthenelse bool_val"];
    OK (State f (if b then s1 else s2) k e le m)
| State f (Sloop s1 s2) k e le m =>
    OK (State f s1 (Kloop1 s1 s2 k) e le m)
| State f Sskip (Kloop1 s1 s2 k) e le m =>
    OK (State f s2 (Kloop2 s1 s2 k) e le m)
| State f Scontinue (Kloop1 s1 s2 k) e le m =>
    OK (State f s2 (Kloop2 s1 s2 k) e le m)
| State f Sbreak (Kloop1 s1 s2 k) e le m =>
    OK (State f Sskip k e le m)
| State f Sskip (Kloop2 s1 s2 k) e le m =>
    OK (State f (Sloop s1 s2) k e le m)
| State f Sbreak (Kloop2 s1 s2 k) e le m =>
    OK (State f Sskip k e le m)
| State f (Sreturn None) k e le m =>
     do m' <- force_opt (Mem.free_list m (blocks_of_env ge e)) [MSG "Sreturn None free_list"];
     OK (Returnstate Vundef (call_cont k) m')
| State f (Sreturn (Some a)) k e le m =>
     do v <- eval_expr e le m (Ecast a f.(fn_return));
     do m' <- force_opt (Mem.free_list m (blocks_of_env ge e)) [MSG "Sreturn None free_list"];
     OK (Returnstate v (call_cont k) m')
| State f Sskip Kstop e le m =>
     do m' <- force_opt (Mem.free_list m (blocks_of_env ge e)) [MSG "Sreturn None free_list"];
     OK (Returnstate Vundef Kstop m')
| State f Sskip (Kcall i f' e' le' k) e le m =>
     do m' <- force_opt (Mem.free_list m (blocks_of_env ge e)) [MSG "Sreturn None free_list"];
     OK (Returnstate Vundef (Kcall i f' e' le' k) m')
| State f (Sswitch a sl) k e le m =>
      do v <- eval_expr e le m a;
      do n <- force_opt (sem_switch_arg v (typeof a)) [MSG "switch arg"];
       OK  (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| State f Sskip (Kswitch k) e le m =>
       OK (State f Sskip k e le m)
| State f Sbreak (Kswitch k) e le m =>
       OK (State f Sskip k e le m)
| State f Scontinue (Kswitch k) e le m =>
       OK (State f Scontinue k e le m)
| State f (Slabel lbl s) k e le m =>
       OK (State f s k e le m)
| State f (Sgoto lbl) k e le m =>
      do (s',k') <- force_opt (find_label lbl f.(fn_body) (call_cont k)) [MSG "find_label"];
      OK (State f s' k' e le m)
| Callstate (Internal f) vargs k m =>
      do (e,m') <- alloc_variables empty_env m f.(fn_vars);
      do le <- force_opt (bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)))
                            [MSG "bind_parameter_temps"];
      OK (State f f.(fn_body) k e le m')
| Callstate (External ef targs tres cconv) vargs k m =>
     do (vres,m') <- do_external ef vargs m;
     OK (Returnstate vres k m')
| Returnstate v (Kcall optid f e le k) m =>
     OK (State f Sskip k e (set_opttemp optid v le) m)
| _ => Error [MSG "Unexpected statement"]
end.

End GENV.

Definition do_initial_state (p: program): res (genv * state) :=
  let ge := globalenv p in
  do m0 <- force_opt (Genv.init_mem p) [MSG "init_mem"];
  do b <- force_opt (Genv.find_symbol ge p.(prog_main)) [MSG "can't find main"];
  do f <- force_opt (Genv.find_funct_ptr ge b) [MSG "can't find main, part 2"];
  check (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default)) , [MSG "type_of_main"];
  OK (ge, Callstate f nil Kstop m0).








Definition at_final_state (S: state): res int :=
  match S with
  | Returnstate (Vint r) Kstop m => OK r
  | _ => Error [MSG "main did not return an int"]
  end.




Definition is_stopped s :=
  match s with Returnstate _ Kstop _ => true | _ => false end.

Function stepstar (ge: genv) (s: state) (nenv:M.t Ast.name) (fuel: Z)  {measure Z.to_nat fuel}: (bigStepResult state state) :=
  if Z.leb fuel Z0 
  then OutOfTime s
  else match step ge s with OK s' =>
          if is_stopped s' then Result s' else stepstar ge s' nenv (Zpred fuel)
                       | Error err => certiClasses.Error (print_error err (Some nenv)) (Some s)
     end.
Proof.
intros.
apply Z.leb_gt in teq.
rewrite <- (Z.succ_pred fuel) at 2.
rewrite Z2Nat.inj_succ; omega.
Defined.

(* stepstar with fuel in nat *)
Fixpoint stepstar_n (ge:genv) (s:state) (nenv:M.t Ast.name) (fuel:nat): (bigStepResult state state) :=
  match fuel with
  | O => OutOfTime s
  | S n =>match step ge s with OK s' =>
                               if is_stopped s' then Result s' else stepstar_n ge s' (nenv:M.t Ast.name) n
                          | Error err => certiClasses.Error (print_error err (Some nenv)) (Some s)
          end
  end.


Definition run (e: (M.t Ast.name)* program) (fuel: Z) : bigStepResult state int :=
  let (nenv, p) := e in
  match ( do_initial_state p) with
    | OK (ge,s) =>
      (match (stepstar ge s nenv  fuel) with
      | Result s => (match (at_final_state s) with
                     | OK r => certiClasses.Result r
                     | Error err => certiClasses.Error ("Error in at_final_state: "++(print_error err (Some nenv))) (Some s)
                     end)
      | OutOfTime s => OutOfTime s
      | certiClasses.Error e os => certiClasses.Error e os
       end)
    | Error err => certiClasses.Error ("Error while initializing state: "++(print_error err (Some nenv))) None
  end.

Section WO_MAIN.
(*
Definition threadInfIdent : ident := 31%positive.
Definition bodyIdent:positive := 90.
 *)
Variable (threadInfIdent : ident).
Variable (bodyIdent:ident).

(* 1) find body from generated program
   2) initialize a thread_info (only alloc, limit and args, heap pointer unused)
   3) call body with a pointer to thread_info *)
Definition do_initial_state_wo_main (p: program): res (genv * state * block) :=
  let ge := globalenv p in
  do m0 <- force_opt (Genv.init_mem p) [MSG "init_mem"];
  do b <- force_opt (Genv.find_symbol ge bodyIdent) [MSG "can't find body 2"];
  do f <- force_opt (Genv.find_funct_ptr ge b) [MSG "can't find body, part 3"];
  let (m, b) := Mem.alloc m0 0 (sizeof ge.(genv_cenv) (Tstruct threadInfIdent noattr)) in
  let (m', b0) := Mem.alloc m 0 (size_chunk Mint32) in
  do m'' <- force_opt (Mem.store Mint32 m' b0 0 (Vint (Int.repr 0))) [MSG "0 store failed"];
  do m3 <- force_opt (Mem.store Mint32 m'' b 0 (Vptr b0 (Int.repr 0))) [MSG "alloc ptr store failed"];
  do m4 <- force_opt (Mem.store Mint32 m3 b (size_chunk Mint32) (Vptr b0 (Int.repr 0))) [MSG "limit ptr store failed"];
  OK (ge, Callstate f ((Vptr b (Int.repr 0))::nil) Kstop m4, b).

Definition at_final_state_wo_main (S:state):res unit := 
  match S with
  | Returnstate Vundef Kstop m => OK tt
  | _ => Error [MSG "main did not return an void"]
  end.


(* run w/o main *)
Definition run_wo_main (e: (M.t Ast.name)*program) (fuel: nat) : bigStepResult state int :=
  let (nenv, p) := e in
  match ( do_initial_state_wo_main p) with
    | OK (ge,s, b) =>
      (match (stepstar_n ge s nenv fuel) with
      | Result s => (match (at_final_state_wo_main s) with
                     | OK tt => certiClasses.Result (Int.repr 1)
                     | Error err => certiClasses.Error ("Error in at_final_state: "++(print_error err (Some nenv))) (Some s)
                     end)
      | OutOfTime s => OutOfTime s
      | certiClasses.Error e os => certiClasses.Error e os
       end)
    | Error err => certiClasses.Error ("Error while initializing state: "++(print_error err (Some nenv))) None
  end.

End WO_MAIN.


(*
Require Import L6_to_Clight.

Require Import main.
Require Import gc.
 
Print main.
Print link_program.

Eval native_compute in link_program main.prog gc.prog.


*)


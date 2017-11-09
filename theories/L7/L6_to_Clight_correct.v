(* 
  Proof of correctness of the Clight code generation phase of CertiCoq 

  > Relates values to location in memory (syntactic)
  > Relates expression to statements (syntactic)
  > Relates L7 values (header, payload) to L7 values after GC (syntactic, up to non-function pointer location)
  > Relates L6 states to L7 states according to execution semantics

 *)
From L6 Require Import cps eval
cps_util
List_util
identifiers.

From L7 Require Import L6_to_Clight.

Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec Coq.Relations.Relations.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values
        compcert.common.Globalenvs
        compcert.common.Memory.


 



  (**** Representation relation for L6 values, expressions and functions ****)
Section RELATION.

  (* same as L6_to_Clight *)
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
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).

  Notation threadStructInf := (Tstruct threadInfIdent noattr).
Notation threadInf := (Tpointer threadStructInf noattr).

Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons (Tint I32 Unsigned noattr) Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := false;
                                 cc_unproto := false;
                                 cc_structret := false |}).




Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                        {| attr_volatile := false; attr_alignas := None |}).


Notation val := uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Notation uval := uintTy.

Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

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

Definition c_int' n t := Econst_int (Int.repr n%Z) t.

Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z intTy))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).


  Parameter cenv:L6.cps.cEnv.
  Parameter fenv:L6.cps.fEnv.
  Parameter finfo_env: M.t positive. (* map from a function name to its type info *)
  Parameter p:program.

  
  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Parameter rep_env: M.t cRep.
         

  
 Inductive header_of_rep: cRep -> Z -> Prop :=
 | header_enum: forall t, header_of_rep (enum t) (Z.of_N ((N.shiftl t 1) + 1))
 | header_boxed: forall t a, header_of_rep (boxed t a) (Z.of_N ((N.shiftl a 10) + t)).
  

Inductive repr_asgn_fun': list positive -> list N -> statement -> Prop :=
| repr_asgn_nil: repr_asgn_fun' nil nil (Efield tinfd allocIdent valPtr  :::= allocPtr)
| repr_asgn_cons: forall y ys i inf s, repr_asgn_fun' ys inf s ->
                 repr_asgn_fun' (y::ys) (i::inf) (args[ Z.of_N i ] :::= (var y); s).

Inductive repr_asgn_fun: list positive -> list N -> statement -> Prop :=
  |repr_asgn_wrap: forall ys inf s, repr_asgn_fun' ys inf s ->
                   repr_asgn_fun ys inf (argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr);s).



(* like fromN but for Z, should love to list_util and make a generic one *)
Fixpoint fromZ (z:Z) (m:nat): list Z :=
  match m with
  | 0 => nil
  | S m' => z :: (fromZ (Z.succ z) m')
  end.

Fixpoint fromInt (i:int) (m:nat): list int :=
  match m with
  | 0 => nil
  | S m' => i :: (fromInt (Int.add i Int.one) m')
  end.




Definition Forall_in_mem_block {A} : (A -> (block *  int) -> Prop) -> list A -> (block * int) -> int -> Prop :=
  fun P ls loc z =>
    let (b, z0) := loc in
    let ids := fromInt Int.zero (length ls) in 
    Forall2 (fun a i => P a (b, Int.add z0 (Int.mul i z))) ls ids.




Inductive Forall_statements_in_seq' {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> BinNums.Z -> Prop :=
| Fsis_last: forall (R: (BinNums.Z  -> A -> statement -> Prop)) n v s, R n v s -> Forall_statements_in_seq' R [v] s n
| Fsis_cons: forall R v vs s s' n, Forall_statements_in_seq' R vs s' (Z.succ n) ->
                                   R n v s ->  Forall_statements_in_seq' R (v::vs) (s; s') n.

  

(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > list cannot be empty (o.w. no statement)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s (0%Z).


Inductive var_or_funvar : positive -> expr -> Prop :=
| F_VoF : forall x, 
    (exists def, List.In (x, def) (prog_defs p) ) ->
                var_or_funvar x (funVar x)
| V_VoF : forall x,
    (~ exists def, List.In (x, def) (prog_defs p)) ->
       var_or_funvar x(var x).
    

Inductive is_nth_projection_of_x : positive -> Z -> positive -> statement -> Prop :=
  Make_nth_proj: forall x  n v e,
                          var_or_funvar v  e ->
                          is_nth_projection_of_x x n v (Field(var x, n) :::=  e).


Definition unboxed_header: N -> Z -> Prop :=
 fun t => fun h => h =  (Z.of_N ((N.shiftl t 1) + 1)).


Definition boxed_header: N -> N -> Z -> Prop :=
  fun t => fun a =>  fun h => h = (Z.of_N ((N.shiftl a 10) + t)).


(* TODO: set header *)
Inductive repr_asgn_constr: positive -> cTag -> list positive -> statement -> Prop :=
| Rconstr_ass_boxed: forall x (t:cTag) vs s a n h,
    (* boxed x *)   
    M.get t rep_env = Some (boxed n a) ->
    boxed_header n a h -> 
    Forall_statements_in_seq (is_nth_projection_of_x x) vs s -> 
  repr_asgn_constr x t vs s
| Rconstr_ass_enum: forall x t n h,
    (* unboxed x *)
    M.get t rep_env  = Some (enum n) ->
    unboxed_header n h  ->
    repr_asgn_constr x t nil (x ::= c_int h val).


Inductive repr_switch_L6_L7: positive -> labeled_statements -> labeled_statements -> statement -> Prop :=
| Mk_switch: forall x ls ls',
    repr_switch_L6_L7 x ls ls'
                      (isPtr isptrIdent caseIdent x;
                         Sifthenelse
                           (var caseIdent)
                           (Sswitch (Ebinop Oand (Field(var x, -1)) (Econst_int (Int.repr 255) val) val) ls)
                           (
                             Sswitch (Ebinop Oshr (var x) (Econst_int (Int.repr 1) val) val)
                                     ls')).




(* relate a L6.exp -| cEnv, fEnv to a series of statements in a clight program (passed as parameter) -- syntactic relation that shows the right instructions have been generated for functions body. There should not be function definitions (Efun), or primitive operations (they are not supported by our backend) in this 
TODO: maybe this should be related to a state instead? 
*)
Inductive repr_expr_L6_L7: L6.cps.exp -> statement -> Prop :=
| Rconstr_e:
    forall x t vs  s s' e, 
    repr_asgn_constr x t vs s -> 
    repr_expr_L6_L7 e  s' ->
    repr_expr_L6_L7 (Econstr x t vs e)  (s; s')    
| Rproj_e: forall x t n v e  s,
    repr_expr_L6_L7 e  s ->
    repr_expr_L6_L7 (Eproj x t n v e)  (x ::= Field(var v, Z.of_N n) ; s)
| R_app_e: forall f inf ys t s,
    (* 1 - assign vs to the right args acording to fenv(f)*)
    M.get f fenv = Some inf ->
    repr_asgn_fun ys (snd inf) s -> 
    (* 2 - call f *)
    repr_expr_L6_L7 (Eapp f t ys)  (s; call ([pfunTy]funVar f))

| R_halt_e: forall v ,
    (* halt v <-> end with v in args[1] *)
    repr_expr_L6_L7 (Ehalt v)  (args[Z.of_nat 1 ] :::= (var v) ; Sreturn None)
| Rcase_e: forall v cl ls ls' s ,
    (* 1 - branches matches the lists of two lists of labeled statements *)
    repr_branches_L6_L7 cl ls ls' -> 
    (* 2 - switch-header matches  *)
    repr_switch_L6_L7 v ls ls' s ->
    repr_expr_L6_L7  (Ecase v cl)  s
(* TODO: fix the default case *)
with repr_branches_L6_L7: list (cTag * exp) -> labeled_statements -> labeled_statements -> Prop :=
     | Rempty_br : repr_branches_L6_L7 nil LSnil LSnil
     | Runboxed_br: forall cl ls ls' t n tag e s, repr_branches_L6_L7 cl ls ls' ->
                                                repr_expr_L6_L7 e s ->
                                                M.get t rep_env  = Some (enum n) ->
                                                unboxed_header n tag ->
                                                repr_branches_L6_L7 ((t, e) ::cl) ls (LScons (Some (Z.shiftr tag 1)) (Ssequence s Sbreak) ls') 
     | Rboxed_br : forall cl ls ls' t a n tag e s, repr_branches_L6_L7 cl ls ls' ->
                                           repr_expr_L6_L7 e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           boxed_header n a tag ->
                                           repr_branches_L6_L7 ((t, e)::cl) (LScons (Some (Z.land tag 255)) (Ssequence s Sbreak)  ls) ls'.

                    



Definition gc_vars := ((allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, val) ::nil).

Definition gc_set := (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr)).


Definition gc_test (gcArrIdent:positive) (l:N) := (reserve allocIdent limitIdent gcIdent threadInfIdent tinfIdent gcArrIdent
                                                            (Z.of_N (l + 2))).

Inductive right_param_asgn: list positive -> list N -> statement -> Prop :=
| asgn_nil: right_param_asgn nil nil Sskip
| asgn_cons: forall v vs n ns s,  right_param_asgn vs ns s -> right_param_asgn (v::vs) (n::ns) ((v ::=args[Z.of_N n]);s).



(* relate a  L6.val -| cEnv, fEnv to an address in a Clight memory  *)
Inductive repr_val_ptr_L6_L7: L6.cps.val -> mem -> (block *  int) ->   Prop :=
| RPint_v : forall n m b i,
    (* TODO: this needs to be shifted *)
    (* need to be sure that this is an int and not a ptr stored *)
    Mem.load Mint32 m b (Int.unsigned i) = Some (Vint n) -> 
    repr_val_ptr_L6_L7 (cps.Vint (Int.unsigned  n)) m (b, i)
| RPconstr_enum_v: forall t n m b i h,
    M.get t rep_env = Some (enum n) ->
    Mem.load Mint32 m b (Int.unsigned i) = Some (Vint h) ->
    unboxed_header n (Int.unsigned h) ->
    repr_val_ptr_L6_L7 (cps.Vconstr t nil) m (b, i)
| RPconstr_boxed_v :
    forall t vs m b i h a n,
      M.get t rep_env = Some (boxed n a) ->
      (* 1) well-formedness of the header block *)
      Mem.load Mint32 m b (Int.unsigned (Int.sub i Int.one)) = Some (Vint h) ->
      boxed_header n a  (Int.unsigned h) ->
      (* 2) all the fields are also well-represented *)
      Forall_in_mem_block (fun v loc => repr_val_ptr_L6_L7 v m loc) vs (b, i) (Int.repr (sizeof (M.empty composite) uintTy)) ->      
    repr_val_ptr_L6_L7 (cps.Vconstr t vs) m (b, i)
| RPfun_v :
    forall  vars fds f m b i F t vs e asgn body l locs finfo,
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some finfo -> (* TODO: check this *)
      (* b points to an internal function in the heap [and i is 0] *)
      Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler, 
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      fn_return F = Tvoid ->
      (*
       - calling convention?  
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       fn_params F = ((tinfIdent, threadInf)::nil) ->
      (*
        - all the vars match + the 3 gc vars *)       
       fn_vars F = List.app vars gc_vars ->
       Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
       (* - no temps *)
       fn_temps F = nil ->
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_L6_L7)
        *)
              fn_body F = Ssequence gc_set (Ssequence (gc_test finfo l)
                                               (Ssequence asgn body)) ->              
       right_param_asgn vs locs asgn ->
       repr_expr_L6_L7 e body ->
    repr_val_ptr_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (b, i).


(* the memory blocks in the sequence (b, i), (b, i+off) ... (b, i+((n-1)*off)) are pairwise related with the sequence (b', i'), (b', i'+off) ... (b', i'+(n-1*off))  *)
Inductive For_N_blocks (P:(block * int) -> (block * int) -> Prop) (loc:block * int) (loc':block * int) (off: int) :  nat -> Prop :=
| FNb_O: For_N_blocks P loc loc' off 0
| FNb_S: forall n,
    P (fst loc, Int.add (snd loc) (Int.mul off (Int.repr (Z.of_nat n)))) (fst loc', Int.add (snd loc') (Int.mul off (Int.repr (Z.of_nat n)))) ->
    For_N_blocks P  loc loc' off n -> 
    For_N_blocks P loc  loc' off (S n). 


(* TODO: related (deep copy) vals that may have been moved by the GC, in such way that they can be used in place of the other in repr_val_ptr_L6_L7  *)
Inductive same_vals_L7: mem -> (block *  int) -> mem -> (block *  int) -> Prop :=
(* same int/unboxed constructor *)
| SV_int :
    forall m b i n m' b' i' h,
    Mem.load Mint32 m b (Int.unsigned i) = Some (Vint h) ->
    Mem.load Mint32 m' b' (Int.unsigned i') = Some (Vint h) ->
    unboxed_header n (Int.unsigned h) ->
    same_vals_L7 m (b,i) m' (b', i')
| SV_fun :
    (* same fun *)
    forall m m' b i b' i' F,
      b = b' /\ i = i' ->
      Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
      same_vals_L7 m (b,i) m' (b', i')           
| SV_constr_boxed :
    forall m m' b i b' i' h h' n a,
    (* same tag *)
      Mem.load Mint32 m b (Int.unsigned (Int.sub i Int.one)) = Some (Vint h) ->
      boxed_header n a  (Int.unsigned h) ->
      Mem.load Mint32 m' b' (Int.unsigned (Int.sub i' Int.one)) = Some (Vint h') ->
      boxed_header n a  (Int.unsigned h') ->      
    (* each of the a (arrity) fields are related according to same_vals *)
      For_N_blocks (fun loc loc' => same_vals_L7 m loc m' loc') (b,i) (b', i') (Int.repr (sizeof (M.empty composite) uintTy)) (N.to_nat a) -> 
    same_vals_L7 m (b,i) m' (b', i').



Theorem repr_same_vals_L6_L7 :
  forall m m' v b i b' i',
  repr_val_ptr_L6_L7 v m (b, i) -> 
  same_vals_L7 m (b,i) m' (b', i') ->
  repr_val_ptr_L6_L7 v m' (b', i').
Proof.
  induction v; intros; inv H.
  -  (* enum *)
      admit.
  - (* boxed *)
      admit.
  - (* Vfun*)
    inv H0; subst.
    admit.
    destruct H5; subst.
    rewrite H9 in H19. inv H19; subst.
    econstructor; eauto.
    admit.
  - (* int *)
    inv H0.
    constructor.
    rewrite H7 in H4. inv H4. auto.
    (* impossible m is disjoint from globenv *) admit.
    admit.
Admitted.

    
(* like repr_val but not defered (i.e. positive is in tempval 
  if local_env is really holding blocks to lookup in memory, then should rework this *)
Inductive repr_val_L6_L7:  L6.cps.val -> mem -> Values.val -> Prop :=
| Rint_v: forall z r m,
    unboxed_header (Z.to_N z) (Int.unsigned r) ->
    repr_val_L6_L7 (L6.cps.Vint z) m (Vint r)
| Rconstr_unboxed_v:
    forall t arr n m,
      M.get t rep_env = Some (enum arr) ->
      unboxed_header arr (Int.unsigned n) ->
      repr_val_L6_L7 (L6.cps.Vconstr t nil) m (Vint n)
| Rconstr_boxed_v: forall t vs arr a b i m,
    (* t is a boxed constructor, n ends with 0 and represents 
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed arr a) ->
    repr_val_ptr_L6_L7 (L6.cps.Vconstr t vs) m (b, i) ->
    (* todo: this might actually be a Vint that needs to be interpreted as a pointer *)
    repr_val_L6_L7 (L6.cps.Vconstr t vs) m (Vptr b i)
.


(* TODO: write this to ensure that the GC nevers runs out of space in the middle of a function*)
Inductive correct_alloc: exp -> int -> Prop :=.

(* see make_fundef_info, this is w.r.t. some fenv, another prop should assert the fenv is correct w.r.t. all functions *)
Inductive correct_fundef_info: positive -> fTag -> list positive -> exp -> ident -> Prop :=
  c_funinfo: forall f t vs e tag n l b finfo fi_0 fi_1 fi_rest,
    (* the tag for f points to a record r *)
    M.get f fenv =  Some (n, l) ->
    n = N.of_nat (length l) ->
    (* id points to an array in global memory *)
    Genv.find_symbol (globalenv p) tag = Some b ->
    Genv.find_var_info (globalenv p) b = Some finfo ->
    
    (* the record has the right information w.r.t. vs and r 
       fi[0] = alloc(e)
       fi[1] = number of roots
       |fi| = 2+fi[1] *)
    gvar_init finfo = ((Init_int32 fi_0)::(Init_int32 fi_1)::fi_rest) ->
    correct_alloc e fi_0 ->
    fi_1 = Int.repr (Z.of_N n) ->
    n = N.of_nat (length fi_rest) -> 
    correct_fundef_info f t vs e tag. 


(* P is true of every fundefs in a bundle *)
(* TODO: move this to cps_util *)
Inductive Forall_fundefs: (L6.cps.var -> fTag -> list L6.cps.var -> exp -> Prop) -> fundefs -> Prop :=
| Ff_cons : forall (P:(L6.cps.var -> fTag -> list L6.cps.var -> exp -> Prop)) f t vs e fds,
         P f t vs e -> 
         Forall_fundefs P fds ->
         Forall_fundefs P (Fcons f t vs e fds)         
| Ff_nil: forall P, Forall_fundefs P Fnil.


Theorem Forall_fundefs_In:
  forall P f t vs e fds,
  Forall_fundefs P fds ->
  fun_in_fundefs fds (f,t,vs,e) ->
  P f t vs e.
Proof.
  induction fds; intros.
  - inv H; inv H0; subst.
    + inv H; auto.
    +  apply IHfds; auto.
  - inv H0.
Qed.
(* END TODO *)


(* 1) finfo_env has the correct finfo
   2) fenv is consistent with the info
   3) global env holds a correct L7 representation of the function *)
Definition correct_environments_for_function:
  genv -> fEnv -> M.t positive -> mem -> fundefs ->  L6.cps.var ->
  fTag -> list L6.cps.var -> exp ->  Prop
  := fun ge fenv finfo_env m fds f t vs e =>
       exists l locs finfo b, 
         (*1*)
         M.get f finfo_env = Some finfo /\
         correct_fundef_info f t vs e finfo /\
         (*2*)
         M.get t fenv = Some (l, locs) /\
         l = N.of_nat (length vs) /\
         (* may want to check that locs are distinct and same as in finfo? *)
         (*3*)
         Genv.find_symbol (globalenv p) f = Some b /\
         repr_val_ptr_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (b, Int.zero).
                                                                                                    (* relates the top level bundle of function fds to a map of fundef_info and a global environment with related functions *) 
Definition correct_environments_for_functions: fundefs -> genv -> fEnv -> M.t positive -> mem ->  Prop := fun fds ge fenv finfo_env m =>
  Forall_fundefs (correct_environments_for_function ge fenv finfo_env m fds) fds.                                                                                                   


(* relates a L6 evaluation environment to a Clight memory up to the free variables in e *)
(* If x is a free variable of e, then it might be in the generated code:
   1) a function (may want to handle this separately as they won't get moved by the GC) in the global environment, evaluates to a location related to f by repr_val_ptr_L6_L7
   2) a local variable in le related to (rho x) according to repr_val_L6_L7 -- this happens when e.g. x := proj m, or after function initialization


Note that parameters are heap allocated, and at function entry "free variables" are held in args and related according to repr_val_ptr_L6_L7
 
TODO: move out of section and parameterize w.r.t. the environments
 *)
    Definition rel_mem_L6_L7: exp -> L6.eval.env -> mem -> temp_env -> Prop :=
    fun e rho m le =>
      forall x, occurs_free e x ->
                exists v6, M.get x rho = Some v6 /\
                              match v6 with
                              | Vfun rho fl f => True (* this is handled by correct_env_for_functions at the top level *)
(*                                exists b,
                                (* maybe should look in ve first to do same as Clight.eval_var? *)
                                Genv.find_symbol (globalenv p) x = Some b 
                                /\ repr_val_ptr_L6_L7 v6 m (b, (Int.zero))*)
                              | _ => exists v7, M.get x le = Some v7 /\ repr_val_L6_L7 v6 m v7
                              end.

                       


Fixpoint mem_of_state (s:state) : mem :=
  match s with
  | State f s k e le m => m
  | Callstate f vs k m => m
  | Returnstate x k m =>  m
  end.



(* [pure] step with no built-in, i.e. trace is always E0 *)
Definition traceless_step2:  genv -> state -> state -> Prop := fun ge s s' => step2 ge s nil s'. 

Definition m_tstep2 (ge:genv):=  clos_trans state (traceless_step2 ge).


(* given a program (which at top level is the certicoq translation of e... 
TODO: add disjunct for basecase (Returnstate) 
TODO: additional constraints on the environment(s), top level statement, f k etc...
TODO: move out of section and deal with param *)
Theorem repr_L6_L7_are_related:
  forall e s rho rho' e' f stm k env lenv m, 
   s = State f stm k env lenv m -> 
  repr_expr_L6_L7 e stm ->
  rel_mem_L6_L7 e rho m lenv ->
  L6.eval.step (M.empty _) cenv (rho, e) (rho', e') ->
  exists  f' stm' k' env' lenv' m', m_tstep2 (globalenv p) s (State f' stm' k' env' lenv' m') /\ repr_expr_L6_L7 e' stm' /\ rel_mem_L6_L7 e' rho' m' lenv'.
Admitted.




End RELATION.

  
(* 
  Translation from L6 to CompCert CLight
  
  2016 -- Matthew Weaver 
 *)
Require Import Coq.ZArith.ZArith
        Coq.Program.Basics
        Coq.Strings.String
        Coq.Lists.List List_util.

Require Import ExtLib.Structures.Monads
        ExtLib.Data.Monads.OptionMonad
        ExtLib.Data.Monads.StateMonad
        ExtLib.Data.String.

Import MonadNotation.
Open Scope monad_scope.

Require Import Template.BasicAst.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values.

Require Import L6.cps
        L6.identifiers.

Require Import Clightdefs.
Require Import L6.cps_show.

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
  Variable (isptrIdent: ident). (* ident for the is_ptr external function *)
  Variable (caseIdent:ident). (* ident for the case variable , TODO: generate that automatically and only when needed *)

  Definition nParam:nat := 11.
  
  Definition maxArgs := 1024%Z.

 
  (* temporary function to get something working *)
  (* returns (n-1)::(n-2):...::0::nil for a list of size n *)
Fixpoint makeArgList' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList' vs')
  end.

Definition makeArgList (vs : list positive) : list N := rev (makeArgList' vs).


(* Compute an fEnv by looking at the number of arguments functions are applied to, assumes that all functions sharing the same tags have the same arity *)
Fixpoint compute_fEnv' (n : nat) (fenv : fEnv) (e : exp) : fEnv :=
  match n with
  | 0 => fenv
  | S n' => match e with
           | Econstr x t vs e' => compute_fEnv' n' fenv e'
           | Ecase x cs => fold_left (compute_fEnv' n') (map snd cs) fenv
           | Eproj x t n v e' => compute_fEnv' n' fenv e'
           | Efun fnd e' => compute_fEnv' n'
                                         (compute_fEnv_fundefs n' fnd fenv)
                                         e'
           | Eapp x t vs => M.set t (N.of_nat (length vs) , makeArgList vs) fenv
           | Eprim x p vs e' => compute_fEnv' n' fenv e'
           | Ehalt x => fenv
           end
  end
with compute_fEnv_fundefs n fnd fenv :=
       match n with
       | 0 => fenv
       | S n' => match fnd with
                | Fnil => fenv
                | Fcons f t vs e fnd' =>
                  let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
                  compute_fEnv_fundefs n' fnd' (compute_fEnv' n' fenv' e)
                end
       end.



Fixpoint max_depth (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => S (max_depth e')
  | Ecase x cs => S (fold_left Nat.max
                              (map (compose max_depth snd) cs)
                              (S 0))
  | Eproj x t n v e' => S (max_depth e')
  | Efun fnd e' => S (Nat.max
                       (max_depth_fundefs fnd)
                       (max_depth e'))
  | Eapp x t vs => 1
  | Eprim x p vs e' => S (max_depth e')
  | Ehalt x => 1
  end
with max_depth_fundefs fnd :=
       match fnd with
       | Fnil => S 0
       | Fcons _ _ _ e fnd' => S (Nat.max (max_depth e)
                                         (max_depth_fundefs fnd'))
       end.

(* OS: this only computes fenv for known function. *) 
Fixpoint compute_fEnv_fds fnd fenv:=
  match fnd with
  | Fnil => fenv
  | Fcons f t vs e fnd' =>
    let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
    compute_fEnv_fds fnd' fenv'
  end.

(* fEnv maps tags to function info  *)

Definition compute_fEnv (e : exp) : option fEnv :=
  match e with
  | Efun fds e' => ret ( compute_fEnv' (max_depth e) (M.empty fTyInfo) e)
                        (* (compute_fEnv_fds fds (M.empty fTyInfo))) *)
  | _ => None
  end.







Fixpoint get_allocs (e : exp) : list positive :=
  match e with
  | Econstr x t vs e' => x :: (get_allocs e')
  | Ecase x cs =>
    (fix helper (cs : list (cTag * exp)) :=
       match cs with
       | nil => nil
       | cons (z, e') cs' => (get_allocs e') ++ (helper cs')
       end) cs
  | Eproj x t n v e' => x :: (get_allocs e')
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

(* Max number of value-sized words allocated by the translation of expression e 
  For constructor: 1 word per argument + 1 for header if boxed (more than 1 param), otherwise 0 (since enum) *)
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    | nil => max_allocs e'
    | _ => S (max_allocs e' + length vs)
    end
  | Ecase x cs =>
    (fix helper (cs : list (cTag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_allocs e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_allocs e'
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
    (fix helper (cs : list (cTag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_args e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_args e'
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

(* named ienv *)
(* TODO: move this to cps and replace the current definition of iTyInfo *)
(* 1) name of inductive type
   2) list containing
      2.1 name of the constructor
      2.2 tag of the contructor (in cEnv)
      2.3 arity of the constructor
      2.4 ordinal of the constructor *)
Definition n_iTyInfo:Type := BasicAst.name * list (BasicAst.name * cTag * N * N).

Definition n_iEnv := M.t n_iTyInfo.



Definition update_iEnv (ienv : n_iEnv) (p : positive) (cInf : cTyInfo) : n_iEnv :=
  let '(name, nameTy, t, arity, ord) := cInf in
  match (M.get t ienv) with
  | None => M.set t (nameTy, ((name, p, arity, ord) :: nil)) ienv
  | Some (nameTy, iInf) => M.set t (nameTy, (name, p, arity, ord) :: iInf) ienv
  end.

Definition compute_iEnv (cenv : cEnv) : n_iEnv :=
  M.fold update_iEnv cenv (M.empty _).


Inductive cRep : Type :=
| enum : N -> cRep
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| boxed : N -> N -> cRep.
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)



Definition make_cRep (cenv:cEnv) (ct : cTag) : option cRep :=
  p <- M.get ct cenv ;;
    let '(name, _, it , a , n) := p in
      match (a =? 0)%N with
      | true =>
        ret (enum n)
      | false =>
        ret (boxed n a)
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
Definition val := if Archi.ptr64 then ulongTy else uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *) 
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






Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

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



Definition reserve_body (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
    (Scall None gc (arr :: tinf :: nil) ; allocIdent ::= Efield tinfd allocIdent valPtr)
    Sskip.


Definition reserve_body' (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  let allocF := Efield tinfd allocIdent valPtr in
  let limitF := Efield tinfd limitIdent valPtr in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uval) (limitF -' allocF) type_bool))
    (Scall None gc (arr :: tinf :: nil))
    Sskip.


(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition makeTagZ (cenv:cEnv) (ct : cTag) : option Z :=
      match make_cRep cenv ct with
      | Some (enum t) => Some ((Z.shiftl (Z.of_N t) 1) + 1)%Z
      | Some (boxed t a) => Some  ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z
      | None => None
      end.

Definition makeTag (cenv: cEnv) (ct : cTag) : option expr :=
  match makeTagZ cenv ct with
    | Some t =>
      Some (c_int t val)
    | None => None
  end.

Definition mkFunVar x (locs : list N) := (Evar x (mkFunTy (length (firstn nParam locs)))).

Definition makeVar (x:positive) (fenv :fEnv) :=
  match M.get x fenv with
  | None => var x
  | Some (l , locs) => mkFunVar x locs
  end.


(* OS: assignConstructor' without the rev *)
Fixpoint assignConstructorS' (fenv: fEnv) (x : positive) (cur:nat) (vs : list positive): statement :=
  match vs with
  | nil => (* shouldn't be reached *)
       Sskip
  | cons v nil =>
    let vv := makeVar v fenv in
    (Field(var x, Z.of_nat cur) :::= (*[val]*) vv)
  | cons v vs' =>
    let vv := makeVar v fenv in  
    let prog := assignConstructorS' fenv x (cur+1)  vs'  in
         (* if v is a function name, funVar, otherwise lvar *)
             (Field(var x, Z.of_nat cur) :::= (*[val]*) vv; prog)
  end.


Definition assignConstructorS (cenv:cEnv) (ienv : n_iEnv) (fenv : fEnv) (x : positive) (t : cTag) (vs : list positive) :=
      tag <- makeTag cenv t;;
        rep <- make_cRep cenv t ;;
        match rep with
        | enum _ =>           
          ret (x ::= tag)
        | boxed _ a =>
          let stm := assignConstructorS' fenv x 0 vs in 
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

Definition isBoxed (cenv:cEnv) (ienv : n_iEnv) (ct : cTag) : bool :=
  match make_cRep cenv  ct with
  | None => false
  | Some rep => match rep with
               | enum t => false
               | boxed t a => true
               end
  end.

Fixpoint mkCallVars (vs : list positive) : list expr :=
  match vs with
  | nil => nil
  | cons v vs' => (Etempvar v valPtr) :: mkCallVars vs'
  end.

Definition mkCall (f : expr) (vs : list positive) : statement :=
         Scall None f (tinf :: (mkCallVars (firstn nParam vs))).
        
Fixpoint asgnFunVars' (vs : list positive) (ind : list N) :
  option statement := 
  match vs with
  | nil =>
    match ind with
    | nil => ret Sskip
    | cons _ _ => None
    end
  | cons v vs' =>
    match ind with
    | nil => None
    | cons i ind' =>             
      rest <- asgnFunVars' vs' ind' ;;
           ret  (v ::= args[ Z.of_N i ] ;
                rest)
    end
  end.

Definition asgnFunVars (vs : list positive) (ind : list N) :
  option statement := asgnFunVars' (skipn nParam vs) (skipn nParam ind).
       
Fixpoint asgnAppVars'' (vs : list positive) (ind : list N) (fenv : fEnv) :
  option statement := 
  match vs, ind with
  | nil, nil => ret Sskip 
  | cons v vs' , cons i ind' =>
      let s_iv :=  args[ Z.of_N i ] :::= (makeVar v fenv) in 
        rest <- asgnAppVars'' vs' ind' fenv;;
        ret (rest ; s_iv)
  | _, _ => None
  end.

Definition asgnAppVars' (vs : list positive) (ind : list N) (fenv : fEnv) :
  option statement := asgnAppVars'' (skipn nParam vs) (skipn nParam ind) fenv.

Fixpoint get_ind {A} (Aeq : A -> A -> bool) (l : list A) (a : A) : option nat :=
  match l with
  | nil => None
  | x :: l' =>
    match Aeq a x with
    | true => Some 0
    | false =>
      n <- get_ind Aeq l' a ;;
        ret (S n)
    end
  end.

Fixpoint remove_AppVars (myvs vs : list positive) (myind ind : list N) : option (list positive * list N) :=
  match vs , ind with
  | nil , nil => Some (nil , nil)
  | v :: vs' , i :: ind' =>
    '(vs' , ind') <- remove_AppVars myvs vs' myind ind' ;;
    match get_ind Pos.eqb myvs v with
    | Some n =>
      match nth_error myind n with
      | Some i' =>
        match N.eqb i i' with
        | true => ret (vs' , ind')
        | false => ret (v :: vs' , i :: ind')
        end
      | None => ret (v :: vs' , i :: ind')
      end
    | None => ret (v :: vs' , i :: ind')
    end
  | _ , _ => None
  end.
          
Definition asgnAppVars_fast' (myvs vs : list positive) (myind ind : list N) (fenv : fEnv) : option statement :=
  '(vs' , ind') <- remove_AppVars myvs (skipn nParam vs) myind (skipn nParam ind) ;;
  asgnAppVars'' vs' ind' fenv.

(* Optional, reduce register pressure *)
Definition asgnAppVars vs ind (fenv : fEnv) :=
  match asgnAppVars' vs ind fenv with
    | Some s =>
     ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s)
    | None => None 
  end.

Definition asgnAppVars_fast myvs vs myind ind (fenv : fEnv) :=
  match asgnAppVars_fast' myvs vs myind ind fenv with
    | Some s =>
     ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s)
    | None => None 
  end.

Definition reserve (funInf : positive) (l : Z) (vs : list positive) (ind : list N) (fenv : fEnv) : option statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  match asgnAppVars'' (firstn nParam vs) (firstn nParam ind) fenv , asgnFunVars' (firstn nParam vs) (firstn nParam ind) with
  | Some bef , Some aft =>
    Some (Sifthenelse
            (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
            (bef ; Scall None gc (arr :: tinf :: nil) ; allocIdent ::= Efield tinfd allocIdent valPtr ; aft)
            Sskip)
  | _, _ => None
  end.

Definition reserve' (funInf : positive) (l : Z) (vs : list positive) (ind : list N) (fenv : fEnv) : option statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  let allocF := Efield tinfd allocIdent valPtr in
  let limitF := Efield tinfd limitIdent valPtr in
  match asgnAppVars'' (firstn nParam vs) (firstn nParam ind) fenv , asgnFunVars' (firstn nParam vs) (firstn nParam ind) with
  | Some bef , Some aft =>
    Some (Sifthenelse
            (!(Ebinop Ole (Ederef arr uval) (limitF -' allocF) type_bool))
            (bef ; Scall None gc (arr :: tinf :: nil) ; aft)
            Sskip)
  | _, _ => None
  end.

Definition make_case_switch (x:positive) (ls:labeled_statements) (ls': labeled_statements):=
      (isPtr caseIdent x;
             Sifthenelse
               (bvar caseIdent)
               (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
             (
               Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
                      ls')).




Fixpoint translate_body (e : exp) (fenv : fEnv) (cenv:cEnv) (ienv : n_iEnv) (map : M.t positive) : option statement :=
  match e with
  | Econstr x t vs e' =>
    prog <- assignConstructorS cenv ienv fenv x t vs ;;
         prog' <- translate_body e' fenv cenv ienv map ;;
         ret (prog ; prog')
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (cTag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body (snd p) fenv cenv ienv map ;;
                   p' <- makeCases l' ;;
                   let '(ls , ls') := p' in
                   match (make_cRep cenv (fst p)) with
                   | Some (boxed t a ) =>
                     let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                     (match ls with
                     | LSnil =>
                       ret ((LScons None
                                    (Ssequence prog Sbreak)
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.land tag 255))
                                    (Ssequence prog Sbreak)
                                    ls), ls')
                     end)
                   | Some (enum t) =>
                     let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                     (match ls' with
                     | LSnil =>
                       ret (ls, (LScons None
                                        (Ssequence prog Sbreak)
                                        ls'))
                     | LScons _ _ _ =>
                       ret (ls, (LScons (Some (Z.shiftr tag 1))
                                        (Ssequence prog Sbreak)
                                        ls'))
                     end)                       
                   | None => None
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (make_case_switch x ls ls')
  | Eproj x t n v e' =>
    prog <- translate_body e' fenv cenv ienv map ;;
         ret (x ::= Field(var v, Z.of_N n) ;
                prog)
  | Efun fnd e => None
  | Eapp x t vs =>

    inf <- M.get t fenv ;;
        asgn <- asgnAppVars vs (snd inf) fenv ;;
    let vv := makeVar x fenv in
                      ret (asgn ; Efield tinfd allocIdent valPtr  :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
                                    (mkCall ([mkFunTy (length (firstn nParam vs))] vv) vs))
  | Eprim x p vs e => None
  | Ehalt x =>
    (* set args[1] to x  and return *)
    ret ((args[ Z.of_nat 1 ] :::= (makeVar x fenv)))
  end.

Fixpoint translate_body_fast (e : exp) (fenv : fEnv) (cenv:cEnv) (ienv : n_iEnv) (map : M.t positive) (myvs : list positive) (myind : list N) : option statement :=
  match e with
  | Econstr x t vs e' =>
    prog <- assignConstructorS cenv ienv fenv x t vs ;;
         prog' <- translate_body e' fenv cenv ienv map ;;
         ret (prog ; prog')
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (cTag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body (snd p) fenv cenv ienv map ;;
                   p' <- makeCases l' ;;
                   let '(ls , ls') := p' in
                   match (make_cRep cenv (fst p)) with
                   | Some (boxed t a ) =>
                     let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                     (match ls with
                     | LSnil =>
                       ret ((LScons None
                                    (Ssequence prog Sbreak)
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.land tag 255))
                                    (Ssequence prog Sbreak)
                                    ls), ls')
                     end)
                   | Some (enum t) =>
                     let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                     (match ls' with
                     | LSnil =>
                       ret (ls, (LScons None
                                        (Ssequence prog Sbreak)
                                        ls'))
                     | LScons _ _ _ =>
                       ret (ls, (LScons (Some (Z.shiftr tag 1))
                                        (Ssequence prog Sbreak)
                                        ls'))
                     end)                       
                   | None => None
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (make_case_switch x ls ls')
  | Eproj x t n v e' =>
    prog <- translate_body e' fenv cenv ienv map ;;
         ret (x ::= Field(var v, Z.of_N n) ;
                prog)
  | Efun fnd e => None
  | Eapp x t vs =>

    inf <- M.get t fenv ;;
        asgn <- asgnAppVars_fast myvs vs myind (snd inf) fenv ;;
    let vv := makeVar x fenv in
                      ret (asgn ; Efield tinfd allocIdent valPtr  :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
                                    (mkCall ([mkFunTy (length (firstn nParam vs))] vv) vs))
  | Eprim x p vs e => None
  | Ehalt x =>
    (* set args[1] to x  and return *)
    ret ((args[ Z.of_nat 1 ] :::= (makeVar x fenv)))
  end.

Definition mkFun (vs : list positive) (loc : list positive) (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             ((tinfIdent , threadInf) :: (map (fun x => (x , val)) (firstn nParam vs)))
             ((map (fun x => (x , val)) ((skipn nParam vs) ++ loc))++(allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, boolTy) ::nil)
             nil
             body.

Fixpoint translate_fundefs (fnd : fundefs) (fenv : fEnv) (cenv: cEnv) (ienv : n_iEnv) (map : M.t positive) : 
  option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    match translate_fundefs fnd' fenv cenv ienv map with
    | None => None
    | Some rest =>
      match translate_body e fenv cenv ienv map with
      | None => None
      | Some body =>
         match M.get t fenv with
         | None => None
         | Some inf =>
             let '(l, locs) := inf in
             match asgnFunVars vs locs with
             | None => None
             | Some asgn =>
                  match M.get f map with
                  | None => None
                  | Some gcArrIdent =>
                    match reserve gcArrIdent (Z.of_N (l + 2)) vs locs fenv with
                    | None => None
                    | Some res =>
                         ret ((f , Gfun (Internal
                                           (mkFun vs (get_allocs e)
                                                  ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                                    res) ;
                                                    asgn ;
                                                    body)))) :: rest)
                         end
                  end
             end
         end
      end
    end
  end.

Fixpoint translate_fundefs_fast (fnd : fundefs) (fenv : fEnv) (cenv: cEnv) (ienv : n_iEnv) (map : M.t positive) : 
  option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    match translate_fundefs_fast fnd' fenv cenv ienv map with
    | None => None
    | Some rest =>
      match M.get t fenv with
      | None => None
      | Some inf =>
         let '(l, locs) := inf in
         match translate_body_fast e fenv cenv ienv map vs locs  with
         | None => None
         | Some body =>
             match asgnFunVars vs locs with
             | None => None
             | Some asgn =>
                  match M.get f map with
                  | None => None
                  | Some gcArrIdent =>
                    match reserve gcArrIdent (Z.of_N (l + 2)) vs locs fenv with
                    | None => None
                    | Some res =>
                         ret ((f , Gfun (Internal
                                           (mkFun vs (get_allocs e)
                                                  ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                                    res) ;
                                                    asgn ;
                                                    body)))) :: rest)
                         end
                  end
             end
         end
      end
    end
  end.


Definition make_extern_decl (nenv:M.t BasicAst.name) (def:(positive * globdef Clight.fundef type)) (gv:bool): option (positive * globdef Clight.fundef type) :=
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

              
Fixpoint make_extern_decls (nenv:M.t BasicAst.name) (defs:list (positive * globdef Clight.fundef type)) (gv:bool): (list (positive * globdef Clight.fundef type)) :=
  match defs with
  | fdefs::defs' =>
    let decls := make_extern_decls nenv defs' gv in
    (match make_extern_decl nenv fdefs gv with
    | Some decl =>
      decl :: decls
    | None => decls
    end)
  | nil => nil
  end.

Definition body_external_decl (e : exp): (positive * globdef Clight.fundef type) :=
  let localVars := get_allocs e in 
  let params := (type_of_params (((tinfIdent, threadInf)::(map (fun x => (x , valPtr)) (firstn nParam localVars))))) in
     (bodyIdent,  Gfun (External (EF_external ("body"%string) (signature_of_type  params Tvoid cc_default)) params Tvoid cc_default)).

Fixpoint translate_funs (e : exp) (fenv : fEnv) (cenv: cEnv) (ienv : n_iEnv) (m : M.t positive) :
  option (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e =>                      (* currently assuming e is body *)
    funs <- translate_fundefs_fast fnd fenv cenv ienv m ;; 
         let localVars := get_allocs e in (* ADD ALLOC ETC>>> HERE *)
         body <- translate_body e fenv cenv ienv m ;;
              gcArrIdent <- M.get mainIdent m ;;
              ret ((bodyIdent , Gfun (Internal
                                        (mkfunction Tvoid
                                                    cc_default
                                                    ((tinfIdent, threadInf)::nil)
                                                    ((map (fun x => (x , val)) localVars) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::nil)
                                                    nil
                                                    ( allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                      limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                      argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                                                      reserve_body gcArrIdent 2%Z ;
                                                      body))))
                     :: funs)
  | _ => None
  end.

Definition nState := ExtLib.Data.Monads.StateMonad.state positive.

Definition getName : nState positive :=
  n <- get ;;
    put (n+1)%positive ;;
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


Definition show_pos x :=  pos2string x. (*nat2string10 (Pos.to_nat x). *)

Definition update_nEnv_fun_info (f f_inf : positive) (nenv : M.t BasicAst.name) : M.t BasicAst.name :=
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

Fixpoint make_fundef_info (fnd : fundefs) (fenv : fEnv) (nenv : M.t BasicAst.name)
  : nState (option (list (positive * globdef Clight.fundef type) * M.t positive * M.t BasicAst.name)) :=
  match fnd with
  | Fnil => ret (Some (nil, M.empty positive, nenv))
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => ret None
    | Some inf =>
      let '(n, l) := inf in
      rest <- make_fundef_info fnd' fenv nenv ;;
           match rest with
           | None => ret None
           | Some rest' =>
             let '(defs, map, nenv') := rest' in 
             info_name <- getName ;;
                       let len := Z.of_nat (length l) in
                       (* it should be the case that n (computed arrity from tag) = len (actual arrity) *)
                       let ind :=
                           mkglobvar
                             (Tarray uval
                                     (len + 2%Z)
                                     noattr)
                            ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int len) :: (make_ind_array l)) true false in
                       ret (Some (((info_name , Gvar ind) :: defs) ,
                                  M.set x info_name map ,
                                  update_nEnv_fun_info x info_name nenv'))
           end
    end
  end.

                

Fixpoint add_bodyinfo (e : exp) (fenv : fEnv) (nenv : M.t BasicAst.name) (map: M.t positive) (defs:list (positive * globdef Clight.fundef type)) :=
            info_name <- getName ;;
            let ind :=
                mkglobvar
                  (Tarray uval
                          2%Z
                          noattr)
                  ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int 0%Z) :: nil) true false in
            ret (Some (
                     ((info_name , Gvar ind) :: defs),
                     (M.set mainIdent info_name map),
                     (M.set info_name (nNamed "body_info"%string) nenv))).
                
                

(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Fixpoint make_funinfo (e : exp) (fenv : fEnv) (nenv : M.t BasicAst.name)
  : nState (option (list (positive * globdef Clight.fundef type) * M.t positive * M.t BasicAst.name)) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv;;
      match p with
      | None => ret None
      | Some p' =>
        let '(defs, map, nenv') := p' in
        add_bodyinfo e' fenv nenv' map defs
      end
  | _ => ret None
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

Definition make_defs (e : exp) (fenv : fEnv) (cenv: cEnv) (ienv : n_iEnv) (nenv : M.t BasicAst.name) :
  nState (exceptionMonad.exception (M.t BasicAst.name * (list (positive * globdef Clight.fundef type)))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
           match fun_inf' with
           | Some p =>
             let '(fun_inf, map, nenv') := p in
             match translate_funs e fenv cenv ienv map with
             | None => ret (exceptionMonad.Exc "translate_funs")
             | Some fun_defs' =>
               let fun_defs := rev fun_defs' in
               ret (exceptionMonad.Ret (nenv',
                          ((((global_defs e)
                               ++ fun_inf ++ fun_defs))))) 
             end
           | None => ret (exceptionMonad.Exc "make_funinfo")
           end.


Definition composites : list composite_definition :=
 (Composite threadInfIdent Struct
   ((allocIdent, valPtr) ::
                         (limitIdent, valPtr) :: (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) ::
                         (argsIdent, (Tarray uval maxArgs noattr))::nil)
   noattr ::  nil).

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) (add_comp:bool): option Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites defs (bodyIdent :: nil) main in
  match res with
  | Error e => None
  | OK p => Some p
  end.



(* Wrap program in empty Efun if e.g. fully inlined *)
Definition wrap_in_fun (e:exp) :=
  match e with
  | Efun fds e' =>
    e
  | _ => Efun Fnil e
  end. 

Definition add_inf_vars (nenv: M.t BasicAst.name): M.t BasicAst.name :=
  M.set isptrIdent (nNamed "is_ptr"%string) (
  M.set argsIdent (nNamed "args"%string) (
          M.set allocIdent (nNamed "alloc"%string) (
                  M.set limitIdent (nNamed "limit"%string) (
                        M.set gcIdent (nNamed "garbage_collect"%string) (
                                M.set mainIdent (nNamed "main"%string) (
                                       M.set bodyIdent (nNamed "body"%string) (
                                               M.set threadInfIdent (nNamed "thread_info"%string) (
                                                       M.set tinfIdent (nNamed "tinfo"%string) (
                                                               M.set heapInfIdent (nNamed "heap"%string) (
                                                                     M.set numArgsIdent (nNamed "num_args"%string) nenv)))))))))).
     
     

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


Fixpoint make_argList' (n:nat) (nenv:M.t BasicAst.name) : nState (M.t BasicAst.name * list (ident * type)) :=
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

Fixpoint make_argList (n:nat) (nenv:M.t BasicAst.name) : nState (M.t BasicAst.name * list (ident * type)) :=
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
 1 ) Constructors and eliminators for every inductive types in the n_iEnv
2 ) Direct style calling functions for the original (named) functions 
 *)
 
Fixpoint make_constructors (cenv:cEnv) (nTy:BasicAst.ident) (ctrs: list (BasicAst.name * cTag * N * N)) (nenv : M.t BasicAst.name): nState (M.t BasicAst.name * (list (positive * globdef Clight.fundef type))) :=
  match ctrs with
  | nil => ret (nenv, nil)
  | (nAnon, tag, 0%N, ord)::ctrs =>
    make_constructors cenv nTy ctrs nenv
  | (nAnon, ctag, Npos _ , _)::ctrs =>
    make_constructors cenv nTy ctrs nenv
  | (nNamed nCtr, ctag, 0%N, ord)::ctrs => (* unboxed *)
    constr_fun_id <- getName;;
                let constr_body := Sreturn (Some (Econst_int (Int.repr (Z.add (Z.shiftl (Z.of_N ord) 1) 1)) val)) in
                let constr_fun := Internal (mkfunction
                                      val
                                      cc_default
                                      nil
                                      nil
                                      nil
                                      constr_body
                                           ) in
                let nenv := M.set constr_fun_id (nNamed (append "make_" (append nTy (append "_" nCtr)))) nenv in
    (* elet cFun :=  (Internal (mkFun )) *)
                l <- make_constructors cenv nTy ctrs nenv;;
                  let (nenv, funs) := l in                  
              ret (nenv, (constr_fun_id ,(Gfun constr_fun))::funs)
  | (nNamed nCtr, ctag, Npos arr, ord)::ctrs => (* boxed *)
    constr_fun_id <- getName;;
                  argvIdent <- getName;;
                  argList <- make_argList (Pos.to_nat arr) nenv;;
                  let (nenv, argList) := argList in
                  let asgn_s := make_constrAsgn argvIdent argList in
                  let header := c_int (Z.of_N ((N.shiftl (Npos arr) 10) + ord)) val in
                  let constr_body := Ssequence (Sassign (Field(var argvIdent, 0%Z)) header)
                                               (Ssequence asgn_s (Sreturn (Some (add (Evar argvIdent argvTy) (c_int 1%Z val))))) in
                  let constr_fun := Internal (mkfunction
                                                val
                                                cc_default
                                                (argList ++ ((argvIdent, argvTy)::nil))
                                                nil
                                                nil
                                                constr_body
                                             ) in
                  let nenv :=
                              M.set argvIdent (nNamed "argv"%string) (
                                      M.set constr_fun_id (nNamed (append "make_" (append nTy (append "_" nCtr)))) nenv) in
                  (* elet cFun :=  (Internal (mkFun )) *)
                  l <- make_constructors cenv nTy ctrs nenv;;
                    let (nenv, funs) := l in                  
                    ret (nenv, (constr_fun_id ,(Gfun constr_fun))::funs)
  end.


(* make a function discriminating over the different constructors of an inductive type *)


Notation charPtrTy :=
  (Tpointer
     tschar
        noattr).
    
Notation nameTy :=
  (Tpointer charPtrTy
      noattr).

Notation arityTy :=
  (Tpointer val noattr).



Fixpoint make_elim_Asgn (argv:ident) (valIdent:ident) (arr:nat): statement :=
  let argv_proj := make_proj (var argv) 0%nat arr in
  let val_proj := make_proj (var valIdent) 0%nat arr in
  make_Asgn argv_proj val_proj.




Fixpoint asgn_string_init (s:string) : list init_data :=
 match s with
| EmptyString => (Init_int8 Int.zero::nil)
| String c s' =>
  let l := asgn_string_init s' in
  let i := (Int.repr (Z.of_N (N_of_ascii c))) in
  (Init_int8 i::l)                                               
 end.

(* create a global variable with a string constant, return its id *)
Definition asgn_string_gv  (s:string) : nState ( ident * globdef Clight.fundef type) :=
  strIdent <- getName;;
           let len := String.length s in
           let init := asgn_string_init s in
           let gv := Gvar (mkglobvar (tarray tschar (Z.of_nat len))
                     init
                     true
                     false) in
           ret (strIdent, gv).
  

Definition asgn_string (charPtr:ident) (n:name): nState (statement *  list (ident * globdef Clight.fundef type)) := 
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


Definition pad_char_init (l: list init_data) (n:nat) :=
  let m := n - (length l) in
  l++(List.repeat (Init_int8 Int.zero) m).

Fixpoint make_names_init (nameList:list BasicAst.name) (n:nat) :=
  match nameList with
  | nil =>
    (n, nil)
  | (nNamed s)::nameList' =>
    let (max_len, init_l) := make_names_init nameList' (max n ((String.length s)+1)) in
    let i := pad_char_init (asgn_string_init s) max_len in
    (max_len, i++init_l)
  | (nAnon)::nameList' =>
    let (max_len, init_l) := make_names_init nameList' n in
    let i := pad_char_init (asgn_string_init "") max_len in
    (max_len, i++init_l)
  end.
    

Definition make_namesGV (nameList:list BasicAst.name ): (globdef Clight.fundef type) :=
  let (max_len, init_l) := make_names_init nameList 1 in
  Gvar (mkglobvar (tarray (tarray tschar (Z.of_nat max_len)) (Z.of_nat (length nameList)))
                     init_l
                     true
                     false).

  
Definition make_eliminator (cenv: cEnv) (nTy:BasicAst.ident) (ctrs: list (BasicAst.name * cTag * N * N)) (nenv:M.t BasicAst.name): nState (M.t BasicAst.name * (list (ident * globdef Clight.fundef type))) :=
  valIdent <- getName;;
  ordIdent <- getName;;         
  argvIdent <- getName;;
  elim_fun_id <- getName;;
  nameIdent <- getName;;
  gv_arrIdent <- getName;;
  gv_namesIdent <- getName;;
 temp <- (fix make_elim_cases (ctrs: list (BasicAst.name * cTag * N * N)) (currOrd:nat) :=
                       match ctrs with
                       | nil => ret (LSnil, LSnil, nil, nil)
                       | (nName, ctag, n, ord)::ctrs =>
                         temp <- make_elim_cases ctrs (S currOrd) ;;
                              let '(ls, ls', nameList,  arrList) := temp in
(*                              name_p <- asgn_string nameIdent nName;;
                                let '(name_s, name_gv) := name_p in *)
                         let curr_s := Ssequence
                                         (* name_s *) Sskip
                                         (Ssequence                                          
                                            (Sassign (Field(var ordIdent, 0%Z)) (c_int (Z.of_nat currOrd) val))
                                            (Ssequence (make_elim_Asgn argvIdent valIdent (N.to_nat n))
                                                       Sbreak)) in
                         (match n with
                         | 0%N => ret (ls, LScons (Some (Z.of_N ord)) curr_s ls', nName::nameList,  n::arrList)
                         | Npos p => ret (LScons (Some (Z.of_N ord)) curr_s ls, ls', nName::nameList, n::arrList)
                          end)
                       end) ctrs 0;;
 let '( ls, ls', nameList, arrList) := temp in
      let gv_names := make_namesGV nameList in
      let gv_arr :=  make_arrGV arrList in
  let elim_body := (make_case_switch valIdent ls  ls') in
  let elim_fun :=
      Internal (mkfunction
                  Tvoid
                  cc_default
                  ((valIdent, val)::(ordIdent, valPtr)::(argvIdent, argvTy)::nil)
                  ((caseIdent, boolTy)::nil)
                  nil
                  elim_body
               ) in
  let nenv :=
      M.set gv_namesIdent (nNamed (append "names_of_" nTy)) (
      M.set gv_arrIdent (nNamed (append "arities_of_" nTy)) (
      M.set ordIdent (nNamed "ordinal"%string) (
              M.set valIdent (nNamed "val"%string) (
              M.set argvIdent (nNamed "argv"%string) (
                      M.set elim_fun_id (nNamed (append "elim_" nTy)) nenv))))) in
  
    ret (nenv, (gv_namesIdent, gv_names)::(gv_arrIdent, gv_arr)::(elim_fun_id ,Gfun elim_fun)::nil).
  

Fixpoint make_interface (cenv: cEnv)(ienv_list:list (positive * n_iTyInfo)) (nenv : M.t BasicAst.name):  nState (M.t BasicAst.name * (list (ident * globdef Clight.fundef type))) :=
  match ienv_list with
  | nil => ret (nenv, nil)
  | (_, (nAnon, _))::ienv_list' =>
  (* skip anon-types *)
    make_interface cenv ienv_list' nenv
  | (_, (nNamed nTy, lCtr))::ienv_list' =>    
    l1 <- make_constructors cenv nTy lCtr nenv;;
       let (nenv, def1) := l1 in
       l2 <- make_eliminator cenv nTy lCtr nenv;;
      let (nenv, def2) := l2 in
      l3 <- make_interface cenv ienv_list' nenv;;
         let (nenv, def3) := l3 in
         ret (nenv, (def1++def2++def3))
  end.
    




Definition make_tinfoIdent := 20%positive.
Definition exportIdent := 21%positive.


Definition make_tinfo_rec: (positive * globdef Clight.fundef type) := (make_tinfoIdent , Gfun (External (EF_external "make_tinfo"
                                              (mksignature (nil) (Some val_typ) cc_default))
                                 Tnil
                                 threadInf
                                 cc_default
    )).

Definition export_rec: (positive * globdef Clight.fundef type) := (exportIdent , Gfun (External (EF_external "export"
                                              (mksignature (cons val_typ nil) (Some val_typ) cc_default))
                                 (Tcons threadInf Tnil)
                                 valPtr
                                 cc_default
    )).



(* make direct-style function that calls function with a new tinfo and a halting termination and exports the result outside of the GC-heap 
 f_name is the given name of the function (direct-style will be set to "direct_"++f_name
 f_ident is the function id as compiled by certicoq
 f_ar is the arity of the function (including environment)

 The generated function expects that the first f_ar+1 projections of argv are its environment and the expected arguments to f

OS note 09/05/18, this is deprecated, we instead generate special eliminators for closures

Definition make_direct (f_name:string) (f_ident: ident) (f_ar:nat) (nenv:M.t BasicAst.name): nState (M.t BasicAst.name * (ident * globdef Clight.fundef type)) :=
    directFunIdent <- getName;;
    argcIdent <- getName;;
    argvIdent <- getName;;
    tinfoIdent <- getName;;
    retIdent <- getName;;
    let left_args := make_proj (Efield (Evar tinfoIdent threadInf) argsIdent valPtr) 2 f_ar in
    let right_args := make_proj (var argvIdent) 0 f_ar in
    let asgn_s := make_Asgn left_args right_args in
    let body_s := Ssequence
                    asgn_s
                    (Ssequence 
                    (Scall (Some tinfoIdent) (Evar make_tinfoIdent make_tinfoTy) nil)
                    (Ssequence
                       (Scall None (Evar f_ident funTy) (cons (Evar tinfoIdent threadInf) nil))
                       (Ssequence
                          (Scall (Some retIdent) (Evar exportIdent exportTy) (cons (Evar tinfoIdent threadInf) nil))
                          (Sreturn  (Some (Etempvar retIdent valPtr))))))
                    
                    
    in
    let nenv :=
        M.set tinfoIdent (nNamed "tinfo"%string) (
                M.set retIdent (nNamed "ret"%string) (
                        M.set argcIdent (nNamed "argc"%string) (
                                M.set argvIdent (nNamed "argv"%string) nenv))) in
  ret (nenv, (directFunIdent, Gfun (Internal
                                      (mkfunction
                                         (Tpointer Tvoid noattr)
                                         cc_default
                                         ((argcIdent, intTy)::(argvIdent, argvTy)::nil)
                                         nil
                                         ((retIdent, valPtr)::(tinfoIdent, threadInf)::nil)
                                         body_s)))).
*)

(* generate a function equivalent to halt, received a tinfo, desired results is already in tinfo.args[1], and
 a halting continuation closure *)
Definition make_halt (nenv:M.t BasicAst.name): nState (M.t BasicAst.name * (ident * globdef Clight.fundef type) * (ident * globdef Clight.fundef type)) :=
  haltIdent <- getName;;
            halt_cloIdent <- getName;;
            let nenv := M.set halt_cloIdent (nNamed "halt_clo"%string) (M.set haltIdent (nNamed "halt"%string) nenv) in            
  ret (nenv, (haltIdent, Gfun (Internal
                                      (mkfunction
                                         Tvoid
                                         cc_default
                                         ((tinfIdent, threadInf)::nil)
                                         nil
                                         nil
                                         (Sreturn None)))), (halt_cloIdent, Gvar (mkglobvar  (tarray uval 2) ((Init_addrof haltIdent Ptrofs.zero) ::
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

Definition make_call (closExpr:expr) (fIdent:ident) (envIdent:ident) (argsExpr:expr) (argIdent:ident) (haltIdent:ident) :=
  
  (fIdent ::=  (Field(closExpr , Z.of_nat 0));
                                      envIdent ::= (Field(closExpr, Z.of_nat 1));

                    (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar envIdent val));
                    (Sassign (Field(argsExpr, Z.of_nat 1)) (Evar haltIdent val));
                    (Sassign (Field(argsExpr, Z.of_nat 2)) (Etempvar argIdent val));
                    (call ([pfunTy] (funVar fIdent)))).

Fixpoint make_n_calls (n:nat) (closIdent:ident) (fIdent:ident) (envIdent:ident) (argsExpr:expr) (argPairs:list (ident * type)) (retIdent:ident) (haltIdent:ident) :=
  match n, argPairs with
  | S 0, ((argIdent, argTy)::tl) =>
    make_call (Etempvar closIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent
  | S (S n), ((argIdent, _)::tl) =>
    let s := make_n_calls (S n) closIdent  fIdent envIdent argsExpr tl retIdent haltIdent in
    Ssequence s
              ( retIdent ::= (Field(argsExpr, Z.of_nat 1)); make_call (Etempvar retIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent)
  | _, _ => Sskip
  end.
    

Definition make_call_n_export_b (nenv:M.t BasicAst.name) (n:nat) (export:bool) (haltIdent:ident): nState (M.t BasicAst.name * (ident * globdef Clight.fundef type)) :=
    callIdent <- getName;;
    retIdent <- getName;;
    clo_ident <- getName;;
    f_ident <- getName;;
    env_ident <- getName;;
    t <- make_argList n nenv;;
    (*    let tinfo_s := if export then (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) else Sskip in *)
    let tinfo_s := Sifthenelse (Ebinop Oeq (Evar tinfIdent threadInf)
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) Sskip in
    let (nenv, argsL) := t in
    let argsS :=  (Efield tinfd argsIdent valPtr) in
    let left_args := make_proj argsS 2 n in
    let asgn_s := make_n_calls n clo_ident f_ident env_ident argsS (rev argsL) retIdent haltIdent in
(*     let asgn_s := ( f_ident ::=  (Field(Etempvar clo_ident valPtr , Z.of_nat 0));
                                 2     env_ident ::= (Field(Etempvar clo_ident valPtr, Z.of_nat 1));

                    (Sassign (Field(argsS, Z.of_nat 0)) (Etempvar env_ident val));
                    (Sassign (Field(argsS, Z.of_nat 1)) (Evar haltIdent val));
                       (make_Asgn left_args (List.map (fun (s:ident*type) => let (i, t) := s in
                                                                Etempvar i t
                                                     ) argsL))) in *)
    let export_s := (if export then
                      (Scall (Some retIdent) (Evar exportIdent exportTy) (cons tinf nil))
                    else
                      (retIdent ::= (Field(argsS, Z.of_nat 1)))) in
    let body_s := Ssequence                    
                    (tinfo_s; asgn_s)
                    (export_s; Sreturn  (Some (Etempvar retIdent valPtr)))
                    
                    
    in
    let callStr := append "call_" (nat2string10 n) in
    let callStr := if export then append callStr "_export" else callStr in
    let nenv :=
        M.set env_ident (nNamed "envi"%string) (M.set clo_ident (nNamed "clos"%string) (M.set callIdent (nNamed callStr)  (M.set f_ident (nNamed "f"%string) (M.set retIdent (nNamed "ret"%string) nenv)))) in
    (* if export, tinf is local, otherwise is a param *)
    let params := ((clo_ident, val)::argsL) in
    let vars := ((f_ident, valPtr)::(env_ident, valPtr)::(retIdent, valPtr)::nil) in
  ret (nenv, (callIdent, Gfun (Internal
                                      (mkfunction
                                         (Tpointer Tvoid noattr)
                                         cc_default
                                         params
                                         nil
                                         vars
                                         body_s)))).


Definition tinf_def:globdef Clight.fundef type :=
  Gvar (mkglobvar threadInf ((Init_space 4%Z)::nil) false false).


Definition make_empty_header (cenv:cEnv) (ienv:n_iEnv) (e:exp) (nenv : M.t BasicAst.name):  nState (option (M.t BasicAst.name  * (list (ident * globdef Clight.fundef type)))) :=
    ret (Some (nenv, nil)).


Definition make_header (cenv:cEnv) (ienv:n_iEnv) (e:exp) (nenv : M.t BasicAst.name):  nState (option (M.t BasicAst.name  * (list (ident * globdef Clight.fundef type)))) :=
  l <- make_interface cenv (M.elements ienv) nenv;;
    let (nenv, inter_l) := l in
    l <- make_halt nenv;;
      let  '(nenv, halt_f, (halt_cloIdent, halt_clo_def)) := l in
      l <- make_call_n_export_b nenv 1 false halt_cloIdent;;
        let  '(nenv, call_0) := l in
     l <- make_call_n_export_b nenv 2 false halt_cloIdent;;
        let  '(nenv, call_2) := l in
        l <- make_call_n_export_b nenv 1 true halt_cloIdent;;
          let  '(nenv, call_1) := l in
        l <- make_call_n_export_b nenv 3 true halt_cloIdent;;
          let  '(nenv, call_3) := l in
          ret (Some (nenv, (halt_f::(halt_cloIdent, halt_clo_def)::(tinfIdent, tinf_def)::call_0::call_1::call_2::call_3::inter_l))).




(* end of header file *)

Definition compile (e : exp) (cenv : cEnv) (nenv : M.t BasicAst.name) :
  exceptionMonad.exception (M.t BasicAst.name * option Clight.program * option Clight.program) :=
  let e := wrap_in_fun e in 
  match compute_fEnv e with
  | None => exceptionMonad.Exc "L6_to_Clight: Failure in compute_fEnv, e is not a function"
  | Some fenv => 
    (let ienv := compute_iEnv cenv in
     let p'' := make_defs e fenv cenv ienv nenv in
     let n := ((max_var e 100) + 1)%positive in
     let p' :=  (p''.(runState) n) in
     let m := snd p' in
     match fst p' with
     | exceptionMonad.Exc s => exceptionMonad.Exc (append "L6_to_Clight: Failure in make_defs:" s)
     | exceptionMonad.Ret p =>
       let '(nenv, defs) := p in
       let nenv := (add_inf_vars (ensure_unique nenv)) in 
       let forward_defs := make_extern_decls nenv defs false in
       (* replace this by make_header to generate interface for datatypes *)
       let header_pre := make_empty_header cenv ienv e nenv in 
       (*     let header_p := (header_pre.(runState) m%positive) in *)
       let header_p := (header_pre.(runState) 1000000%positive) in (* should be m, but m causes collision in nenv for some reason *)
       (match fst header_p with
        | None => exceptionMonad.Exc "L6_to_Clight: Failure in make_header"
        | Some (nenv, hdefs) =>
          exceptionMonad.Ret (M.set make_tinfoIdent (nNamed "make_tinfo"%string) (M.set exportIdent (nNamed "export"%string) nenv), mk_prog_opt ((body_external_decl e)::(make_extern_decls nenv hdefs true)) mainIdent false, mk_prog_opt (make_tinfo_rec::export_rec::forward_defs++defs++hdefs) mainIdent true)
        end)
  end) end.



Definition err {A : Type} (s : String.string) : res A :=
  Error ((MSG s) :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil mainIdent nil eq_refl.

Definition stripOption (p : (option Clight.program))
  : Clight.program := 
     match p with
     | None => empty_program
     | Some p' => p'
     end.


                    

Definition print_Clight_dest_names : Clight.program -> list (positive * name) -> String.string -> unit :=
  fun p s l => print_Clight_dest_names' p
                                        s
                                        l.

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

(*
Definition print_test := print_Clight (test_result).
 *)
End TRANSLATION.
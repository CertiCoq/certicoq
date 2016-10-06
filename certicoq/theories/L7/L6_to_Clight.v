(* 
  Translation from L6 to CompCert CLight
  
  2016 -- Matthew Weaver 
 *)
Require Import Coq.ZArith.ZArith
Coq.Lists.List List_util
Coq.Program.Basics.

Require Import ExtLib.Structures.Monads
        ExtLib.Data.Monads.OptionMonad
        ExtLib.Data.Monads.StateMonad.

Import MonadNotation.
Open Scope monad_scope.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.lib.Maps
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight.

Require Import L6.cps.

Variable (argsIdent : ident).
Variable (allocIdent : ident).
Variable (limitIdent : ident).
Variable (gcIdent : ident).
Variable (mainIdent : ident).
Variable (bodyIdent : ident).
Variable (threadInfIdent : ident).
Variable (tinfIdent : ident).
Variable (heapInfIdent : ident).

(* temporary function to get something working *)
Fixpoint makeArgList (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList vs')
  end.

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

Definition compute_fEnv (e : exp) : fEnv :=
  compute_fEnv' (max_depth e) (M.empty fTyInfo) e.


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

Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => S (max_allocs e')
  | Ecase x cs =>
    (fix helper (cs : list (cTag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_allocs e') (helper cs')
       end) cs
  | Eproj x t n v e' => S (max_allocs e')
  | Efun fnd e' => max (max_allocs_fundefs fnd) (max_allocs e')
  | Eapp x t vs => 0
  | Eprim x p vs e' => S (max_allocs e')
  | Ehalt x => 0
  end
with max_allocs_fundefs (fnd : fundefs) :=
       match fnd with
       | Fnil => 0
       | Fcons f t vs e fnd' => max ((length vs) + (max_allocs e))
                                   (max_allocs_fundefs fnd')
       end.

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
  | Ehalt x => 0
  end
with max_args_fundefs (fnd : fundefs) :=
       match fnd with
       | Fnil => 0
       | Fcons f t vs e fnd' => max (max (length vs) (max_args e))
                                   (max_allocs_fundefs fnd')
       end.

Definition update_iEnv (ienv : iEnv) (p : positive) (cInf : cTyInfo) : iEnv :=
  let '(t, arity, ord) := cInf in
  match (M.get t ienv) with
  | None => M.set t ((p, arity) :: nil) ienv
  | Some iInf => M.set t ((p, arity) :: iInf) ienv
  end.

Definition compute_iEnv (cenv : cEnv) : iEnv :=
  M.fold update_iEnv cenv (M.empty _).

Fixpoint getEnumOrdinal' (ct : cTag) (l : list (cTag * N)) : option N :=
  match l with
  | nil => None
  | cons (ct' , n) l' =>
    match (n =? 0)%N with
    | true => 
      match (ct =? ct')%positive with
      | true => ret 0%N
      | false =>
        n' <- getEnumOrdinal' ct l' ;;
           ret (n' + 1)%N
      end
    | false => getEnumOrdinal' ct l'
    end
  end.

Definition getEnumOrdinal (ct : cTag) (l : list (cTag * N)) : option N :=
  getEnumOrdinal' ct (rev l).

Fixpoint getBoxedOrdinal' (ct : cTag) (l : list (cTag * N)) : option N :=
  match l with
  | nil => None
  | cons (ct' , n) l' =>
    match (n =? 0)%N with
    | true => getBoxedOrdinal' ct l'
    | false => 
      match (ct =? ct')%positive with
      | true => Some 0%N
      | false =>
        n' <- getBoxedOrdinal' ct l';;
           ret (n' + 1)%N
      end
    end
  end.

Definition getBoxedOrdinal (ct : cTag) (l : list (cTag * N)) : option N :=
  getBoxedOrdinal' ct (rev l).

Inductive cRep : Type :=
| enum : N -> cRep
(* [enum t] represents a constructor with no parameters with tag [t] *)
| boxed : N -> N -> cRep.
(* [boxed t a] represents a construct with arity [a] and tag [t]  *)

Definition make_cRep (cenv : cEnv) (ct : cTag) : option cRep :=
  p <- M.get ct cenv ;;
    let '(it , n , r) := p in
    let ienv := compute_iEnv cenv in
    l <- M.get it ienv ;;
      match (n =? 0)%N with
      | true =>
        n' <- getEnumOrdinal ct l ;;
           ret (enum n')
      | false =>
        n' <- getBoxedOrdinal ct l ;;
           ret (boxed n' r)
      end.

Notation funTy := (Tfunction Tnil Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation intTy := (Tint I32 Signed
                       {| attr_volatile := false; attr_alignas := None |}).

Notation val := intTy. (* in Clight, SIZEOF_PTR == SIZEOF_INT *)

Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Notation allocPtr := (Evar allocIdent valPtr).
Notation limitPtr := (Evar limitIdent valPtr).
Notation args := (Evar argsIdent valPtr). (*wrong! is array *) 
Notation gc := (Evar gcIdent funTy).
Notation threadInf := (Tstruct threadInfIdent noattr).
Notation tinf := (Evar tinfIdent threadInf).
Notation heapInf := (Tstruct heapInfIdent noattr).

Definition add (a b : expr) := Ebinop Oadd a b valPtr.
Notation " a '+'' b " := (add a b) (at level 30).

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

Notation "'call' f " := (Scall None f nil) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z intTy))) (at level 36). (* what is the type of int being added? *)

Definition reserve (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray intTy l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (allocPtr +' (Ederef arr intTy)) limitPtr type_bool))
    (Scall None gc (arr :: tinf :: nil))
    Sskip.
     
Fixpoint makeTagZ (cenv : cEnv) (ct : cTag) : option Z :=
  rep <- make_cRep cenv ct ;;
      match rep with
      | enum t => ret (Z.of_N (t * 2 + 1))
      | boxed t a => ret (Z.of_N (a * 2 ^ 10 + t * 2))
      end.

Definition makeTag (cenv : cEnv) (ct : cTag) : option expr :=
  t <- makeTagZ cenv ct ;;
    ret (c_int t val).

Fixpoint assignConstructor (cenv : cEnv) (x : positive) (t : cTag) (vs : list positive) :=
  match vs with
  | nil =>
    tag <- makeTag cenv t;;
        rep <- make_cRep cenv t ;;
        match rep with
        | enum _ =>           
          ret (x ::= tag)
        | boxed _ a =>
          ret (x ::= allocPtr +' (c_int Z.one val);
                 allocPtr :::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val) ;
                 Field(var x, -1) :::= tag)
        end
  | cons v vs' =>
    prog <- assignConstructor cenv x t vs' ;;
         ret (prog ;
                Field(var x, Z.of_nat (length vs')) :::= var v)
  end.

Definition isPtr (x : positive) :=
  int_eq
    (Ebinop Oand
            ([intTy] (var x))
            (c_int 1 intTy)
            intTy)
    (c_int 0 intTy).

Definition isBoxed (cenv : cEnv) (ct : cTag) : bool :=
  match make_cRep cenv ct with
  | None => false
  | Some rep => match rep with
               | enum t => false
               | boxed t a => true
               end
  end.

Fixpoint asgnFunVars (vs : list positive) (ind : list N) :
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
      rest <- asgnFunVars vs' ind' ;;
           ret (v ::= Field(args, Z.of_N i) ;
                  rest)
    end
  end.

Fixpoint asgnAppVars (vs : list positive) (ind : list N) :
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
      rest <- asgnAppVars vs' ind' ;;
           ret (Field(args, Z.of_N i) :::= (var v) ;
                  rest)
    end
  end.

(* FIX: Think am using wrong type annotation in [Ederef] expressions *)
Fixpoint translate_body (e : exp) (fenv : fEnv) (cenv : cEnv) (map : M.tree positive) : option statement :=
  match e with
  | Econstr x t vs e' =>
    prog <- assignConstructor cenv x t vs ;;
         prog' <- translate_body e' fenv cenv map ;;
         ret (prog ; prog')
  | Ecase x cs =>
    p <- ((fix makeCases (l : list (cTag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body (snd p) fenv cenv map ;;
                   p' <- makeCases l' ;;
                   tag <- makeTagZ cenv (fst p) ;;
                   let '(ls , ls') := p' in
                   match isBoxed cenv (fst p) with
                   | false =>
                     ret ((LScons (Some tag)
                                  prog
                                  ls), ls')
                   | true =>
                     ret (ls, (LScons (Some tag)
                                      prog
                                      ls'))
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (Sifthenelse
             (isPtr x)
             (Sswitch (var x)
                      ls)  
             (Sswitch ( *([valPtr] (var x)))
                      ls')) 
  | Eproj x t n v e' =>
    prog <- translate_body e' fenv cenv map ;;
         ret (x ::= Field(var v, Z.of_N n) ;
                prog)
  | Efun fnd e => None
  | Eapp x t vs =>
    inf <- M.get t fenv ;;
        asgn <- asgnAppVars vs (snd inf) ;;
        ret (asgn ; 
               call ([funTy] (var x)))
  | Eprim x p vs e => None
  | Ehalt x => Some (Sreturn (Some (var x)))
  end.

Definition mkFun (vs : list positive) (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             nil
             (map (fun x => (x , val)) vs)
             nil
             body.

Fixpoint translate_fundefs (fnd : fundefs) (fenv : fEnv) (cenv : cEnv) (map : M.tree positive) : 
  option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    rest <- translate_fundefs fnd' fenv cenv map ;;
         body <- translate_body e fenv cenv map ;;
         let localVars := vs ++ (get_allocs e) in
         inf <- M.get t fenv ;;
             let '(l, locs) := inf in
             asgn <- asgnFunVars vs locs;;
                  gcArrIdent <- M.get f map ;;
                  ret ((f , Gfun (Internal
                                    (mkFun localVars
                                           ((reserve gcArrIdent
                                                     (Z.of_nat ((length l) + 2))) ;
                                              asgn ;
                                              body)))) :: rest)
  end.

Fixpoint translate_funs (e : exp) (fenv : fEnv) (cenv : cEnv) (map : M.tree positive) :
  option (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e =>                      (* currently assuming e is main *)
    funs <- translate_fundefs fnd fenv cenv map ;; 
         let localVars := get_allocs e in
         body <- translate_body e fenv cenv map ;;
              gcArrIdent <- M.get mainIdent map ;;
              ret ((bodyIdent , Gfun (Internal
                                        (mkFun localVars
                                               (reserve gcArrIdent 2%Z) ;
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
  | n :: l' => (Init_int32 (Int.repr (Z.of_N n))) :: (make_ind_array l')
  end.


(* needs cleanup (pull out more helper functions) *)
Fixpoint make_fundef_info (fnd : fundefs) (fenv : fEnv)
  : nState (option ((list (positive * globdef Clight.fundef type)) * (M.tree positive))) :=
  match fnd with
  | Fnil => ret (Some (nil, M.empty positive))
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => ret None
    | Some inf =>
      let '(n, l) := inf in
      rest <- make_fundef_info fnd' fenv ;;
           match rest with
           | None => ret None
           | Some rest' =>
             let '(defs, map) := rest' in 
             info_name <- getName ;;
                       let len := Z.of_nat (length l) in
                       let ind :=
                           mkglobvar
                             (Tarray intTy
                                     (len + 2%Z)
                                     noattr)
                            ((Init_int32 (Int.repr (Z.of_N n))) :: (Init_int32 (Int.repr len)) :: (make_ind_array l)) false false in
                       ret (Some (((info_name , Gvar ind) :: defs) ,
                                 M.set x info_name map))
           end
    end
  end.

Fixpoint make_funinfo (e : exp) (fenv : fEnv) : nState (option ((list (positive * globdef Clight.fundef type)) * M.tree positive)) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv
      match p with
      | None => None
      | Some p' =>
        let '(defs, map) := p' in 
        info_name <- getName ;;
                  let ind :=
                      mkglobvar
                        (Tarray intTy
                                2%Z
                                noattr)
                        ((Init_int32 (Int.repr (Z.of_N (maxAllocs e')))) :: (Init_int32 Int.zero) :: nil) false false in
                  ret (Some (((info_name , Gvar ind) :: defs) ,
                             M.set mainIdent info_name map))
  | _ => ret None
  end.

Definition global_defs (e : exp)
  : list (positive * globdef Clight.fundef type) :=
  let maxArgs := (Z.of_nat (max_args e)) in
  (allocIdent, Gvar (mkglobvar valPtr nil false false))
    :: (limitIdent , Gvar (mkglobvar valPtr nil false false))
    :: (argsIdent , Gvar (mkglobvar (Tarray val maxArgs noattr)
                                    nil
                                    false false))
    :: (gcIdent , Gfun (External (EF_external "gc"
                                              (mksignature (Tany32 :: nil) None cc_default))
                                 (Tcons threadInf (Tcons heapInf Tnil))
                                 Tvoid
                                 cc_default
       ))
    :: nil.

Definition make_defs (e : exp) (fenv : fEnv) (cenv : cEnv) :
  nState (option ((list (positive * globdef Clight.fundef type)))) :=
  fun_inf' <- make_funinfo e fenv ;;
           match fun_inf' with
           | Some p =>
             let '(fun_inf, map) := p in
             match translate_funs e fenv cenv map with
             | None => ret None
             | Some fun_defs =>
               ret (Some ((((global_defs e)
                              ++ ((tinfIdent , Gvar (
                                                   mkglobvar
                                                     threadInf
                                                     ((Init_addrof argsIdent Int.zero)
                                                        :: (Init_int32 (Int.repr ((Z.of_nat (max_args e)))))
                                                        :: (Init_addrof allocIdent Int.zero)
                                                        :: (Init_addrof limitIdent Int.zero) :: nil)
                                                     false false
                                  )) :: nil) ++ fun_inf ++ fun_defs))))
             | None => ret None 
             end
           end.

(*
Require Import Clightdefs.

Definition composites : list composite_definition :=
(Composite threadInfIdent Struct
   ((argsIdent, (tptr tint)) :: (numArgsIdent, tint) :: (allocIdent, (tptr (tptr tint))) ::
    (limitIdent, (tptr (tptr tint))) :: (heapIdent, (tptr (Tstruct heapInfIdent noattr))) ::
    nil)
   noattr :: nil).
*)

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) : option Clight.program :=
  let res := Ctypes.make_program nil defs (bodyIdent :: nil) main in
  match res with
  | Error e => None
  | OK p => Some p
  end.

Theorem refl {A : Type} {a : A} : a = a.
Proof.
  reflexivity.
Qed.

Definition compile' (e : exp) (cenv : cEnv) :
  nState (option Clight.program) :=
  let fenv := compute_fEnv e in
  p <- make_defs e fenv cenv ;;
          match p with
          | None => ret None
          | Some defs =>
             ret (mk_prog_opt defs mainIdent)
          end.

Definition x : ident := 40%positive.
Definition y : ident := 41%positive.
Definition z : ident := 42%positive.
Definition w : ident := 43%positive.
Definition f : positive:= 12%positive.
Definition b : positive := 8%positive.
Definition c : positive := 2%positive.
Definition t : cTag := 9%positive.
Definition t' : fTag := 13%positive.
Definition t'' : fTag := 15%positive.

Definition test : exp := Efun
                          (Fcons f t'
                                 (y :: z :: nil)
                                 (Eapp y t'' (z :: nil))
                                 Fnil)
                          (Eproj b t 2%N x
                                 (Eproj c t 4%N x
                                        (Eapp f t' (b :: c :: nil)))).

Definition testRes := compile' test (M.empty _).

Definition compile (e : exp) (cenv : cEnv) :
  nState (option Clight.program) :=
  let fenv := compute_fEnv e in
  p <- make_defs e fenv cenv ;;
          match p with
          | None => ret None
          | Some defs =>
             ret (mk_prog_opt defs mainIdent)
          end.

Definition err {A : Type} (s : String.string) : res A :=
  Error ((MSG s) :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil mainIdent nil refl.

Definition stripOption (p : nState (option Clight.program))
  : nState Clight.program :=
  p' <- p ;; 
     match p' with
     | None => ret empty_program
     | Some p'' => ret p''
     end.

Definition stripOption' (p : nState (option Clight.program)) (q : Clight.program)
  : nState Clight.program :=
  p' <- p ;; 
     match p' with
     | None => ret q
     | Some p'' => ret p''
     end.

Definition bogus : positive := 3000%positive.
Definition stripNameState {A : Type} (p : nState A) : A :=
  fst (p.(runState) bogus).

Definition test_result := stripNameState (stripOption (compile test (M.empty _))).

Variable (print_Clight : Clight.program -> unit).
Variable (print : String.string -> unit).

Require Import String.

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

Definition print_test := print_Clight (test_result).

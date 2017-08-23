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

Require Import Template.Ast.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values.

Require Import L6.cps
               L6.identifiers.

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

(* fEnv maps tags to function info *)
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

Definition update_iEnv (ienv : iEnv) (p : positive) (cInf : cTyInfo) : iEnv :=
  let '(name, t, arity, ord) := cInf in
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
    let '(name, it , a , n) := p in
    let ienv := compute_iEnv cenv in
    l <- M.get it ienv ;;
      match (a =? 0)%N with
      | true =>
        n' <- getEnumOrdinal ct l ;;
           ret (enum n')
      | false =>
        n' <- getBoxedOrdinal ct l ;;
           ret (boxed n' a)
      end.

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



Definition reserve (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uintTy l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uintTy) (limitPtr -' allocPtr) type_bool))
    (Scall None gc (arr :: tinf :: nil) ; allocIdent ::= Efield tinfd allocIdent valPtr)
    Sskip.


(* Don't shift the tag for boxed, make sure it is under 255 *)
Fixpoint makeTagZ (cenv : cEnv) (ct : cTag) : option Z :=
  rep <- make_cRep cenv ct ;;
      match rep with
      | enum t => ret (Z.of_N ((N.shiftl t 1) + 1))
      | boxed t a => ret (Z.of_N ((N.shiftl a 10) + t))
      end.

Definition makeTag (cenv : cEnv) (ct : cTag) : option expr :=
  t <- makeTagZ cenv ct ;;
    ret (c_int t val).

(* If x is a in our global map, then Evar, otherwise Etempvar *)
Definition makeVar (x:positive) (m:M.t positive) :=
  match M.get x m with
  | None => var x
  | Some _ => funVar x
  end.   

(* map is here to identify which value represents function  *)
Fixpoint assignConstructor' (cenv : cEnv) (map:M.t positive) (x : positive) (t : cTag) (vs : list positive) :=
  match vs with
  | nil =>
    tag <- makeTag cenv t;;
        rep <- make_cRep cenv t ;;
        match rep with
        | enum _ =>           
          ret (x ::= tag)
        | boxed _ a =>
          ret (x ::= [val] (allocPtr +' (c_int Z.one val));
                 allocIdent ::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val) ;
                 Field(var x, -1) :::= tag)
        end
  | cons v vs' =>
    prog <- assignConstructor' cenv map x t vs' ;;
         (* if v is a function name, funVar, otherwise lvar *)
    let vv := makeVar v map in      
            ret (prog ;
                   Field(var x, Z.of_nat (length vs')) :::= (*[val]*) vv)                                 
  end.

Definition assignConstructor (cenv : cEnv) (map:M.t positive) (x : positive) (t : cTag) (vs : list positive) := assignConstructor' cenv map x t (rev vs).


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
           ret  (v ::= args[ Z.of_N i ] ;
                rest)
    end
  end.


       
Fixpoint asgnAppVars' (vs : list positive) (ind : list N) :
  option statement := 
  match vs with
  | nil =>
    match ind with
    | nil => ret (Efield tinfd allocIdent valPtr  :::= allocPtr)
    | cons _ _ => None
    end
  | cons v vs' =>
    match ind with
    | nil => None
    | cons i ind' =>             
      rest <- asgnAppVars' vs' ind' ;;
           ret (args[ Z.of_N i ] :::= (var v) ;
               rest)
    end
  end.

(* Optional, reduce register pressure *)
Definition asgnAppVars vs ind :=
  match asgnAppVars' vs ind with
    | Some s =>
     ret (argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr);s)
    | None => None 
  end.



Fixpoint translate_body (e : exp) (fenv : fEnv) (cenv : cEnv) (map : M.t positive) : option statement :=
  match e with
  | Econstr x t vs e' =>
    prog <- assignConstructor cenv map x t vs ;;
         prog' <- translate_body e' fenv cenv map ;;
         ret (prog ; prog')
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (cTag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body (snd p) fenv cenv map ;;
                   p' <- makeCases l' ;;
                   tag <- makeTagZ cenv (fst p) ;;
                   let '(ls , ls') := p' in
                   match isBoxed cenv (fst p) with
                   | true =>
                     match ls with
                     | LSnil =>
                       ret ((LScons None
                                    prog
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.land tag 255))
                                    (Ssequence prog Sbreak)
                                    ls), ls')
                     end
                   | false =>
                     match ls' with
                     | LSnil =>
                       ret (ls, (LScons None
                                        prog
                                        ls'))
                     | LScons _ _ _ =>
                       ret (ls, (LScons (Some (Z.shiftr tag 1))
                                        (Ssequence prog Sbreak)
                                        ls'))
                     end
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (isPtr caseIdent x;
             Sifthenelse
               (var caseIdent)
               (Sswitch (Ebinop Oand (Field(var x, -1)) (Econst_int (Int.repr 255) val) val) ls)
             (
               Sswitch (Ebinop Oshr (var x) (Econst_int (Int.repr 1) val) val)
                      ls'))
  | Eproj x t n v e' =>
    prog <- translate_body e' fenv cenv map ;;
         ret (x ::= Field(var v, Z.of_N n) ;
                prog)
  | Efun fnd e => None
  | Eapp x t vs =>

    inf <- M.get t fenv ;;
        asgn <- asgnAppVars vs (snd inf) ;;
    let vv := makeVar x map  in
                      ret (asgn ; 
                                    call ([pfunTy] vv))
  | Eprim x p vs e => None
  | Ehalt x =>
    (* set args[1] to x  and return *)
    ret ((args[ Z.of_nat 1 ] :::= (var x)) ; Sreturn None)
  end.

Definition mkFun (vs : list positive) (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             ((tinfIdent , threadInf) :: nil)
             ((map (fun x => (x , val)) vs)++(allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, val) ::nil)
             nil
             body.

Fixpoint translate_fundefs (fnd : fundefs) (fenv : fEnv) (cenv : cEnv) (map : M.t positive) : 
  option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    match translate_fundefs fnd' fenv cenv map with
    | None => None
    | Some rest =>
      match translate_body e fenv cenv map with
      | None => None
      | Some body =>
         let localVars := vs ++ (get_allocs e) in  (* ADD ALLOC ETC>>> HERE *)
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
                         ret ((f , Gfun (Internal
                                           (mkFun localVars
                                                  ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr);
                                                    (reserve gcArrIdent
                                                            (Z.of_N (l + 2)))) ;
                                                    asgn ;
                                                    body)))) :: rest)
                  end
             end
         end
      end
    end
  end.



Fixpoint translate_funs (e : exp) (fenv : fEnv) (cenv : cEnv) (m : M.t positive) :
  option (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e =>                      (* currently assuming e is body *)
    funs <- translate_fundefs fnd fenv cenv m ;; 
         let localVars := get_allocs e in (* ADD ALLOC ETC>>> HERE *)
         body <- translate_body e fenv cenv m ;;
              gcArrIdent <- M.get mainIdent m ;;
              ret ((bodyIdent , Gfun (Internal
                                        (mkfunction Tvoid
                                                    cc_default
                                                    ((tinfIdent, threadInf)::nil)
                                                    ((map (fun x => (x , val)) localVars) ++ (allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::nil)
                                                    nil
                                                    ( allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                      limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                      argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr);
                                                      reserve gcArrIdent 2%Z ;
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

Definition show_pos x := nat2string10 (Pos.to_nat x).

Definition update_nEnv_fun_info (f f_inf : positive) (nenv : M.t Ast.name) : M.t Ast.name :=
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

Fixpoint make_fundef_info (fnd : fundefs) (fenv : fEnv) (nenv : M.t Ast.name)
  : nState (option (list (positive * globdef Clight.fundef type) * M.t positive * M.t Ast.name)) :=
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
                             (Tarray uintTy
                                     (len + 2%Z)
                                     noattr)
                            ((Init_int32 (Int.repr (Z.of_nat (max_allocs e)))) :: (Init_int32 (Int.repr len)) :: (make_ind_array l)) true false in
                       ret (Some (((info_name , Gvar ind) :: defs) ,
                                  M.set x info_name map ,
                                  update_nEnv_fun_info x info_name nenv'))
           end
    end
  end.

                

Fixpoint add_bodyinfo (e : exp) (fenv : fEnv) (nenv : M.t Ast.name) (map: M.t positive) (defs:list (positive * globdef Clight.fundef type)) :=
            info_name <- getName ;;
            let ind :=
                mkglobvar
                  (Tarray uintTy
                          2%Z
                          noattr)
                  ((Init_int32 (Int.repr (Z.of_nat (max_allocs e)))) :: (Init_int32 Int.zero) :: nil) true false in
            ret (Some (
                     ((info_name , Gvar ind) :: defs),
                     (M.set mainIdent info_name map),
                     (M.set info_name (nNamed "body_info"%string) nenv))).
                
                

(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Fixpoint make_funinfo (e : exp) (fenv : fEnv) (nenv : M.t Ast.name)
  : nState (option (list (positive * globdef Clight.fundef type) * M.t positive * M.t Ast.name)) :=
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
  (allocIdent, Gvar (mkglobvar valPtr ((Init_int32 (Int.zero)) :: nil) false false))
    :: (limitIdent , Gvar (mkglobvar valPtr  ((Init_int32 (Int.zero)) :: nil) false false))
    :: (argsIdent , Gvar (mkglobvar (Tarray val maxArgs noattr)
                                    ((Init_int32 (Int.zero)) :: nil)
                                    false false))
    :: *)
    (gcIdent , Gfun (External (EF_external "gc"
                                              (mksignature (Tany32 :: nil) None cc_default))
                                 (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil))
                                 Tvoid
                                 cc_default
    ))::
      (isptrIdent , Gfun (External (EF_external "is_ptr"
                                             (mksignature (Tany32 :: nil) None cc_default))
                                (Tcons (Tint I32 Unsigned noattr) Tnil) (Tint IBool Unsigned noattr)
                                cc_default
      ))
    :: nil.

Definition make_defs (e : exp) (fenv : fEnv) (cenv : cEnv) (nenv : M.t Ast.name) :
  nState (option (M.t Ast.name * (list (positive * globdef Clight.fundef type)))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
           match fun_inf' with
           | Some p =>
             let '(fun_inf, map, nenv') := p in
             match translate_funs e fenv cenv map with
             | None => ret None
             | Some fun_defs' =>
               let fun_defs := rev fun_defs' in
               ret (Some (nenv',
                          ((((global_defs e)
                               ++ fun_inf ++ fun_defs))))) 
             end
           | None => ret None
           end.

Require Import Clightdefs.

Print members.

Definition composites : list composite_definition :=
 (Composite threadInfIdent Struct
   ((allocIdent, valPtr) ::
                         (limitIdent, valPtr) :: (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) ::
                         (argsIdent, (Tarray uintTy maxArgs noattr))::nil)
   noattr ::  nil).

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) : option Clight.program :=
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

Definition add_inf_vars (nenv: M.t Ast.name): M.t Ast.name :=
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


Definition compile (e : exp) (cenv : cEnv) (nenv : M.t Ast.name) :
  M.t Ast.name * option Clight.program :=
  let e := wrap_in_fun e in 
  let fenv := compute_fEnv e in
  let p'' := make_defs e fenv cenv nenv in
  let n := ((max_var e 100) + 1)%positive in
  let p' := fst (p''.(runState) n) in
  match p' with
  | None => (nenv, None)
  | Some p =>
    let '(nenv', defs) := p in
    (add_inf_vars (ensure_unique nenv'), (mk_prog_opt defs mainIdent))
  end.



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


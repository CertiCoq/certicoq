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

(* temporary function to get something working *)
Fixpoint makeArgList' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList' vs')
  end.

Definition makeArgList (vs : list positive) : list N := rev (makeArgList' vs).

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

Notation funTy := (Tfunction Tnil Tvoid
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

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Notation allocPtr := (Evar allocIdent valPtr).
Notation limitPtr := (Evar limitIdent valPtr).
Notation args := (Evar argsIdent valPtr).
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

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).

Definition reserve (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uintTy l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (allocPtr +' (Ederef arr uintTy)) limitPtr type_bool))
    (Scall None gc (arr :: (Eaddrof tinf (Tpointer threadInf noattr)) :: nil))
    Sskip.
     
Fixpoint makeTagZ (cenv : cEnv) (ct : cTag) : option Z :=
  rep <- make_cRep cenv ct ;;
      match rep with
      | enum t => ret (Z.of_N ((N.shiftl t 1) + 1))
      | boxed t a => ret (Z.of_N ((N.shiftl a 10) + (N.shiftl t 1)))
      end.

Definition makeTag (cenv : cEnv) (ct : cTag) : option expr :=
  t <- makeTagZ cenv ct ;;
    ret (c_int t val).

Fixpoint assignConstructor' (cenv : cEnv) (x : positive) (t : cTag) (vs : list positive) :=
  match vs with
  | nil =>
    tag <- makeTag cenv t;;
        rep <- make_cRep cenv t ;;
        match rep with
        | enum _ =>           
          ret (x ::= tag)
        | boxed _ a =>
          ret (x ::= [val] (allocPtr +' (c_int Z.one val));
                 allocPtr :::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val) ;
                 Field(var x, -1) :::= tag)
        end
  | cons v vs' =>
    prog <- assignConstructor' cenv x t vs' ;;
         ret (prog ;
                Field(var x, Z.of_nat (length vs')) :::= [val] (var v))
  end.

Definition assignConstructor (cenv : cEnv) (x : positive) (t : cTag) (vs : list positive) := assignConstructor' cenv x t (rev vs).

Definition isPtr (x : positive) :=
  int_eq
    (Ebinop Oand
            ([val] (var x))
            (c_int 1 val)
            val)
    (c_int 0 val).

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
           ret (args[ Z.of_N i ] :::= (var v) ;
               rest)
    end
  end.

Fixpoint translate_body (e : exp) (fenv : fEnv) (cenv : cEnv) (map : M.t positive) : option statement :=
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
                   | true =>
                     match ls with
                     | LSnil =>
                       ret ((LScons None
                                    prog
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.shiftr (Z.land tag 255) 1))
                                    prog
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
                                        prog
                                        ls'))
                     end
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (Sifthenelse
             (isPtr x)
             (Sswitch (Ebinop Oshr (Ebinop Oand (Field(var x, -1)) (Econst_int (Int.repr 255) val) val) (Econst_int (Int.repr 1) val) val)
                      ls)  
             (Sswitch (Ebinop Oshr (var x) (Econst_int (Int.repr 1) val) val)
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
  | Ehalt x => ret (Sreturn None)
  end.

Definition mkFun (vs : list positive) (body : statement) : function :=
  mkfunction Tvoid
             cc_default
             nil
             (map (fun x => (x , val)) vs)
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
         let localVars := vs ++ (get_allocs e) in
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
                                                  ((reserve gcArrIdent
                                                            (Z.of_N (l + 2))) ;
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
  | Efun fnd e =>                      (* currently assuming e is main *)
    funs <- translate_fundefs fnd fenv cenv m ;; 
         let localVars := get_allocs e in
         body <- translate_body e fenv cenv m ;;
              gcArrIdent <- M.get mainIdent m ;;
              ret ((bodyIdent , Gfun (Internal
                                        (mkfunction val
                                                    cc_default
                                                    nil
                                                    (map (fun x => (x , val)) localVars)
                                                    nil
                                                    (reserve gcArrIdent 2%Z ;
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
                       let ind :=
                           mkglobvar
                             (Tarray uintTy
                                     (len + 2%Z)
                                     noattr)
                            ((Init_int32 (Int.repr (Z.of_N n))) :: (Init_int32 (Int.repr len)) :: (make_ind_array l)) true false in
                       ret (Some (((info_name , Gvar ind) :: defs) ,
                                  M.set x info_name map ,
                                  update_nEnv_fun_info x info_name nenv'))
           end
    end
  end.

Fixpoint make_funinfo (e : exp) (fenv : fEnv) (nenv : M.t Ast.name)
  : nState (option (list (positive * globdef Clight.fundef type) * M.t positive * M.t Ast.name)) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv ;;
      match p with
      | None => ret None
      | Some p' =>
        let '(defs, map, nenv') := p' in 
        info_name <- getName ;;
                  let ind :=
                      mkglobvar
                        (Tarray uintTy
                                2%Z
                                noattr)
                        ((Init_int32 (Int.repr (Z.of_nat (max_allocs e')))) :: (Init_int32 Int.zero) :: nil) true false in
                  ret (Some (
                           ((info_name , Gvar ind) :: defs),
                           (M.set mainIdent info_name map),
                           (M.set info_name (nNamed "body_info"%string) nenv')))
      end
  | _ => ret None
  end.

Definition global_defs (e : exp)
  : list (positive * globdef Clight.fundef type) :=
  let maxArgs := (Z.of_nat (max_args e)) in
  (allocIdent, Gvar (mkglobvar valPtr ((Init_int32 (Int.zero)) :: nil) false false))
    :: (limitIdent , Gvar (mkglobvar valPtr  ((Init_int32 (Int.zero)) :: nil) false false))
    :: (argsIdent , Gvar (mkglobvar (Tarray val maxArgs noattr)
                                    ((Init_int32 (Int.zero)) :: nil)
                                    false false))
    :: (gcIdent , Gfun (External (EF_external "gc"
                                              (mksignature (Tany32 :: nil) None cc_default))
                                 (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons (Tpointer threadInf noattr) Tnil))
                                 Tvoid
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
                               ++ ((tinfIdent , Gvar (
                                                    mkglobvar
                                                      threadInf
                                                      ((Init_addrof argsIdent Int.zero)
                                                         :: (Init_int32 (Int.repr ((Z.of_nat (max_args e)))))
                                                         :: (Init_addrof allocIdent Int.zero)
                                                         :: (Init_addrof limitIdent Int.zero) :: nil)
                                                      false false
                                   )) :: nil) ++ fun_inf ++ fun_defs))))) 
             end
           | None => ret None
           end.

Require Import Clightdefs.

Print members.

Definition composites : list composite_definition :=
(Composite threadInfIdent Struct
   ((argsIdent, tptr valPtr) :: (numArgsIdent, tint) :: (allocIdent, tptr valPtr) ::
    (limitIdent, tptr valPtr) :: (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) ::
    nil)
   noattr :: nil).

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) : option Clight.program :=
  let res := Ctypes.make_program composites defs (bodyIdent :: nil) main in
  match res with
  | Error e => None
  | OK p => Some p
  end.

Check make_defs.

Definition compile (e : exp) (cenv : cEnv) (nenv : M.t Ast.name) :
  M.t Ast.name * option Clight.program :=
  let fenv := compute_fEnv e in
  let p'' := make_defs e fenv cenv nenv in
  let n := ((max_var e 100) + 1)%positive in
  let p' := fst (p''.(runState) n) in
  match p' with
  | None => (nenv, None)
  | Some p =>
    let '(nenv', defs) := p in
    (nenv', (mk_prog_opt defs mainIdent))
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

Variable (print_Clight : Clight.program -> unit).
Variable (print_Clight_dest : Clight.program -> String.string -> unit).
Variable (print_Clight_dest_names' : Clight.program -> list (positive * name) -> String.string -> unit).
Variable (print : String.string -> unit).

Definition ensure_unique : list (positive * name) -> list (positive * name) :=
  fun l => map (fun p =>
                  let '(x , n) := p in
                  match n with
                  | nAnon => (x , n)
                  | nNamed s => (x , nNamed (append s (append "_"%string (show_pos x))))
                  end) l.
                    

Definition print_Clight_dest_names : Clight.program -> list (positive * name) -> String.string -> unit :=
  fun p s l => print_Clight_dest_names' p
                                        ((argsIdent, nNamed "args"%string)
                                           :: (allocIdent, nNamed "alloc"%string)
                                           :: (limitIdent, nNamed "limit"%string)
                                           :: (gcIdent, nNamed "garbage_collect"%string)
                                           :: (mainIdent, nNamed "main"%string)
                                           :: (bodyIdent, nNamed "body"%string)
                                           :: (threadInfIdent, nNamed "thread_info"%string)
                                           :: (tinfIdent, nNamed "tinfo"%string)
                                           :: (heapInfIdent, nNamed "heap"%string)
                                           :: (numArgsIdent, nNamed "num_args"%string)
                                           :: (ensure_unique s))
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
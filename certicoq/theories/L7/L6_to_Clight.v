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
        compcert.cfrontend.Clight
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Cop.

Require Import L6.cps.

Module L6_to_Clight.

  Variable (cenv : cEnv).
  Variable (ienv : iEnv).

  
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (argsIdent : ident). 
  Variable (gcIdent : ident).
  Variable (incrHeapIdent : ident).
  Variable (mainIdent : ident).
  Variable (rootsIdent : ident).
  Variable (lenIdent : ident).
  Variable (numAlIdent : ident).
  Variable (funIdent : ident).
  Variable (funInfIdent : ident).
  
  Variable (alloc_init : list init_data).
  Variable (limit_init : list init_data).
  
  Variable (gc_vs : list positive).
  Variable (gc_body : statement).
  
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
                  | Fcons _ _ _ e fnd' =>
                    compute_fEnv_fundefs n' fnd' (compute_fEnv' n' fenv e)
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
    | Eapp x t vs => nil (* alloc into args, not new vars *) 
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

  Definition make_cRep (ct : cTag) : option cRep :=
    p <- M.get ct cenv ;;
      let '(it , n , r) := p in
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
  Notation "'funVar' x" := (Evar x funTy) (at level 20). (* not temp...correct? *)

  
  Notation allocPtr := (Evar allocIdent val). (* not temp...correct? *)
  Notation limitPtr := (Evar limitIdent val).
  Notation args := (Evar argsIdent valPtr).
  Notation gc := (Evar gcIdent funTy).
  Notation incrHeap := (Evar incrHeapIdent funTy).
  Notation roots := (Etempvar rootsIdent valPtr). 
  Notation len := (Etempvar lenIdent intTy). (* maybe want unsinged? *)


  Definition add (a b : expr) := Ebinop Oadd a b valPtr.
  Notation " a '+'' b " := (add a b) (at level 30).
  
  Definition int_eq (a b : expr) := Ebinop Oeq a b type_bool.
  Notation " a '='' b " := (int_eq a b) (at level 35).
  
  Definition not (a : expr) := Eunop Onotbool a type_bool.
  Notation "'!' a " := (not a) (at level 40).
  
  Notation seq := Ssequence.
  
  Notation " p ';' q " := (seq p q)
                           (at level 100, format " p ';' '//' q ").

  (*TODO: for non-tempvars must use Sassign *)
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
    ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)
  
  Fixpoint reserve' (l : N) (locs : list N) : statement :=
    match locs with
    | nil =>
      (Sifthenelse
         (!(Ebinop Ole allocPtr limitPtr type_bool))
         (Scall None gc (roots :: len :: nil)) (* needs to be called with correct function struct *)
         Sskip)
    | n :: locs' =>
      Field(roots, Z.of_nat (length locs')) :::= &Field(args, Z.of_N n) ;
        (reserve' l locs')
    end. 

  Definition reserve (l : N) (locs : list N) : statement := (* old/wrong *)
    roots :::= allocPtr ;
      len :::= c_int (Z.of_N l) intTy ;
      allocPtr :::= (add allocPtr
                        (c_int (Z.of_N l) val)) ;
      (reserve' l locs).
  
  Fixpoint makeTagZ (ct : cTag) : option Z :=
    rep <- make_cRep ct ;;
        match rep with
        | enum t => ret (Z.of_N (t * 2 + 1))
        | boxed t a => ret (Z.of_N (a * 2 ^ 10 + t * 2))
        end.
  
  Definition makeTag (ct : cTag) : option expr :=
    t <- makeTagZ ct ;;
      ret (c_int t val).
  
  Fixpoint assignConstructor (x : positive) (t : cTag) (vs : list positive) :=
    match vs with
    | nil =>
      tag <- makeTag t;;
          rep <- make_cRep t ;;
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
      prog <- assignConstructor x t vs' ;;
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
  
  Definition isBoxed (ct : cTag) : bool :=
    match make_cRep ct with
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
  Fixpoint translate_body (e : exp) (fenv : fEnv) : option statement :=
    match e with
    | Econstr x t vs e' =>
      prog <- assignConstructor x t vs ;;
           prog' <- translate_body e' fenv ;;
           ret (prog ; prog')
    | Ecase x cs =>
      p <- ((fix makeCases (l : list (cTag * exp)) :=
              match l with
              | nil => ret (LSnil, LSnil)
              | cons p l' =>
                prog <- translate_body (snd p) fenv ;;
                     p' <- makeCases l' ;;
                     tag <- makeTagZ (fst p) ;;
                     let '(ls , ls') := p' in
                     match isBoxed (fst p) with
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
      prog <- translate_body e' fenv ;;
           ret (x ::= Field(var v, Z.of_N n) ;
                  prog)
    | Efun fnd e => None
    | Eapp x t vs =>
      inf <- M.get t fenv ;;
          asgn <- asgnAppVars vs (snd inf) ;;
          ret (asgn ; 
                 call ([funTy] (var x)))
    | Eprim x p vs e => None
    | Ehalt x => Some Sbreak
    end.

  Definition mkFun (vs : list positive) (body : statement) : function :=
    mkfunction Tvoid
               cc_default
               nil
               (map (fun x => (x , val)) vs)
               nil
               body.

  Fixpoint translate_fundefs (fnd : fundefs) (fenv : fEnv) : 
    option (list (positive * globdef Clight.fundef type)) :=
    match fnd with
    | Fnil => ret nil
    | Fcons f t vs e fnd' =>
      rest <- translate_fundefs fnd' fenv ;;
           body <- translate_body e fenv ;;
           let localVars := vs ++ (get_allocs e) in
           inf <- M.get t fenv ;;
               let '(l, locs) := inf in
               asgn <- asgnFunVars vs locs;;    
                    ret ((f , Gfun (Internal
                                      (mkFun localVars
                                             ((reserve l locs) ;
                                                asgn ;
                                                body)))) :: rest)
    end.

  Fixpoint translate_funs' (e : exp) (fenv : fEnv) :
    option (list (positive * globdef Clight.fundef type)) :=
    match e with
    | Efun fnd e =>                      (* currently assuming e is main *)
      funs <- translate_fundefs fnd fenv ;;
           let localVars := get_allocs e in
           body <- translate_body e fenv ;;      
                ret ((mainIdent , Gfun (Internal
                                          (mkFun localVars
                                                 ((reserve 0%N nil) ;
                                                    body))))
                       :: funs)
    | _ => None
    end.

  Definition translate_funs (e : exp) := translate_funs' e (compute_fEnv e).

  Definition nState := ExtLib.Data.Monads.StateMonad.state positive.

  Definition getName : nState positive :=
    n <- get ;;
      put (n+1)%positive ;;
      ret n.
  
  Definition fInfoBaseCompDef : composite_definition :=
    Composite funInfIdent Struct nil noattr.
  
  Fixpoint make_ind_array (l : list N) : list init_data :=
    match l with
    | nil => nil
    | n :: l' => (Init_int32 (Int.repr (Z.of_N n))) :: (make_ind_array l')
    end.

  (* needs cleanup (pull out more helper functions) *)
  Fixpoint make_fundef_structs (fnd : fundefs) (fenv : fEnv)
    : nState (option ((list (positive * globdef Clight.fundef type)) * composite_definition)) :=
    match fnd with
    | Fnil => ret (Some (nil, fInfoBaseCompDef))
    | Fcons x t vs e fnd' =>
      match M.get x fenv with
      | None => ret None
      | Some inf =>
        let '(n, l) := inf in
        rest <- make_fundef_structs fnd' fenv ;;
             match rest with
             | None => ret None
             | Some rest' =>
               ind_list_name <- getName ;;
                             struct_name <- getName ;;
                             let ind :=
                                 mkglobvar
                                   (Tarray intTy
                                           (Z.of_nat (length l))
                                           noattr)
                                   (make_ind_array l) false false in
                             let str :=
                                 mkglobvar
                                   (Tstruct funInfIdent noattr)
                                   ((Init_addrof x Int.zero)
                                      :: (Init_int32 (Int.repr (Z.of_nat (length (get_allocs e)))))
                                      :: (Init_int32 (Int.repr (Z.of_nat (length l))))
                                      :: (Init_addrof ind_list_name Int.zero)
                                      :: nil)
                                   false false in
                             let '(deflist, cdef) := rest' in
                             match cdef with
                             | Composite i s elems a =>
                               ret (Some (((ind_list_name, Gvar ind)
                                       :: (struct_name, Gvar str)
                                       :: deflist),
                                    Composite i s ((struct_name,
                                                    Tstruct funInfIdent noattr)
                                                     :: elems) a))
                             end
             end
      end
    end.

  (* Still need to write/generate

  Definition fInfoBaseComp : composite := 
    
  Definition fInfoBaseCompEnv : composite_env :=
   *)
  
  (* must add struct defs *)
  Definition global_defs (e : exp)
    : list (positive * globdef Clight.fundef type) :=
    (allocIdent, Gvar (mkglobvar val alloc_init false false))
      :: (limitIdent , Gvar (mkglobvar val limit_init false false))
      :: (argsIdent , Gvar (mkglobvar valPtr
                                      ((Init_space
                                          (Z.of_nat (max_args e)))
                                         :: nil)
                                      false false))
      :: (gcIdent , Gfun (Internal (mkFun gc_vs gc_body)))
      :: nil.

  Definition make_defs (e : exp) :
    option (list (positive * globdef Clight.fundef type)) :=
    fun_defs <- translate_funs e ;;
             ret ((global_defs e) ++ fun_defs).

  Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
             (main: ident) : option Clight.program :=
    let res := Ctypes.make_program nil defs nil main in
    match res with
    | Error e => None
    | OK p => Some p
    end.
  
  Definition compile (e : exp) :
    option Clight.program :=
    defs <- make_defs e ;;
         prog <- mk_prog_opt defs mainIdent ;;
         ret prog.

  Theorem refl {A : Type} {a : A} : a = a.
  Proof.
    reflexivity.
  Qed.
  
  Definition empty_program : Clight.program :=
    Build_program nil nil mainIdent nil refl.
  
  Definition stripOption (p : option Clight.program) :=
    match p with
    | None => empty_program
    | Some p' => p'
    end.
  
  Definition x : ident := 7%positive.

  Definition y : ident := 8%positive.

  Definition z : ident := 2%positive.

  Definition stmt : statement :=
    (Swhile
       (!(Ebinop Ole (var x) (var y) type_bool))
       (call (funVar z)));
      x ::= (add (var x) (c_int  8 valPtr));
      y::=  Field(var z, 2);
      (Sreturn None).

  Print stmt.

  Definition a : fTag := 7%positive.
  Definition b : fTag := 8%positive.
  Definition c : fTag := 2%positive.
  Definition t : cTag := 9%positive.

  Definition test : exp := Efun Fnil (Eproj b t 2%N a
                                           (Eproj c t 4%N a
                                                  (Eapp a x (cons b (cons c nil))))).

  Definition test_result := Eval compute in (stripOption (compile test)).

  Print test_result.

End L6_to_Clight.
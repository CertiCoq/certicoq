(* Computational definition and declarative spec for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Template Require Import BasicAst. (* For identifier names *)
Require Import Common.AstCommon.

From CertiCoq.L6 Require Import cps cps_util set_util relations hoisting identifiers ctx
                         Ensembles_util List_util alpha_conv functions.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Coq.Strings.String.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations Nnat MonadNotation.

From compcert.lib Require Import Coqlib Maps. 

Open Scope monad_scope.
Open Scope ctx_scope.
Open Scope fun_scope.
Open Scope string.

(** * Closure conversion as a relation  *)

Section CC.

  Variable (clo_tag : cTag). (* Tag for closure records *)


  (* The free-variable set of a source program *)
  Definition FV (Scope : Ensemble var) (Funs : Ensemble var) (FVs : list var) :=
    Scope :|: (Funs \\ Scope) :|: (FromList FVs \\ (Scope :|: Funs)).
  
  (* The free-variable set of a closure converted *)
  Definition FV_cc (Scope : Ensemble var) (Funs : Ensemble var) (γ : var  -> var) (Γ : var) :=
    Scope :|: (Funs \\ Scope) :|: image γ (Funs \\ Scope) :|: [set Γ].

  (* Closure application *)
  Definition AppClo f t xs f' Γ :=
    Eproj f' clo_tag 0%N f
          (Eproj Γ clo_tag 1%N f
                 (Eapp f' t (Γ :: xs))).
  
  Inductive project_var :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Functions not yet constructed *)
    (var -> var) -> (* function mapping functions to environments *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* Current environment *)
    list var -> (* The environment *)
    var -> (* Before projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* New current scope *)
    Ensemble var -> (* New funs *)
    Prop :=
  | Var_in_Scope :
      forall Scope Funs fenv c FVs x Γ,
        x \in Scope ->
        project_var Scope Funs fenv c Γ FVs x Hole_c Scope Funs
  | Var_in_Funs :
      forall Scope Funs fenv c FVs f Γ,
        ~ f \in Scope ->
        f \in Funs ->
        (* adds the function in scope so that it's not constructed again *)
        project_var Scope Funs fenv c Γ FVs f
                    (Econstr_c f clo_tag [f ; (fenv f)] Hole_c) (f |: Scope) (Funs \\ [set f])
  | Var_in_FVs :
      forall Scope Funs fenv c FVs x N Γ,
        ~ x \in Scope ->
        ~ x \in Funs ->
        nthN FVs N = Some x ->
        (* adds the var in scope so that it's not projected again *)
        project_var Scope Funs fenv c Γ FVs x
                    (Eproj_c x c N Γ Hole_c) (x |: Scope) Funs.
  
  Inductive project_vars :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Functions not yet constructed *)
    (var -> var) -> (* function mapping functions to environments *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables *)
    list var -> (* Before projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* New current scope *)
    Ensemble var -> (* Funs *)
    Prop :=
  | VarsNil :
      forall Scope Funs fenv c Γ FVs,
        project_vars Scope Funs fenv c Γ FVs [] Hole_c Scope Funs
  | VarsCons :
      forall Scope1 Scope2 Scope3 Funs1 Funs2 Funs3 fenv c Γ FVs y ys C1 C2,
        project_var Scope1 Funs1 fenv c Γ FVs y C1 Scope2 Funs2 ->
        project_vars Scope2 Funs2 fenv c Γ FVs ys C2 Scope3 Funs3  ->
        project_vars Scope1 Funs1 fenv c Γ FVs (y :: ys) (comp_ctx_f C1 C2) Scope3 Funs3.

  Definition extend_fundefs' (f : var -> var) (B : fundefs) (x : var) : var -> var :=
    fun y => if (@Dec _ (name_in_fundefs B) _) y then x else f y.


  Inductive Closure_conversion :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Functions that are not yet constructed *)
    (var -> var) -> (* function mapping functions to environments *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables - need to be ordered *)
    exp -> (* Before cc *)
    exp -> (* After cc *)
    exp_ctx -> (* The context that the output expression should be put in *)
    Prop :=
  | CC_Econstr :
      forall Scope Scope' Funs Funs' fenv c Γ FVs x ys C C' t e e',
        project_vars Scope Funs fenv c Γ FVs ys C Scope' Funs' ->
        Closure_conversion (x |: Scope') Funs' fenv c Γ FVs e e' C' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Econstr x t ys e) 
                           (Econstr x t ys (C' |[ e' ]|)) C
  | CC_Ecase :
      forall Scope Scope' Funs Funs' fenv c Γ FVs x C pats pats',
        project_var Scope Funs fenv c Γ FVs x C Scope' Funs' ->
        Forall2 (fun (pat pat' : cTag * exp) =>
                   (fst pat) = (fst pat') /\
                   exists C' e',
                     snd pat' = C' |[ e' ]| /\
                     Closure_conversion Scope' Funs' fenv c Γ FVs (snd pat) e' C')
                pats pats' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Ecase x pats) (Ecase x pats') C
  | CC_Eproj :
      forall Scope Scope' Funs Funs' fenv c Γ FVs x y C C' t N e e',
        project_var Scope Funs fenv c Γ FVs y C Scope' Funs' ->
        Closure_conversion (x |: Scope') Funs' fenv c Γ FVs e e' C' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Eproj x t N y e)
                           (Eproj x t N y (C' |[ e' ]|)) C
  | CC_Efun :
      forall Scope Scope' Funs Funs' fenv c Γ c' Γ' FVs FVs' B B' e e' C Ce,
        (* The environment contains all the variables that are free in B *)
        (occurs_free_fundefs B) <--> (FromList FVs') ->
        (* needed for cost preservation *)
        NoDup FVs' ->
        project_vars Scope Funs fenv c Γ FVs FVs' C Scope' Funs' ->
        (* Γ' is the variable that will hold the record of the environment *)
        ~ Γ' \in (bound_var (Efun B e) :|: FromList FVs' :|: FV Scope Funs FVs :|:
                  FV_cc Scope Funs fenv Γ) ->
        (* closure convert function blocks *)
        Closure_conversion_fundefs B c' FVs' B B' ->
        (* closure convert the rest of the program *)
        Closure_conversion (Scope' \\ name_in_fundefs B)
                           ((name_in_fundefs B) :|: Funs') (extend_fundefs' fenv B Γ') c Γ FVs e e' Ce  ->
        Closure_conversion Scope Funs fenv c Γ FVs (Efun B e)
                           (Efun B' (Ce |[ e' ]|)) (comp_ctx_f C (Econstr_c Γ' c' FVs' Hole_c))
  | CC_Eapp :
      forall Scope Scope' Funs Funs' fenv c Γ FVs f f' ft env' ys C S,
        Disjoint _ S (FV_cc Scope' Funs' fenv Γ) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs fenv c Γ FVs (f :: ys) C Scope' Funs' ->
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        f' \in S -> env' \in S -> f' <> env' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Eapp f ft ys) (AppClo f ft ys f' env') C
  | CC_Eprim :
      forall Scope Scope' Funs Funs' fenv c Γ FVs x ys C C' f e e',
        project_vars Scope Funs fenv c Γ FVs ys C Scope' Funs' ->
        Closure_conversion (x |: Scope') Funs' fenv c Γ FVs e e' C' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Eprim x f ys e)
                           (Eprim x f ys (C' |[ e' ]|)) C
  | CC_Ehalt :
      forall Scope Scope' Funs Funs' fenv c Γ FVs x C,
        (* Project the function name and the actual parameter *)
        project_var Scope Funs fenv c Γ FVs x C Scope' Funs' ->
        Closure_conversion Scope Funs fenv c Γ FVs (Ehalt x) (Ehalt x) C
  with Closure_conversion_fundefs :
         fundefs -> (* The current block. Needed to make closures upon entry. *)
         cTag -> (* tag of the current environment constructor *)
         list var -> (* The environment *)
         fundefs -> (* Before cc *)
         fundefs -> (* After cc *)
         Prop :=
       | CC_Fccons :
           forall B c Γ' FVs S f t ys e e' C defs defs',
             (* The environment binding should not shadow the current scope
               (i.e. the names of the mut. rec. functions and the other arguments) *)
             Disjoint _ S ((name_in_fundefs B) :|: (FromList ys) :|: (bound_var e) :|: FromList FVs) ->
             (* new argument *)
             In _ S  Γ' ->
             Closure_conversion_fundefs B c FVs defs defs' ->
             Closure_conversion (FromList ys) (name_in_fundefs B) (extend_fundefs' id B Γ')
                                c Γ' FVs e e' C ->
             Closure_conversion_fundefs B c FVs (Fcons f t ys e defs )
                                        (Fcons f t (Γ' :: ys) (C |[ e' ]|) defs')
       | CC_Fnil :
           forall B c FVs,
             Closure_conversion_fundefs B c FVs Fnil Fnil.
  

  (** * Computational definition of closure conversion *)
  
  Inductive VarInfo : Type :=
  (* A free variable, i.e. a variable outside the scope of the current function.
   The argument is position of a free variable in the env record *)
  | FVar : N -> VarInfo
  (* A function defined in the current block of function definitions. The first
   argument is the closure environment  *)
  | MRFun : var -> VarInfo
  (* A variable declared in the scope of the current function *)
  | BoundVar : VarInfo.
  
  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := M.t VarInfo.

  Record state_contents :=
    mkSt { var_map : VarInfoMap ; 
           next_var : var ; (* next fresh name *)
           nect_cTag : cTag ; (* next unique tag for closures *)
           next_iTag : iTag; cenv : cEnv;
           name_env : M.t BasicAst.name }.
  
  (** The state is the next available free variable, cTag and iTag and the tag environment *)
  Definition ccstate :=
    state state_contents.

  Definition get_var_entry (x : var) : ccstate (option VarInfo)  :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    match vm ! x with
      | Some info => ret (Some info)
      | None => ret None
    end.

  Definition set_var_entry (x : var) (info : VarInfo) : ccstate unit :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt (M.set x info vm) n c i e names) ;;
    ret tt.

  (** Get a the name entry of a variable *)
  Definition get_name_entry (x : var) : ccstate BasicAst.name :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    match names ! x with
      | Some name => ret name
      | None => ret nAnon
    end.

  (** Set a the name entry of a variable *)
  Definition set_name_entry (x : var) (name : BasicAst.name) : ccstate unit :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt vm n c i e (M.set x name names)) ;;
    ret tt.

  Definition pop_var_map (t : unit) : ccstate VarInfoMap :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt (M.empty VarInfo) n c i e names) ;;
    ret vm.

  Definition peak_var_map (t : unit) : ccstate VarInfoMap :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    ret vm.

  Definition push_var_map (map : VarInfoMap) : ccstate unit :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt map n c i e names) ;;
    ret tt.
  

  (* (** Add name *) *)
  Definition add_name (fresh : var) (name : string): ccstate unit :=
    set_name_entry fresh (nNamed name).

  (** Add_name as suffix *)
  Definition add_name_suff (fresh old : var) (suff : string) :=
    oldn <- get_name_entry old ;;
    match oldn with
      | nNamed s =>
        set_name_entry fresh (nNamed (append s suff))
      | nAnon =>
        set_name_entry fresh (nNamed (append "anon" suff))
    end.

  (** Commonly used suffixes *)
  Definition clo_env_suffix := "_env".
  Definition clo_suffix := "_clo".
  Definition code_suffix := "_code".
  Definition proj_suffix := "_proj".


  (** Get a fresh name, and create a pretty name *)
  Definition get_name (old_var : var) (suff : string) : ccstate var :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt vm ((n+1)%positive) c i e names) ;;
    add_name_suff n old_var suff ;;
    ret n.

  (** Get a fresh name, and create a pretty name *)
  Definition get_name_no_suff (name : string) : ccstate var :=
    p <- get ;;
    let '(mkSt vm n c i e names) := p in
    put (mkSt vm ((n+1)%positive) c i e names) ;;
    add_name n name ;;
    ret n.

  
  Definition make_record_cTag (n : N) : ccstate cTag :=
    p <- get ;;
    let '(mkSt vm x c i e names) := p  in
    let inf := (nAnon, nAnon, i, n, 0%N) : cTyInfo in
    let e' := ((M.set c inf e) : cEnv) in
    put (mkSt vm x (c+1)%positive (i+1)%positive e' names) ;;
    ret c.

  (** Looks up a variable in the map and handles it appropriately *) 
  Definition get_var (x : var) (c : cTag) (Γ : var): ccstate exp_ctx :=
    info <- get_var_entry x ;;
    match info with
      | Some entry =>
        match entry with
        | FVar pos =>
          set_var_entry x BoundVar ;; 
          ret (Eproj_c x c pos Γ Hole_c) 
        | MRFun env_ptr  =>
          set_var_entry x BoundVar ;; 
          ret (Econstr_c x clo_tag [x; env_ptr] Hole_c)
        | BoundVar => ret Hole_c
        end
      | None => ret Hole_c (* should never reach here *)
    end.
   
  Fixpoint get_vars (xs : list var) (c : cTag) (Γ : var) : ccstate exp_ctx :=
    match xs with
      | [] => ret Hole_c
      | x :: xs =>
        C1 <- get_var x c Γ ;;
        C2 <- get_vars xs c Γ ;; 
        ret (comp_ctx_f C1 C2)
    end.

  (** Add some bound variables in the map *)
  Fixpoint add_params args : ccstate unit :=
    match args with
      | [] => ret tt
      | x :: xs =>
        set_var_entry x BoundVar ;;
        add_params xs
    end.
  
  (** Add the free variables in the map *)
  Fixpoint add_fvs xs n : ccstate unit :=
    match xs with
      | [] => ret tt
      | x :: xs =>
        set_var_entry x (FVar n) ;;
        add_fvs xs (n + 1)%N
    end.

  Fixpoint add_funs B Γ : ccstate unit :=
    match B with
    | Fcons f typ xs e B' =>
      set_var_entry f (MRFun Γ) ;;
      add_funs B' Γ 
    | Fnil => ret tt
    end.


  (** Construct the closure environment  *)
  Definition make_env (fvs : list var) (c_old : cTag) (Γ_new Γ_old : var)
  : ccstate (cTag * exp_ctx) :=
    C <- get_vars fvs c_old Γ_old  ;;
    c_new <- make_record_cTag (N_as_OT.of_nat (List.length fvs)) ;; (* TODO fix *)
    ret (c_new, comp_ctx_f C (Econstr_c Γ_new c_new fvs Hole_c)).


  Fixpoint exp_closure_conv (e : exp)
           (c : cTag) (Γ : var) : ccstate (exp * exp_ctx) := 
    match e with
    | Econstr x tag ys e' =>
      C1 <- get_vars ys c Γ ;;
      set_var_entry x BoundVar ;;
      ef <- exp_closure_conv e' c Γ ;;
      let (e_cc, C) := ef in 
      ret (Econstr x tag ys (C |[ e_cc ]|), C1)
    | Ecase x pats =>
      C1 <- get_var x c Γ ;;
      pats' <-
      (fix mapM_cc l :=
         match l with
         | [] => ret []
         | (y, e) :: xs =>
           var_map <- peak_var_map tt ;;
           ef <- exp_closure_conv e c Γ ;;
           push_var_map var_map ;;
           xs' <- mapM_cc xs ;;
           ret ((y, ((snd ef) |[ fst ef ]|)) :: xs')
         end) pats;;
        ret (Ecase x pats', C1)
      | Eproj x tag n y e' =>
        C1 <- get_var y c Γ ;;
        set_var_entry x BoundVar ;;
        ef <- exp_closure_conv e' c Γ ;;
        let (e_cc, C) := ef in 
        ret (Eproj x tag n y (C |[ e_cc ]|), C1)
      | Efun defs e =>
        (* precompute free vars so this computation does not mess up the complexity *)
        let fv_set := fundefs_fv defs in
        let fvs := PS.elements fv_set in 
        Γ' <- get_name_no_suff "env";;
        t1 <- make_env fvs c Γ' Γ ;;
        let '(c', Cenv) := t1 in
        (* fundefs *)
        var_map <- pop_var_map tt ;;
        add_fvs fvs 0%N ;;
        defs' <- fundefs_closure_conv defs defs c' ;;
        push_var_map var_map ;;
        (* end fundefs *)
        add_funs defs Γ' ;;
        ef <- exp_closure_conv e c Γ ;;
        let (e_cc, C) := ef in 
        ret (Efun defs' (C |[ e_cc ]|), Cenv)
      | Eapp f ft xs =>
        C1 <- get_vars (f :: xs) c Γ ;;
        ptr <- get_name f code_suffix ;;
        Γ <- get_name f clo_env_suffix ;;
        ret (Eproj ptr clo_tag 0 f
                   (Eproj Γ clo_tag 1 f
                          (Eapp ptr ft (Γ :: xs))), C1)
    | Eprim x prim ys e' =>
      C1 <- get_vars ys c Γ ;;
      set_var_entry x BoundVar ;;
      ef <- exp_closure_conv e' c Γ ;;
      let (e_cc, C) := ef in 
      ret (Eprim x prim ys (C |[ e_cc ]|), C1)
    | Ehalt x =>
      C1 <- get_var x c Γ ;;
      ret (Ehalt x, C1)
    end
  with fundefs_closure_conv B (defs : fundefs) (c : cTag)
       : ccstate fundefs  :=
         match defs with
           | Fcons f tag ys e defs' =>
             var_map <- peak_var_map tt ;;
             (* formal parameter for the environment pointer *)
             Γ <- get_name f clo_env_suffix ;;
             add_funs B Γ ;;
             (* Add arguments to the map *)
             add_params ys ;;
             ef <- exp_closure_conv e c Γ ;;
             let (e_cc, C) := ef in 
             push_var_map var_map ;;
             defs'' <- fundefs_closure_conv B defs' c ;;
             ret (Fcons f tag (Γ :: ys) (C |[ e_cc ]|) defs'')
           | Fnil => ret Fnil
         end.


  (* Toplevel closure conversion program *)
  Definition closure_conversion_top
             (e : exp) (c : cTag) (Γ : var) (i : iTag) (cenv : cEnv) (nmap:M.t BasicAst.name) : exp * exp_ctx :=
    let next := ((Pos.max (max_var e 1%positive) Γ) + 1)%positive in
    let state := mkSt (Maps.PTree.empty VarInfo) next c i cenv nmap in
    let '(e, C, s) := runState
                        (exp_closure_conv e 1%positive Γ)
                        state in
<<<<<<< HEAD
    
    (e, C).

End CC.
=======
    exp_hoist (f e).
  
End CC.
>>>>>>> Adapt to MetaCoq

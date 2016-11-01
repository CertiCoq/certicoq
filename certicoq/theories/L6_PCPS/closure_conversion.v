Require Import L6.cps L6.cps_util L6.set_util L6.relations L6.hoisting L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.alpha_conv L6.functions.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Coq.Strings.String.
Require Import Common.AstCommon.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
Require Import Libraries.Maps.

Open Scope ctx_scope.
Open Scope fun_scope.
Open Scope string.

(** * Closure conversion as a relation  *)

Section CC.
  Variable (clo_tag : cTag). (* Tag for closure records *)

  Inductive project_var :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    (var -> var) -> (* renaming of function names *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The environment *)
    Ensemble var -> (* The free set *)
    var -> (* Before projection *)
    var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | Var_in_Scope :
      forall Scope Funs f c Γ FVs S x,
        In _ Scope x ->
        project_var Scope Funs f c Γ FVs S x x Hole_c S
  | Var_in_Funs :
      forall Scope Funs f c Γ FVs S x y,
        ~ In _ Scope x ->
        In _ Funs x ->
        In _ S y ->
        project_var Scope Funs f c Γ FVs S x y
                    (Econstr_c y clo_tag [(f x); Γ] Hole_c) (Setminus _ S (Singleton _ y))
  | Var_in_FVs :
      forall Scope Funs f c Γ FVs S x y N,
        ~ In _ Scope x ->
        ~ In _ Funs x -> 
        nthN FVs N = Some x ->
        In _ S y ->
        project_var Scope Funs f c Γ FVs S x y
                    (Eproj_c y c N Γ Hole_c) (Setminus _ S (Singleton _ y)).

  Inductive project_vars :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    (var -> var) -> (* renaming of function names *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables *)
    Ensemble var -> (* The free set *)
    list var -> (* Before projection *)
    list var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | VarsNil :
      forall Scope Funs f c Γ FVs S,
        project_vars Scope Funs f c Γ FVs S [] [] Hole_c S
  | VarsCons :
      forall Scope Funs f c Γ FVs y y' ys ys' C1 C2 S1 S2 S3,
        project_var Scope Funs f c Γ FVs S1 y y' C1 S2 ->
        project_vars Scope Funs f c Γ FVs S2 ys ys' C2 S3 ->
        project_vars Scope Funs f c Γ FVs S1 (y :: ys) (y' :: ys') (comp_ctx_f C1 C2) S3.

  Inductive make_closures :
    fundefs -> (* The function block *)
    Ensemble var -> (* The free set *)
    var -> (* The environment variable *)
    exp_ctx -> (* The context that constructs the closures *)
    (var -> var) -> (* The renaming *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | closures_Fnil :
      forall Γ f S,
        make_closures Fnil S Γ Hole_c f S
  | closures_Fcons :
      forall f f' xs t e B Γ C g g' S S',
        make_closures B (Setminus _ S (Singleton _ f')) Γ C g S' ->
        In _ S f' ->
        f_eq (g {f ~> f'}) g' ->
        make_closures (Fcons f t xs e B) S Γ
                      (Econstr_c f clo_tag [f' ; Γ] C)
                      g' S'.

  Inductive Closure_conversion :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    (var -> var) -> (* renaming of function names *)
    cTag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables - need to be ordered *)
    exp -> (* Before cc *)
    exp -> (* After cc *)
    exp_ctx -> (* The context that the output expression should be put in *)
    Prop :=
  | CC_Econstr :
      forall Scope Funs f c Γ FVs S' S x ys ys' C C' t e e',
        (* Variables for projected vars should not shadow the variables in
         scope, i.e. Scope U FV U { Γ } *)
        Disjoint _ S (Union _ Scope
                            (Union _ (image f (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        project_vars Scope Funs f c Γ FVs S ys ys' C S' ->
        (* We do not care about ys'. Should never be accessed again so do not
         add them aτ the current scope *)
        Closure_conversion (Union _ (Singleton _ x) Scope) Funs f c Γ FVs e e' C' ->
        Closure_conversion Scope Funs f c Γ FVs (Econstr x t ys e)
                           (Econstr x t ys' (C' |[ e' ]|)) C
  | CC_Ecase :
      forall Scope Funs f c Γ FVs x x' C S S' pats pats',
        Disjoint _ S (Union _ Scope
                            (Union _ (image f (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        project_var Scope Funs f c Γ FVs S x x' C S' ->
        Forall2 (fun (pat pat' : cTag * exp) =>
                   (fst pat) = (fst pat') /\
                   exists C' e',
                     snd pat' = C' |[ e' ]| /\
                                            Closure_conversion Scope Funs f c Γ FVs (snd pat) e' C')
                pats pats' ->
        Closure_conversion Scope Funs f c Γ FVs (Ecase x pats) (Ecase x' pats') C
  | CC_Eproj :
      forall Scope Funs f c Γ FVs S S' x y y' C C' t N e e',
        Disjoint _ S (Union _ Scope
                            (Union _ (image f (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        project_var Scope Funs f c Γ FVs S y y' C S' ->
        Closure_conversion (Union _ (Singleton _ x) Scope) Funs f c Γ FVs e e' C' ->
        Closure_conversion Scope Funs f c Γ FVs (Eproj x t N y e)
                           (Eproj x t N y' (C' |[ e' ]|)) C
  | CC_Efun :
      forall Scope Funs f f' c Γ c' Γ' FVs FVs' FVs'' B B' e e' C C' Ce S1 S1' S2 S2' S3,
        (* The environment contains all the variables that are free in B *)
        Same_set _ (occurs_free_fundefs B) (FromList FVs') ->
        (* Project the FVs to construct the environment *)
        Disjoint _ S1 (Union _ Scope
                             (Union _ (image f (Setminus _ Funs Scope))
                                    (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        project_vars Scope Funs f c Γ FVs S1 FVs' FVs'' C' S1' ->
        (* Γ' is the variable that will hold the record of the environment *)
        Disjoint _ S3 (Union _ (name_in_fundefs B)
                             (Union _ Scope
                                    (Union _ (image f (Setminus _ Funs Scope))
                                           (Union _ (FromList FVs) (Singleton _ Γ))))) ->
        In _ S3 Γ' ->
        Disjoint _ S2 (Union _ (bound_var_fundefs B)
                             (Union _ (Singleton _ Γ')
                                    (Union _ Scope
                                           (Union _ (image f (Setminus _ Funs Scope))
                                                  (Union _ (FromList FVs) (Singleton _ Γ)))))) ->
        make_closures B S2  Γ' C f' S2' ->
        Closure_conversion_fundefs (name_in_fundefs B) f' c' FVs' B B' ->
        Closure_conversion (Union _ (name_in_fundefs B) Scope) Funs f c Γ FVs e e' Ce  ->
        Closure_conversion Scope Funs f c Γ FVs (Efun B e)
                           (Efun B' (C |[ Ce |[ e' ]| ]|)) (comp_ctx_f C' (Econstr_c Γ' c' FVs'' Hole_c))
  | CC_Eapp :
      forall Scope Funs g c Γ FVs f f' f'' ft env' ys ys' C S S',
        Disjoint _ S (Union _ Scope
                            (Union _ (image g (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs g c Γ FVs S (f :: ys) (f' :: ys') C S' ->
        (* (* Project the actual parameters *) *)
        (* project_vars Scope Funs Γ FVs S1 ys ys' C2 S2 -> *)
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        In _ S' f'' -> In _ S' env' -> f'' <> env' ->
        Closure_conversion Scope Funs g c Γ FVs (Eapp f ft ys)
                           (Eproj f'' clo_tag 0%N f'
                                  (Eproj env' clo_tag 1%N f'
                                         (Eapp f'' ft (env' :: ys')))) C
  | CC_Eprim :
      forall Scope Funs g c Γ FVs S S' x ys ys' C C' f e e',
        Disjoint _ S (Union _ Scope
                            (Union _ (image g (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        project_vars Scope Funs g c Γ FVs S ys ys' C S' ->
        Closure_conversion (Union _ (Singleton _ x) Scope) Funs g c Γ FVs e e' C' ->
        Closure_conversion Scope Funs g c Γ FVs (Eprim x f ys e)
                           (Eprim x f ys' (C' |[ e' ]|)) C
  | CC_Ehalt :
      forall Scope Funs g c Γ FVs x x' C S S',
        Disjoint _ S (Union _ Scope
                            (Union _ (image g (Setminus _ Funs Scope))
                                   (Union _ (FromList FVs) (Singleton _ Γ)))) ->
        (* Project the function name and the actual parameter *)
        project_var Scope Funs g c Γ FVs S x x' C S' ->
        Closure_conversion Scope Funs g c Γ FVs (Ehalt x) (Ehalt x') C
  with Closure_conversion_fundefs :
         Ensemble var -> (* The function names in the current block *)
         (var -> var) -> (* renaming of function names *)
         cTag -> (* tag of the current environment constructor *)
         list var -> (* The environment *)
         fundefs -> (* Before cc *)
         fundefs -> (* After cc *)
         Prop :=
       | CC_Fcons :
           forall Funs g c Γ' FVs S f t ys e e' C defs defs',
             (* The environment binding should not shadow the current scope
         (i.e. the names of the mut. rec. functions and the other arguments) *)
             Disjoint _ S (Union _ (image g Funs) (Union _ (FromList ys) (bound_var e))) ->
             In _ S  Γ' ->
             Closure_conversion_fundefs Funs g c FVs defs defs' ->
             Closure_conversion (FromList ys) Funs g c Γ' FVs e e' C ->
             Closure_conversion_fundefs Funs g c FVs (Fcons f t ys e defs )
                                        (Fcons (g f) t (Γ' :: ys) (C |[ e' ]|) defs')
       | CC_Fnil :
           forall Funs g c FVs,
             Closure_conversion_fundefs Funs g c FVs Fnil Fnil.


  (** * Computational defintion of closure conversion *)
  
  Inductive VarInfo : Type :=
  (* A free variable, i.e. a variable outside the scope of the current function.
   The argument is position of a free variable in the env record *)
  | FVar : N -> VarInfo
  (* A function defined in the current block of function definitions. The first
   argument is the new name of the function (code pointer) *)
  | MRFun : var -> VarInfo
  (* A variable declared in the scope of the current function *)
  | BoundVar : VarInfo.

  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := Maps.PTree.t VarInfo.

  Record state_contents :=
    mkCont { next_var : var ; nect_cTag : cTag ; next_iTag : iTag; cenv : cEnv;
             name_env : M.t Ast.name }.
  
  (** The state is the next available free variable, cTag and iTag and the tag environment *)
  Definition ccstate :=
    state state_contents.
  
  (** Get a the name entry of a variable *)
  Definition get_name_entry (x : var) : ccstate Ast.name :=
    p <- get ;;
    let '(mkCont n c i e names) := p in
    match names ! x with
      | Some name => ret name
      | None => ret nAnon
    end.

  (** Set a the name entry of a variable *)
  Definition set_name_entry (x : var) (name : Ast.name) : ccstate unit :=
    p <- get ;;
    let '(mkCont n c i e names) := p in
    put (mkCont n c i e (M.set x name names)) ;;
    ret tt.


  (** Add name *)
  Definition add_name (fresh : var) (name : string): ccstate unit :=
    set_name_entry fresh (nNamed "env").

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
    let '(mkCont n c i e names) := p in
    put (mkCont ((n+1)%positive) c i e names) ;;
    add_name_suff n old_var suff ;;
    ret n.

  (** Get a fresh name, and create a pretty name *)
  Definition get_name_no_suff (name : string) : ccstate var :=
    p <- get ;;
    let '(mkCont n c i e names) := p in
    put (mkCont ((n+1)%positive) c i e names) ;;
    add_name n name ;;
    ret n.

  
  Definition make_record_cTag (n : N) : ccstate cTag :=
    p <- get ;;
    let '(mkCont x c i e names) := p  in
    let inf := (nAnon, i, n, 0%N) : cTyInfo in
    let e' := ((M.set c inf e) : cEnv) in
    put (mkCont x (c+1)%positive (i+1)%positive e' names) ;;
    ret c.

  (** Looks up a variable in the map and handles it appropriately *) 
  Definition get_var (x : var) (map : VarInfoMap) (c : cTag) (Γ : var)
  : ccstate (var * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos =>
            (* pick a fresh name, register its pretty name *)
            y <- get_name x proj_suffix ;;
            ret (y, fun e => Eproj y c pos Γ e)   
          | MRFun code_ptr  =>
            (* get the new name of the function and pack it together with the
               current environment argument to construct the closure *)
            y <- get_name x clo_suffix ;;
            ret (y, fun e => Econstr y clo_tag [code_ptr; Γ] e)
          | BoundVar => ret (x, id)
        end
      | None => ret (x, id) (* should never reach here *)
    end.
  
  Fixpoint get_vars (xs : list var) (map : VarInfoMap)
           (c : cTag) (Γ : var) : ccstate (list var * (exp -> exp)) :=
    match xs with
      | [] => ret ([], id)
      | x :: xs =>
        t1 <- get_var x map c Γ ;;
        let '(y, f) := t1 in
        t2 <- get_vars xs map c Γ ;; 
        let '(ys, f') := t2 in
        ret (y :: ys, fun e => f (f' e))
    end.

  (** Add some bound variables in the map *)
  Fixpoint add_params args  (mapfv : VarInfoMap) : VarInfoMap :=
    match args with
      | [] => mapfv
      | x :: xs =>
        M.set x BoundVar (add_params xs mapfv)
    end.


  (** Construct the closure environment and the new variable map *)
  Definition make_env (fv : FVSet) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (c_old : cTag) (Γ_new Γ_old : var)
  : ccstate (cTag * VarInfoMap * (exp -> exp)) :=
    (* put the free variables in a new map *)
    let fvs := PS.elements fv in
    let '(map_new', n) :=
        (fix add_fvs l n map :=
           match l with
             | [] => (map, n)
             | x :: xs =>
               add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
           end) fvs 0%N (Maps.PTree.empty VarInfo)
    in
    t1 <- get_vars fvs mapfv_old c_old Γ_old ;;
    let '(fv', g') :=  t1 in
    c_new <- make_record_cTag n ;;
    ret (c_new, map_new', fun e => g' (Econstr Γ_new c_new fv' e)).
  
  (** Construct closures after a function definition block *)
  Fixpoint make_full_closure (defs : fundefs) (mapfv_new mapfv_old : VarInfoMap)
           (Γ : var)
  : ccstate (VarInfoMap * VarInfoMap * (exp -> exp)) :=
    match defs with
      | Fcons f typ xs e defs' =>
        (* The new name of the function *)
        code_ptr <- get_name f code_suffix ;;
        t <- make_full_closure defs' mapfv_new mapfv_old Γ ;;
        let '(mapfv_new', mapfv_old', g') := t in
        (* update the new map *)
        let mapfv_new'' :=
            Maps.PTree.set f (MRFun code_ptr) mapfv_new'
        in
        (* update the old map *)
        let mapfv_old'' :=
            Maps.PTree.set f BoundVar mapfv_old'
        in
        ret (mapfv_new'', mapfv_old'',
             (fun e => Econstr f clo_tag [code_ptr; Γ] (g' e)))
      | Fnil => ret (mapfv_new, mapfv_old, id)
    end.




  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap)
           (c : cTag) (Γ : var) : ccstate (exp * (exp -> exp)) := 
    match e with
      | Econstr x tag ys e' =>
        t1 <- get_vars ys mapfv c Γ ;;
        let '(ys', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) c Γ ;;
        ret (Econstr x tag ys' ((snd ef) (fst ef)), f)
      | Ecase x pats =>
        pats' <-
        (fix mapM_cc l :=
         match l with
           | [] => ret []
           | (y, e) :: xs =>
             ef <- exp_closure_conv e mapfv c Γ ;;
             xs' <- mapM_cc xs ;;
             ret ((y, ((snd ef) (fst ef))) :: xs')
         end) pats;;
        t1 <- get_var x mapfv c Γ ;;
        let '(x', f1) := t1 in           
        ret (Ecase x' pats', f1)
      | Eproj x tag n y e' =>
        t1 <- get_var y mapfv c Γ ;;
        let '(y', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) c Γ ;;
        ret (Eproj x tag n y' ((snd ef) (fst ef)), f)
      | Efun defs e =>
        (* precompute free vars so this computation does not mess up the complexity *)
        let fv := fundefs_fv defs in
        Γ' <- get_name_no_suff "env";;
        (* register its pretty name *)
        t1 <- make_env fv (Maps.PTree.empty VarInfo) mapfv c Γ' Γ ;;
        let '(c', mapfv_new, g1) := t1 in
        t2 <- make_full_closure defs mapfv_new mapfv Γ'  ;;
        let '(mapfv_new', mapfv_old', g2) := t2 in
        ef <- exp_closure_conv e mapfv_old' c Γ ;;
        defs' <- fundefs_closure_conv defs mapfv_new' c' ;;
        ret (Efun defs' (g2 ((snd ef) (fst ef))), g1)
      | Eapp f ft xs =>
        t1 <- get_var f mapfv c Γ ;;
        let '(f', g1) := t1 in     
        t2 <- get_vars xs mapfv c Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name f code_suffix ;;
        Γ <- get_name f clo_env_suffix ;;
        ret (Eproj ptr clo_tag 0 f'
                   (Eproj Γ clo_tag 1 f'
                          (Eapp ptr ft (Γ :: xs'))), fun e => g1 (g2 e))
    | Eprim x prim ys e' =>
      t1 <- get_vars ys mapfv c Γ ;;
      let '(ys', f) := t1 in
      ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) c Γ ;;
         ret (Eprim x prim ys' ((snd ef) (fst ef)), f)
    | Ehalt x =>
      t1 <- get_var x mapfv c Γ ;;
      let '(x', f) := t1 in
      ret (Ehalt x', f)
    end
  with fundefs_closure_conv (defs : fundefs) (mapfv : VarInfoMap) (c : cTag)
       : ccstate fundefs  :=
         match defs with
           | Fcons f tag ys e defs' =>
             (* Add arguments to the map *)
             let mapfv' := add_params ys mapfv in
             (* formal parameter for the environment pointer *)
             Γ <- get_name f clo_env_suffix ;;
             ef <- exp_closure_conv e mapfv' c Γ ;;
             defs'' <- fundefs_closure_conv defs' mapfv c ;;
             (* find the new name of the function *)
             let code_ptr :=
                 match Maps.PTree.get (f : var) (mapfv : VarInfoMap) with
                   | Some entry =>
                     match entry with
                       | MRFun ptr => ptr
                       | _ => f (* should never reach here *)
                     end
                   | None => f (* should never reach here *)
                 end
             in
             ret (Fcons code_ptr tag (Γ :: ys) ((snd ef) (fst ef)) defs'')
           | Fnil => ret Fnil
         end.

  Definition closure_conversion_hoist (e : exp) ctag itag cenv' nmap : cEnv * M.t Ast.name * exp :=
    let Γ := ((max_var e 1%positive) + 1)%positive in
    let next := (Γ + 1)%positive in
    let state := mkCont next ctag itag cenv' nmap in
    let '(e, f, s) := runState
                        (exp_closure_conv e (Maps.PTree.empty VarInfo) 1%positive Γ)
                        state in
    (s.(cenv), s.(name_env), exp_hoist (f e)).

  Definition populate_map (l : list (var * val)) map  :=
    fold_left (fun map x => M.set (fst x) BoundVar map) l map.

  Definition closure_conversion_hoist_open (rho : eval.env) (e : exp) ctag itag cenv nmap : exp :=
    let Γ := ((max_list (map fst (M.elements rho)) (max_var e 1%positive)) + 1)%positive in
    let map := populate_map (M.elements rho) (Maps.PTree.empty VarInfo) in
    let next := (Γ + 1)%positive in
    let state := mkCont next ctag itag cenv nmap in
    let '(e, f, s) := runState
                        (exp_closure_conv e map 1%positive Γ)
                        state in
    exp_hoist (f e).
  
End CC.
Require Import cps cps_util set_util relations hoisting identifiers ctx
        Ensembles_util List_util alpha_conv.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
Require Maps.

Open Scope ctx_scope.
Open Scope alpha_scope.

(** * Closure conversion as a relation  *)

Inductive project_var :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  (var -> var) -> (* renaming of function names *)
  var -> (* The environment argument *)
  list var -> (* The environment *)
  Ensemble var -> (* The free set *)
  var -> (* Before projection *)
  var -> (* After projection *)
  exp_ctx -> (* Context that will perform the projection *)
  Ensemble var -> (* The new free set *)
  Prop :=
| Var_in_Scope :
    forall Scope Funs f Γ FVs S x,
      In _ Scope x ->
      project_var Scope Funs f Γ FVs S x x Hole_c S
| Var_in_Funs :
    forall Scope Funs f Γ FVs S x y t tau,
      ~ In _ Scope x ->
      In _ Funs x ->
      In _ S y ->
      project_var Scope Funs f Γ FVs S x y
                  (Econstr_c y t tau [(f x); Γ] Hole_c) (Setminus _ S (Singleton _ y))
| Var_in_FVs :
    forall Scope Funs f Γ FVs S x y N tau,
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      In _ S y ->
      project_var Scope Funs f Γ FVs S x y
                  (Eproj_c y tau N Γ Hole_c) (Setminus _ S (Singleton _ y)).

Inductive project_vars :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  (var -> var) -> (* renaming of function names *)
  var -> (* The environment argument *)
  list var -> (* The free variables *)
  Ensemble var -> (* The free set *)
  list var -> (* Before projection *)
  list var -> (* After projection *)
  exp_ctx -> (* Context that will perform the projection *)
  Ensemble var -> (* The new free set *)
  Prop :=
| VarsNil :
    forall Scope Funs f Γ FVs S,
      project_vars Scope Funs f Γ FVs S [] [] Hole_c S
| VarsCons :
    forall Scope Funs f Γ FVs y y' ys ys' C1 C2 S1 S2 S3,
      project_var Scope Funs f Γ FVs S1 y y' C1 S2 ->
      project_vars Scope Funs f Γ FVs S2 ys ys' C2 S3 ->
      project_vars Scope Funs f Γ FVs S1 (y :: ys) (y' :: ys') (comp_ctx_f C1 C2) S3.

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
    forall f f' xs tau e B Γ C tau' t' g g' S S',
      make_closures B (Setminus _ S (Singleton _ f')) Γ C g S' ->
      In _ S f' ->
      f_eq (g {f ~> f'}) g' ->
      make_closures (Fcons f tau xs e B) S Γ
                    (Econstr_c f tau' t' [f' ; Γ] C)
                    g' S'.

Inductive Closure_conversion :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  (var -> var) -> (* renaming of function names *)
  var -> (* The environment argument *)
  list var -> (* The free variables - needs to be ordered *)
  exp -> (* Before cc *)
  exp -> (* After cc *)
  exp_ctx -> (* The context that the output expression should be put in *)
  Prop :=
| CC_Econstr :
    forall Scope Funs f Γ FVs S' S x ys ys' C C' tau tau' t e e',
      (* Variables for projected vars should not shadow the variables in
         scope, i.e. Scope U FV U { Γ } *)
      Disjoint _ S (Union _ Scope
                          (Union _ (image f (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs f Γ FVs S ys ys' C S' ->
      (* We do not care about ys'. Should never be accessed again so do not
         add them aτ the current scope *)
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs f Γ FVs e e' C' ->
      Closure_conversion Scope Funs f Γ FVs (Econstr x tau t ys e)
                         (Econstr x tau' t ys' (C' |[ e' ]|)) C
| CC_Ecase :
    forall Scope Funs f Γ FVs x x' C S S' pats pats',
      Disjoint _ S (Union _ Scope
                          (Union _ (image f (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_var Scope Funs f Γ FVs S x x' C S' ->
      Forall2 (fun (pat pat' : tag * exp) =>
                 (fst pat) = (fst pat') /\
                 exists C' e',
                   snd pat' = C' |[ e' ]| /\
                   Closure_conversion Scope Funs f Γ FVs (snd pat) e' C')
              pats pats' ->
      Closure_conversion Scope Funs f Γ FVs (Ecase x pats) (Ecase x' pats') C
| CC_Eproj :
    forall Scope Funs f Γ FVs S S' x y y' C C' tau tau' N e e',
      Disjoint _ S (Union _ Scope
                          (Union _ (image f (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_var Scope Funs f Γ FVs S y y' C S' ->
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs f Γ FVs e e' C' ->
      Closure_conversion Scope Funs f Γ FVs (Eproj x tau N y e)
                         (Eproj x tau' N y' (C' |[ e' ]|)) C
| CC_Efun :
    forall Scope Funs f f' Γ Γ' FVs FVs' FVs'' B B' e e' C C' Ce S1 S1' S2 S2' S3 tau t,
      (* The environment contains all the variables that are free in B *)
      Same_set _ (occurs_free_fundefs B) (FromList FVs') ->
      (* Project the FVs to construct the environment *)
      Disjoint _ S1 (Union _ Scope
                          (Union _ (image f (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs f Γ FVs S1 FVs' FVs'' C' S1' ->
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
      Closure_conversion_fundefs (name_in_fundefs B) f' FVs' B B' ->
      Closure_conversion (Union _ (name_in_fundefs B) Scope) Funs f Γ FVs e e' Ce  ->
      Closure_conversion Scope Funs f Γ FVs (Efun B e)
                         (Efun B' (C |[ Ce |[ e' ]| ]|)) (comp_ctx_f C' (Econstr_c Γ' tau t FVs'' Hole_c))
| CC_Eapp :
    forall Scope Funs g Γ FVs f f' f'' env' ys ys' C S S' tau tau',
      Disjoint _ S (Union _ Scope
                          (Union _ (image g (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      (* Project the function name and the actual parameter *)
      project_vars Scope Funs g Γ FVs S (f :: ys) (f' :: ys') C S' ->
      (* (* Project the actual parameters *) *)
      (* project_vars Scope Funs Γ FVs S1 ys ys' C2 S2 -> *)
      (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
      In _ S' f'' -> In _ S' env' -> f'' <> env' ->
      Closure_conversion Scope Funs g Γ FVs (Eapp f ys)
                         (Eproj f'' tau 0%N f'
                                (Eproj env' tau' 1%N f'
                                       (Eapp f'' (env' :: ys')))) C
| CC_Eprim :
    forall Scope Funs g Γ FVs S S' x ys ys' C C' tau tau' f e e',
      Disjoint _ S (Union _ Scope
                          (Union _ (image g (Setminus _ Funs Scope))
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs g Γ FVs S ys ys' C S' ->
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs g Γ FVs e e' C' ->
      Closure_conversion Scope Funs g Γ FVs (Eprim x tau f ys e)
                         (Eprim x tau' f ys' (C' |[ e' ]|)) C
with Closure_conversion_fundefs :
  Ensemble var -> (* The function names in the current block *)
  (var -> var) -> (* renaming of function names *)
  list var -> (* The environment *)
  fundefs -> (* Before cc *)
  fundefs -> (* After cc *)
  Prop :=
| CC_Fcons :
    forall Funs g Γ' FVs S f tau tau' ys e e' C defs defs',
      (* The environment binding should not shadow the current scope
         (i.e. the names of the mut. rec. functions and the other arguments) *)
      Disjoint _ S (Union _ (image g Funs) (Union _ (FromList ys) (bound_var e))) ->
      In _ S  Γ' ->
      Closure_conversion_fundefs Funs g FVs defs defs' ->
      Closure_conversion (FromList ys) Funs g Γ' FVs e e' C ->
      Closure_conversion_fundefs Funs g FVs (Fcons f tau ys e defs )
                                 (Fcons (g f) tau' (Γ' :: ys) (C |[ e' ]|) defs')
| CC_Fnil :
    forall Funs g FVs,
      Closure_conversion_fundefs Funs g FVs Fnil Fnil.


(* Definition Closure_conversion_alpha (Scope Funs : Ensemble var) (Γ : var) *)
(*            (FVs : list var) (C : exp_ctx) sbst *)
(* : relation exp  := *)
(*   fun e e' => *)
(*     exists e'' C'', Closure_conversion Scope Funs Γ FVs e e'' C'' /\ *)
(*                Alpha_conv_ctx C'' C sbst /\ Alpha_conv e'' e' sbst. *)

(* Definition Closure_conversion_fundefs_alpha (Funs : Ensemble var) (FVs : list var) sbst *)
(* : relation fundefs  := *)
(*   relations.compose (Closure_conversion_fundefs Funs FVs) (fun B B' => Alpha_conv_fundefs B B' sbst). *)


(** * Computational defintion of closure conversion *)

Record FunInfo : Type :=
  mkFunInfo
    { (* free variables of the function definition block *)
      fv_set_def : FVSet;
      (* the names of the functions in the block *)
      rec_names  : FVSet }.

(** Maps function name to [FunInfo] *)
Definition FunInfoMap := Maps.PTree.t FunInfo.

Definition TypeMap := Maps.PTree.t type.

Inductive VarInfo : Type :=
(* A free variable, i.e. a variable outside the scope of the current function.
   The first argument is position of a free variable in the env record and the
   second its type *)
| FVar : N -> type -> VarInfo
(* A function defined in the current block of function definitions. The first
   argument is the new name of the function (code pointer), the second its the
   type of the function and the third the type of the
   closure *)
| MRFun : var -> type -> type -> VarInfo
(* A variable declared in the scope of the current function *)
| BoundVar : type -> VarInfo.

(* Maps variables to [VarInfo] *)
Definition VarInfoMap := Maps.PTree.t VarInfo.

(** The state is the next available free variable and the type dictionary *)
Definition ccstate := state (var * TDict.t).

(** Get a fresh name *)
Definition get_name : ccstate var :=
  p <- get ;;
  let '(n, d) := p in
  put ((n+1)%positive, d) ;;
  ret n.

(** Setter and getter for types *)
Definition set_typeinfo (t : typeinfo) : ccstate type :=
  p <- get ;;
  let '(n, d) := p in
  let (h, d') := TDict.hash t d in
  put (n, d') ;;
  ret h.

Definition get_typeinfo (i : type) : ccstate typeinfo :=
  p <- get ;;
  let '(n, d) := p in
  match TDict.get i d with
    | Some typinfo => ret typinfo
    | None => ret Tunknown (* should not happen *)
  end.

(** Construct the [FunInfo] map *)
Fixpoint exp_info (e : exp) (acc : FunInfoMap) : FunInfoMap :=
  match e with
    | Econstr x tau c ys e =>
      exp_info e acc
    | Ecase x pats =>
      fold_left (fun map te => exp_info (snd te) map) pats acc 
    | Eproj x tau n y e =>
      exp_info e acc
    | Efun defs e =>
      let names := fundefs_names defs in
      let acc' := fundefs_info defs (fundefs_fv defs names) names acc in
      exp_info e acc'
    | Eapp x xs => acc
    | Eprim x tau prim ys e =>
      exp_info e acc
  end
with fundefs_info (defs : fundefs) (fv : FVSet) (names : FVSet)
                  (acc : FunInfoMap) : FunInfoMap :=
       match defs with
         | Fcons f tau ys e defs' =>
           let acc' := Maps.PTree.set f
                                      {| fv_set_def := fv;
                                         rec_names := names |}
                                      acc in
           let acc'' := exp_info e acc' in
           fundefs_info defs' names fv acc'' 
         | Fnil => acc
       end.

Section CC.
  Context (utag : tag) (* Tag for types with unique constructor *)
          (env_tag : tag) (* Tag for the type of environments *)
          (tag_bij : tag -> tag) (* mapping from function tags to closure 
                                    records tags *)
          (unknown_type : type).

  (** Looks up a variable in the map and handles it appropriately *) 
  Definition get_var (x : var) (map : VarInfoMap) (Γ : var)
  : ccstate (var * type * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos typ =>
            (* pick a fresh name *)
            y <- get_name ;;
            ret (y, typ, fun e => Eproj y typ pos Γ e)   
          | MRFun code_ptr typ cl_typ =>
            (* get the new name of the function and pack it together with the
               current environment argument to construct the closure *)
            y <- get_name ;;
            ret (y, cl_typ, fun e => Econstr y cl_typ utag [code_ptr; Γ] e)
          | BoundVar typ => ret (x, typ, id)
        end
      | None => ret (x, 1%positive, id) (* should never reach here *)
    end.

  Fixpoint get_vars (xs : list var) (map : VarInfoMap)
           (cl : var) : ccstate (list var * (exp -> exp)) :=
    match xs with
      | [] => ret ([], id)
      | x :: xs =>
        t1 <- get_var x map cl ;;
        let '(y, f) := t1 in
        t2 <- get_vars xs map cl ;; 
        let '(ys, f') := t2 in
        ret (fst y :: ys, fun e => f (f' e))
    end.

  Fixpoint get_vars_with_types (xs : list var) (map : VarInfoMap) (cl : var)
  : ccstate (list var * list type * (exp -> exp)) :=
    match xs with
      | [] => ret ([], [], id)
      | x :: xs =>
        t1 <- get_var x map cl ;;
        let '(y, f) := t1 in
        t2 <- get_vars_with_types xs map cl ;; 
        let '(ys, ts, f') := t2 in
        ret (fst y :: ys, snd y :: ts, fun e => f (f' e))
    end.

  (** Construct the closure environment and the new variable map *)
  Definition make_env (fv : FVSet) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (Γ_new Γ_old : var)
  : ccstate (type * VarInfoMap * (exp -> exp)) :=
    (* put the free variables in a new map *)
    let fvs := PS.elements fv in
    let map_new' :=
        (fix add_fvs l n map :=
           match l with
             | [] => map
             | x :: xs =>
               let typ :=
                   match Maps.PTree.get x mapfv_old with
                     | Some entry  =>
                       match entry with
                         | FVar _ t | BoundVar t
                         | MRFun _ _ t => t
                       end
                     | None => 1%positive (* should not happen *)
                   end
               in
               add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n typ) map)
           end) fvs 0%N (Maps.PTree.empty VarInfo)
    in
    t1 <- get_vars_with_types fvs mapfv_old Γ_old ;;
    let '(fv', ts, g') :=  t1 in
    env_typ <- set_typeinfo (Tdata [(env_tag, ts)]) ;;
    ret (env_typ, map_new',
         fun e => g' (Econstr Γ_new env_typ utag fv' e)).

(* recursive lookup for types -- needs termination proof *)
(* Fixpoint closure_type (fun_typ env_type : type) : ccstate type := *)
(*   ftyp <- get_typeinfo fun_typ ;; *)
(*   match ftyp with *)
(*     | Tfun tag lst => *)
(*       lst' <- mapM (fun f => closure_type f env_type) lst ;; *)
(*       let ptr_inf := Tfun tag (env_type :: lst') in *)
(*       ptr_typ <- set_typeinfo ptr_inf ;;  *)
(*       let clo_inf := Tdata [(tag_bij tag, [ptr_typ; env_type])] in *)
(*       typ <- set_typeinfo clo_inf ;; *)
(*       ret typ *)
(*     | _ => ret fun_typ *)
(*   end. *)
  
  (** Construct closures after a function definition block *)
  Fixpoint make_full_closure (defs : fundefs) (mapfv_new mapfv_old : VarInfoMap)
           (Γ : var) (env_type : type)
  : ccstate (VarInfoMap * VarInfoMap * (exp -> exp)) :=
    match defs with
      | Fcons f typ xs e defs' =>
        (* The new name of the function *)
        code_ptr <- get_name ;;
        t <- make_full_closure defs' mapfv_new mapfv_old Γ env_type ;;
        let '(mapfv_new', mapfv_old', g') := t in
        tinf <- get_typeinfo typ ;;
        p <- match tinf with
               | Tfun tag args =>
                 (* The new type of the code pointer *)
                 (* XXX change args type - This is wrong *)
                 let tinf' := Tfun tag (env_type :: args) in
                 typ' <- set_typeinfo tinf' ;;
                 (* The type of the closure *)
                 let tinf'' := Tdata [(tag_bij tag, [typ'; unknown_type])] in
                 typ'' <- set_typeinfo tinf'' ;;
                  ret (typ', typ'') 
               | _ => ret (1%positive, 1%positive)
             end ;;
        let (typ', typ'') := p in (* (type of code ptr * type of closure) *)
        (* update the new map *)
        let mapfv_new'' :=
            Maps.PTree.set f (MRFun code_ptr typ' typ'') mapfv_new'
        in
        (* update the old map *)
        let mapfv_old'' :=
            Maps.PTree.set f (BoundVar typ'') mapfv_old'
        in
        ret (mapfv_new'', mapfv_old'',
             (fun e => Econstr f typ'' utag [code_ptr; Γ] (g' e)))
      | Fnil => ret (mapfv_new, mapfv_old, id)
    end.

  (** Add some bound variables in the map *)
  Fixpoint add_params args args_typ (mapfv : VarInfoMap) : VarInfoMap :=
    match args with
      | [] => mapfv
      | x :: xs =>
        let (typ, typs) :=
            match args_typ with
              | [] => (1%positive, [])
              | t :: ts => (t, ts) 
            end
        in
        M.set x (BoundVar typ) (add_params xs typs mapfv)
    end.
  
  (* Todo : Fix argument type bug *)
  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap)
           (Γ : var) : ccstate (exp * (exp -> exp)) := 
    match e with
      | Econstr x typ c ys e' =>
        t1 <- get_vars ys mapfv Γ ;;
        let '(ys', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
        ret (Econstr x typ c ys' ((snd ef) (fst ef)), f)
      | Ecase x pats =>
        pats' <-
        (fix mapM_cc l :=
         match l with
           | [] => ret []
           | (y, e) :: xs =>
             ef <- exp_closure_conv e mapfv Γ ;;
             xs' <- mapM_cc xs ;;
             ret ((y, ((snd ef) (fst ef))) :: xs')
         end) pats;;
        t1 <- get_var x mapfv Γ ;;
        (* let pats_st := List.map (fun (p : tag * exp) => *)
        (*                           let (t, e) := p in *)
        (*                           e' <- exp_closure_conv e mapfv Γ ;; *)
        (*                           ret (t, e')) pats in *)
        (* pats' <- sequence pats_st ;; *)
        (* could do [mapM] here but it stops guessing the decreasing arg :( *) 
        (* pats' <- mapM (fun (p : tag * exp) => *)
        (*                 let (t, e) := p in *)
        (*                 let e_st := exp_closure_conv e mapfv Γ in *)
        (*                 e' <-  e_st ;; *)
        (*                 ret (t, e')) pats ;; *)
        let '(x', _, f1) := t1 in           
        ret (Ecase x' pats', f1)
      | Eproj x typ n y e' =>
        t1 <- get_var y mapfv
           Γ ;;
        let '(y', _, f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
        ret (Eproj x typ n y' ((snd ef) (fst ef)), f)
      | Efun defs e =>
        let names := fundefs_names defs in
        let fv := fundefs_fv defs names in
        Γ' <- get_name ;;
        t1 <- make_env fv (Maps.PTree.empty VarInfo) mapfv Γ' Γ ;;
        let '(env_type, mapfv_new, g1) := t1 in
        t2 <- make_full_closure defs mapfv_new mapfv Γ' env_type ;;
        let '(mapfv_new', mapfv_old', g2) := t2 in
        ef <- exp_closure_conv e mapfv_old' Γ ;;
        defs' <- fundefs_closure_conv defs mapfv_new' ;;
        ret (Efun defs' (g2 ((snd ef) (fst ef))), g1)
      | Eapp f xs =>
        t1 <- get_var f mapfv Γ ;;
        let '(f', typ, g1) := t1 in     
        t2 <- get_vars xs mapfv Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name ;;
        Γ <- get_name ;;
        typinf <- get_typeinfo typ;;    
        let ftyp :=
            match typinf with
              | Tdata [(_, (ftyp :: _))] => ftyp
              | _ => 1%positive (* should not happen *) 
            end
        in
        ret (Eproj ptr ftyp 0 f'
                   (Eproj Γ unknown_type 1 f'
                          (Eapp ptr (Γ :: xs'))), fun e => g1 (g2 e))
    | Eprim x typ prim ys e' =>
      t1 <- get_vars ys mapfv Γ ;;
      let '(ys', f) := t1 in
      ef <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
      ret (Eprim x typ prim ys' ((snd ef) (fst ef)), f)
    end
  with fundefs_closure_conv (defs : fundefs) (mapfv : VarInfoMap)
       : ccstate fundefs  :=
         match defs with
           | Fcons f typ ys e defs' =>
             typinf <- get_typeinfo typ ;;
             let args_typ :=
                 match typinf with
                   | Tfun _ typs => typs
                   | _ => []
                 end
             in
             (* Add arguments to the map *)
             let mapfv' := add_params ys args_typ mapfv in
             (* formal parameter for the environment pointer *)
             Γ <- get_name ;;
             ef <- exp_closure_conv e mapfv' Γ ;;
             defs'' <- fundefs_closure_conv defs' mapfv ;;
             (* find the new name of the function *)
             let (code_ptr, typ') :=
                 match Maps.PTree.get f mapfv with
                   | Some entry =>
                     match entry with
                       | MRFun ptr typ _ => (ptr, typ)
                       | _ => (f, 1%positive) (* should never reach here *)
                     end
                   | None => (f, 1%positive) (* should never reach here *)
                 end
             in
             ret (Fcons code_ptr typ' (Γ::ys) ((snd ef) (fst ef)) defs'')
           | Fnil => ret Fnil
         end.

End CC.


Fixpoint max_list ls : positive :=
  let fix aux ls (n : positive) :=
      match ls with
        | nil => n
        | cons x xs => aux xs (Pos.max x n)
      end
  in
    aux ls 1%positive.

Fixpoint max_var e z :=
  match e with
  | Econstr x _ _ ys e => max_var e (max_list (z::x::ys)) 
  | Ecase x ys => max_list (z::x::(List.map fst ys))
  | Eproj x _ _ y e => max_var e (max_list (z::x::y::nil))
  | Efun defs e =>
    let z' := max_var_fundefs defs z in
    max_var e z'
  | Eapp f xs => max_list (z::f::xs)
  | Eprim x _ _ ys e => max_var e (max_list (z::x::ys))
  end
with max_var_fundefs defs z :=
       match defs with
         | Fcons f _ ys e defs =>
           let z' := max_var e z in
           max_var_fundefs defs (max_list (z::f::ys))
         | Fnil => z
       end.


(* XXX closure conversion does not currently handles types right. *)
Definition closure_conversion (e : exp) : exp :=
  let next :=
      let x := max_var e 1%positive in
      if Pos.leb x 3%positive then 3%positive else (x+1)%positive
  in
  let state := (next, TDict.empty) in
  let '(e, f, s) := runState
                  (exp_closure_conv 1%positive 1%positive id 1%positive
                                    e (Maps.PTree.empty VarInfo) 1%positive)
                  state in
  exp_hoist (f e).

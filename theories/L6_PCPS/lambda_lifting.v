(* Computational definition and declarative spec for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import Common.compM.
Require Import L6.cps L6.cps_util L6.ctx L6.state L6.set_util L6.identifiers L6.List_util
        L6.functions L6.Ensembles_util.
Require Import Coq.ZArith.Znumtheory Coq.Strings.String.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Import ListNotations Nnat MonadNotation PS.
Require Import compcert.lib.Maps.

Close Scope Z_scope.
Open Scope monad_scope.


(** * Lambda lifting *)

(** This transformation assumes that all bindings are unique and disjoint from
    the free variables of an expression.

    Given an expression of the form

    let f_1 x_1 = e_1
        ....
    and f_n x_n = e_n
    in e

    it will turn it (modulo α-renaming) into the expression

    let f_1' x_1 fvs = [e_1]
    and f_1 x_1 = f_1' x_1 fvs
        ....
    and f_n' x_n fvs = [e_n]
    and f_n x_n = f_n' x_n fvs
    in [e]

    where fvs are the free variables of the mutually recursive function
    definition.

    In [·] each occurrence of f_i in escaping position is left as it is, while
    each occurrence in applied position, for instance f_i z, for some z, is
    replaced with f_i' z fvs.

    If f_i is known, i.e. there are no escaping occurrences, after lambda
    lifting the definition f_i will be dead code and, thus, it can be erased
    (note that all the occurrences in applied positions have been replaced by
    f_i'). Since f_i' is closed it's closure during closure conversion will be
    empty. If a function is escaping, f_i will be closure converted in
    subsequent passes.

**)

(** * Optimizations of the above transformation *)

(*

     In order to never incur extra closure allocation, only the known
     occurrences in the same scope should use the lambda lifted version. More
     precisely:

     1) All recursive calls should use the lambda lifter version

     2) All known calls in the same scope that the function is defined should
     use the lambda lifted version

     3) All other known calls should use the lambda lifted version only if the
     free variables of the function are free variables of the scope

     To avoid performance cost when the wrapper is called from the outside, we
     inline the lambda lifted function inside the wrapper. This way we avoid
     bouncing through the wrapper but we also call the lambda lifted version in
     recursive calls.
   
     Code duplication: Since every function is duplicated, a function nested at
     level n will have 2^n copies. To avoid that we can (i.e. should) do lambda
     lifting bottom up and un-nest the (closed) lambda lifted functions. This is
     not possible when a function escapes inside it's own definition (or a mut.
     def. function) in this case


     Comparing to -unbox-closures of flambda:

     1.) Does not optimize recursive calls when an unknown function is called.

     2.) Since it relies on inliner to unfold the wrapper, it might cause more
     closure allocation
 
*)

(** * Computational Defintion *)


Section LambdaLifting.

  (* Decision about Lambda Lifting of rec functions *)
  Context (lift :  bool ->    (* True if it's a rec call (directly or from a nested function) *)
                   bool).    (* Lifting decision *)
  
  Inductive VarInfo : Type :=
  (* A variable that is free in the current function definition.
   The first argument is the name of the parameter of the lambda
   lifted function that corresponds to this free variable *)
  | FreeVar : var -> VarInfo
  | WrapperFun : var -> VarInfo.

  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := Maps.PTree.t VarInfo.

  Inductive FunInfo : Type := 
  (* A known function. The first argument is the name of the lambda lifted version,
   the second the new fun_tag and the third and forth the are free variables of the
   function as a list and as a set *)
  | Fun : var -> fun_tag -> list var -> PS.t -> FunInfo.

  (* Maps variables to [FunInfo] *)
  Definition FunInfoMap := Maps.PTree.t FunInfo.

  (* A global function name *)
  Inductive GFunInfo : Type := GFun : var -> GFunInfo.

  Definition GFunMap := M.t GFunInfo.

  Definition lambdaM := @compM' unit.

  Fixpoint add_functions (B : fundefs) (fvs : list var) (sfvs : PS.t) (m : FunInfoMap) (gfuns : GFunMap)
           (is_closed : bool)
    : lambdaM (FunInfoMap * GFunMap):=
    match B with
    | Fcons f ft xs _ B =>
      maps <- add_functions B fvs sfvs m gfuns is_closed ;;
      let '(m', gfuns') := maps in
      (* new name for lambda lifted definition - this function will always be known *)
      f' <- get_name f "_lifted";;
      (* new fun_tag for lambda listed definition *)
      ft' <- get_ftag (N.of_nat (length xs)) ;;
      (* if the function block is closed add it to the global function map *)
      let gfuns'' := if is_closed then M.set f (GFun f') gfuns' else gfuns' in
      ret (M.set f (Fun f' ft' fvs sfvs) m', gfuns'')
    | Fnil => ret (m, gfuns)
    end.
  
  Definition rename (map : VarInfoMap) (x : var) : var :=
    match M.get x map with
    | Some inf =>
      match inf with
      | FreeVar y => y
      | WrapperFun y => y
      end
    | None => x
    end.

  Definition rename_lst (map : VarInfoMap) (xs : list var) : list var :=
    (* all list of variables in the AST are in an escaping positions *)
    List.map (rename map) xs.

  Fixpoint add_free_vars (fvs : list var) (m : VarInfoMap)
    : lambdaM (list var * VarInfoMap) :=
    match fvs with
    | [] => ret ([], m)
    | y :: ys =>
      p <- add_free_vars ys m ;; 
      y' <- get_name y "";;
      let (ys', m') := p in
      ret (y' :: ys', M.set y (FreeVar y') m')
    end.

  Definition FVMap := Maps.PTree.t PS.t.

  Section TrueFV.
    
    Variable (funmap : FunInfoMap).
    Variable (active_fun : FVSet). (* Functions whose scope is currently active *)
  
    (** The set of the *true* free variables of an [exp]. The true free variables
    are the variables that appear free plus the free variables of the known
    functions that are called inside the expression. Relies on the the
    assumption that the free and bound variables are disjoint. *)
    Fixpoint exp_true_fv_aux (e : exp)
             (scope  : FVSet) (* the current variables in scope. Initially empty *)
             (fvset : PS.t) : PS.t :=
      match e with
      | Econstr x c ys e =>
        let fvset' := add_list scope fvset ys in 
        exp_true_fv_aux e (add x scope) fvset'
      | Ecase x pats =>
        let fvset' := fold_left (fun fvs p => exp_true_fv_aux (snd p) scope fvs) pats fvset in
        if mem x scope then fvset' else PS.add x fvset'
      | Eproj x tau n y e =>
        let fvset' := if mem y scope then fvset else PS.add y fvset in
        exp_true_fv_aux e (add x scope) fvset'
      | Eletapp x f ft ys e =>
        let fvset' := match funmap ! f with
                      | Some inf => (* A known function call that can be lifted *)
                        match inf with
                        | Fun f' ft' fvs _ =>
                          let is_rec := PS.mem f' active_fun in
                          if lift is_rec then union_list fvset fvs  (* f' should not count as a fv since it's a known closed function *)
                          else if mem f scope then fvset else PS.add f fvset
                        end
                      | None => if mem f scope then fvset else PS.add f fvset
                      end
        in
        let fvset'' := add_list scope fvset' ys in 
        exp_true_fv_aux e (add x scope) fvset''
      | Efun defs e =>
        let fvs':=  fundefs_fv defs in 
        let '(scope', fvset') := fundefs_true_fv_aux defs scope fvset in 
        exp_true_fv_aux e scope' fvset'
      | Eapp x ft xs =>
        let fvset' := match funmap ! x with
                      | Some inf => (* A known function call that can be lifted *)
                        match inf with
                        | Fun f' ft' fvs _ =>
                          let is_rec := PS.mem f' active_fun in
                          if lift is_rec then union_list fvset fvs (* count the fvs of the known function (LL def -> closed) but not its name *) 
                          else if mem x scope then fvset else PS.add x fvset
                        end
                      | None => if mem x scope then fvset else PS.add x fvset
                      end
        in
        add_list scope fvset' xs
      | Eprim x prim ys e =>
        let fvset' := add_list scope fvset ys in 
        exp_true_fv_aux e (add x scope) fvset'
      | Ehalt x => if mem x scope then fvset else PS.add x fvset
    end
    with fundefs_true_fv_aux (defs : fundefs) (scope : FVSet) (fvset : PS.t) : FVSet * PS.t :=
           match defs with
           | Fcons f t ys e defs' =>
             let (scope', fvset') := fundefs_true_fv_aux defs' (add f scope) fvset in
             (scope', exp_true_fv_aux e (union_list scope' ys) fvset')
           | Fnil => (scope, fvset)
           end.
  
    Definition exp_true_fv e := exp_true_fv_aux e PS.empty PS.empty.
    
    Definition fundefs_true_fv B := snd (fundefs_true_fv_aux B PS.empty PS.empty). 
    
  End TrueFV.
  
  Fixpoint make_wrappers (B: fundefs) (fvm : VarInfoMap) (fm: FunInfoMap) : lambdaM (exp_ctx * VarInfoMap):=
    match B with
    | Fcons f ft xs e B =>
      match M.get f fm with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs =>
          g <- get_name f "_wrapper" ;;
          xs' <- get_names_lst xs "" ;;
          cm <- make_wrappers B fvm fm ;;
          let (c, fvm') := cm in
          let fvm'' := M.set f (WrapperFun g) fvm' in
          ret (Efun1_c (Fcons g ft xs' (Eapp f' ft' (xs' ++ (rename_lst fvm fvs))) Fnil) c, fvm'')
        end
      | None => ret (Hole_c, fvm) (* should never match *)
      end
    | Fnil => ret (Hole_c, fvm)
    end.
  

  Definition name_block B :=
    match B with
    | Fcons f _ _ _ _ => f
    | Fnil => 1%positive
    end.
  
  Fixpoint exp_lambda_lift (e : exp) (scope: PS.t) (active_funs : PS.t)
           (fvm : VarInfoMap) (fm : FunInfoMap) (gfuns : GFunMap) : lambdaM exp :=
    match e with
    | Econstr x t ys e => 
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Econstr x t (rename_lst fvm ys) e')
    | Ecase x P =>
      P' <-
      (fix mapM_ll l :=
         match l with
         | [] => ret []
         | (c, e) :: P =>
           e' <- exp_lambda_lift e scope active_funs fvm fm gfuns ;;
              P' <- mapM_ll P ;;
              ret ((c, e') :: P')
         end) P ;;
      ret (Ecase (rename fvm x) P')
    | Eproj x t N y e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Eproj x t N (rename fvm y) e')
    | Eletapp x f ft ys e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      match fm ! f with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs =>
          (* only call the known function if its free variables can be accessed *)
          if PS.subset sfvs scope || lift (PS.mem f active_funs) then 
            ret (Eletapp x (rename fvm f') ft' (rename_lst fvm (ys ++ fvs)) e')
          else ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
        end
      | None =>
        ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
      end
    | Efun B e =>
      let sfvsi := fundefs_true_fv fm active_funs B in
      let sfvs := PS.filter (fun x => match M.get x gfuns with Some _ => false | None => true end) sfvsi in
      let fvs := PS.elements sfvs in
      (* DEBUG *)
      b_name <- get_pp_name (name_block B) ;;
      fv_names <- get_pp_names_list (PS.elements sfvsi) ;;
      log_msg (String.concat " " ("Block" :: b_name :: "has fvs :" :: fv_names)) ;;

      let is_closed := match fvs with [] => true | _ => false end in
      maps' <- add_functions B fvs sfvs fm gfuns is_closed ;;
      let (fm', gfuns') := maps' in
      let names := fundefs_names B in
      let scope' := PS.union names scope in
      B' <- fundefs_lambda_lift B B names (PS.union names active_funs) fvm fm' gfuns' ;;
      cm <- make_wrappers B fvm fm' ;;
      let (C, fvm') := cm in
      e' <- exp_lambda_lift e (PS.union names scope) active_funs fvm' fm' gfuns' ;;
      ret (Efun B' (C |[ e' ]|))
    | Eapp f ft xs => 
      match fm ! f with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs =>
          (* only call the known function if its free variables can be accessed *)
          if PS.subset sfvs scope || lift (PS.mem f active_funs) then 
            ret (Eapp (rename fvm f') ft' (rename_lst fvm (xs ++ fvs)))
          else ret (Eapp (rename fvm f) ft (rename_lst fvm xs))
        end
      | None =>
        ret (Eapp (rename fvm f) ft (rename_lst fvm xs))
      end
    | Eprim x f ys e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Eprim x f (rename_lst fvm ys) e')
    | Ehalt x => ret (Ehalt (rename fvm x))
    end
  with fundefs_lambda_lift B Bfull (fnames : FVSet) active_funs fvm (fm : FunInfoMap) (gfuns : GFunMap) :=
         match B with
         | Fcons f ft xs e B => 
           match M.get f fm with
           | Some inf =>
             match inf with
             | Fun f' ft' fvs sfvs =>
               (* Debug *)
               f_str <- get_pp_name f ;;
               fv_names <- get_pp_names_list fvs ;;
               log_msg (String.concat " " (f_str :: "has fvs :" :: fv_names)) ;;
               (* *)
               p <- add_free_vars fvs fvm ;;
               let (ys, fvm') := p in
               cm <- make_wrappers Bfull fvm' fm ;;
               let (C, fvm'') := cm in
               (* Variables in scope are : 1. Whatever variables are locally bound (current functions, arguments, local defs)
                  and 2. The FVs of the current function *)
               e' <- exp_lambda_lift e (PS.union fnames (union_list sfvs xs)) active_funs fvm'' fm gfuns ;;
               B' <- fundefs_lambda_lift B Bfull fnames active_funs fvm fm gfuns ;;
               ret (Fcons f' ft' (xs ++ ys) (C |[ e' ]|)  B')
             end
           | None => ret (Fcons f ft xs e B) (* should never match *)
           end
         | Fnil => ret Fnil
         end.


  (* Example :
     
   let f x =
     let g y = x + y + z in
       g 3 + x 

   ==>

   let f' x z' =
       let g' y x' z'' = y + x' + z'' in
       let g y = g' y x z'
       in g' 3 x z' + 3 in
   let f x = f' x z
   *)

End LambdaLifting.

Definition lift_all (is_rec : bool) := true.

Definition lift_rec (is_rec : bool) := is_rec.

Definition lift_conservative (is_rec : bool) := false.

Definition lambda_lift (e : exp) (c : comp_data) : error exp * comp_data :=
  let '(e', (c', _)) := run_compM (exp_lambda_lift lift_rec e PS.empty PS.empty (Maps.PTree.empty VarInfo)
                                                   (Maps.PTree.empty FunInfo) (M.empty GFunInfo))
                                  c tt in  
  (e', c').


(** * Relational Defintion *)

Inductive Add_functions :
  fundefs ->
  list var ->
  (var -> var) ->
  (var -> option (var * fun_tag * list var)) ->
  Ensemble var ->
  (var -> var) ->
  (var -> option (var * fun_tag * list var)) ->
  Ensemble var ->
  Prop :=
| Add_Fcons :
    forall f ft xs e B fvs σ σ' ζ ζ' S S' f' ft',
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Ensembles.In _ S' f' ->
      Add_functions (Fcons f ft xs e B) fvs σ ζ S
                    (σ' {f ~> f} {f' ~> f'}) (ζ' {f ~> Some (f', ft', fvs)})
                    (Setminus _ S' (Singleton _ f'))
| Add_Fnil :
    forall fvs σ ζ S,
      Add_functions Fnil fvs σ ζ S σ ζ S.

(* Map from the original name to the name of the lifted function *)
Definition lifted_name (ζ : var -> option (var * fun_tag * list var)) : var -> option var :=
  fun f => (liftM (fun x => (fst (fst x)))) (ζ f).

(* Map from the original name to the list of free vars *)
Definition free_vars (ζ : var -> option (var * fun_tag * list var)) : var -> option (list var) :=
  fun f => (liftM (fun x => snd x)) (ζ f).

(** The domain of ζ *)
Definition Funs (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  domain (lifted_name ζ).

(** The image of ζ on its domain - i.e. the names of the lifted functions *)
Definition LiftedFuns (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  image' (lifted_name ζ) (Funs ζ).

(**  The free variables of functions in ζ, alternative definition *)
Definition FunsFVsLst (ζ : var -> option (var * fun_tag * list var)) : Ensemble (list var) :=
  fun fvs => exists f f' ft', ζ f = Some (f', ft', fvs).

(**  The free variables of functions in ζ *)
Definition FunsFVs (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  fun v => exists f f' ft' fvs, ζ f = Some (f', ft', fvs) /\
                        Ensembles.In _ (FromList fvs) v.

Inductive Exp_lambda_lift :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  exp ->
  Ensemble var ->
  exp ->
  Ensemble var ->
  Prop :=
| LL_Econstr :
    forall ζ σ x t ys e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Econstr x t ys e) S (Econstr x t (map σ ys) e') S'
| LL_Ecase_nil :
    forall ζ σ x S,
      Exp_lambda_lift ζ σ (Ecase x []) S (Ecase (σ x) []) S
| LL_Ecase_cons :
    forall ζ σ x y c e e' P P' S S' S'',
      Exp_lambda_lift ζ σ e S e' S' ->
      Exp_lambda_lift ζ σ (Ecase x P) S' (Ecase y P') S'' ->
      Exp_lambda_lift ζ σ (Ecase x ((c, e) :: P)) S (Ecase (σ x) ((c, e') :: P')) S''
| LL_Eproj :
    forall ζ σ x t N y e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eproj x t N y e) S (Eproj x t N (σ y) e') S'
| LL_Efun :
    forall B B' e e' σ σ' ζ ζ' fvs S S' S'' S''',
      Included _ (FromList fvs) (Union _ (occurs_free_fundefs B)
                                       (Union _ (FunsFVs ζ) (LiftedFuns ζ))) ->
      NoDup fvs ->
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Fundefs_lambda_lift ζ' σ' B S' B' S'' ->
      Exp_lambda_lift ζ' σ' e S'' e' S''' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S'''
| LL_Eapp_known :
    forall ζ σ f ft xs f' ft' fvs S,
      ζ f = Some (f', ft', fvs) -> 
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp (σ f') ft' (map σ (xs ++ fvs))) S
| LL_Eapp_unknown :
    forall ζ σ f ft xs S,
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp (σ f) ft (map σ xs)) S
| LL_Eprim :
    forall ζ σ x f ys e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eprim x f ys e) S (Eprim x f (map σ ys) e') S'
| LL_Ehalt :
    forall ζ σ x S,
      Exp_lambda_lift ζ σ (Ehalt x) S (Ehalt (σ x)) S
with Fundefs_lambda_lift :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons :
         forall ζ σ f ft xs xs' e e' B B' S S' S'' f' ft' fvs ys,
           ζ f = Some (f', ft', fvs) ->
           Included _ (FromList ys) S ->
           Included _ (FromList xs') (Setminus _ S (FromList ys)) ->
           NoDup ys -> NoDup xs' ->
           length ys = length fvs ->
           length xs' = length xs -> 
           Exp_lambda_lift ζ (σ <{ (xs ++ fvs) ~> (xs ++ ys) }>)
                           e (Setminus _ (Setminus _ S (FromList ys)) (FromList xs'))
                           e' S' ->
           Fundefs_lambda_lift ζ σ B S' B' S'' ->
           Fundefs_lambda_lift ζ σ (Fcons f ft xs e B) S
                               (Fcons f' ft' (xs ++ ys) e'
                                      (Fcons f ft xs'
                                             (Eapp f' ft' (xs' ++ (map σ fvs))) B')) S''
     | LL_Fnil :
         forall ζ σ S,
           Fundefs_lambda_lift ζ σ Fnil S Fnil S.

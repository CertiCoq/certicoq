(* Computational definition and declarative spec for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import Common.compM.
Require Import L6.alpha_conv L6.cps L6.cps_util L6.ctx L6.state L6.set_util L6.identifiers L6.List_util
        L6.functions L6.Ensembles_util L6.uncurry L6.tactics.
Require Import Coq.ZArith.Znumtheory Coq.Strings.String.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Require Import compcert.lib.Coqlib.

Import ListNotations Nnat MonadNotation PS.
Require Import compcert.lib.Maps.

Close Scope Z_scope.
Open Scope monad_scope.
 

(** * Lambda lifting *)

(* XXX TODO Comments are not uptodate with the implementation *)

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
  Context (max_args : nat). (* Maximum number of arguments that a function can have *)
  Context (max_push : nat). (* Maximum amount of times that a lifted var is allows to be stored in the stack. *)
                          (* To calculate the tradeoff between projecting from environment/stack push *)
  
  Inductive VarInfo : Type :=
  (* A variable that is free in the current function definition.
   The first argument is the name of the parameter of the lambda
   lifted function that corresponds to this free variable *)
  | FreeVar : var -> VarInfo
  | WrapperFun : var -> VarInfo.

  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := Maps.PTree.t VarInfo.

  Inductive FunInfo : Type := 
  (* A known function. *)
  | Fun :
      var ->        (* New name for the lambda lifted version *)
      fun_tag ->    (* New fun_tag *)
      list var ->   (* Free variables as list *)
      PS.t ->       (* Free variables as sets *)
      list var ->   (* Lifted variables *)
      FunInfo.

  (* Maps variables to [FunInfo] *)
  Definition FunInfoMap := Maps.PTree.t FunInfo.

  (* A global function name *)
  Inductive GFunInfo : Type :=
    GFun : var -> GFunInfo (* Original global function *)
  | LGFun : GFunInfo.

  Definition GFunMap := M.t GFunInfo.

  Definition lambdaM := @compM' unit.

  Fixpoint add_functions (B : fundefs) (fvs : list var) (sfvs : PS.t) (args : list var)
           (m : FunInfoMap) (gfuns : GFunMap)
    : lambdaM (FunInfoMap * GFunMap):=
    match B with
    | Fcons f ft xs _ B =>
      maps <- add_functions B fvs sfvs args m gfuns ;;
      let '(m', gfuns') := maps in
      (* new name for lambda lifted definition - this function will always be known *)
      f' <- get_name f "_lifted";;
      (* new fun_tag for lambda lifted definition *)
      ft' <- get_ftag (N.of_nat (length xs)) ;;
      (* is the original function closed? *)
      let is_closed := match fvs with [] => true | _ => false end in
      (* is the lifted function closed? *)
      let is_closed_lifted := Nat.eqb (length fvs) (length args) in
      (* if the function block is closed add it to the global function map *)
      let gfuns'' := if is_closed then M.set f (GFun f') gfuns' else gfuns' in
      let gfuns''' := if is_closed_lifted then M.set f' LGFun gfuns' else gfuns' in
      ret (M.set f (Fun f' ft' fvs sfvs args) m', gfuns'')
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
  
  Fixpoint make_wrappers (B: fundefs) (fvm : VarInfoMap) (fm: FunInfoMap) : lambdaM (exp_ctx * VarInfoMap):=
    match B with
    | Fcons f ft xs e B =>
      match M.get f fm with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs args =>
          g <- get_name f "_wrapper" ;;
          xs' <- get_names_lst xs "" ;;
          cm <- make_wrappers B fvm fm ;;
          let (c, fvm') := cm in
          let fvm'' := M.set f (WrapperFun g) fvm' in
          ret (Efun1_c (Fcons g ft xs' (Eapp f' ft' (xs' ++ (rename_lst fvm args))) Fnil) c, fvm'')
        end
      | None => failwith "make_wrappers: Function not found"
      end
    | Fnil => ret (Hole_c, fvm) 
    end.

  Definition fundefs_max_params (B: fundefs) : nat :=
    (fix aux B p : nat :=      
       match B with
       | Fcons f ft xs e B =>
         aux B (max (length xs) p)
       | Fnil => 0
       end) B 0.

  Definition name_block B :=
    match B with
    | Fcons f _ _ _ _ => f
    | Fnil => 1%positive
    end.

  Section TrueFV.

    (* Returns the FV of an exp after a function call is replaced with lambda lifted version *)

    Variable (funmap : FunInfoMap).
    Variable (active_fun : FVSet). (* Functions whose scope is currently active *)


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
                        | Fun f' ft' fvs _ _ =>
                          let is_in_scope := PS.mem f active_fun in (* XXX update lifting decisions *)
                          if lift is_in_scope then union_list fvset (f' :: fvs)
                          else if mem f scope then fvset else PS.add f fvset
                        end
                      | None => if mem f scope then fvset else PS.add f fvset
                      end
        in
        let fvset'' := add_list scope fvset' ys in
        exp_true_fv_aux e (add x scope) fvset''
      | Efun defs e =>
        let fvs':= fundefs_fv defs in
        let '(scope', fvset') := fundefs_true_fv_aux defs scope fvset in
        exp_true_fv_aux e scope' fvset'
      | Eapp f ft xs =>
        let fvset' := match funmap ! f with
                      | Some inf => (* A known function call that can be lifted *)
                        match inf with
                        | Fun f' ft' fvs _ _ =>
                          let is_in_scope := PS.mem f active_fun in
                          if lift is_in_scope then union_list fvset (f' :: fvs)
                          else if mem f scope then fvset else PS.add f fvset
                        end
                      | None => if mem f scope then fvset else PS.add f fvset
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


  (* TODO move *)
  Definition subset_list (l : list var) (s : PS.t) :=
    fold_left (fun b e => PS.mem e s && b) l true. 

  Fixpoint take {A} (n: nat) (l : list A) :=
    match n with
    | 0 => []
    | S n =>
      match l with
      | [] => []
      | x :: xs => x :: take n xs
      end
    end.

  Fixpoint occurs_in_exp (k:var) (curr_f: PS.t) (e:exp) : bool :=
    match e with
    | Econstr z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Ecase x arms =>
      eq_var k x ||
              (fix occurs_in_arms (arms: list (ctor_tag * exp)) : bool :=
                 match arms with
                 | nil => false
                 | p::arms1 => match p with
                               | (_,e) => occurs_in_exp k curr_f e || occurs_in_arms arms1
                               end
                 end) arms
    | Eproj z _ _ x e1 =>
      eq_var z k || eq_var k x || occurs_in_exp k curr_f e1
    | Eletapp z f _ xs e1 =>
      (* If the call is recursive, then after lambda lifting k will appear free in the subexpression *)
      eq_var z k || eq_var f k || PS.mem f curr_f || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Efun fds e =>
      occurs_in_fundefs k curr_f fds || occurs_in_exp k curr_f e
    | Eapp x _ xs => eq_var k x || PS.mem x curr_f || occurs_in_vars k xs
    | Eprim z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Ehalt x => eq_var x k
    end
  (* Returns true iff [k] occurs within the function definitions [fds] *)
  with occurs_in_fundefs (k:var) (curr_f: PS.t) (fds:fundefs) : bool :=
         match fds with
         | Fnil => false
         | Fcons z _ zs e fds1 =>
           eq_var z k || occurs_in_vars k zs || occurs_in_exp k curr_f e ||
                   occurs_in_fundefs k curr_f fds1
         end.



  (* Calculate how many times an argument has to be pushed on to the shadow stack because
   * of intermediate calls. Assumes unique binders *)
  Fixpoint stack_push (x : var) (curr_f : PS.t) (e : exp) : nat :=
    match e with
    | Econstr _ _ _ e
    | Eproj _ _ _ _ e
    | Eprim _ _ _ e 
    | Efun _ e =>
      stack_push x curr_f e
    | Eapp _ _ _
    | Ehalt _ => 0
    | Ecase _ P =>
      fold_left (fun n br => max n (stack_push x curr_f (snd br))) P 0
    | Eletapp _ f ft ys e =>
      let n := stack_push x curr_f e in
      (* Before the call, if x is used in e, then it has to be stored *)
      if occurs_in_exp x curr_f e then n + 1 else n
    end. 

  Fixpoint stack_push_fundefs_aux (x : var) (curr_f : PS.t)  (B : fundefs) : nat :=
    match B with
    | Fcons f ft xs e B' =>
      max (stack_push x curr_f e) (stack_push_fundefs_aux x curr_f B')
    | Fnil => 0
    end.
  
  Definition stack_push_fundefs (x : var) (B : fundefs) : nat :=
    stack_push_fundefs_aux x (fundefs_names B) B. 
  
  
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
        | Fun f' ft' fvs sfvs args =>
          (* only call the known function if its free variables can be accessed *)
          (* TODO : lift the arguments that are available at the time of the call? *)
          if subset_list args scope || lift (PS.mem f active_funs) then 
            ret (Eletapp x (rename fvm f') ft' (rename_lst fvm (ys ++ args)) e')
          else ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
        end
      | None =>
        ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
      end
    | Efun B e =>
      (* Find the free variables of the fundefs *)
      let sfvsi := fundefs_true_fv fm active_funs B in
      (* Remove global functions *)
      let sfvs := PS.filter (fun x => match M.get x gfuns with Some _ => false | None => true end) sfvsi in
      (* Turn to list *)
      let fvs := PS.elements sfvs in
      (* Filter out arguments that is expensive to lift *)
      let lfvs := List.filter (fun x => let n := stack_push_fundefs x B in Nat.leb n max_push) fvs in
      (* DEBUG *)
      b_name <- get_pp_name (name_block B) ;;
      fv_names <- get_pp_names_list (PS.elements sfvsi) ;;
      log_msg (String.concat " " ("Block" :: b_name :: "has fvs :" :: fv_names)) ;;
      (* END DEBUG *)
      (* Number of argument slots available. By convention lift exactly the same no of args in each mut. rec. function *)
      let lifted_args := max_args - (fundefs_max_params B) in
      maps' <- add_functions B fvs sfvs (take lifted_args lfvs) fm gfuns ;;
      let (fm', gfuns') := maps' in
      let names := fundefs_names B in
      let scope' := PS.union names scope in
      let max_params := fundefs_max_params B in
      B' <- fundefs_lambda_lift B B names (PS.union names active_funs) fvm fm' gfuns' lifted_args ;;
      cm <- make_wrappers B fvm fm' ;;
      let (C, fvm') := cm in
      e' <- exp_lambda_lift e (PS.union names scope) active_funs fvm' fm' gfuns' ;;
      ret (Efun B' (C |[ e' ]|))
    | Eapp f ft xs => 
      match fm ! f with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs args =>
          (* only call the known function if its free variables can be accessed *)
          if PS.subset sfvs scope || lift (PS.mem f active_funs) then 
            ret (Eapp (rename fvm f') ft' (rename_lst fvm (xs ++ args)))
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
  with fundefs_lambda_lift B Bfull (fnames : FVSet) active_funs fvm (fm : FunInfoMap) (gfuns : GFunMap) (fv_no : nat) :=
         match B with
         | Fcons f ft xs e B => 
           match M.get f fm with
           | Some inf =>
             match inf with
             | Fun f' ft' fvs sfvs args =>
               (* Debug *)
               f_str <- get_pp_name f ;;
               fv_names <- get_pp_names_list fvs ;;
               log_msg (String.concat " " (f_str :: "has fvs :" :: fv_names)) ;;
               (* *)
               p <- add_free_vars args fvm ;;
               let (ys, fvm') := p in
               cm <- make_wrappers Bfull fvm' fm ;;
               let (C, fvm'') := cm in
               (* Variables in scope are : 1. Whatever variables are locally bound (current functions, arguments, local defs)
                  and 2. The FVs of the current function *)
               e' <- exp_lambda_lift e (PS.union fnames (union_list sfvs xs)) active_funs fvm'' fm gfuns ;;
               B' <- fundefs_lambda_lift B Bfull fnames active_funs fvm fm gfuns fv_no ;;
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

Definition lambda_lift (e : exp) (args : nat) (no_push : nat) (c : comp_data) : error exp * comp_data :=
  let '(e', (c', _)) := run_compM (exp_lambda_lift lift_rec args no_push e PS.empty PS.empty (Maps.PTree.empty VarInfo)
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

Inductive Make_wrappers :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  (var -> var) ->
  Prop :=
| MW_Fnil :
    forall ζ σ S, Make_wrappers ζ σ Fnil S Fnil S σ
| MW_Fcons :
    forall  (ζ : var -> option (var * fun_tag * list var)) σ σ' f ft xs xs' e B fds S S' f' ft' fvs g,
      ζ f = Some (f', ft', fvs) ->
      (FromList xs') \subset S ->
      NoDup xs' -> length xs = length xs' ->
      g \in (S \\ FromList xs') ->
      Make_wrappers ζ σ B (S \\ FromList xs' \\ [set g]) fds S' σ' ->
      Make_wrappers ζ σ (Fcons f ft xs e B) S (Fcons g ft xs' (Eapp f' ft' (xs' ++ (map σ fvs))) fds) S' (σ' {f ~> g}). 


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
| LL_Efun1 : (* wrappers are mutually defined *)
    forall B B' e e' σ σ' ζ ζ' fvs S S' S'' S''',
      Included _ (FromList fvs) (occurs_free_fundefs B) ->
(* Previous less restrictive version *)
(*   Included _ (FromList fvs) (Union _ (occurs_free_fundefs B)
                                       (Union _ (FunsFVs ζ) (LiftedFuns ζ))) *)
      NoDup fvs ->
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Fundefs_lambda_lift1 ζ' σ' B S' B' S'' ->
      Exp_lambda_lift ζ' σ' e S'' e' S''' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S'''
| LL_Efun2 : (* wrappers are defined afterwards *)
    forall B B' e e' fds σ σ' σ'' ζ ζ' fvs S S' S'' S''' S'''',
      Included _ (FromList fvs) (occurs_free_fundefs B) ->
      NoDup fvs ->
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Fundefs_lambda_lift2 ζ' σ' B B S' B' S'' ->
      Make_wrappers ζ' σ' B S'' fds S''' σ'' ->
      Exp_lambda_lift ζ' σ'' e S''' e' S'''' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' (Efun fds e')) S''''
| LL_Efun3 : (* No Lambda Lifting *)
    forall B B' e e' σ ζ S S' S'',
      Fundefs_lambda_lift3 ζ σ B B S B' S' ->
      Exp_lambda_lift ζ (extend_fundefs σ B B) e S' e' S'' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S''
| LL_Eletapp_known :
    forall ζ σ x f ft xs e e' f' ft' fvs S S',
      ζ f = Some (f', ft', fvs) ->
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eletapp x f ft xs e) S (Eletapp x (σ f') ft' (map σ (xs ++ fvs)) e') S'
| LL_Eletapp_unknown :
    forall ζ σ x f ft xs e e' S S',
      Exp_lambda_lift ζ  (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eletapp x f ft xs e) S (Eletapp x (σ f) ft (map σ xs) e') S'
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
with Fundefs_lambda_lift1 :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons1 :
         forall ζ σ f ft xs xs' e e' B B' S S' S'' f' ft' fvs ys,
           ζ f = Some (f', ft', fvs) ->
           FromList ys \subset S ->
           FromList xs' \subset (S \\ (FromList ys)) ->
           NoDup ys -> NoDup xs' ->
           length ys = length fvs ->
           length xs' = length xs -> 
           Exp_lambda_lift ζ (σ <{ (xs ++ fvs) ~> (xs ++ ys) }>)
                           e ((S \\ (FromList ys)) \\ (FromList xs')) e' S' ->
           Fundefs_lambda_lift1 ζ σ B S' B' S'' ->
           Fundefs_lambda_lift1 ζ σ (Fcons f ft xs e B) S
                                (Fcons f' ft' (xs ++ ys) e'
                                       (Fcons f ft xs'
                                              (Eapp f' ft' (xs' ++ (map σ fvs))) B')) S''
     | LL_Fnil1 :
         forall ζ σ S,
           Fundefs_lambda_lift1 ζ σ Fnil S Fnil S
with Fundefs_lambda_lift2 :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs -> (* original fundefs *)
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons2 :
         forall ζ σ σ' f ft xs e e' B0 B B' S S' S'' S''' f' ft' fvs ys fds,
           ζ f = Some (f', ft', fvs) ->
           Included _ (FromList ys) S ->
           NoDup ys ->
           length ys = length fvs ->
           Make_wrappers ζ (σ <{ (xs ++ fvs) ~> (xs ++ ys) }>) B0 (S \\ FromList ys) fds S' σ' ->  
           Exp_lambda_lift ζ σ' e S' e' S'' ->
           Fundefs_lambda_lift2 ζ σ B0 B S'' B' S''' ->
           Fundefs_lambda_lift2 ζ σ B0 (Fcons f ft xs e B) S
                                (Fcons f' ft' (xs ++ ys) (Efun fds e') B') S'''
     | LL_Fnil2 :
         forall ζ σ S B0,
           Fundefs_lambda_lift2 ζ σ B0 Fnil S Fnil S
with Fundefs_lambda_lift3 :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons3 :
         forall ζ σ  f ft xs e e' B0 B B' S S' S'',
           Exp_lambda_lift ζ ((extend_fundefs σ B0 B0) <{ xs ~> xs }>) e S e' S' ->
           Fundefs_lambda_lift3 ζ σ B0 B S' B' S'' ->
           Fundefs_lambda_lift3 ζ σ B0 (Fcons f ft xs e B) S (Fcons f ft xs e' B') S''
     | LL_Fnil3 :
         forall ζ σ B0 S,
           Fundefs_lambda_lift3 ζ σ B0 Fnil S Fnil S.


(** * Some syntactic properties of  the lambda lifting relation *)

  (** * Lemmas about [lifted_name], [Funs], [LiftedFuns], [FunsFVs] and [FunsFVsLst] *)

  Lemma lifted_name_extend f x x' xs l :
    f_eq (lifted_name (f {x ~> Some (x', xs, l)})) ((lifted_name f) { x ~> Some x' }).
  Proof.
    intros y. unfold lifted_name; simpl.
    destruct (peq x y); subst.
    - rewrite !extend_gss. reflexivity.
    - rewrite !extend_gso; eauto.
  Qed.

  Lemma lifted_name_eq f x x' xs l :
    f x = Some (x', xs, l) ->
    lifted_name f x = Some x'.
  Proof.
    intros Heq; unfold lifted_name; rewrite Heq; eauto.
  Qed.

  Lemma Funs_extend_Some ζ f f' ft fvs :
    Included _ (Funs (ζ {f ~> Some (f', ft, fvs)}))
             (Union _ (Funs ζ) (Singleton _ f)).
  Proof.
    intros x [val H].
    destruct (peq f x); subst.
    - rewrite lifted_name_extend, extend_gss in H. inv H. eauto.
    - rewrite lifted_name_extend, extend_gso in H; eauto.
      left. eexists; eauto.
  Qed.

  Lemma LiftedFuns_extend_Some ζ f f' ft fvs :
    Included _ (LiftedFuns (ζ {f ~> Some (f', ft, fvs)}))
            (Union _ (LiftedFuns ζ) (Singleton _ f')).
  Proof.
    intros x [g [H1 H2]].
    destruct (peq f g); subst; rewrite lifted_name_extend in H2;
    apply Funs_extend_Some in H1.
    - rewrite extend_gss in H2. inv H2. eauto.
    - rewrite extend_gso in H2; eauto. inv H1; eauto.
      left. repeat eexists; eauto.
      inv H; congruence.
  Qed.
  
  Lemma FunsFVs_extend_Some ζ f f' ft fvs :
    Included _ (FunsFVs (ζ {f ~> Some (f', ft, fvs)}))
            (Union _ (FunsFVs ζ) (FromList fvs)).
  Proof.
    intros x [g [g' [gt' [fvs' [H1 H2]]]]].
    destruct (peq f g); subst.
    - rewrite extend_gss in H1. inv H1. eauto.
    - rewrite extend_gso in H1; eauto.
      left. eexists; eauto.
  Qed.
  
  Lemma FunsFVs_extend_Some_eq ζ f f' ft fvs :
    ~ f \in Funs ζ ->
    Same_set var (FunsFVs (ζ {f ~> Some (f', ft, fvs)}))
             (Union var (FunsFVs ζ) (FromList fvs)).
  Proof.
    intros Hn; split.
    - now apply FunsFVs_extend_Some.
    - intros x Hin. inv Hin.
      destruct H as [g [g' [fg [l [Heq Hin]]]]].
      repeat eexists; eauto. rewrite extend_gso.
      eassumption. intros Hc; apply Hn. subst.
      repeat eexists; eauto. eapply lifted_name_eq.
      subst. eassumption.
      repeat eexists; eauto. rewrite extend_gss.
      reflexivity.
  Qed.
  
  Lemma lifted_name_f_eq_subdomain S f1 f2 :
    f_eq_subdomain S f1 f2 ->
    f_eq_subdomain S (lifted_name f1) (lifted_name f2).
  Proof.
    intros Heq x Hin. unfold lifted_name. simpl; rewrite Heq; eauto.
  Qed.

(** * Lemmas about [Add_functions] *)

Lemma Add_functions_free_set_Included B fvs ζ σ S ζ' σ' S' :
  Add_functions B fvs ζ σ S ζ' σ' S' ->
  Included _ S' S.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd...
Qed.

Lemma Add_functions_fvs_eq B fvs σ ζ S σ' ζ' S' f f' ft fvs' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  ζ' f = Some (f', ft, fvs') ->
  f \in name_in_fundefs B ->
  fvs' = fvs.
Proof.
  intros Hadd Heq Hin; induction Hadd.
  - destruct (peq f f0); subst.
    + rewrite extend_gss in Heq. inv Heq. eauto.
    + inv Hin. inv H0; congruence.
      rewrite extend_gso in Heq; eauto.
  - inv Hin.
Qed.

Lemma Add_functions_eq B fvs σ ζ S σ' ζ' S' f :
  ~ f \in name_in_fundefs B ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  ζ' f = ζ f.
Proof.
  intros Hin Hadd; induction Hadd.
  - rewrite extend_gso. eapply IHHadd.
    + intros Hc. eapply Hin. now right.
    + intros Hc. subst. eapply Hin. left. reflexivity.
  - reflexivity.
Qed.

Lemma Add_functions_image_Included Q B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  (image σ' Q) \subset
               ((image σ (Q \\ ((name_in_fundefs B) :|: (S \\ S')))) :|: (name_in_fundefs B :|: (S \\ S'))).
Proof with now eauto with Ensembles_DB.
  intros Hadd. revert Q. induction Hadd; intros Q.
  - eapply Included_trans. now eapply image_extend_Included'.
    eapply Union_Included.
    eapply Included_trans. now eapply image_extend_Included'. 
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Included_trans. eapply IHHadd.
    simpl. eapply Included_Union_compat.
    rewrite !Setminus_Union. eapply image_monotonic.
    eapply Included_Setminus_compat. reflexivity.
    apply Union_Included. now eauto with Ensembles_DB.
    eapply Included_trans. eapply Setminus_Setminus_Included.
    now eauto with typeclass_instances.
    now eauto with Ensembles_DB.
    apply Union_Included. now eauto with Ensembles_DB.
    apply Included_Union_preserv_r. apply Included_Setminus_compat.
    reflexivity. now eauto with Ensembles_DB.
    simpl. do 2 apply Included_Union_preserv_r.
    apply Singleton_Included. constructor.
    eapply Add_functions_free_set_Included; now eauto.
    intros Hc; inv Hc; eauto.
  - simpl. rewrite Setminus_Same_set_Empty_set at 1.
    rewrite Setminus_Same_set_Empty_set at 1.
    repeat rewrite Union_Empty_set_neut_r at 1.
    rewrite Setminus_Empty_set_neut_r. reflexivity.
Qed.

Lemma Add_functions_LiftedFuns_Included_r B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Included _ (LiftedFuns ζ') (Union _ (LiftedFuns ζ) (Setminus _ S S')).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply LiftedFuns_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r.
    eapply Singleton_Included. constructor.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc. inv Hc. eauto.
  - now eauto with Ensembles_DB.
Qed.


Lemma Add_functions_lifted_name_Same_set B fvs σ ζ S σ' ζ' S' Q :
  unique_bindings_fundefs B ->
  Disjoint _ Q (name_in_fundefs B) ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Same_set _ (image' (lifted_name ζ') (Union _ Q (name_in_fundefs B)))
           (Union _ (image' (lifted_name ζ) Q) (Setminus _ S S')).
Proof with now eauto with Ensembles_DB.
  intros Hun HD Hadd. revert Q HD; induction Hadd; intros Q HD.
  - inv Hun. rewrite lifted_name_extend. simpl.
    rewrite image'_extend_is_Some_In_P.
    rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite (Setminus_Disjoint (name_in_fundefs B)).
    rewrite IHHadd, Setminus_Setminus_Same_set. 
    rewrite Setminus_Disjoint, Union_assoc...
    now eauto with typeclass_instances.
    apply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    eassumption.
    eapply Disjoint_Included; [| | now apply HD ]...
    eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.
    eapply Disjoint_Singleton_r. eassumption.
    now eauto with Ensembles_DB.
  - simpl. rewrite Union_Empty_set_neut_r, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r...
Qed.

Lemma Add_functions_Funs_Included B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Included _ (Funs ζ') (Union _ (Funs ζ) (name_in_fundefs B)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply Funs_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r...
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_Funs_Same_set B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Same_set _ (Funs ζ') (Union _ (Funs ζ) (name_in_fundefs B)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - unfold Funs. rewrite lifted_name_extend, domain_extend_is_Some_Same_set, IHHadd.
    simpl. unfold Funs...
  - rewrite Union_Empty_set_neut_r...
Qed.

Lemma Add_functions_LiftedFuns_Included_l B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (Funs ζ) (name_in_fundefs B) ->
  Included _ (LiftedFuns ζ)  (LiftedFuns ζ').
Proof with now eauto  with Ensembles_DB.
  intros Hadd Hun HD. unfold LiftedFuns.
  rewrite Add_functions_Funs_Same_set with (ζ' := ζ'); eauto.
  rewrite Add_functions_lifted_name_Same_set; eauto.
  now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_FunsFVs_Included_r B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Included _ (FunsFVs ζ') (Union _ (FunsFVs ζ) (FromList fvs)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply FunsFVs_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r...
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_FunsFVs_Included_l B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (Funs ζ) (name_in_fundefs B) ->
  Included _ (FunsFVs ζ) (FunsFVs ζ').
Proof with now eauto with Ensembles_DB.
  intros Hadd Hun HD. induction Hadd.
  - inv Hun. eapply Included_trans. eapply IHHadd.
    eassumption. now eauto with Ensembles_DB.
    rewrite FunsFVs_extend_Some_eq.
    now eauto with Ensembles_DB.
    intros Hc. 
    eapply Add_functions_Funs_Included in Hc; [| eassumption ].
    inv Hc. eapply HD. constructor; eauto. left; eauto.
    eapply H6. apply name_in_fundefs_bound_var_fundefs. eassumption.
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_σ_eq B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  f_eq_subdomain (Complement _ (Union _ (name_in_fundefs B) (Setminus _ S S'))) σ σ'.
Proof.
  intros Hadd. induction Hadd; simpl.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc; apply Hc.
    eapply Singleton_Included. right. constructor.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc'. inv Hc'. now eauto. now eauto.
    eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc; apply Hc. now eauto.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    now eauto with Ensembles_DB.
  - reflexivity.
Qed.

Lemma Add_functions_lifted_name_Disjoint B fvs σ ζ S σ' ζ' S' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (LiftedFuns ζ) S ->
  Disjoint _ (image (lifted_name ζ') (name_in_fundefs B))
           (image (lifted_name ζ') (Complement _ (name_in_fundefs B))).
Proof.
  intros Hadd Hun HD. induction Hadd; simpl.
  - inv Hun. rewrite image_Union. apply Union_Disjoint_l.
    rewrite image_Singleton.
    rewrite !lifted_name_extend, !extend_gss.
    rewrite image_extend_not_In_S; eauto.
    constructor. intros x Hc. inv Hc. inv H0.
    destruct H1 as [x' [Hin Heq]].
    assert (Hin' : f' \in LiftedFuns ζ').
    now repeat eexists; eauto.
    eapply Add_functions_LiftedFuns_Included_r in Hin'; [| eassumption ].
    inv Hin'. eapply HD.  constructor; eauto.
    eapply Add_functions_free_set_Included; eassumption.
    inv H0; eauto.
    eapply Disjoint_Included; [| | now apply IHHadd ].
    rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
    apply image_monotonic...
    now eauto with Ensembles_DB.
    rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
    reflexivity. intros Hc. eapply H6.
    now eapply name_in_fundefs_bound_var_fundefs.
  - rewrite image_Empty_set. now eauto with Ensembles_DB.
Qed.


Lemma Add_functions_map_eq B fvs σ ζ S σ' ζ' S' l :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Disjoint _ (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S'))->
  map σ l = map σ' l.
Proof.
  intros Hadd HD. induction l; eauto.
  simpl. rewrite FromList_cons in HD.
  erewrite Add_functions_σ_eq; [| eassumption |].
  rewrite IHl. reflexivity.
  now eauto with Ensembles_DB.
  intros Hc. eapply HD. constructor; eauto.
Qed.

Lemma Add_functions_FunsFVs_Included_alt Q B fvs σ ζ S σ' ζ' S' f f' ft fvs' :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Disjoint _ (FunsFVs ζ) Q ->
  ζ' f = Some (f', ft, fvs') ->
  fvs' = fvs \/ Disjoint _ (FromList fvs') Q.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd; intros Hin Heq.
  - destruct (peq f0 f); subst.
    + rewrite extend_gss in Heq.
      inv Heq; eauto.        
    + rewrite extend_gso in Heq; eauto.
  - right. eapply Disjoint_Included_l; [| eassumption ].
    repeat eexists; eauto.
Qed.

(* Lemma Add_functions_injective_subdomain P B fvs σ ζ S σ' ζ' S'  : *)
(*   Add_functions B fvs σ ζ S σ' ζ' S' -> *)
(*   unique_bindings_fundefs B -> *)
(*   injective_subdomain (Setminus _ P (name_in_fundefs B)) σ -> *)
(*   Disjoint _ (image σ (Setminus _ P (name_in_fundefs B))) (name_in_fundefs B) -> *)
(*   injective_subdomain P σ'. *)
(* Proof with now eauto with Ensembles_DB. *)
(*   intros Hadd. revert P; induction Hadd; intros P Hun Hinj HD. *)
(*   - inv Hun. eapply injective_subdomain_extend'. *)
(*     eapply IHHadd. eassumption. now rewrite Setminus_Union. *)
(*     rewrite Setminus_Union... *)
(*     intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ]. *)
(*     inv Hc. eapply HD. *)
(*     constructor; eauto. rewrite Setminus_Union in H0; eassumption. *)
(*     left; eauto. *)
(*     eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption. *)
(*   - simpl in Hinj. now rewrite Setminus_Empty_set_neut_r in Hinj. *)
(* Qed. *)

Lemma Add_functions_image_LiftedFuns_Included B fvs σ ζ S σ' ζ' S' x f :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  lifted_name ζ' x = Some f ->
  x \in name_in_fundefs B  ->
  f \in S /\ ~ f \in S'.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd; intros Heq Hin.
  - destruct (peq f0 x); subst.
    + rewrite lifted_name_extend, extend_gss in Heq. inv Heq.
      split.
      eapply Add_functions_free_set_Included; eassumption.
      intros Hc. inv Hc; eauto.
    + rewrite lifted_name_extend, extend_gso in Heq; eauto.
      inv Hin. inv H0; congruence.
      eapply IHHadd in Heq; eauto. inv Heq.
      split; eauto. intros Hc. inv Hc. eauto.
  - inv Hin.
Qed.

Lemma Add_functions_injective_subdomain_LiftedFuns B fvs σ ζ S σ' ζ' S'  :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  injective_subdomain (name_in_fundefs B) (lifted_name ζ').
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - simpl. rewrite lifted_name_extend. eapply injective_subdomain_extend.
    eassumption.
    intros [x [Hin Heq]]; subst. inv Hin.
    eapply Add_functions_image_LiftedFuns_Included in Hadd; try eassumption.
    inv Hadd; eauto.
  - eapply injective_subdomain_Empty_set.
Qed.

Lemma Add_functions_map_Disjoint B fvs f g S f' g' S' l :
  Add_functions B fvs f g S f' g' S' ->
  Disjoint positive (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S')) ->
  map f' l = map f l.
Proof with now eauto with Ensembles_DB.
  intros Hadd HD. induction Hadd.
  - rewrite !map_extend_not_In. eapply IHHadd...
    intros Hc. eapply HD; eauto.
    constructor; eauto. left. left; eauto.
    intros Hc. eapply HD; eauto.
    constructor; eauto. right. constructor; eauto.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc'; inv Hc'; eauto.
  - reflexivity.
Qed.

Lemma Add_functions_is_Some B fvs σ ζ S σ' ζ' S' f :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  f \in name_in_fundefs B -> 
        exists f' ft',  ζ' f = Some (f', ft', fvs) /\ f' \in (S \\ S').
Proof.
  intros Hadd Hin; induction Hadd.
  - destruct (peq f f0); subst.
    + do 2 eexists. rewrite extend_gss. split. reflexivity.
      constructor. eapply Add_functions_free_set_Included; eassumption. 
      intros Hc; inv Hc. eauto.
    + inv Hin. inv H0; contradiction.
      rewrite extend_gso; eauto.
      edestruct IHHadd as (f'' & ft'' & Heq & Hin). eassumption.
      do 2 eexists. split. eassumption. inv Hin.
      constructor; eauto. intros Hc; inv Hc; eauto. 
  - inv Hin.
Qed. 

Lemma Add_functions_lifted_name_Disjoint_Same_set B fvs σ ζ S σ' ζ' S' Q :
  Disjoint _ Q (Union _ S (name_in_fundefs B)) ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  image' (lifted_name ζ') Q <--> image' (lifted_name ζ) Q.
Proof with now eauto with Ensembles_DB.
  intros HD Hadd. induction Hadd.
  - rewrite lifted_name_extend. rewrite image'_extend_is_Some_not_In_P.
    eapply IHHadd. simpl in *...
    intros Hc. eapply HD. constructor; eauto.
    right; left; eauto.
  - reflexivity.
Qed.

Lemma Add_functions_image_LiftedFuns_Same_set B fvs σ ζ S σ' ζ' S' :
  Disjoint _ S (name_in_fundefs B) ->
  unique_bindings_fundefs B ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  image σ' (S \\ S') <--> (S \\ S').
Proof with now eauto with Ensembles_DB.
  intros HD Hun Hadd. induction Hadd; simpl.
  - inv Hun.
    rewrite image_extend_In_S, image_extend_not_In_S, !Setminus_Setminus_Same_set,
    !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
    rewrite !(Setminus_Disjoint (Setminus var S S')).
    rewrite IHHadd; eauto. reflexivity.
    now eauto with Ensembles_DB.
    eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto.
    now eauto with typeclass_instances.
    eapply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    intros Hc. inv Hc. inv H0.
    eapply HD; constructor; eauto. now left; eauto.
    constructor.
    now eapply Add_functions_free_set_Included; eauto.
    now intros Hc; inv Hc; eauto.
  - rewrite !Setminus_Same_set_Empty_set, image_Empty_set...
Qed.

Lemma Add_functions_image_Disjoint_Same_set B fvs σ ζ S σ' ζ' S' Q :
  Disjoint _ Q (Union _ S (name_in_fundefs B)) ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Same_set _ (image σ' Q) (image σ Q).
Proof with now eauto with Ensembles_DB.
  intros HD Hadd. induction Hadd.
  - rewrite !image_extend_not_In_S.
    eapply IHHadd. simpl in *...
    intros Hc; eapply HD. constructor; eauto.
    now right; left; eauto.
    intros Hc; eapply HD. constructor; eauto.
    left. now eapply Add_functions_free_set_Included; eauto.
  - reflexivity.
Qed.


Lemma Add_functions_image_name_in_fundefs B fvs σ ζ S σ' ζ' S' :
  Disjoint _ (name_in_fundefs B) S ->
  unique_bindings_fundefs B ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  image σ' (name_in_fundefs B) <--> name_in_fundefs B.
Proof with now eauto with Ensembles_DB.
  intros HD Hun Hadd. induction Hadd.
  - rewrite image_extend_not_In_S.
    2:{ intros Hc. eapply HD. constructor. eassumption.
        eapply Add_functions_free_set_Included. eassumption. eassumption. }      
    simpl. rewrite image_extend_In_S; [| sets ]. rewrite Setminus_Union_distr.
    rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite Setminus_Disjoint. rewrite Union_commut. rewrite IHHadd. reflexivity. sets.
    inv Hun. eassumption. inv Hun. eapply Disjoint_Singleton_r.
    intros Hc. eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption.
  - simpl. rewrite image_Empty_set. reflexivity.
Qed.

Lemma Add_functions_image_Same_set B fvs σ ζ S σ' ζ' S' Q :
  Disjoint _ S (name_in_fundefs B) ->
  Disjoint _ Q (name_in_fundefs B) ->
  Disjoint _ (image' (lifted_name ζ) Q) (Union var S (name_in_fundefs B)) ->
  unique_bindings_fundefs B ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Same_set _ (image σ' (image' (lifted_name ζ') (Union _ Q (name_in_fundefs B))))
           (Union _ (Setminus _ S S') (image σ (image' (lifted_name ζ) Q))).
Proof with now eauto with Ensembles_DB.
  intros. rewrite Add_functions_lifted_name_Same_set; eauto.
  rewrite image_Union, Union_commut. apply Same_set_Union_compat.
  rewrite Add_functions_image_LiftedFuns_Same_set...
  rewrite Add_functions_image_Disjoint_Same_set; eauto.
  reflexivity. 
Qed.

Lemma Add_functions_same_name B fvs σ ζ S σ' ζ' S' f :
  f \in (name_in_fundefs B :|: (S \\ S')) ->
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  σ' f = f.
Proof.
  intros Hin Hadd. induction Hadd; eauto.
  - destruct (peq f f'); subst.
    + rewrite extend_gss; eauto.
    + rewrite extend_gso; eauto. destruct (peq f0 f); subst.
      * rewrite extend_gss; eauto.
      * rewrite extend_gso; eauto. eapply IHHadd.
        inv Hin. inv H0. inv H1; congruence. now eauto.
        right. inv H0. constructor; eauto.
        intros Hc. eapply H2. constructor; eauto.
        intros Hc'; inv Hc'; congruence.
  - inv Hin. inv H. rewrite Setminus_Same_set_Empty_set in H. inv H.
Qed.

Lemma Add_functions_name_in_fundefs B1 fvs σ ζ S σ' ζ' S' :
  unique_bindings_fundefs B1 ->
  Add_functions B1 fvs σ ζ S σ' ζ' S' ->
  Same_set _ (image' (lifted_name ζ') (name_in_fundefs B1))
           (Setminus var S S').
Proof with now eauto with Ensembles_DB.
  intros Hun Hadd. induction Hadd; simpl in *.
  - rewrite lifted_name_extend, image'_Union, image'_Singleton_is_Some;
      [| now rewrite extend_gss; eauto ]. inv Hun.
    rewrite image'_extend_is_Some_not_In_P.
    rewrite IHHadd, Setminus_Setminus_Same_set; eauto.
    now eauto with Ensembles_DB.
    now eauto with typeclass_instances.
    eapply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    intros Hc. eapply H6.
    now apply name_in_fundefs_bound_var_fundefs.
  - rewrite image'_Empty_set, Setminus_Same_set_Empty_set... 
Qed.

Lemma Add_functions_σ_eq_alt (B : fundefs) (fvs : list var) (σ : var -> var) (ζ : var -> option (var * fun_tag * list var)) 
      (Q S : Ensemble var) (σ' : var -> var) (ζ' : var -> option (var * fun_tag * list var)) (S' : Ensemble var) :
  Add_functions B fvs σ ζ S σ' ζ' S' ->
  Disjoint _ Q (name_in_fundefs B :|: (S \\ S')) ->
  f_eq_subdomain Q σ σ'.
Proof.
  intros. eapply f_eq_subdomain_antimon; [| eapply Add_functions_σ_eq; eassumption ].
  intros x Hin Hin'. eapply H0; constructor; eauto.
Qed. 


(** * Lemmas about [Make_wrappers] *)

Lemma Make_wrappers_free_set_Included ζ σ B S C S' ζ' :
  Make_wrappers ζ σ B S C S' ζ' ->
  Included _ S' S.
Proof with eauto with Ensembles_DB.
  intros Hmake. induction Hmake...
  - eapply Included_trans; [ eassumption | ]...
Qed.

Lemma Make_wrapper_image Q ζ σ B S C S' σ' :
  Make_wrappers ζ σ B S C S' σ' ->
  Disjoint _ Q (name_in_fundefs B) ->
  image σ Q <--> image σ' Q.
Proof.
  intros Hw Hd. induction Hw.
  - reflexivity.
  - rewrite image_extend_not_In_S. eapply IHHw.
    now sets.
    intros Hc. eapply Hd. constructor. eassumption. now left.
Qed.

Lemma Make_wrappers_f_eq_subdomain Q ζ σ B S C S' σ' :
  Make_wrappers ζ σ B S C S' σ' ->
  Disjoint _ Q (name_in_fundefs B) ->
  f_eq_subdomain Q σ σ'.
Proof.
  intros Hw Hd. induction Hw.
  - reflexivity.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc. eapply Hd. constructor. eassumption. now left.
    eapply IHHw. sets.
Qed.

Lemma Make_wrapper_image_name_in_fundefs ζ σ B S C S' σ' :
  Make_wrappers ζ σ B S C S' σ' ->
  unique_bindings_fundefs B ->
  image σ' (name_in_fundefs B) \subset S \\ S'.
Proof.
  intros Hw Hun. induction Hw.
  - rewrite image_Empty_set, Setminus_Same_set_Empty_set. reflexivity.
  - inv Hun. simpl. rewrite image_Union, image_Singleton.
    eapply Union_Included.
    + rewrite extend_gss. apply Singleton_Included. inv H3. constructor; eauto.
      intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ]. inv Hc. now eauto.
    + rewrite image_extend_not_In_S. eapply Included_trans. eapply IHHw. eassumption.
      now sets. intros Hc. eapply H10. eapply name_in_fundefs_bound_var_fundefs. eassumption.
Qed.

Lemma Make_wrappers_find_def f1 f2 z B S1 fds S2 f ft xs e :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  find_def f B = Some (ft, xs, e) ->
  Disjoint _ (FunsFVs z) (name_in_fundefs B) -> 
  unique_bindings_fundefs B -> 
  exists f' ft' fvs g xs',
    z f = Some (f', ft', fvs) /\
    FromList xs' \subset S1 /\
    g \in S1 \\ FromList xs' /\
          length xs = length xs' /\ NoDup xs' /\            
          f2 f = g /\
          find_def g fds = Some (ft, xs', Eapp f' ft' (xs' ++ map f1 fvs)).
Proof.
  intros Hw Hdef Hd Hun. induction Hw.
  - inv Hdef.
  - simpl in Hdef.
    destruct (M.elt_eq f f0); subst.
    + inv Hdef.
      do 5 eexists. repeat (split; first eassumption).
      split.
      * rewrite extend_gss. reflexivity.
      * simpl. rewrite peq_true. reflexivity.
    + inv Hun. edestruct IHHw as (f'' & ft'' & fvs' & g1 & xs'' & Hzeq & Hsub & Hin & Hleq & Hnd  & Heq & Hf); eauto.
      now sets. 
      do 4 eexists. exists xs''. repeat (split; first eassumption).
      split; [| split; [| split; [| split; [| split ]]]]; try eassumption.
      * eapply Included_trans. eassumption. sets.
      * eapply Included_trans; [| | eapply Hin ]. reflexivity. sets.
      * rewrite extend_gso; eassumption.
      * simpl. rewrite peq_false; eauto. 
        intros Hc. subst. inv Hin. inv H4; eauto.
Qed.


Lemma Make_wrappers_name_in_fundefs z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  name_in_fundefs fds \subset S1 \\ S2.
Proof.
  intros Hw; induction Hw. now sets.
  simpl. eapply Union_Included. eapply Singleton_Included. inv H3; eauto.
  constructor; eauto.
  intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ].
  inv Hc; eauto.
  eapply Included_trans. eapply IHHw. sets.
Qed.

Lemma Make_wrappers_name_in_fundefs_image z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  unique_bindings_fundefs B ->
  name_in_fundefs fds <--> image f2 (name_in_fundefs B).
Proof.
  intros Hw Hun; induction Hw.
  - simpl. rewrite image_Empty_set. reflexivity.
  - simpl. rewrite image_Union, image_Singleton. rewrite extend_gss.
    eapply Same_set_Union_compat. reflexivity.
    inv Hun. rewrite image_extend_not_In_S. eapply IHHw. eassumption.
    intros Hc. eapply H10. eapply name_in_fundefs_bound_var_fundefs. eassumption.
Qed.


Lemma Make_wrappers_image_Included S z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  image f2 S \subset image f1 (S \\ name_in_fundefs B) :|: (S1 \\ S2).
Proof.
  intros Hw; revert S; induction Hw; intros Q.
  - simpl. sets.
  - simpl. eapply Included_trans.
    eapply image_extend_Included'. eapply Union_Included.
    + eapply Included_trans. eapply IHHw.
      eapply Included_Union_compat; [| now sets ].
      now xsets.
    + eapply Included_Union_preserv_r. eapply Singleton_Included. inv H3.
      constructor; eauto. intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ].
      inv Hc. now eauto. 
Qed.


(** * Lemmas about [Exp_lambda_lift] and [Fundefs_lambda_lift] *)

Lemma Fundefs_lambda_lift_name_in_fundefs1 ζ σ B S B' S' :
  Fundefs_lambda_lift1 ζ σ B S B' S' ->
  Included _ (name_in_fundefs B') (Union _ (name_in_fundefs B) (LiftedFuns ζ)).
Proof.
  intros Hadd; induction Hadd; simpl.
  - assert (Heq := lifted_name_eq _ _ _ _ _ H).
    assert (Hin : Included _ (Singleton var f') (LiftedFuns ζ)).
    { eapply Singleton_Included. repeat eexists; eauto. }
    eapply Union_Included.
    now eauto with Ensembles_DB.
    eapply Union_Included. now eauto with Ensembles_DB.
    eapply Included_trans; now eauto with Ensembles_DB.
  - now eauto with Ensembles_DB.
Qed.

Lemma Fundefs_lambda_lift_name_in_fundefs2 ζ σ B0 B S B' S' :
  Fundefs_lambda_lift2 ζ σ B0 B S B' S' ->
  name_in_fundefs B' <--> (image' (lifted_name ζ) (name_in_fundefs B)).
Proof.
  intros Hadd; induction Hadd; simpl.
  - assert (Heq := lifted_name_eq _ _ _ _ _ H).
    rewrite IHHadd. rewrite image'_Union, image'_Singleton_is_Some; eauto.
    reflexivity. 
  - rewrite image'_Empty_set. reflexivity.
Qed.

Lemma Lambda_lift_free_set_Included_mut :
  (forall e ζ σ S e' S',
      Exp_lambda_lift ζ σ e S e' S' ->
      Included _ S' S) /\
  (forall B B0 ζ σ S B' S',
      Fundefs_lambda_lift1 ζ σ B S B' S' \/
      Fundefs_lambda_lift2 ζ σ B0 B S B' S' \/
      Fundefs_lambda_lift3 ζ σ B0 B S B' S' ->
      Included _ S' S).
Proof with now eauto with Ensembles_DB.
  exp_defs_induction IHe IHl IHB; intros; inv H; try inv H0; try now eauto with Ensembles_DB.
  - eapply Included_trans. now eapply IHl; eauto.
    eapply IHe; eauto.
  - eapply Included_trans. now eapply IHe; eauto.
    eapply Included_trans. eapply (IHB f2); eauto.
    eapply Add_functions_free_set_Included; eauto.
  - eapply Included_trans. now eapply IHe; eauto.
    eapply Included_trans. now eapply Make_wrappers_free_set_Included; eauto.
    eapply Included_trans. now eapply IHB; eauto. 
    eapply Add_functions_free_set_Included; eauto.
  - eapply Included_trans. now eapply IHe; eauto.
    eapply (IHB f2); eauto.
  - eapply Included_trans. now eapply (IHB f5); eauto. 
    eapply Included_trans. now eapply IHe; eauto.
    now sets. 
  - inv H. eapply Included_trans. now eapply IHB; eauto.
    eapply Included_trans. now eapply IHe; eauto.
    eapply Included_trans. now eapply Make_wrappers_free_set_Included; eauto.     
    now sets.
  - inv H. eapply Included_trans. now eapply (IHB B0); eauto.
    now eapply IHe; eauto.
  - inv H. reflexivity.
  - inv H. reflexivity.
Qed.

Corollary Exp_Lambda_lift_free_set_Included :
  forall e ζ σ S e' S',
    Exp_lambda_lift ζ σ e S e' S' ->
    Included _ S' S.
Proof.
  destruct Lambda_lift_free_set_Included_mut; eauto.
Qed.

Corollary Fundefs_Lambda_lift_free_set_Included1 :
  forall B ζ σ S B' S',
    Fundefs_lambda_lift1 ζ σ B S B' S' ->
    Included _ S' S.
Proof.
  intros B; intros.
  destruct Lambda_lift_free_set_Included_mut as [_ HB]. eapply HB with (B0 := B); eauto.
Qed.

Corollary Fundefs_Lambda_lift_free_set_Included2 :
  forall B B0 ζ σ S B' S',
    Fundefs_lambda_lift2 ζ σ B0 B S B' S' ->
    Included _ S' S.
Proof.
  destruct Lambda_lift_free_set_Included_mut; eauto.
Qed.

Corollary Fundefs_Lambda_lift_free_set_Included3 :
  forall B B0 ζ σ S B' S',
    Fundefs_lambda_lift3 ζ σ B0 B S B' S' ->
    Included _ S' S.
Proof.
  intros B; intros.
  destruct Lambda_lift_free_set_Included_mut as [_ HB]. eapply HB with (B0 := B0); eauto.
Qed.

Lemma Fundefs_lambda_lift_find_def1 σ ζ S1 B1 S2 B2 f t xs1 e1 f' t' fvs :
  Fundefs_lambda_lift1 ζ σ B1 S1 B2 S2 ->
  ζ f = Some (f', t', fvs) ->
  Disjoint _ (bound_var_fundefs B1) (LiftedFuns ζ) ->
  injective_subdomain (name_in_fundefs B1) (lifted_name ζ) ->
  find_def f B1 = Some (t, xs1, e1) ->
  exists (xs1' ys : list var) (e2 : exp) S2 S2',
    find_def f B2 = Some (t, xs1', (Eapp f' t' (xs1' ++ map σ fvs))) /\
    find_def f' B2 = Some (t', xs1 ++ ys, e2) /\
    NoDup ys /\ NoDup xs1' /\
    length xs1 = length xs1' /\
    length ys = length fvs /\
    Included _ S2 S1 /\
    Included _ (FromList ys) S1 /\
    Included _ (FromList xs1') S1 /\
    Disjoint _ (FromList ys) S2 /\
    Disjoint _ (FromList xs1') S2 /\
    Disjoint _ (FromList xs1') (FromList ys) /\
    Exp_lambda_lift ζ (σ <{ xs1 ++ fvs ~> xs1 ++ ys }>) e1 S2 e2 S2'.
Proof with now eauto with Ensembles_DB.
  intros Hll. induction Hll; intros Heq HD Hinj Hdef.
  - assert (Heq' := lifted_name_eq _ _ _ _ _ Heq).
    simpl in Hdef. destruct (M.elt_eq f f0); subst.
    + rewrite Heq in H; inv H. inv Hdef.
      exists xs', ys, e'. do 2 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]];
        [ | | | | | | | | | | | | eassumption ]; eauto.
      * simpl. rewrite peq_false, peq_true. reflexivity.
        intros Hc. subst. eapply HD. constructor; eauto.
        repeat eexists; eauto.
      * simpl. rewrite peq_true. reflexivity.
      * now eauto with Ensembles_DB.
      * eapply Included_trans; [ eassumption |]...
      * now eauto with Ensembles_DB.
      * now eauto with Ensembles_DB.
      * eapply Disjoint_Included_l; [ eassumption |]...
    + destruct IHHll as (xs1' & ys' & e2 & S2 & S2' & Hf1 & Hf2 & Hnd1 & Hnd2
                         & Heq1 & Heq2 & Hinc1 & Hinc2 & Hinc3 & Hd1 & Hd2 & Hd3 & Hexp).
      eassumption. normalize_bound_var_in_ctx...
      eapply injective_subdomain_antimon. eassumption.
      now eauto with Ensembles_DB. eassumption.
      eexists xs1', ys', e2. do 2 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]];
        [ | | | | | | | | | | | | eassumption ]; eauto.
      * simpl. rewrite peq_false; eauto. rewrite peq_false; now eauto.
        intros Hc. subst. eapply HD. constructor.
        constructor 2. apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
        eassumption. eexists.
        split; repeat eexists; now unfold lifted_name; rewrite H; eauto.
      * simpl. rewrite peq_false; eauto. rewrite peq_false; eauto.
        intros Hc. subst. eapply HD. constructor. now eauto.
        now repeat eexists; eauto.
        intros Hc; subst. eapply n. eapply Hinj.
        constructor 2. eapply fun_in_fundefs_name_in_fundefs.
        eapply find_def_correct. eassumption.
        now simpl; eauto. erewrite !lifted_name_eq; eauto.
      * eapply Included_trans. eassumption.
        eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included.
        eassumption.
        now eauto with Ensembles_DB.
      * eapply Included_trans. eassumption.
        eapply Included_trans.
        eapply Exp_Lambda_lift_free_set_Included; now eauto.
        now eauto with Ensembles_DB.
      * eapply Included_trans. eassumption.
        eapply Included_trans.
        eapply Exp_Lambda_lift_free_set_Included; now eauto.
        now eauto with Ensembles_DB.
  - inv Hdef.
Qed.

Lemma Fundefs_lambda_lift_find_def2 σ ζ S1 B0 B1 S2 B2 f t xs1 e1 f' t' fvs :
  Fundefs_lambda_lift2 ζ σ B0 B1 S1 B2 S2 ->
  ζ f = Some (f', t', fvs) ->
  Disjoint _ (bound_var_fundefs B1) (LiftedFuns ζ) ->
  injective_subdomain (name_in_fundefs B1) (lifted_name ζ) ->
  find_def f B1 = Some (t, xs1, e1) ->
  exists (ys : list var) (e2 : exp) S2 S3 S4 σ' fds,
    find_def f' B2 = Some (t', xs1 ++ ys, Efun fds e2) /\
    NoDup ys /\
    length ys = length fvs /\
    FromList ys \subset S1 /\
    S2 \subset S1 \\ FromList ys /\
    Disjoint _ (FromList ys) S2 /\
    Make_wrappers ζ (σ <{ xs1 ++ fvs ~> xs1 ++ ys }>) B0 S2 fds S3 σ' /\ 
    Exp_lambda_lift ζ σ' e1 S3 e2 S4.
Proof with now eauto with Ensembles_DB.
  intros Hll. induction Hll; intros Heq HD Hinj Hdef.
  - assert (Heq' := lifted_name_eq _ _ _ _ _ Heq).
    simpl in Hdef. destruct (M.elt_eq f f0); subst.
    + rewrite Heq in H; inv H. inv Hdef.
      exists ys, e'. do 5 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split ]]]]]];
        [ | | | | | | eassumption | eassumption ]; eauto. 
      * simpl. rewrite peq_true. reflexivity.
      * sets.
      * sets.
    + destruct IHHll as (ys' & e2 & S2 & S3 & S4 & σ'' & fds' & Hf1 & Hnd1 & Heq1 & Hs1 & Hs2 & Hd1 & Hw & Hexp).
      eassumption. normalize_bound_var_in_ctx...
      eapply injective_subdomain_antimon. eassumption.
      now eauto with Ensembles_DB. eassumption.
      eexists ys', e2. do 5 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split ]]]]]];
        [ | | | | | | eassumption | eassumption ]; eauto.
      * simpl. rewrite peq_false; eauto.
        intros Hc; subst. eapply n. eapply Hinj.
        constructor 2. eapply fun_in_fundefs_name_in_fundefs.
        eapply find_def_correct. eassumption.
        now simpl; eauto. erewrite !lifted_name_eq; eauto.
      * eapply Included_trans. eassumption.
        eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included.
        eassumption. eapply Included_trans.
        eapply Make_wrappers_free_set_Included. eassumption. sets.
      * eapply Included_trans. eassumption.
        eapply Included_Setminus_compat; [| reflexivity ]. 
        eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included. eassumption.
        eapply Included_trans. eapply Make_wrappers_free_set_Included. eassumption. now sets.
  - inv Hdef.
Qed.

Lemma Fundefs_lambda_lift_find_def3 σ ζ S1 B B1 S2 B2 f t xs1 e1 :
  Fundefs_lambda_lift3 ζ σ B B1 S1 B2 S2 ->
  find_def f B1 = Some (t, xs1, e1) ->
  exists (e2 : exp) S1' S2',
    find_def f B2 = Some (t, xs1, e2) /\
    S1' \subset S1 /\
    Exp_lambda_lift ζ ((extend_fundefs σ B B) <{ xs1 ~> xs1 }>) e1 S1' e2 S2'.
Proof with now eauto with Ensembles_DB.
  intros Hll. induction Hll; intros (* Heq HD Hinj *) Hdef.
  - simpl in Hdef. destruct (M.elt_eq f f0); subst.
    + inv Hdef. do 3 eexists. split; [| split ].
      * simpl. rewrite peq_true. reflexivity.
      * reflexivity.
      * sets.
    + simpl. rewrite peq_false; eauto.
      destruct IHHll as (e2 & S1' & S2' & Hf1 & Hsub1 & Hexp).
      eassumption. do 3 eexists; split; [| split ]; [ eassumption | | eassumption ].
      eapply Included_trans. eassumption.
      eapply Exp_Lambda_lift_free_set_Included. eassumption.
  - inv Hdef.
Qed.

Lemma Fundefs_lambda_lift_name_in_fundefs_r B1 B2 σ ζ1 ζ2 S S' :
  Fundefs_lambda_lift1 ζ1 σ B1 S B2 S' ->
  unique_bindings_fundefs B1 ->
  f_eq_subdomain (name_in_fundefs B1) ζ1 ζ2 ->
  name_in_fundefs B2 <--> (name_in_fundefs B1 :|: (image' (lifted_name ζ2) (name_in_fundefs B1))).
Proof with now eauto with Ensembles_DB.
  intros Hfuns Hun Hfeq. induction Hfuns; simpl in *.
  - inv Hun. rewrite IHHfuns; eauto. rewrite image'_Union.
    rewrite !(image'_feq_subdomain (lifted_name ζ2) (lifted_name ζ)).
    rewrite image'_Singleton_is_Some; [| erewrite lifted_name_eq; eauto ]...
    apply lifted_name_f_eq_subdomain. symmetry.
    eapply f_eq_subdomain_antimon; [| eassumption ]...
    apply lifted_name_f_eq_subdomain. symmetry.
    eapply f_eq_subdomain_antimon; [| eassumption ]...
    eapply f_eq_subdomain_antimon; [| eassumption ]...
  - rewrite image'_Empty_set...
Qed.

Corollary Add_functions_Fundefs_lambda_lift_name_in_fundefs
          B1 B2 fvs σ ζ S σ1 σ2 ζ1 ζ2 S' S1 S2 :
  Add_functions B1 fvs σ ζ S σ1 ζ1 S' ->
  Fundefs_lambda_lift1 ζ2 σ2 B1 S1 B2 S2 ->
  f_eq_subdomain (name_in_fundefs B1) ζ1 ζ2 ->
  unique_bindings_fundefs B1 ->
  name_in_fundefs B2 <--> (name_in_fundefs B1) :|: (Setminus var S S').
Proof.
  intros. rewrite Fundefs_lambda_lift_name_in_fundefs_r; eauto.
  rewrite Add_functions_name_in_fundefs; eauto. reflexivity.
  symmetry; eauto.
Qed.

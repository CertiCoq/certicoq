Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.List_util
        L6.functions L6.Ensembles_util.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation PS.
Require Import Libraries.Maps.

Close Scope Z_scope.

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


(** * Computational Defintion *)

Inductive VarInfo : Type :=
(* A variable that is free in the current function definition.
   The first argument is the name of the parameter of the lambda
   lifted function that corresponds to this free variable *)
| FreeVar : var -> VarInfo.

Inductive FunInfo : Type := 
(* A known function. The first argument is the name of the lambda lifted version,
   the second the new fTag and the third the list of free variables of the
   function *)
| Fun : var -> fTag -> list var -> FunInfo.

(* Maps variables to [VarInfo] *)
Definition VarInfoMap := Maps.PTree.t VarInfo.

(* Maps variables to [FunInfo] *)
Definition FunInfoMap := Maps.PTree.t FunInfo.


Record state_contents :=
    mkCont { next_var : var ; next_fTag : fTag }.

Definition state :=
  state state_contents.
  
(** Get a fresh name *)
Definition get_name : state var :=
  p <- get ;;
  let '(mkCont n f) := p in
  put (mkCont ((n+1)%positive) f) ;;
  ret n.

(** Get a list of fresh names *)
Fixpoint get_names (n : nat) : state (list var) :=
  match n with
    | 0 => ret []
    | S n =>
      x <- get_name ;;
      xs <- get_names n ;;
      ret (x :: xs)
  end.

(** Get a fresh function tag *)
Definition get_tag : state fTag :=
  p <- get ;;
  let '(mkCont n f) := p in
  put (mkCont n ((f+1)%positive)) ;;
  ret f.

Definition rename (map : VarInfoMap) (x : var) : var :=
  match M.get x map with
    | Some inf =>
      match inf with
        | FreeVar y => y
      end
    | None => x
  end.

Definition rename_lst (map : VarInfoMap) (xs : list var) : list var :=
  (* all list of variables in the AST are in an escaping positions *)
  List.map (rename map) xs.

Fixpoint add_functions (B : fundefs) (fvs : list var) (m : FunInfoMap)
: state FunInfoMap :=
  match B with
    | Fcons f ft xs _ B =>
      m' <- add_functions B fvs m ;;
      (* new name for lambda lifted definition - this function will always be known *)
      f' <- get_name ;;
      (* new fTag for lambda listed definition *)
      ft' <- get_tag ;;
      ret (M.set f (Fun f' ft' fvs) m')
    | Fnil => ret m
  end.

Fixpoint add_free_vars (fvs : list var) (m : VarInfoMap)
: state (list var * VarInfoMap) :=
  match fvs with
    | [] => ret ([], m)
    | y :: ys =>
      p <- add_free_vars ys m ;; 
      y' <- get_name ;;
      let (ys', m') := p in
      ret (y' :: ys', M.set y (FreeVar y') m')
  end.

(* Fixpoint add_params (ys : list var) (m : VarInfoMap) : VarInfoMap := *)
(*   match ys with *)
(*     | [] => m *)
(*     | y :: ys => *)
(*       M.set y BoundVar (add_params ys m) *)
(*   end. *)

Definition FVMap := Maps.PTree.t PS.t.

Section TrueFV.

  Variable (funmap : FunInfoMap).
  
  (** The set of the *true* free variables of an [exp]. The true free variables
    are the variables that appear free plus the free variables of the known
    functions that are called inside the expression. Relies on the the
    assumption that the free and bound variables are disjoint. *)
  Fixpoint exp_true_fv_aux (e : exp) (scope  : FVSet) (fvset : PS.t) : PS.t :=
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
      | Efun defs e =>
        let '(scope', fvset') := fundefs_true_fv_aux defs scope fvset in 
        exp_true_fv_aux e scope' fvset'
      | Eapp x ft xs =>
        let fvset' := match funmap ! x with
                     | Some inf =>
                        match inf with
                          | Fun f' ft' fvs => union_list fvset (f' :: fvs)
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
  
  Definition exp_true_fv e := exp_true_fv_aux e empty PS.empty.
  
  Definition fundefs_true_fv B := snd (fundefs_true_fv_aux B empty PS.empty). 

End TrueFV.

Fixpoint exp_lambda_lift (e : exp) (fvm : VarInfoMap) (fm : FunInfoMap) : state exp :=
  match e with
  (* We are (too) conservative here and we assume that all variables that are
     being wrapped in a constructor are escaping. *)  
  | Econstr x t ys e => 
    e' <- exp_lambda_lift e fvm fm ;;
    ret (Econstr x t (rename_lst fvm ys) e')
  | Ecase x P =>
    P' <-
    (fix mapM_ll l :=
       match l with
         | [] => ret []
         | (c, e) :: P =>
           e' <- exp_lambda_lift e fvm fm ;;
           P' <- mapM_ll P ;;
           ret ((c, e') :: P')
       end) P ;;
    ret (Ecase (rename fvm x) P')
  | Eproj x t N y e =>
    e' <- exp_lambda_lift e fvm fm ;;
    ret (Eproj x t N (rename fvm y) e')
  | Efun B e =>
    let fvs := PS.elements (fundefs_true_fv fm B) in
    fm' <- add_functions B fvs fm ;;
    B' <- fundefs_lambda_lift B fvm fm' ;;
    e' <- exp_lambda_lift e fvm fm' ;;
    ret (Efun B' e')
  | Eapp f ft xs => 
    match fm ! f with
      | Some inf =>
        match inf with
          | Fun f' ft' fvs =>
            ret (Eapp (rename fvm f') ft' (rename_lst fvm (xs ++ fvs)))
        end
      | None =>
        ret (Eapp (rename fvm f) ft (rename_lst fvm xs))
    end
  | Eprim x f ys e =>
    e' <- exp_lambda_lift e fvm fm ;;
    ret (Eprim x f (rename_lst fvm ys) e')
  | Ehalt x => ret (Ehalt (rename fvm x))
  end
with fundefs_lambda_lift B fvm fm :=
       match B with
         | Fcons f ft xs e B => 
           match M.get f fm with
             | Some inf =>
               match inf with
                 | Fun f' ft' fvs =>
                   p <- add_free_vars fvs fvm ;;
                   let (ys, fvm') := p in
                   xs' <- get_names (length xs) ;;
                   e' <- exp_lambda_lift e fvm' fm ;;
                   B' <- fundefs_lambda_lift B fvm fm ;;
                   ret (Fcons f' ft' (xs ++ ys) e'
                              (Fcons f ft xs'
                                     (Eapp f' ft' (xs' ++ (rename_lst fvm fvs)))
                                     B'))
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
       let g' y x' z'' = y + x' + z''
       and g y = g y x z'
       in g' 3 x z' + 3
   and f x = f' x z

 *)


(** * Relational Defintion *)

Inductive Add_functions :
  fundefs ->
  list var ->
  (var -> var) ->
  (var -> option (var * fTag * list var)) ->
  Ensemble var ->
  (var -> var) ->
  (var -> option (var * fTag * list var)) ->
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
Definition lifted_name (ζ : var -> option (var * fTag * list var)) : var -> option var :=
  fun f => (liftM (fun x => (fst (fst x)))) (ζ f).

(* Map from the original name to the list of free vars *)
Definition free_vars (ζ : var -> option (var * fTag * list var)) : var -> option (list var) :=
  fun f => (liftM (fun x => snd x)) (ζ f).

(** The domain of ζ *)
Definition Funs (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
  domain (lifted_name ζ).

(** The image of ζ on its domain - i.e. the names of the lifted functions *)
Definition LiftedFuns (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
  image' (lifted_name ζ) (Funs ζ).

(**  The free variables of functions in ζ, alternative definition *)
Definition FunsFVsLst (ζ : var -> option (var * fTag * list var)) : Ensemble (list var) :=
  fun fvs => exists f f' ft', ζ f = Some (f', ft', fvs).

(**  The free variables of functions in ζ *)
Definition FunsFVs (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
  fun v => exists f f' ft' fvs, ζ f = Some (f', ft', fvs) /\
                        Ensembles.In _ (FromList fvs) v.

Inductive Exp_lambda_lift :
  (var -> option (var * fTag * list var)) ->
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
      ζ f = None -> 
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp (σ f) ft (map σ xs)) S
| LL_Eprim :
    forall ζ σ x f ys e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eprim x f ys e) S (Eprim x f (map σ ys) e') S'
| LL_Ehalt :
    forall ζ σ x S,
      Exp_lambda_lift ζ σ (Ehalt x) S (Ehalt (σ x)) S
with Fundefs_lambda_lift :
  (var -> option (var * fTag * list var)) ->
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

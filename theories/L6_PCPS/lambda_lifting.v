Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.List_util
        L6.functions L6.Ensembles_util.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
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

    A better idea would be  to turn it into

    let f_1' x_1 fvs = [e_1]
    and f_1 x_1 = [e1]
        ....
    and f_n' x_n fvs = [e_n]
    and f_n x_n = [e_n]
    in [e]

    or even

    let f_1 x_1 = [e1]
        ....
    and f_n x_n = [e_n]
    in 
    let f_1' x_1 fvs = [e_1]
        ....
    and f_n' x_n fvs = [e_n]
    in [e]


    and then use f_i and f_i' as above. This way we will avoid an extra
    function call an more importantly after closure conversion we will
    not have to project all the values from the record (even those that
    will not be needed).
**)


(** * Computational Defintion *)

Inductive VarInfo : Type :=
(* A variable bound in the current scope *)
| BoundVar : VarInfo
(* A variable that is free in the current function definition.
   The first argument is the name of the parameter of the lambda
   lifted function that corresponds to this free variable *)
| FreeVar : var -> VarInfo
(* A function. The first argument is the name of the lambda lifted version,
   the second the new fTag and the third the list of free variables of the
   function *)
| Fun : var -> fTag -> list var -> VarInfo.

(* Maps variables to [VarInfo] *)
Definition VarInfoMap := Maps.PTree.t VarInfo.

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
        | BoundVar | Fun _ _ _ => x
        | FreeVar y => y
      end
    | None => x
  end.

Definition rename_lst (map : VarInfoMap) (xs : list var) : list var :=
  (* all list of variables in the AST are in an escaping positions *)
  List.map (rename map) xs.

Fixpoint add_functions (B : fundefs) (fvs : list var) (m : VarInfoMap)
: state VarInfoMap :=
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

Fixpoint add_params (ys : list var) (m : VarInfoMap) : VarInfoMap :=
  match ys with
    | [] => m
    | y :: ys =>
      M.set y BoundVar (add_params ys m)
  end.


Fixpoint exp_lambda_lift (e : exp) (m : VarInfoMap) : state exp :=
  match e with
  (* We are (too) conservative here and we assume that all variables that are
     being wrapped in a constructor are escaping. *)  
  | Econstr x t ys e =>
    e' <- exp_lambda_lift e (M.set x BoundVar m) ;;
    ret (Econstr x t (rename_lst m ys) e')
  | Ecase x P =>
    P' <-
    (fix mapM_ll l :=
       match l with
         | [] => ret []
         | (c, e) :: P =>
           e' <- exp_lambda_lift e m ;;
           P' <- mapM_ll P ;;
           ret ((c, e') :: P')
       end) P ;;
    ret (Ecase (rename m x) P')
  | Eproj x t N y e =>
    e' <- exp_lambda_lift e (M.set x BoundVar m) ;;
    ret (Eproj x t N (rename m y) e')
  | Efun B e =>
    let fvs := PS.elements (fundefs_fv B (fundefs_names B)) in
    m' <- add_functions B fvs m ;;
    B' <- fundefs_lambda_lift B m' ;;
    e' <- exp_lambda_lift e m' ;;
    ret (Efun B' e')
  | Eapp f ft xs =>
    match M.get f m with
      | Some inf =>
        match inf with
          | BoundVar =>
            ret (Eapp f ft (rename_lst m xs))
          | FreeVar f' =>
            ret (Eapp f' ft (rename_lst m xs))
          | Fun f' ft' fvs =>
            ret (Eapp f' ft' (rename_lst m (xs ++ fvs)))
        end
      | None =>
        ret (Eapp f ft (rename_lst m xs))
    end
  | Eprim x f ys e =>
    e' <- exp_lambda_lift e (M.set x BoundVar m) ;;
       ret (Eprim x f (rename_lst m ys) e')
  | Ehalt x => ret (Ehalt (rename m x))
  end
with fundefs_lambda_lift B m :=
       match B with
         | Fcons f ft xs e B =>
           match M.get f m with
             | Some inf =>
               match inf with
                 | Fun f' ft' fvs =>
                   p <- add_free_vars fvs (add_params xs m) ;;
                   let (ys, m') := p in
                   xs' <- get_names (length xs) ;;
                   e' <- exp_lambda_lift e m' ;;
                   B' <- fundefs_lambda_lift B m ;;
                   ret (Fcons f' ft' (xs ++ ys) e
                              (Fcons f ft xs'
                                     (Eapp f' ft' (xs' ++ (rename_lst m fvs)))
                                     B'))
                 | _ => ret (Fcons f ft xs e B) (* should never match *)
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
      In _ S' f' ->
      Add_functions (Fcons f ft xs e B) fvs σ ζ S
                    (σ' {f ~> f}) (ζ' {f ~> Some (f', ft', fvs)})
                    (Setminus _ S' (Singleton _ f'))
| Add_Fnil :
    forall fvs σ ζ S,
      Add_functions Fnil fvs σ ζ S σ ζ S.

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
      Included _ (FromList fvs) (occurs_free_fundefs B) ->
      NoDup fvs ->
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Fundefs_lambda_lift ζ' σ' B S' B' S'' ->
      Exp_lambda_lift ζ' σ' e S'' e' S''' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S'''
| LL_Eapp_known :
    forall ζ σ f ft xs f' ft' fvs S,
      ζ f = Some (f', ft', fvs) -> 
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp f' ft' (map σ (xs ++ fvs))) S
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


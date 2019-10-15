open BinNat
open Datatypes
open List0
open Maps
open Monad0
open StateMonad
open Cps
open Ctx
open Identifiers
open Set_util
open State

let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_VarInfo =
| FreeVar of var
| WrapperFun of var

type coq_VarInfoMap = coq_VarInfo PTree.t

type 't lambdaM = (unit, 't) compM

(** val rename : coq_VarInfoMap -> var -> var **)

let rename map0 x =
  match M.get x map0 with
  | Some inf -> (match inf with
                 | FreeVar y -> y
                 | WrapperFun y -> y)
  | None -> x

(** val rename_lst : coq_VarInfoMap -> var list -> var list **)

let rename_lst map0 xs =
  map (rename map0) xs

(** val add_free_vars :
    var list -> coq_VarInfoMap -> (var list * coq_VarInfoMap) lambdaM **)

let rec add_free_vars fvs m =
  match fvs with
  | [] -> ret (Obj.magic coq_Monad_state) ([], m)
  | y :: ys ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (add_free_vars ys m) (fun p ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_name y []) (fun y' ->
        let (ys', m') = p in
        ret (Obj.magic coq_Monad_state) ((y' :: ys'),
          (M.set y (FreeVar y') m'))))

type coq_FunInfo' =
| Fun' of var * fTag * var list * PS.t

type coq_FunInfoMap' = coq_FunInfo' PTree.t

type coq_GFunInfo = var
  (* singleton inductive, whose constructor was GFun *)

type coq_GFunMap = coq_GFunInfo M.t

(** val add_functions' :
    fundefs -> var list -> PS.t -> coq_FunInfoMap' -> coq_GFunMap -> bool ->
    (coq_FunInfoMap' * coq_GFunMap) lambdaM **)

let rec add_functions' b fvs sfvs m gfuns is_closed =
  match b with
  | Fcons (f, _, xs, _, b0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (add_functions' b0 fvs sfvs m gfuns is_closed) (fun maps ->
      let (m', gfuns') = maps in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_name f
          ('_'::('l'::('i'::('f'::('t'::('e'::('d'::[])))))))) (fun f' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic get_ftag (N.of_nat (length xs))) (fun ft' ->
          let gfuns'' = if is_closed then M.set f f' gfuns' else gfuns' in
          ret (Obj.magic coq_Monad_state)
            ((M.set f (Fun' (f', ft', fvs, sfvs)) m'), gfuns''))))
  | Fnil -> ret (Obj.magic coq_Monad_state) (m, gfuns)

(** val make_wrappers :
    fundefs -> coq_VarInfoMap -> coq_FunInfoMap' ->
    (exp_ctx * coq_VarInfoMap) lambdaM **)

let rec make_wrappers b fvm fm =
  match b with
  | Fcons (f, ft, xs, _, b0) ->
    (match M.get f fm with
     | Some inf ->
       let Fun' (f', ft', fvs, _) = inf in
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (Obj.magic get_name f
           ('_'::('w'::('r'::('a'::('p'::('p'::('e'::('r'::[])))))))))
         (fun g ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (Obj.magic get_names_lst xs []) (fun xs' ->
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (make_wrappers b0 fvm fm) (fun cm ->
             let (c, fvm') = cm in
             let fvm'' = M.set f (WrapperFun g) fvm' in
             ret (Obj.magic coq_Monad_state) ((Efun1_c ((Fcons (g, ft, xs',
               (Eapp (f', ft', (app xs' (rename_lst fvm fvs)))), Fnil)), c)),
               fvm''))))
     | None -> ret (Obj.magic coq_Monad_state) (Hole_c, fvm))
  | Fnil -> ret (Obj.magic coq_Monad_state) (Hole_c, fvm)

(** val exp_lambda_lift' :
    exp -> PS.t -> coq_VarInfoMap -> coq_FunInfoMap' -> coq_GFunMap -> exp
    lambdaM **)

let rec exp_lambda_lift' e curr_fvs fvm fm gfuns =
  match e with
  | Econstr (x, t0, ys, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (exp_lambda_lift' e0 curr_fvs fvm fm gfuns) (fun e' ->
      ret (Obj.magic coq_Monad_state) (Econstr (x, t0, (rename_lst fvm ys),
        e')))
  | Ecase (x, p) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (let rec mapM_ll = function
       | [] -> ret (Obj.magic coq_Monad_state) []
       | y :: p0 ->
         let (c, e0) = y in
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (exp_lambda_lift' e0 curr_fvs fvm fm gfuns) (fun e' ->
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (mapM_ll p0) (fun p' ->
             ret (Obj.magic coq_Monad_state) ((c, e') :: p')))
       in mapM_ll p) (fun p' ->
      ret (Obj.magic coq_Monad_state) (Ecase ((rename fvm x), p')))
  | Eproj (x, t0, n, y, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (exp_lambda_lift' e0 curr_fvs fvm fm gfuns) (fun e' ->
      ret (Obj.magic coq_Monad_state) (Eproj (x, t0, n, (rename fvm y), e')))
  | Efun (b, e0) ->
    let sfvs = fundefs_fv b in
    let fvs =
      filter (fun x ->
        match M.get x gfuns with
        | Some _ -> false
        | None -> true) (PS.elements sfvs)
    in
    let is_closed = match fvs with
                    | [] -> true
                    | _ :: _ -> false in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic add_functions' b fvs sfvs fm gfuns is_closed) (fun maps' ->
      let (fm', gfuns') = maps' in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic fundefs_lambda_lift' b b fvm fm' gfuns') (fun b' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic make_wrappers b fvm fm') (fun cm ->
          let (c, fvm') = cm in
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (exp_lambda_lift' e0 curr_fvs fvm' fm' gfuns') (fun e' ->
            ret (Obj.magic coq_Monad_state) (Efun (b', (app_ctx_f c e')))))))
  | Eapp (f, ft, xs) ->
    (match PTree.get f fm with
     | Some inf ->
       let Fun' (f', ft', fvs, sfvs) = inf in
       if PS.subset sfvs curr_fvs
       then ret (Obj.magic coq_Monad_state) (Eapp ((rename fvm f'), ft',
              (rename_lst fvm (app xs fvs))))
       else ret (Obj.magic coq_Monad_state) (Eapp ((rename fvm f), ft,
              (rename_lst fvm xs)))
     | None ->
       ret (Obj.magic coq_Monad_state) (Eapp ((rename fvm f), ft,
         (rename_lst fvm xs))))
  | Eprim (x, f, ys, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (exp_lambda_lift' e0 curr_fvs fvm fm gfuns) (fun e' ->
      ret (Obj.magic coq_Monad_state) (Eprim (x, f, (rename_lst fvm ys), e')))
  | Ehalt x -> ret (Obj.magic coq_Monad_state) (Ehalt (rename fvm x))

(** val fundefs_lambda_lift' :
    fundefs -> fundefs -> coq_VarInfoMap -> coq_FunInfoMap' -> coq_GFunMap ->
    fundefs lambdaM **)

and fundefs_lambda_lift' b bfull fvm fm gfuns =
  match b with
  | Fcons (f, ft, xs, e, b0) ->
    (match M.get f fm with
     | Some inf ->
       let Fun' (f', ft', fvs, sfvs) = inf in
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (Obj.magic add_free_vars fvs fvm) (fun p ->
         let (ys, fvm') = p in
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (Obj.magic make_wrappers bfull fvm' fm) (fun cm ->
           let (c, fvm'') = cm in
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __)
             (Obj.magic exp_lambda_lift' e sfvs fvm'' fm gfuns) (fun e' ->
             pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
               (Obj.magic __) (fundefs_lambda_lift' b0 bfull fvm fm gfuns)
               (fun b' ->
               ret (Obj.magic coq_Monad_state) (Fcons (f', ft', (app xs ys),
                 (app_ctx_f c e'), b'))))))
     | None -> ret (Obj.magic coq_Monad_state) (Fcons (f, ft, xs, e, b0)))
  | Fnil -> ret (Obj.magic coq_Monad_state) Fnil

(** val lambda_lift' : exp -> comp_data -> exp * comp_data **)

let lambda_lift' e c =
  let (e', p) =
    run_compM (exp_lambda_lift' e PS.empty PTree.empty PTree.empty M.empty) c
      ()
  in
  let (c', _) = p in (e', c')

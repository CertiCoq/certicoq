open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICChecker
open PCUICLiftSubst
open Monad_utils
open Univ0
open Utils

(** val type_of_as_sort :
    coq_Fuel -> global_context -> (context -> term -> term typing_result) ->
    context -> term -> universe typing_result **)

let type_of_as_sort f _UU03a3_ type_of0 _UU0393_ t =
  bind (Obj.magic typing_monad) (Obj.magic type_of0 _UU0393_ t) (fun tx ->
    reduce_to_sort f (fst _UU03a3_) _UU0393_ tx)

(** val type_of :
    coq_Fuel -> global_context -> context -> term -> term typing_result **)

let rec type_of f _UU03a3_ _UU0393_ = function
| Coq_tRel n ->
  (match nth_error _UU0393_ n with
   | Some d -> ret (Obj.magic typing_monad) (lift (S n) O d.decl_type)
   | None -> raise (Obj.magic monad_exc) (UnboundRel n))
| Coq_tVar n -> raise (Obj.magic monad_exc) (UnboundVar n)
| Coq_tMeta n -> raise (Obj.magic monad_exc) (UnboundMeta n)
| Coq_tEvar (ev, _) -> raise (Obj.magic monad_exc) (UnboundEvar ev)
| Coq_tSort s -> ret (Obj.magic typing_monad) (Coq_tSort (try_suc s))
| Coq_tProd (n, t0, b) ->
  bind (Obj.magic typing_monad)
    (Obj.magic type_of_as_sort f _UU03a3_ (type_of f _UU03a3_) _UU0393_ t0)
    (fun s1 ->
    bind (Obj.magic typing_monad)
      (Obj.magic type_of_as_sort f _UU03a3_ (type_of f _UU03a3_)
        (snoc _UU0393_ (vass n t0)) b) (fun s2 ->
      ret (Obj.magic typing_monad) (Coq_tSort
        (Universe.sort_of_product s1 s2))))
| Coq_tLambda (n, t0, b) ->
  bind (Obj.magic typing_monad)
    (type_of f _UU03a3_ (snoc _UU0393_ (vass n t0)) b) (fun t2 ->
    ret (Obj.magic typing_monad) (Coq_tProd (n, t0, t2)))
| Coq_tLetIn (n, b, b_ty, b') ->
  bind (Obj.magic typing_monad)
    (type_of f _UU03a3_ (snoc _UU0393_ (vdef n b b_ty)) b') (fun b'_ty ->
    ret (Obj.magic typing_monad) (Coq_tLetIn (n, b, b_ty, b'_ty)))
| Coq_tApp (t0, a) ->
  bind (Obj.magic typing_monad) (type_of f _UU03a3_ _UU0393_ t0) (fun ty ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_prod f (fst _UU03a3_) _UU0393_ ty) (fun pi ->
      let (_, b1) = pi in ret (Obj.magic typing_monad) (subst1 a O b1)))
| Coq_tConst (cst, u) -> lookup_constant_type _UU03a3_ cst u
| Coq_tInd (i0, u) ->
  let { inductive_mind = ind; inductive_ind = i } = i0 in
  lookup_ind_type _UU03a3_ ind i u
| Coq_tConstruct (i0, k, u) ->
  let { inductive_mind = ind; inductive_ind = i } = i0 in
  lookup_constructor_type _UU03a3_ ind i k u
| Coq_tCase (p0, p, c, _) ->
  let (_, par) = p0 in
  bind (Obj.magic typing_monad) (type_of f _UU03a3_ _UU0393_ c) (fun ty ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_ind f (fst _UU03a3_) _UU0393_ ty) (fun indargs ->
      let (_, args) = indargs in
      ret (Obj.magic typing_monad) (mkApps p (app (skipn par args) (c :: [])))))
| Coq_tProj (_, c) ->
  bind (Obj.magic typing_monad) (type_of f _UU03a3_ _UU0393_ c) (fun ty ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_ind f (fst _UU03a3_) _UU0393_ ty) (fun _ ->
      ret (Obj.magic typing_monad) ty))
| Coq_tFix (mfix, n) ->
  (match nth_error mfix n with
   | Some f0 -> ret (Obj.magic typing_monad) f0.dtype
   | None -> raise (Obj.magic monad_exc) (IllFormedFix (mfix, n)))
| Coq_tCoFix (mfix, n) ->
  (match nth_error mfix n with
   | Some f0 -> ret (Obj.magic typing_monad) f0.dtype
   | None -> raise (Obj.magic monad_exc) (IllFormedFix (mfix, n)))

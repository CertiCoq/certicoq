open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICTyping
open PCUICUnivSubst
open Monad_utils
open Univ0
open Utils

type __ = Obj.t

module RedFlags =
 struct
  type t = { beta : bool; iota : bool; zeta : bool; delta : bool;
             fix_ : bool; cofix_ : bool }

  (** val beta : t -> bool **)

  let beta x = x.beta

  (** val iota : t -> bool **)

  let iota x = x.iota

  (** val zeta : t -> bool **)

  let zeta x = x.zeta

  (** val delta : t -> bool **)

  let delta x = x.delta

  (** val fix_ : t -> bool **)

  let fix_ x = x.fix_

  (** val default : t **)

  let default =
    { beta = true; iota = true; zeta = true; delta = true; fix_ = true;
      cofix_ = true }
 end

(** val zip : (term * term list) -> term **)

let zip t0 =
  mkApps (fst t0) (snd t0)

(** val reduce_stack :
    RedFlags.t -> global_declarations -> context -> nat -> term -> term list
    -> (term * term list) option **)

let rec reduce_stack flags _UU03a3_ _UU0393_ n t0 stack =
  match n with
  | O -> None
  | S n0 ->
    (match t0 with
     | Coq_tRel c ->
       if flags.RedFlags.zeta
       then bind (Obj.magic option_monad) (nth_error (Obj.magic _UU0393_) c)
              (fun d ->
              match d.decl_body with
              | Some b ->
                reduce_stack flags _UU03a3_ _UU0393_ n0 (lift (S c) O b) stack
              | None -> ret (Obj.magic option_monad) (t0, stack))
       else ret (Obj.magic option_monad) (t0, stack)
     | Coq_tLambda (_, _, b) ->
       if flags.RedFlags.beta
       then (match stack with
             | [] -> ret (Obj.magic option_monad) (t0, stack)
             | a :: args' ->
               reduce_stack flags _UU03a3_ _UU0393_ n0 (subst1 a O b) args')
       else ret (Obj.magic option_monad) (t0, stack)
     | Coq_tLetIn (_, b, _, c) ->
       if flags.RedFlags.zeta
       then reduce_stack flags _UU03a3_ _UU0393_ n0 (subst1 b O c) stack
       else ret (Obj.magic option_monad) (t0, stack)
     | Coq_tApp (f, a) ->
       reduce_stack flags _UU03a3_ _UU0393_ n0 f (a :: stack)
     | Coq_tConst (c, u) ->
       if flags.RedFlags.delta
       then (match lookup_env _UU03a3_ c with
             | Some g ->
               (match g with
                | ConstantDecl (_, c0) ->
                  let { cst_type = _; cst_body = cst_body0; cst_universes =
                    _ } = c0
                  in
                  (match cst_body0 with
                   | Some body ->
                     let body' = subst_instance_constr u body in
                     reduce_stack flags _UU03a3_ _UU0393_ n0 body' stack
                   | None -> ret (Obj.magic option_monad) (t0, stack))
                | InductiveDecl (_, _) ->
                  ret (Obj.magic option_monad) (t0, stack))
             | None -> ret (Obj.magic option_monad) (t0, stack))
       else ret (Obj.magic option_monad) (t0, stack)
     | Coq_tCase (p0, p, c, brs) ->
       let (ind, par) = p0 in
       if flags.RedFlags.iota
       then bind (Obj.magic option_monad)
              (reduce_stack flags _UU03a3_ _UU0393_ n0 c []) (fun c' ->
              let (y, args) = c' in
              (match y with
               | Coq_tConstruct (_, c0, _) ->
                 reduce_stack flags _UU03a3_ _UU0393_ n0
                   (iota_red par c0 args brs) stack
               | _ ->
                 ret (Obj.magic option_monad) ((Coq_tCase ((ind, par), p,
                   (zip c'), brs)), stack)))
       else ret (Obj.magic option_monad) (t0, stack)
     | Coq_tFix (mfix, idx) ->
       if flags.RedFlags.fix_
       then bind (Obj.magic option_monad) (Obj.magic unfold_fix mfix idx)
              (fun nf ->
              let (narg, fn) = nf in
              (match nth_error stack narg with
               | Some c ->
                 bind (Obj.magic option_monad)
                   (reduce_stack flags _UU03a3_ _UU0393_ n0 c []) (fun c' ->
                   match fst c' with
                   | Coq_tConstruct (_, _, _) ->
                     reduce_stack flags _UU03a3_ _UU0393_ n0 fn stack
                   | _ -> ret (Obj.magic option_monad) (t0, stack))
               | None -> ret (Obj.magic option_monad) (t0, stack)))
       else ret (Obj.magic option_monad) (t0, stack)
     | _ -> ret (Obj.magic option_monad) (t0, stack))

(** val fix_decls : term mfixpoint -> context_decl list **)

let fix_decls l =
  let rec aux acc = function
  | [] -> acc
  | d :: ds0 -> aux ((vass d.dname d.dtype) :: acc) ds0
  in aux [] l

(** val lookup_env : global_context -> ident -> global_decl option **)

let lookup_env _UU03a3_ c =
  lookup_env (fst _UU03a3_) c

type type_error =
| UnboundRel of nat
| UnboundVar of char list
| UnboundMeta of nat
| UnboundEvar of nat
| UndeclaredConstant of char list
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotConvertible of context * term * term * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| NotEnoughFuel of nat

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

(** val typing_monad : __ typing_result coq_Monad **)

let typing_monad =
  { ret = (fun _ a -> Checked a); bind = (fun _ _ m f ->
    match m with
    | Checked a -> f a
    | TypeError t0 -> TypeError t0) }

(** val monad_exc : (type_error, __ typing_result) coq_MonadExc **)

let monad_exc =
  { raise = (fun _ e -> TypeError e); catch = (fun _ m f ->
    match m with
    | Checked _ -> m
    | TypeError t0 -> f t0) }

(** val hnf_stack :
    coq_Fuel -> global_declarations -> context -> term -> (term * term list)
    typing_result **)

let hnf_stack f _UU03a3_ _UU0393_ t0 =
  match reduce_stack RedFlags.default _UU03a3_ _UU0393_ (fuel f) t0 [] with
  | Some t' -> ret (Obj.magic typing_monad) t'
  | None -> raise (Obj.magic monad_exc) (NotEnoughFuel (fuel f))

(** val reduce_to_sort :
    coq_Fuel -> global_declarations -> context -> term -> universe
    typing_result **)

let reduce_to_sort f _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tRel _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tVar _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tMeta _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tEvar (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tSort s -> ret (Obj.magic typing_monad) s
| Coq_tProd (_, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tLambda (_, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tLetIn (_, _, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tApp (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tConst (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tInd (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tConstruct (_, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tCase (_, _, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tProj (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tFix (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))
| Coq_tCoFix (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tSort s ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) s
        | _ :: _ -> raise (Obj.magic monad_exc) (NotASort t0))
     | _ -> raise (Obj.magic monad_exc) (NotASort t0)))

(** val reduce_to_prod :
    coq_Fuel -> global_declarations -> context -> term -> (term * term)
    typing_result **)

let reduce_to_prod f _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tRel _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tVar _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tMeta _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tEvar (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tSort _ ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tProd (_, a, b) -> ret (Obj.magic typing_monad) (a, b)
| Coq_tLambda (_, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tLetIn (_, _, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tApp (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tConst (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tInd (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tConstruct (_, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tCase (_, _, _, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tProj (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tFix (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))
| Coq_tCoFix (_, _) ->
  bind (Obj.magic typing_monad) (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0)
    (fun t' ->
    let (y, y0) = t' in
    (match y with
     | Coq_tProd (_, a, b) ->
       (match y0 with
        | [] -> ret (Obj.magic typing_monad) (a, b)
        | _ :: _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t'))))
     | _ -> raise (Obj.magic monad_exc) (NotAProduct (t0, (zip t')))))

(** val reduce_to_ind :
    coq_Fuel -> global_declarations -> context -> term ->
    ((inductive * Level.t list) * term list) typing_result **)

let reduce_to_ind f _UU03a3_ _UU0393_ t0 =
  let (t1, l) = decompose_app t0 in
  (match t1 with
   | Coq_tRel _ ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tVar _ ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tMeta _ ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tEvar (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tSort _ ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tProd (_, _, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tLambda (_, _, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tLetIn (_, _, _, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tApp (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tConst (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l)
   | Coq_tConstruct (_, _, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tCase (_, _, _, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tProj (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tFix (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0)))
   | Coq_tCoFix (_, _) ->
     bind (Obj.magic typing_monad)
       (Obj.magic hnf_stack f _UU03a3_ _UU0393_ t0) (fun t' ->
       let (y, l0) = t' in
       (match y with
        | Coq_tInd (i, u) -> ret (Obj.magic typing_monad) ((i, u), l0)
        | _ -> raise (Obj.magic monad_exc) (NotAnInductive t0))))

(** val lookup_constant_type :
    global_context -> ident -> universe_instance -> term typing_result **)

let lookup_constant_type _UU03a3_ cst u =
  match lookup_env _UU03a3_ cst with
  | Some g ->
    (match g with
     | ConstantDecl (_, c) ->
       let { cst_type = ty; cst_body = _; cst_universes = _ } = c in
       ret (Obj.magic typing_monad) (subst_instance_constr u ty)
     | InductiveDecl (_, _) ->
       raise (Obj.magic monad_exc) (UndeclaredConstant cst))
  | None -> raise (Obj.magic monad_exc) (UndeclaredConstant cst)

(** val lookup_ind_decl :
    global_context -> ident -> nat -> ((one_inductive_body
    list * universe_context) * one_inductive_body) typing_result **)

let lookup_ind_decl _UU03a3_ ind i =
  match lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | ConstantDecl (_, _) ->
       raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind =
         ind; inductive_ind = i })
     | InductiveDecl (_, m) ->
       let { ind_npars = _; ind_params = _; ind_bodies = l; ind_universes =
         uctx } = m
       in
       (match nth_error l i with
        | Some body -> ret (Obj.magic typing_monad) ((l, uctx), body)
        | None ->
          raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind =
            ind; inductive_ind = i })))
  | None ->
    raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind = ind;
      inductive_ind = i })

(** val lookup_ind_type :
    global_context -> ident -> nat -> Level.t list -> term typing_result **)

let lookup_ind_type _UU03a3_ ind i u =
  bind (Obj.magic typing_monad) (Obj.magic lookup_ind_decl _UU03a3_ ind i)
    (fun res ->
    ret (Obj.magic typing_monad) (subst_instance_constr u (snd res).ind_type))

(** val lookup_constructor_decl :
    global_context -> ident -> nat -> nat -> ((one_inductive_body
    list * universe_context) * term) typing_result **)

let lookup_constructor_decl _UU03a3_ ind i k =
  bind (Obj.magic typing_monad) (Obj.magic lookup_ind_decl _UU03a3_ ind i)
    (fun res ->
    let (y, body) = res in
    let (l, uctx) = y in
    (match nth_error body.ind_ctors k with
     | Some p ->
       let (p0, _) = p in
       let (_, ty) = p0 in ret (Obj.magic typing_monad) ((l, uctx), ty)
     | None ->
       raise (Obj.magic monad_exc) (UndeclaredConstructor ({ inductive_mind =
         ind; inductive_ind = i }, k))))

(** val lookup_constructor_type :
    global_context -> ident -> nat -> nat -> universe_instance -> term
    typing_result **)

let lookup_constructor_type _UU03a3_ ind i k u =
  bind (Obj.magic typing_monad)
    (Obj.magic lookup_constructor_decl _UU03a3_ ind i k) (fun res ->
    let (y, ty) = res in
    let (l, _) = y in
    ret (Obj.magic typing_monad)
      (subst (inds ind u l) O (subst_instance_constr u ty)))

(** val try_suc : Universe.t -> Universe.t **)

let try_suc u =
  map (fun pat -> let (l, _) = pat in (l, true)) u

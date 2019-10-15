open BasicAst
open Datatypes
open EAst
open List0
open PCUICAst
open PCUICAstUtils
open PCUICChecker
open PCUICMetaTheory
open PCUICRetyping
open Monad_utils
open UGraph0
open Univ0
open Utils

(** val is_prop_sort : Universe.t -> bool **)

let is_prop_sort s =
  match Universe.level s with
  | Some l -> Level.is_prop l
  | None -> false

(** val is_arity :
    global_context -> context -> coq_Fuel -> term -> bool typing_result **)

let rec is_arity _UU03a3_ _UU0393_ f t0 =
  match f with
  | O -> raise (Obj.magic monad_exc) (NotEnoughFuel f)
  | S f0 ->
    (match reduce_to_sort f (fst_ctx _UU03a3_) _UU0393_ t0 with
     | Checked _ -> ret (Obj.magic typing_monad) true
     | TypeError _ ->
       bind (Obj.magic typing_monad)
         (Obj.magic reduce_to_prod f (fst_ctx _UU03a3_) _UU0393_ t0)
         (fun p -> is_arity _UU03a3_ _UU0393_ f0 (snd p)))

(** val is_type_or_proof :
    coq_Fuel -> global_context -> context -> term -> bool typing_result **)

let is_type_or_proof f _UU03a3_ _UU0393_ t0 =
  bind (Obj.magic typing_monad) (Obj.magic type_of f _UU03a3_ _UU0393_ t0)
    (fun ty ->
    match is_arity _UU03a3_ _UU0393_ f ty with
    | Checked _ -> ret (Obj.magic typing_monad) true
    | TypeError _ ->
      bind (Obj.magic typing_monad)
        (Obj.magic type_of_as_sort f _UU03a3_ (type_of f _UU03a3_) _UU0393_
          ty) (fun s -> ret (Obj.magic typing_monad) (is_prop_sort s)))

module E = EAst

(** val is_box : E.term -> bool **)

let is_box = function
| E.Coq_tBox -> true
| _ -> false

(** val mkAppBox : E.term -> nat -> E.term **)

let rec mkAppBox c = function
| O -> c
| S n0 -> mkAppBox (E.Coq_tApp (c, E.Coq_tBox)) n0

(** val extract_mfix :
    (context -> term -> E.term typing_result) -> context_decl list -> term
    BasicAst.mfixpoint -> E.term mfixpoint typing_result **)

let extract_mfix extract0 _UU0393_ defs =
  let _UU0393_' = app (fix_decls defs) _UU0393_ in
  monad_map (Obj.magic typing_monad) (fun d ->
    bind (Obj.magic typing_monad)
      (Obj.magic extract0 _UU0393_' d.BasicAst.dbody) (fun dbody' ->
      ret (Obj.magic typing_monad) { E.dname = d.BasicAst.dname; E.dbody =
        dbody'; E.rarg = d.BasicAst.rarg })) defs

(** val extract :
    coq_Fuel -> global_context -> context -> term -> E.term typing_result **)

let rec extract f _UU03a3_ _UU0393_ t0 =
  bind (Obj.magic typing_monad)
    (Obj.magic is_type_or_proof f _UU03a3_ _UU0393_ t0) (fun b ->
    if b
    then ret (Obj.magic typing_monad) E.Coq_tBox
    else (match t0 with
          | Coq_tRel i -> ret (Obj.magic typing_monad) (E.Coq_tRel i)
          | Coq_tVar n -> ret (Obj.magic typing_monad) (E.Coq_tVar n)
          | Coq_tMeta m -> ret (Obj.magic typing_monad) (E.Coq_tMeta m)
          | Coq_tEvar (m, l) ->
            bind (Obj.magic typing_monad)
              (monad_map (Obj.magic typing_monad)
                (extract f _UU03a3_ _UU0393_) l) (fun l' ->
              ret (Obj.magic typing_monad) (E.Coq_tEvar (m, l')))
          | Coq_tLambda (na, b0, t1) ->
            bind (Obj.magic typing_monad)
              (extract f _UU03a3_ ((vass na b0) :: _UU0393_) t1) (fun t' ->
              ret (Obj.magic typing_monad) (E.Coq_tLambda (na, t')))
          | Coq_tLetIn (na, b0, t1, t2) ->
            bind (Obj.magic typing_monad) (extract f _UU03a3_ _UU0393_ b0)
              (fun b' ->
              bind (Obj.magic typing_monad)
                (extract f _UU03a3_ ((vdef na b0 t1) :: _UU0393_) t2)
                (fun t1' ->
                ret (Obj.magic typing_monad) (E.Coq_tLetIn (na, b', t1'))))
          | Coq_tApp (f0, u) ->
            bind (Obj.magic typing_monad) (extract f _UU03a3_ _UU0393_ f0)
              (fun f' ->
              bind (Obj.magic typing_monad) (extract f _UU03a3_ _UU0393_ u)
                (fun l' -> ret (Obj.magic typing_monad) (E.Coq_tApp (f', l'))))
          | Coq_tConst (kn, _) ->
            ret (Obj.magic typing_monad) (E.Coq_tConst kn)
          | Coq_tConstruct (kn, k, _) ->
            ret (Obj.magic typing_monad) (E.Coq_tConstruct (kn, k))
          | Coq_tCase (ip, _, c, brs) ->
            bind (Obj.magic typing_monad) (extract f _UU03a3_ _UU0393_ c)
              (fun c' ->
              if is_box c'
              then (match brs with
                    | [] ->
                      ret (Obj.magic typing_monad) (E.Coq_tCase (ip, c', []))
                    | p :: _ ->
                      let (n, x) = p in
                      bind (Obj.magic typing_monad)
                        (extract f _UU03a3_ _UU0393_ x) (fun x' ->
                        ret (Obj.magic typing_monad) (mkAppBox x' n)))
              else bind (Obj.magic typing_monad)
                     (monad_map (Obj.magic typing_monad) (fun x ->
                       bind (Obj.magic typing_monad)
                         (extract f _UU03a3_ _UU0393_ (snd x)) (fun x' ->
                         ret (Obj.magic typing_monad) ((fst x), x'))) brs)
                     (fun brs' ->
                     ret (Obj.magic typing_monad) (E.Coq_tCase (ip, c', brs'))))
          | Coq_tProj (p, c) ->
            bind (Obj.magic typing_monad) (extract f _UU03a3_ _UU0393_ c)
              (fun c' -> ret (Obj.magic typing_monad) (E.Coq_tProj (p, c')))
          | Coq_tFix (mfix, n) ->
            bind (Obj.magic typing_monad)
              (Obj.magic extract_mfix (extract f _UU03a3_) _UU0393_ mfix)
              (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tFix (mfix', n)))
          | Coq_tCoFix (mfix, n) ->
            bind (Obj.magic typing_monad)
              (Obj.magic extract_mfix (extract f _UU03a3_) _UU0393_ mfix)
              (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tCoFix (mfix', n)))
          | _ -> ret (Obj.magic typing_monad) E.Coq_tBox))

(** val optM : 'a1 coq_Monad -> 'a2 option -> ('a2 -> 'a1) -> 'a1 **)

let optM h x f =
  match x with
  | Some x0 -> bind h (f x0) (fun y -> ret h (Some y))
  | None -> ret h None

(** val extract_constant_body :
    coq_Fuel -> global_context -> constant_body -> E.constant_body
    typing_result **)

let extract_constant_body f _UU03a3_ cb =
  bind (Obj.magic typing_monad) (Obj.magic extract f _UU03a3_ [] cb.cst_type)
    (fun ty ->
    bind (Obj.magic typing_monad)
      (optM (Obj.magic typing_monad) cb.cst_body (fun b ->
        Obj.magic extract f _UU03a3_ [] b)) (fun body ->
      ret (Obj.magic typing_monad) { E.cst_type = ty; E.cst_body = body }))

(** val lift_opt_typing : 'a1 option -> type_error -> 'a1 typing_result **)

let lift_opt_typing a e =
  match a with
  | Some x -> ret (Obj.magic typing_monad) x
  | None -> raise (Obj.magic monad_exc) e

(** val extract_one_inductive_body :
    coq_Fuel -> global_context -> nat -> context -> one_inductive_body ->
    E.one_inductive_body typing_result **)

let extract_one_inductive_body f _UU03a3_ npars arities oib =
  bind (Obj.magic typing_monad)
    (lift_opt_typing (Obj.magic decompose_prod_n_assum [] npars oib.ind_type)
      (NotAnInductive oib.ind_type)) (fun _ ->
    bind (Obj.magic typing_monad)
      (Obj.magic extract f _UU03a3_ [] oib.ind_type) (fun type0 ->
      bind (Obj.magic typing_monad)
        (monad_map (Obj.magic typing_monad) (fun pat ->
          let (y0, z) = pat in
          let (x, y) = y0 in
          bind (Obj.magic typing_monad)
            (Obj.magic extract f _UU03a3_ arities y) (fun y' ->
            ret (Obj.magic typing_monad) ((x, y'), z))) oib.ind_ctors)
        (fun ctors ->
        bind (Obj.magic typing_monad)
          (monad_map (Obj.magic typing_monad) (fun pat ->
            let (x, y) = pat in
            bind (Obj.magic typing_monad) (Obj.magic extract f _UU03a3_ [] y)
              (fun y' -> ret (Obj.magic typing_monad) (x, y'))) oib.ind_projs)
          (fun projs ->
          ret (Obj.magic typing_monad) { E.ind_name = oib.ind_name;
            E.ind_type = type0; E.ind_kelim = oib.ind_kelim; E.ind_ctors =
            ctors; E.ind_projs = projs }))))

(** val extract_mutual_inductive_body :
    coq_Fuel -> global_context -> mutual_inductive_body ->
    E.mutual_inductive_body typing_result **)

let extract_mutual_inductive_body f _UU03a3_ mib =
  let bds = mib.ind_bodies in
  let arities = arities_context bds in
  bind (Obj.magic typing_monad)
    (monad_map (Obj.magic typing_monad)
      (Obj.magic extract_one_inductive_body f _UU03a3_ mib.ind_npars arities)
      bds) (fun bodies ->
    ret (Obj.magic typing_monad) { E.ind_npars = mib.ind_npars;
      E.ind_bodies = bodies })

(** val extract_global_decls :
    coq_Fuel -> t -> global_decl list -> E.global_declarations typing_result **)

let rec extract_global_decls f univs = function
| [] -> ret (Obj.magic typing_monad) []
| y :: _UU03a3_0 ->
  (match y with
   | ConstantDecl (kn, cb) ->
     bind (Obj.magic typing_monad)
       (Obj.magic extract_constant_body f (_UU03a3_0, univs) cb) (fun cb' ->
       bind (Obj.magic typing_monad) (extract_global_decls f univs _UU03a3_0)
         (fun _UU03a3_' ->
         ret (Obj.magic typing_monad) ((E.ConstantDecl (kn,
           cb')) :: _UU03a3_')))
   | InductiveDecl (kn, mib) ->
     bind (Obj.magic typing_monad)
       (Obj.magic extract_mutual_inductive_body f (_UU03a3_0, univs) mib)
       (fun mib' ->
       bind (Obj.magic typing_monad) (extract_global_decls f univs _UU03a3_0)
         (fun _UU03a3_' ->
         ret (Obj.magic typing_monad) ((E.InductiveDecl (kn,
           mib')) :: _UU03a3_'))))

(** val extract_global :
    coq_Fuel -> (global_decl list * t) -> E.global_decl list typing_result **)

let extract_global f = function
| (_UU03a3_0, univs) ->
  bind (Obj.magic typing_monad)
    (extract_global_decls f univs (rev _UU03a3_0)) (fun _UU03a3_' ->
    ret (Obj.magic typing_monad) (rev _UU03a3_'))

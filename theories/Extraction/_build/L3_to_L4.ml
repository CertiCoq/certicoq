open Ast0
open AstCommon
open BasicAst
open BinNat
open Datatypes
open L3_to_L3_eta
open List0
open RandyPrelude
open Compile0
open Compile1
open Expression
open Utils

type __ = Obj.t

module L3t = Compile1

(** val dcon_of_con : inductive -> nat -> inductive * int **)

let dcon_of_con i n =
  (i, (N.of_nat n))

type env = (char list * exp) list

(** val cst_offset : env -> char list -> int **)

let rec cst_offset e s =
  match e with
  | [] -> 0
  | p :: tl ->
    let (c, _) = p in
    if string_eq_bool s c then 0 else N.add 1 (cst_offset tl s)

type ienv = (char list * itypPack) list

(** val map_terms : (L3t.coq_Term -> exp) -> L3t.coq_Terms -> exps **)

let rec map_terms f = function
| L3t.Coq_tnil -> Coq_enil
| L3t.Coq_tcons (t, ts) -> Coq_econs ((f t), (map_terms f ts))

(** val strip_lam : nat -> exp -> name list * exp **)

let rec strip_lam k e =
  match k with
  | O -> ([], e)
  | S n ->
    (match e with
     | Lam_e (na, e0) ->
       let (names, e1) = strip_lam n e0 in ((na :: names), e1)
     | _ -> ([], e))

(** val trans_args :
    (int -> L3t.coq_Term -> exp) -> int -> L3t.coq_Terms -> exps **)

let trans_args trans0 k t =
  map_terms (trans0 k) t

(** val trans_brs :
    (int -> L3t.coq_Term -> exp) -> inductive -> int -> int -> L3t.coq_Brs ->
    branches_e **)

let rec trans_brs trans0 ind k n = function
| L3t.Coq_bnil -> Coq_brnil_e
| L3t.Coq_bcons (nargs, t, ts) ->
  let (names, t') = strip_lam nargs (trans0 k t) in
  Coq_brcons_e ((ind, n), ((N.of_nat nargs), names), t',
  (trans_brs trans0 ind k (N.add n 1) ts))

(** val trans_fixes :
    (int -> L3t.coq_Term -> exp) -> int -> L3t.coq_Defs -> efnlst **)

let rec trans_fixes trans0 k = function
| L3t.Coq_dnil -> Coq_eflnil
| L3t.Coq_dcons (na, t, _, l') ->
  Coq_eflcons (na, (trans0 k t), (trans_fixes trans0 k l'))

(** val trans : env -> int -> L3t.coq_Term -> exp **)

let rec trans e k = function
| L3t.TRel n -> Var_e (N.of_nat n)
| L3t.TLambda (n, t0) -> Lam_e (n, (trans e (N.add 1 k) t0))
| L3t.TLetIn (n, t0, u) -> Let_e (n, (trans e k t0), (trans e (N.add 1 k) u))
| L3t.TApp (t0, u) -> App_e ((trans e k t0), (trans e k u))
| L3t.TConst s -> Var_e (N.add (cst_offset e s) k)
| L3t.TConstruct (ind, c, args) ->
  let args' = trans_args (trans e) k args in
  Con_e ((dcon_of_con ind c), args')
| L3t.TCase (ind, t0, brs) ->
  let brs' = trans_brs (trans e) ind k 0 brs in
  Match_e ((trans e k t0), 0, brs')
| L3t.TFix (d, n) ->
  let len = L3t.dlength d in
  let defs' = trans_fixes (trans e) (N.add (N.of_nat len) k) d in
  Fix_e (defs', (N.of_nat n))
| _ -> Prf_e

(** val translate : env -> L3t.coq_Term -> exp **)

let translate e t =
  trans e 0 t

(** val translate_entry :
    (char list * L3t.coq_Term envClass) -> env -> (char list * exp) list **)

let translate_entry x acc =
  let (s, y) = x in
  (match y with
   | Coq_ecTrm t -> let t' = translate acc t in (s, t') :: acc
   | Coq_ecTyp (_, _) -> acc)

(** val translate_env_aux : coq_Term environ -> env -> env **)

let translate_env_aux e k =
  fold_right translate_entry k e

(** val translate_env : coq_Term environ -> env **)

let translate_env e =
  translate_env_aux e []

(** val inductive_entry_aux : (char list * 'a1 envClass) -> ienv -> ienv **)

let inductive_entry_aux x acc =
  let (s, e) = x in
  (match e with
   | Coq_ecTrm _ -> acc
   | Coq_ecTyp (_, pack) -> (s, pack) :: acc)

(** val inductive_env : coq_Term environ -> ienv **)

let inductive_env e =
  fold_right inductive_entry_aux [] e

(** val mkLets : env -> exp -> exp **)

let mkLets e t =
  fold_left (fun acc x -> Let_e ((nNameds (fst x)), (snd x), acc)) e t

(** val translate_program :
    coq_Term environ -> L3_to_L3_eta.L3t.coq_Term -> exp **)

let translate_program e t =
  let e' = translate_env e in mkLets e' (translate e' t)

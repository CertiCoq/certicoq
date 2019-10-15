open BasicAst
open Basics
open BinNat
open Datatypes
open FMapPositive
open List0
open Expression
open List1
open PolyEval
open Terms
open TermsDB
open Variables

(** val mkNames : (int * name list) -> name list **)

let mkNames = function
| (n, vnames) ->
  let vnames0 = firstn (N.to_nat n) vnames in
  listPad Coq_nAnon vnames0 (N.to_nat n)

(** val tL4_to_L4_1 : exp -> (name, coq_L4Opid) coq_DTerm **)

let rec tL4_to_L4_1 = function
| Var_e n -> Coq_vterm n
| Lam_e (name0, e0) ->
  Coq_oterm (NLambda, ((Coq_bterm ((name0 :: []), (tL4_to_L4_1 e0))) :: []))
| App_e (f, a) ->
  Coq_oterm (NApply,
    (map (compose (fun x -> Coq_bterm ([], x)) tL4_to_L4_1) (f :: (a :: []))))
| Con_e (d, el) ->
  let el0 = ltL4_to_L4_1 el in
  Coq_oterm ((NDCon (d, (length el0))),
  (map (fun x -> Coq_bterm ([], x)) el0))
| Match_e (d, _, brl) ->
  let brs = btL4_to_L4_1 brl in
  Coq_oterm ((NMatch
  (map (fun b -> ((fst b), (num_bvars (snd (Obj.magic b))))) brs)),
  ((Coq_bterm ([], (tL4_to_L4_1 d))) :: (map (Obj.magic snd) brs)))
| Let_e (name0, e1, e2) ->
  Coq_oterm (NLet, ((Coq_bterm ([], (tL4_to_L4_1 e1))) :: ((Coq_bterm
    ((name0 :: []), (tL4_to_L4_1 e2))) :: [])))
| Fix_e (el, i) ->
  let names = fnames el in
  let lbt = ftL4_to_L4_1 el in
  Coq_oterm ((NFix ((length lbt), (N.to_nat i))),
  (map (fun x -> Coq_bterm (names, x)) lbt))
| Prf_e -> Coq_oterm ((NBox ('p'::('r'::('o'::('o'::('f'::[])))))), [])

(** val ltL4_to_L4_1 : exps -> (name, coq_L4Opid) coq_DTerm list **)

and ltL4_to_L4_1 = function
| Coq_enil -> []
| Coq_econs (h, tl) -> (tL4_to_L4_1 h) :: (ltL4_to_L4_1 tl)

(** val ftL4_to_L4_1 : efnlst -> (name, coq_L4Opid) coq_DTerm list **)

and ftL4_to_L4_1 = function
| Coq_eflnil -> []
| Coq_eflcons (_, h, tl) -> (tL4_to_L4_1 h) :: (ftL4_to_L4_1 tl)

(** val btL4_to_L4_1 : branches_e -> coq_L4Opid branch list **)

and btL4_to_L4_1 = function
| Coq_brnil_e -> []
| Coq_brcons_e (d, n, e, tl) ->
  (d,
    (Obj.magic (Coq_bterm ((mkNames n), (tL4_to_L4_1 e))))) :: (btL4_to_L4_1
                                                                 tl)

(** val mkVar : int -> int **)

let mkVar n =
  (fun p->2*p) (N.succ_pos n)

(** val mkNVar : (int * name) -> coq_NVar **)

let mkNVar = function
| (n, name0) -> ((mkVar n), name0)

type coq_L4_1_Term = (name, coq_L4Opid) coq_DTerm

type coq_L4_2_Term = (coq_NVar, coq_L4Opid) coq_NTerm

(** val tL4_1_to_L4_2 : coq_L4_1_Term -> coq_L4_2_Term **)

let tL4_1_to_L4_2 e =
  fromDB Coq_nAnon mkNVar 0 Empty e

(** val tL4_to_L4_2 : exp -> coq_L4_2_Term **)

let tL4_to_L4_2 =
  compose tL4_1_to_L4_2 tL4_to_L4_1

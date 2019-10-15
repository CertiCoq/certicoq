open Ast0
open AstCommon
open BasicAst
open Datatypes
open Compile0
open Compile1
open Utils

type __ = Obj.t

module L3t = Compile1

(** val eta_expand : nat -> L3t.coq_Term -> L3t.coq_Term **)

let rec eta_expand n t =
  match n with
  | O -> t
  | S n' ->
    L3t.TLambda (Coq_nAnon,
      (eta_expand n' (L3t.TApp ((L3t.lift O t), (L3t.TRel O)))))

(** val trans : L3t.coq_Term -> L3t.coq_Term **)

let rec trans = function
| L3t.TLambda (n, t0) -> L3t.TLambda (n, (trans t0))
| L3t.TLetIn (n, t0, u) -> L3t.TLetIn (n, (trans t0), (trans u))
| L3t.TApp (t0, u) -> L3t.TApp ((trans t0), (trans u))
| L3t.TConstruct (ind, c, args) -> L3t.TConstruct (ind, c, (trans_terms args))
| L3t.TCase (ind, t0, brs) -> L3t.TCase (ind, (trans t0), (trans_brs ind brs))
| L3t.TFix (d, n) -> let defs' = trans_fixes d in L3t.TFix (defs', n)
| L3t.TProj (_, _) -> L3t.TWrong ('T'::('P'::('r'::('o'::('j'::[])))))
| x -> x

(** val trans_terms : L3t.coq_Terms -> L3t.coq_Terms **)

and trans_terms = function
| L3t.Coq_tnil -> L3t.Coq_tnil
| L3t.Coq_tcons (t, ts0) -> L3t.Coq_tcons ((trans t), (trans_terms ts0))

(** val trans_brs : inductive -> L3t.coq_Brs -> L3t.coq_Brs **)

and trans_brs i = function
| L3t.Coq_bnil -> L3t.Coq_bnil
| L3t.Coq_bcons (n, t, brs0) ->
  let transt = trans t in
  let etat = eta_expand n transt in
  L3t.Coq_bcons (n, etat, (trans_brs i brs0))

(** val trans_fixes : L3t.coq_Defs -> L3t.coq_Defs **)

and trans_fixes = function
| L3t.Coq_dnil -> L3t.Coq_dnil
| L3t.Coq_dcons (na, t, n, ds) ->
  L3t.Coq_dcons (na, (trans t), n, (trans_fixes ds))

(** val transEC : L3t.coq_Term envClass -> L3t.coq_Term envClass **)

let transEC = function
| Coq_ecTrm t -> Coq_ecTrm (trans t)
| Coq_ecTyp (n, itp) -> Coq_ecTyp (n, itp)

(** val transEnv : L3t.coq_Term environ -> L3t.coq_Term environ **)

let rec transEnv = function
| [] -> []
| p0 :: q -> let (nm, ec) = p0 in (nm, (transEC ec)) :: (transEnv q)

(** val coq_Program_Program :
    L3t.coq_Term coq_Program -> L3t.coq_Term coq_Program **)

let coq_Program_Program pgm =
  let { main = main0; env = env0 } = pgm in
  { main = (trans main0); env = (transEnv env0) }

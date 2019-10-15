open Datatypes
open List0
open Cps

(** val erase_fundefs :
    exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) -> exp * fundefs **)

let rec erase_fundefs e defs f =
  match e with
  | Econstr (x, tag, ys, e') ->
    erase_fundefs e' defs (fun p ->
      let (e0, defs0) = p in f ((Econstr (x, tag, ys, e0)), defs0))
  | Ecase (x, tes) ->
    fold_left (fun f0 te p ->
      let (c, e0) = te in
      let (e1, defs1) = p in
      erase_fundefs e0 defs1 (fun p2 ->
        let (e2, defs2) = p2 in
        (match e1 with
         | Ecase (x', tes') -> f0 ((Ecase (x', ((c, e2) :: tes'))), defs2)
         | _ -> f0 ((Ecase (x, ((c, e2) :: []))), defs2)))) tes f ((Ecase (x,
      [])), defs)
  | Eproj (x, tag, n, y, e') ->
    erase_fundefs e' defs (fun p ->
      let (e0, defs0) = p in f ((Eproj (x, tag, n, y, e0)), defs0))
  | Efun (fdefs, e') ->
    erase_fundefs e' defs (fun p ->
      let (e'', defs'') = p in erase_nested_fundefs fdefs e'' defs'' f)
  | Eprim (x, prim, ys, e') ->
    erase_fundefs e' defs (fun p ->
      let (e'0, defs') = p in f ((Eprim (x, prim, ys, e'0)), defs'))
  | x -> f (x, defs)

(** val erase_nested_fundefs :
    fundefs -> exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) ->
    exp * fundefs **)

and erase_nested_fundefs defs e hdefs f =
  match defs with
  | Fcons (g, t, xs, e', defs0) ->
    erase_nested_fundefs defs0 e hdefs (fun p1 ->
      let (e1, defs1) = p1 in
      erase_fundefs e' defs1 (fun p2 ->
        let (e2, defs2) = p2 in f (e1, (Fcons (g, t, xs, e2, defs2)))))
  | Fnil -> f (e, hdefs)

(** val exp_hoist : exp -> exp **)

let exp_hoist e =
  let (e0, defs) = erase_fundefs e Fnil id in
  (match defs with
   | Fcons (_, _, _, _, _) -> Efun (defs, e0)
   | Fnil -> e0)

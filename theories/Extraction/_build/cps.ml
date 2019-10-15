open BasicAst
open Maps

module M = PTree

(** val setlist : M.elt list -> 'a1 list -> 'a1 M.t -> 'a1 M.t option **)

let rec setlist xs vs rho =
  match xs with
  | [] -> (match vs with
           | [] -> Some rho
           | _ :: _ -> None)
  | x :: xs' ->
    (match vs with
     | [] -> None
     | v :: vs' ->
       (match setlist xs' vs' rho with
        | Some rho' -> Some (M.set x v rho')
        | None -> None))

type var = M.elt

type fTag = M.elt

type iTag = M.elt

type cTag = M.elt

type prim = M.elt

(** val findtag : (cTag * 'a1) list -> cTag -> 'a1 option **)

let rec findtag cl c =
  match cl with
  | [] -> None
  | p :: cl' ->
    let (c', a) = p in if M.elt_eq c' c then Some a else findtag cl' c

type exp =
| Econstr of var * cTag * var list * exp
| Ecase of var * (cTag * exp) list
| Eproj of var * cTag * int * var * exp
| Efun of fundefs * exp
| Eapp of var * fTag * var list
| Eprim of var * prim * var list * exp
| Ehalt of var
and fundefs =
| Fcons of var * fTag * var list * exp * fundefs
| Fnil

type coq_val =
| Vconstr of cTag * coq_val list
| Vfun of coq_val M.t * fundefs * var
| Vint of int

type cTyInfo = (((name * name) * iTag) * int) * int

type iTyInfo = (cTag * int) list

type cEnv = cTyInfo M.t

type iEnv = iTyInfo M.t

type fTyInfo = int * int list

type fEnv = fTyInfo M.t

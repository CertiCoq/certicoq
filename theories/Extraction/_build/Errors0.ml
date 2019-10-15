
type errcode =
| MSG of char list
| CTX of int
| POS of int

type errmsg = errcode list

type 'a res =
| OK of 'a
| Error of errmsg

(** val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let bind f g =
  match f with
  | OK x -> g x
  | Error msg -> Error msg

(** val bind2 : ('a1 * 'a2) res -> ('a1 -> 'a2 -> 'a3 res) -> 'a3 res **)

let bind2 f g =
  match f with
  | OK p -> let (x, y) = p in g x y
  | Error msg -> Error msg

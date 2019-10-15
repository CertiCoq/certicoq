
type 'a coq_exception =
| Exc of char list
| Ret of 'a

(** val ret : 'a1 -> 'a1 coq_exception **)

let ret x =
  Ret x

(** val raise : char list -> 'a1 coq_exception **)

let raise str =
  Exc str

(** val bind :
    'a1 coq_exception -> ('a1 -> 'a2 coq_exception) -> 'a2 coq_exception **)

let bind a f =
  match a with
  | Exc str -> Exc str
  | Ret x -> f x

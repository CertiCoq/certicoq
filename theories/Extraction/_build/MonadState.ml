
type ('t, 'm) coq_MonadState = { get : 'm; put : ('t -> 'm) }

(** val get : ('a1, 'a2) coq_MonadState -> 'a2 **)

let get x = x.get

(** val put : ('a1, 'a2) coq_MonadState -> 'a1 -> 'a2 **)

let put x = x.put

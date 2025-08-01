
type unit0 =
| Tt

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat2 : 'a1 -> 'a1 -> nat -> 'a1 list

val demo2 : unit0 -> bool list

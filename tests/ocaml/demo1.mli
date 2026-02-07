
type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val repeat : 'a1 -> nat -> 'a1 list

val demo1 : unit0 -> bool list

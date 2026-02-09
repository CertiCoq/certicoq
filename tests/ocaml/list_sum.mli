
type unit0 =
| Tt

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val add : nat -> nat -> nat

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val repeat : 'a1 -> nat -> 'a1 list

val list_sum : unit0 -> nat

open Datatypes

val hd : 'a1 -> 'a1 list -> 'a1

val tl : 'a1 list -> 'a1 list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val nth_error : 'a1 list -> nat -> 'a1 option

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val seq : nat -> nat -> nat list

val repeat : 'a1 -> nat -> 'a1 list

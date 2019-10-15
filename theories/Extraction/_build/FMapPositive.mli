
type 't pmap =
| Empty
| Branch of 't option * 't pmap * 't pmap

val pmap_here : 'a1 pmap -> 'a1 option

val pmap_left : 'a1 pmap -> 'a1 pmap

val pmap_right : 'a1 pmap -> 'a1 pmap

val pmap_lookup : int -> 'a1 pmap -> 'a1 option

val pmap_insert : int -> 'a1 -> 'a1 pmap -> 'a1 pmap

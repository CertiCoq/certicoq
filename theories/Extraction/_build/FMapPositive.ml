
type 't pmap =
| Empty
| Branch of 't option * 't pmap * 't pmap

(** val pmap_here : 'a1 pmap -> 'a1 option **)

let pmap_here = function
| Empty -> None
| Branch (d, _, _) -> d

(** val pmap_left : 'a1 pmap -> 'a1 pmap **)

let pmap_left = function
| Empty -> Empty
| Branch (_, l, _) -> l

(** val pmap_right : 'a1 pmap -> 'a1 pmap **)

let pmap_right = function
| Empty -> Empty
| Branch (_, _, r) -> r

(** val pmap_lookup : int -> 'a1 pmap -> 'a1 option **)

let rec pmap_lookup p = function
| Empty -> None
| Branch (d, l, r) ->
  ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
     (fun p0 -> pmap_lookup p0 r)
     (fun p0 -> pmap_lookup p0 l)
     (fun _ -> d)
     p)

(** val pmap_insert : int -> 'a1 -> 'a1 pmap -> 'a1 pmap **)

let rec pmap_insert p v m =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p0 -> Branch ((pmap_here m), (pmap_left m),
    (pmap_insert p0 v (pmap_right m))))
    (fun p0 -> Branch ((pmap_here m), (pmap_insert p0 v (pmap_left m)),
    (pmap_right m)))
    (fun _ -> Branch ((Some v), (pmap_left m), (pmap_right m)))
    p

open BinPos

(** val digits2_pos : int -> int **)

let rec digits2_pos n =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p -> Pos.succ (digits2_pos p))
    (fun p -> Pos.succ (digits2_pos p))
    (fun _ -> 1)
    n

(** val coq_Zdigits2 : int -> int **)

let coq_Zdigits2 n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> n)
    (fun p -> (digits2_pos p))
    (fun p -> (digits2_pos p))
    n

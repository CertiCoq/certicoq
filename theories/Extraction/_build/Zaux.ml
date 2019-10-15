open BinInt
open BinPos
open Datatypes

type radix = int
  (* singleton inductive, whose constructor was Build_radix *)

(** val radix_val : radix -> int **)

let radix_val r =
  r

(** val radix2 : radix **)

let radix2 =
  ((fun p->2*p) 1)

(** val cond_Zopp : bool -> int -> int **)

let cond_Zopp b m =
  if b then Z.opp m else m

(** val coq_Zpos_div_eucl_aux1 : int -> int -> int * int **)

let rec coq_Zpos_div_eucl_aux1 a b =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun _ -> Z.pos_div_eucl a b)
    (fun b' ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
      (q, (Z.add (Z.mul ((fun p->2*p) 1) r) 1)))
      (fun a' ->
      let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
      (q, (Z.mul ((fun p->2*p) 1) r)))
      (fun _ -> (0, a))
      a)
    (fun _ -> (a, 0))
    b

(** val coq_Zpos_div_eucl_aux : int -> int -> int * int **)

let coq_Zpos_div_eucl_aux a b =
  match Pos.compare a b with
  | Eq -> (1, 0)
  | Lt -> (0, a)
  | Gt -> coq_Zpos_div_eucl_aux1 a b

(** val coq_Zfast_div_eucl : int -> int -> int * int **)

let coq_Zfast_div_eucl a b =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (0, 0))
    (fun a' ->
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun b' -> coq_Zpos_div_eucl_aux a' b')
      (fun b' ->
      let (q, r) = coq_Zpos_div_eucl_aux a' b' in
      ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
         (fun _ -> ((Z.opp q), 0))
         (fun _ -> ((Z.opp (Z.add q 1)), (Z.add b r)))
         (fun _ -> ((Z.opp (Z.add q 1)), (Z.add b r)))
         r))
      b)
    (fun a' ->
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun b' ->
      let (q, r) = coq_Zpos_div_eucl_aux a' b' in
      ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
         (fun _ -> ((Z.opp q), 0))
         (fun _ -> ((Z.opp (Z.add q 1)), (Z.sub b r)))
         (fun _ -> ((Z.opp (Z.add q 1)), (Z.sub b r)))
         r))
      (fun b' -> let (q, r) = coq_Zpos_div_eucl_aux a' b' in (q, (Z.opp r)))
      b)
    a

(** val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1 **)

let rec iter_nat f n x =
  match n with
  | O -> x
  | S n' -> iter_nat f n' (f x)

(** val iter_pos : ('a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun n' -> iter_pos f n' (iter_pos f n' (f x)))
    (fun n' -> iter_pos f n' (iter_pos f n' x))
    (fun _ -> f x)
    n

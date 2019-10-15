open BinNat
open Datatypes

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n p =
    match n with
    | O -> zero
    | S n' ->
      ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun p' -> shift true (loop n' p'))
         (fun p' -> shift false (loop n' p'))
         (fun _ -> one)
         p)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val coq_N_of_digits : bool list -> int **)

let rec coq_N_of_digits = function
| [] -> 0
| b :: l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (coq_N_of_digits l'))

(** val coq_N_of_ascii : char -> int **)

let coq_N_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    coq_N_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (coq_N_of_ascii a)

open Char0
open Datatypes
open NPeano
open Nat0
open String0

(** val nat2string : nat -> nat -> char list **)

let rec nat2string modulus x =
  if Nat.ltb x modulus
  then (digit2ascii x)::[]
  else let m = Nat.div x modulus in
       append (nat2string modulus m)
         ((digit2ascii (sub x (mul modulus m)))::[])

(** val nat2string10 : nat -> char list **)

let nat2string10 =
  nat2string (S (S (S (S (S (S (S (S (S (S O))))))))))

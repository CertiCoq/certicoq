open Datatypes
open NPeano
open Nat0
open PeanoNat
open String0

(** val digit_to_string : nat -> char list **)

let digit_to_string = function
| O -> '0'::[]
| S n0 ->
  (match n0 with
   | O -> '1'::[]
   | S n1 ->
     (match n1 with
      | O -> '2'::[]
      | S n2 ->
        (match n2 with
         | O -> '3'::[]
         | S n3 ->
           (match n3 with
            | O -> '4'::[]
            | S n4 ->
              (match n4 with
               | O -> '5'::[]
               | S n5 ->
                 (match n5 with
                  | O -> '6'::[]
                  | S n6 ->
                    (match n6 with
                     | O -> '7'::[]
                     | S n7 -> (match n7 with
                                | O -> '8'::[]
                                | S _ -> '9'::[]))))))))

(** val nat_to_string : nat -> char list **)

let rec nat_to_string x =
  if Nat.ltb x (S (S (S (S (S (S (S (S (S (S O))))))))))
  then digit_to_string x
  else let m = NPeano.Nat.div x (S (S (S (S (S (S (S (S (S (S O)))))))))) in
       append (nat_to_string m)
         (digit_to_string
           (sub x (mul (S (S (S (S (S (S (S (S (S (S O)))))))))) m)))

(** val string_eq_bool : char list -> char list -> bool **)

let rec string_eq_bool a1 a2 =
  match a1 with
  | [] -> (match a2 with
           | [] -> true
           | _::_ -> false)
  | b::bs ->
    (match bs with
     | [] ->
       (match a2 with
        | [] -> false
        | c::cs -> (&&) ((=) b c) (string_eq_bool bs cs))
     | b2::bs0 ->
       (match a2 with
        | [] -> false
        | c::cs ->
          (match cs with
           | [] -> (&&) ((=) b c) (string_eq_bool bs cs)
           | c2::cs0 ->
             (&&) ((&&) ((=) b c) ((=) b2 c2)) (string_eq_bool bs0 cs0))))

open Ascii
open Datatypes
open Nat0

(** val digit2ascii : nat -> char **)

let digit2ascii n = match n with
| O -> '0'
| S n0 ->
  (match n0 with
   | O -> '1'
   | S n1 ->
     (match n1 with
      | O -> '2'
      | S n2 ->
        (match n2 with
         | O -> '3'
         | S n3 ->
           (match n3 with
            | O -> '4'
            | S n4 ->
              (match n4 with
               | O -> '5'
               | S n5 ->
                 (match n5 with
                  | O -> '6'
                  | S n6 ->
                    (match n6 with
                     | O -> '7'
                     | S n7 ->
                       (match n7 with
                        | O -> '8'
                        | S n8 ->
                          (match n8 with
                           | O -> '9'
                           | S _ ->
                             ascii_of_nat
                               (add
                                 (sub n (S (S (S (S (S (S (S (S (S (S
                                   O))))))))))) (nat_of_ascii 'A')))))))))))

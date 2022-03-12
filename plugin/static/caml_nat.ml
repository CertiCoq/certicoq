let nat_of_caml_int i = 
  let rec aux acc i =
    if i < 0 then acc
    else aux (Datatypes.S acc) (i - 1)
  in aux Datatypes.O (i - 1)

let rec caml_int_of_nat n =
  match n with
  | Datatypes.O -> 0
  | Datatypes.S x -> succ (caml_int_of_nat x)


let of_coq = function
  | Datatypes.Coq_true -> true
  | Datatypes.Coq_false -> false

let to_coq = function
  | true -> Datatypes.Coq_true
  | false -> Datatypes.Coq_false
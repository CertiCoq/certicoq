open DecidableClass

(** val coq_DecConj : coq_Decidable -> coq_Decidable -> coq_Decidable **)

let coq_DecConj h h0 =
  (&&) (decide h) (decide h0)

type 't coq_Deq = 't -> 't -> coq_Decidable

(** val deceq : 'a1 coq_Deq -> 'a1 -> 'a1 -> coq_Decidable **)

let deceq deq =
  deq

type coq_DecidableSumbool = bool

(** val decAsSumbool : coq_DecidableSumbool -> coq_Decidable **)

let decAsSumbool = function
| true -> true
| false -> false

type 't coq_DeqSumbool = 't -> 't -> coq_DecidableSumbool

(** val deceqSumbool :
    'a1 coq_DeqSumbool -> 'a1 -> 'a1 -> coq_DecidableSumbool **)

let deceqSumbool deqSumbool =
  deqSumbool

(** val deqAsSumbool : 'a1 coq_DeqSumbool -> 'a1 coq_Deq **)

let deqAsSumbool h a b =
  decAsSumbool (deceqSumbool h a b)

(** val deq_prod : 'a1 coq_Deq -> 'a2 coq_Deq -> ('a1 * 'a2) coq_Deq **)

let deq_prod h h0 x y =
  let (a, b) = x in
  let (a0, b0) = y in decide (coq_DecConj (deceq h a a0) (deceq h0 b b0))

(** val opExtract : 'a1 -> 'a1 option -> 'a1 **)

let opExtract def = function
| Some name -> name
| None -> def

(** val xor : bool -> bool -> bool **)

let xor b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val ascii_dec_bool : char -> char -> bool **)

let ascii_dec_bool a b =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
      (&&)
        ((&&) ((&&) (xor a0 b0) (xor a1 b1)) ((&&) (xor a2 b2) (xor a3 b3)))
        ((&&) ((&&) (xor a4 b4) (xor a5 b5)) ((&&) (xor a6 b6) (xor a7 b7))))
      b)
    a

(** val string_eq_bool : char list -> char list -> bool **)

let rec string_eq_bool a1 a2 =
  match a1 with
  | [] -> (match a2 with
           | [] -> true
           | _::_ -> false)
  | b::bs ->
    (match a2 with
     | [] -> false
     | c::cs -> (&&) (ascii_dec_bool b c) (string_eq_bool bs cs))

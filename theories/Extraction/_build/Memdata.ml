open AST
open Archi
open BinInt
open Coqlib0
open Datatypes
open Floats
open Integers
open List0
open PeanoNat
open Values

(** val size_chunk : memory_chunk -> int **)

let size_chunk = function
| Mint8signed -> 1
| Mint8unsigned -> 1
| Mint16signed -> ((fun p->2*p) 1)
| Mint16unsigned -> ((fun p->2*p) 1)
| Mint32 -> ((fun p->2*p) ((fun p->2*p) 1))
| Mfloat32 -> ((fun p->2*p) ((fun p->2*p) 1))
| Many32 -> ((fun p->2*p) ((fun p->2*p) 1))
| _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val size_chunk_nat : memory_chunk -> nat **)

let size_chunk_nat chunk =
  nat_of_Z (size_chunk chunk)

(** val align_chunk : memory_chunk -> int **)

let align_chunk = function
| Mint8signed -> 1
| Mint8unsigned -> 1
| Mint16signed -> ((fun p->2*p) 1)
| Mint16unsigned -> ((fun p->2*p) 1)
| Mint64 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| _ -> ((fun p->2*p) ((fun p->2*p) 1))

type quantity =
| Q32
| Q64

(** val quantity_eq : quantity -> quantity -> bool **)

let quantity_eq q1 q2 =
  match q1 with
  | Q32 -> (match q2 with
            | Q32 -> true
            | Q64 -> false)
  | Q64 -> (match q2 with
            | Q32 -> false
            | Q64 -> true)

(** val size_quantity_nat : quantity -> nat **)

let size_quantity_nat = function
| Q32 -> S (S (S (S O)))
| Q64 -> S (S (S (S (S (S (S (S O)))))))

type memval =
| Undef
| Byte of Byte.int
| Fragment of coq_val * quantity * nat

(** val bytes_of_int : nat -> int -> Byte.int list **)

let rec bytes_of_int n x =
  match n with
  | O -> []
  | S m ->
    (Byte.repr x) :: (bytes_of_int m
                       (Z.div x ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                         ((fun p->2*p) ((fun p->2*p) 1))))))))))

(** val int_of_bytes : Byte.int list -> int **)

let rec int_of_bytes = function
| [] -> 0
| b :: l' ->
  Z.add (Byte.unsigned b)
    (Z.mul (int_of_bytes l') ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      1)))))))))

(** val rev_if_be : Byte.int list -> Byte.int list **)

let rev_if_be l =
  if big_endian then rev l else l

(** val encode_int : nat -> int -> Byte.int list **)

let encode_int sz x =
  rev_if_be (bytes_of_int sz x)

(** val decode_int : Byte.int list -> int **)

let decode_int b =
  int_of_bytes (rev_if_be b)

(** val inj_bytes : Byte.int list -> memval list **)

let inj_bytes bl =
  map (fun x -> Byte x) bl

(** val proj_bytes : memval list -> Byte.int list option **)

let rec proj_bytes = function
| [] -> Some []
| m :: vl' ->
  (match m with
   | Byte b ->
     (match proj_bytes vl' with
      | Some bl -> Some (b :: bl)
      | None -> None)
   | _ -> None)

(** val inj_value_rec : nat -> coq_val -> quantity -> memval list **)

let rec inj_value_rec n v q =
  match n with
  | O -> []
  | S m -> (Fragment (v, q, m)) :: (inj_value_rec m v q)

(** val inj_value : quantity -> coq_val -> memval list **)

let inj_value q v =
  inj_value_rec (size_quantity_nat q) v q

(** val check_value : nat -> coq_val -> quantity -> memval list -> bool **)

let rec check_value n v q vl =
  match n with
  | O -> (match vl with
          | [] -> true
          | _ :: _ -> false)
  | S m ->
    (match vl with
     | [] -> false
     | m0 :: vl' ->
       (match m0 with
        | Fragment (v', q', m') ->
          (&&)
            ((&&)
              ((&&) ((fun x -> x) (Val.eq v v'))
                ((fun x -> x) (quantity_eq q q'))) (Nat.eqb m m'))
            (check_value m v q vl')
        | _ -> false))

(** val proj_value : quantity -> memval list -> coq_val **)

let proj_value q vl = match vl with
| [] -> Vundef
| m :: _ ->
  (match m with
   | Fragment (v, _, _) ->
     if check_value (size_quantity_nat q) v q vl then v else Vundef
   | _ -> Vundef)

(** val encode_val : memory_chunk -> coq_val -> memval list **)

let encode_val chunk v = match v with
| Vundef ->
  (match chunk with
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)
| Vint n ->
  (match chunk with
   | Mint8signed -> inj_bytes (encode_int (S O) (Int.unsigned n))
   | Mint8unsigned -> inj_bytes (encode_int (S O) (Int.unsigned n))
   | Mint16signed -> inj_bytes (encode_int (S (S O)) (Int.unsigned n))
   | Mint16unsigned -> inj_bytes (encode_int (S (S O)) (Int.unsigned n))
   | Mint32 -> inj_bytes (encode_int (S (S (S (S O)))) (Int.unsigned n))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)
| Vlong n ->
  (match chunk with
   | Mint64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O)))))))) (Int64.unsigned n))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)
| Vfloat n ->
  (match chunk with
   | Mfloat64 ->
     inj_bytes
       (encode_int (S (S (S (S (S (S (S (S O))))))))
         (Int64.unsigned (Float.to_bits n)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)
| Vsingle n ->
  (match chunk with
   | Mfloat32 ->
     inj_bytes
       (encode_int (S (S (S (S O)))) (Int.unsigned (Float32.to_bits n)))
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)
| Vptr (_, _) ->
  (match chunk with
   | Mint32 ->
     if ptr64 then list_repeat (S (S (S (S O)))) Undef else inj_value Q32 v
   | Mint64 ->
     if ptr64
     then inj_value Q64 v
     else list_repeat (S (S (S (S (S (S (S (S O)))))))) Undef
   | Many32 -> inj_value Q32 v
   | Many64 -> inj_value Q64 v
   | _ -> list_repeat (size_chunk_nat chunk) Undef)

(** val decode_val : memory_chunk -> memval list -> coq_val **)

let decode_val chunk vl =
  match proj_bytes vl with
  | Some bl ->
    (match chunk with
     | Mint8signed ->
       Vint
         (Int.sign_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
           (Int.repr (decode_int bl)))
     | Mint8unsigned ->
       Vint
         (Int.zero_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
           (Int.repr (decode_int bl)))
     | Mint16signed ->
       Vint
         (Int.sign_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) 1)))) (Int.repr (decode_int bl)))
     | Mint16unsigned ->
       Vint
         (Int.zero_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) 1)))) (Int.repr (decode_int bl)))
     | Mint32 -> Vint (Int.repr (decode_int bl))
     | Mint64 -> Vlong (Int64.repr (decode_int bl))
     | Mfloat32 -> Vsingle (Float32.of_bits (Int.repr (decode_int bl)))
     | Mfloat64 -> Vfloat (Float.of_bits (Int64.repr (decode_int bl)))
     | _ -> Vundef)
  | None ->
    (match chunk with
     | Mint32 ->
       if ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
     | Mint64 ->
       if ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
     | Many32 -> Val.load_result chunk (proj_value Q32 vl)
     | Many64 -> Val.load_result chunk (proj_value Q64 vl)
     | _ -> Vundef)

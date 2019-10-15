open AST
open Archi
open BinInt
open Coqlib0
open Datatypes
open Floats
open Integers

type block = int

(** val eq_block : int -> int -> bool **)

let eq_block =
  peq

type coq_val =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

(** val coq_Vzero : coq_val **)

let coq_Vzero =
  Vint Int.zero

(** val coq_Vone : coq_val **)

let coq_Vone =
  Vint Int.one

(** val coq_Vtrue : coq_val **)

let coq_Vtrue =
  Vint Int.one

(** val coq_Vfalse : coq_val **)

let coq_Vfalse =
  Vint Int.zero

(** val coq_Vptrofs : Ptrofs.int -> coq_val **)

let coq_Vptrofs n =
  if ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n)

module Val =
 struct
  (** val eq : coq_val -> coq_val -> bool **)

  let eq x y =
    match x with
    | Vundef -> (match y with
                 | Vundef -> true
                 | _ -> false)
    | Vint x0 -> (match y with
                  | Vint i0 -> Int.eq_dec x0 i0
                  | _ -> false)
    | Vlong x0 -> (match y with
                   | Vlong i0 -> Int64.eq_dec x0 i0
                   | _ -> false)
    | Vfloat x0 -> (match y with
                    | Vfloat f0 -> Float.eq_dec x0 f0
                    | _ -> false)
    | Vsingle x0 ->
      (match y with
       | Vsingle f0 -> Float32.eq_dec x0 f0
       | _ -> false)
    | Vptr (x0, x1) ->
      (match y with
       | Vptr (b0, i0) ->
         if eq_block x0 b0 then Ptrofs.eq_dec x1 i0 else false
       | _ -> false)

  (** val of_bool : bool -> coq_val **)

  let of_bool = function
  | true -> coq_Vtrue
  | false -> coq_Vfalse

  (** val cmp_different_blocks : comparison -> bool option **)

  let cmp_different_blocks = function
  | Ceq -> Some false
  | Cne -> Some true
  | _ -> None

  (** val cmpu_bool :
      (block -> int -> bool) -> comparison -> coq_val -> coq_val -> bool
      option **)

  let cmpu_bool valid_ptr =
    let weak_valid_ptr = fun b ofs ->
      (||) (valid_ptr b ofs) (valid_ptr b (Z.sub ofs 1))
    in
    (fun c v1 v2 ->
    match v1 with
    | Vint n1 ->
      (match v2 with
       | Vint n2 -> Some (Int.cmpu c n1 n2)
       | Vptr (b2, ofs2) ->
         if ptr64
         then None
         else if (&&) (Int.eq n1 Int.zero)
                   (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
              then cmp_different_blocks c
              else None
       | _ -> None)
    | Vptr (b1, ofs1) ->
      (match v2 with
       | Vint n2 ->
         if ptr64
         then None
         else if (&&) (Int.eq n2 Int.zero)
                   (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
              then cmp_different_blocks c
              else None
       | Vptr (b2, ofs2) ->
         if ptr64
         then None
         else if eq_block b1 b2
              then if (&&) (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then Some (Ptrofs.cmpu c ofs1 ofs2)
                   else None
              else if (&&) (valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then cmp_different_blocks c
                   else None
       | _ -> None)
    | _ -> None)

  (** val cmplu_bool :
      (block -> int -> bool) -> comparison -> coq_val -> coq_val -> bool
      option **)

  let cmplu_bool valid_ptr =
    let weak_valid_ptr = fun b ofs ->
      (||) (valid_ptr b ofs) (valid_ptr b (Z.sub ofs 1))
    in
    (fun c v1 v2 ->
    match v1 with
    | Vlong n1 ->
      (match v2 with
       | Vlong n2 -> Some (Int64.cmpu c n1 n2)
       | Vptr (b2, ofs2) ->
         if negb ptr64
         then None
         else if (&&) (Int64.eq n1 Int64.zero)
                   (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
              then cmp_different_blocks c
              else None
       | _ -> None)
    | Vptr (b1, ofs1) ->
      (match v2 with
       | Vlong n2 ->
         if negb ptr64
         then None
         else if (&&) (Int64.eq n2 Int64.zero)
                   (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
              then cmp_different_blocks c
              else None
       | Vptr (b2, ofs2) ->
         if negb ptr64
         then None
         else if eq_block b1 b2
              then if (&&) (weak_valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then Some (Ptrofs.cmpu c ofs1 ofs2)
                   else None
              else if (&&) (valid_ptr b1 (Ptrofs.unsigned ofs1))
                        (valid_ptr b2 (Ptrofs.unsigned ofs2))
                   then cmp_different_blocks c
                   else None
       | _ -> None)
    | _ -> None)

  (** val load_result : memory_chunk -> coq_val -> coq_val **)

  let load_result chunk v =
    match chunk with
    | Mint8signed ->
      (match v with
       | Vint n ->
         Vint (Int.sign_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) n)
       | _ -> Vundef)
    | Mint8unsigned ->
      (match v with
       | Vint n ->
         Vint (Int.zero_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) n)
       | _ -> Vundef)
    | Mint16signed ->
      (match v with
       | Vint n ->
         Vint
           (Int.sign_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
             ((fun p->2*p) 1)))) n)
       | _ -> Vundef)
    | Mint16unsigned ->
      (match v with
       | Vint n ->
         Vint
           (Int.zero_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
             ((fun p->2*p) 1)))) n)
       | _ -> Vundef)
    | Mint32 ->
      (match v with
       | Vint n -> Vint n
       | Vptr (b, ofs) -> if ptr64 then Vundef else Vptr (b, ofs)
       | _ -> Vundef)
    | Mint64 ->
      (match v with
       | Vlong n -> Vlong n
       | Vptr (b, ofs) -> if ptr64 then Vptr (b, ofs) else Vundef
       | _ -> Vundef)
    | Mfloat32 -> (match v with
                   | Vsingle f -> Vsingle f
                   | _ -> Vundef)
    | Mfloat64 -> (match v with
                   | Vfloat f -> Vfloat f
                   | _ -> Vundef)
    | Many32 ->
      (match v with
       | Vint _ -> v
       | Vsingle _ -> v
       | Vptr (_, _) -> if ptr64 then Vundef else v
       | _ -> Vundef)
    | Many64 -> v
 end

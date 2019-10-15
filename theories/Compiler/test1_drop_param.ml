
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | [] -> m0
  | a :: l1 -> a :: (app l1 m0)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : unit -> unit **)

let norm d =
  (fun _ _ _ -> assert false)
    (fun d0 -> (fun _ -> ()) (unorm d0))
    (fun d0 ->
    match nzhead d0 with
    | Nil -> (fun _ -> ()) (D0 Nil)
    | x -> (fun _ -> ()) x)
    d

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)

  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

(** val eqb : int -> int -> bool **)

let rec eqb n m0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      m0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> eqb n' m')
      m0)
    n

(** val leb : int -> int -> bool **)

let rec leb n m0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m0)
    n

(** val ltb : int -> int -> bool **)

let ltb n m0 =
  leb (Pervasives.succ n) m0



(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module Nat =
 struct
  type t = int

  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    Pervasives.succ 0

  (** val two : int **)

  let two =
    Pervasives.succ (Pervasives.succ 0)

  (** val succ : int -> int **)

  let succ x =
    Pervasives.succ x

  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val add : int -> int -> int **)

  let rec add n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m0)
      (fun p -> Pervasives.succ (add p m0))
      n

  (** val double : int -> int **)

  let double n =
    add n n

  (** val mul : int -> int -> int **)

  let rec mul n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m0 (mul p m0))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m0)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m0 =
    (<=) (Pervasives.succ n) m0

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Pervasives.succ (max n' m'))
        m0)
      n

  (** val min : int -> int -> int **)

  let rec min n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> Pervasives.succ (min n' m'))
        m0)
      n

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

  (** val pow : int -> int -> int **)

  let rec pow n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m1 -> mul n (pow n m1))
      m0

  (** val tail_add : int -> int -> int **)

  let rec tail_add n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m0)
      (fun n0 -> tail_add n0 (Pervasives.succ m0))
      n

  (** val tail_addmul : int -> int -> int -> int **)

  let rec tail_addmul r n m0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> r)
      (fun n0 -> tail_addmul (tail_add m0 r) n0 m0)
      n

  (** val tail_mul : int -> int -> int **)

  let tail_mul n m0 =
    tail_addmul 0 n m0

  (** val of_uint_acc : uint -> int -> int **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 d0 ->
      of_uint_acc d0
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc)
    | D1 d0 ->
      of_uint_acc d0 (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc))
    | D2 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))
    | D3 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))
    | D4 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))
    | D5 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))
    | D6 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))))
    | D7 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))))
    | D8 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))))))
    | D9 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))))))

  (** val of_uint : uint -> int **)

  let of_uint d =
    of_uint_acc d 0

  (** val to_little_uint : int -> uint -> uint **)

  let rec to_little_uint n acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> acc)
      (fun n0 -> to_little_uint n0 (Little.succ acc))
      n

  (** val to_uint : int -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil))

  (** val of_int : unit -> int option **)

  let of_int d =
    (fun _ _ _ -> assert false)
      (fun u -> Some (of_uint u))
      (fun _ -> None)
      (norm d)

  (** val to_int : int -> unit **)

  let to_int n =
    (fun _ -> ()) (to_uint n)

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y

  (** val gcd : int -> int -> int **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (Pervasives.succ a')) (Pervasives.succ a'))
      a

  (** val square : int -> int **)

  let square n =
    mul n n

  (** val sqrt_iter : int -> int -> int -> int -> int **)

  let rec sqrt_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        sqrt_iter k' (Pervasives.succ p) (Pervasives.succ (Pervasives.succ q))
          (Pervasives.succ (Pervasives.succ q)))
        (fun r' -> sqrt_iter k' p q r')
        r)
      k

  (** val sqrt : int -> int **)

  let sqrt n =
    sqrt_iter n 0 0 0

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> log2_iter k' (Pervasives.succ p) (Pervasives.succ q) q)
        (fun r' -> log2_iter k' p (Pervasives.succ q) r')
        r)
      k

  (** val log2 : int -> int **)

  let log2 n =
    log2_iter (pred n) 0 (Pervasives.succ 0) 0

  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n f x =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n0 -> f (iter n0 f x))
      n

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val testbit : int -> int -> bool **)

  let rec testbit a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> odd a)
      (fun n0 -> testbit (div2 a) n0)
      n

  (** val shiftl : int -> int -> int **)

  let rec shiftl a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> double (shiftl a n0))
      n

  (** val shiftr : int -> int -> int **)

  let rec shiftr a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> div2 (shiftr a n0))
      n

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then Pervasives.succ 0 else 0)
        (mul (Pervasives.succ (Pervasives.succ 0)) (bitwise op n' (div2 a) (div2 b))))
      n

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    bitwise (&&) a a b

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    bitwise (||) (max a b) a b

  (** val ldiff : int -> int -> int **)

  let ldiff a b =
    bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let rec recursion x f n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n0 -> f n0 (recursion x f n0))
      n

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect ((<=) x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
        'a1 **)

    let max_case_strong n m0 compat hl hr =
      let c = compSpec2Type n m0 (compare n m0) in
      (match c with
       | CompGtT -> compat n (max n m0) __ (hl __)
       | _ -> compat m0 (max n m0) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m0 x x0 x1 =
      max_case_strong n m0 x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m0 =
      max_case n m0 (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
        'a1 **)

    let min_case_strong n m0 compat hl hr =
      let c = compSpec2Type n m0 (compare n m0) in
      (match c with
       | CompGtT -> compat m0 (min n m0) __ (hr __)
       | _ -> compat n (min n m0) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m0 x x0 x1 =
      min_case_strong n m0 x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m0 =
      min_case n m0 (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m0 x x0 =
    Private_Dec.max_case_strong n m0 (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m0 x x0 =
    max_case_strong n m0 (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m0 x x0 =
    Private_Dec.min_case_strong n m0 (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m0 x x0 =
    min_case_strong n m0 (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : int -> int **)

  let sqrt_up a =
    match compare 0 a with
    | Lt -> Pervasives.succ (sqrt (pred a))
    | _ -> 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0

  module Private_NZDiv =
   struct
   end

  (** val lcm : int -> int -> int **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect ((=) x y)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> Pervasives.succ 0
  | false -> 0

  (** val setbit : int -> int -> int **)

  let setbit a n =
    coq_lor a (shiftl (Pervasives.succ 0) n)

  (** val clearbit : int -> int -> int **)

  let clearbit a n =
    ldiff a (shiftl (Pervasives.succ 0) n)

  (** val ones : int -> int **)

  let ones n =
    pred (shiftl (Pervasives.succ 0) n)

  (** val lnot : int -> int -> int **)

  let lnot a n =
    coq_lxor a (ones n)
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  type t = int

  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred : int -> int **)

  let pred = fun n -> Pervasives.max 1 (n-1)

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
  | IsPos q ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsNul)
       q)
  | _ -> IsNeg

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val square : int -> int **)

  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p) (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p) (square p0)))
      (fun _ -> 1)
      p

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Pervasives.succ (size_nat p0))
      (fun p0 -> Pervasives.succ (size_nat p0))
      (fun _ -> Pervasives.succ 0)
      p

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val min : int -> int -> int **)

  let min = Pervasives.min

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step : (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ -> (((fun p->2*p) s), (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val sqrtrem : int -> int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x) (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x) (sqrtrem p1))
        (fun _ -> (1, (IsPos 1)))
        p0)
      (fun _ -> (1, IsNul))
      p

  (** val sqrt : int -> int **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : int -> int -> int -> int **)

  let rec gcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 -> gcdn n0 a b0)
          (fun _ -> 1)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> gcdn n0 a0 b)
          (fun b0 -> (fun p->2*p) (gcdn n0 a0 b0))
          (fun _ -> 1)
          b)
        (fun _ -> 1)
        a)
      n

  (** val gcd : int -> int -> int **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 -> let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val shiftl_nat : int -> int -> int **)

  let rec shiftl_nat p n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun n0 -> (fun p->2*p) (shiftl_nat p n0))
      n

  (** val shiftr_nat : int -> int -> int **)

  let rec shiftr_nat p n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun n0 -> div2 (shiftr_nat p n0))
      n

  (** val shiftl : int -> int -> int **)

  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter (fun x -> (fun p->2*p) x) p n0)
      n

  (** val shiftr : int -> int -> int **)

  let shiftr p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter div2 p n0)
      n

  (** val testbit_nat : int -> int -> bool **)

  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val testbit : int -> int -> bool **)

  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Pervasives.succ 0)

  (** val of_nat : int -> int **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 1)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n

  (** val of_uint_acc : uint -> int -> int **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l -> of_uint_acc l (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc)
    | D1 l ->
      of_uint_acc l (add 1 (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D2 l ->
      of_uint_acc l
        (add ((fun p->2*p) 1) (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D3 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) 1)
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D4 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D5 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D6 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D7 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D8 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D9 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))

  (** val of_uint : uint -> int **)

  let rec of_uint = function
  | Nil -> 0
  | D0 l -> of_uint l
  | D1 l -> (of_uint_acc l 1)
  | D2 l -> (of_uint_acc l ((fun p->2*p) 1))
  | D3 l -> (of_uint_acc l ((fun p->1+2*p) 1))
  | D4 l -> (of_uint_acc l ((fun p->2*p) ((fun p->2*p) 1)))
  | D5 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) 1)))
  | D6 l -> (of_uint_acc l ((fun p->2*p) ((fun p->1+2*p) 1)))
  | D7 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) 1)))
  | D8 l -> (of_uint_acc l ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
  | D9 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))

  (** val of_int : unit -> int option **)

  let of_int d =
    (fun _ _ _ -> assert false)
      (fun d0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> None)
        (fun p -> Some p)
        (of_uint d0))
      (fun _ -> None)
      d

  (** val to_little_uint : int -> uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Little.succ_double (to_little_uint p0))
      (fun p0 -> Little.double (to_little_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_uint : int -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val to_int : int -> unit **)

  let to_int n =
    (fun _ -> ()) (to_uint n)

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p

  (** val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let rec peano_rect a f p =
    let f2 =
      peano_rect (f 1 a) (fun p0 x -> f (succ ((fun p->2*p) p0)) (f ((fun p->2*p) p0) x))
    in
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun q -> f ((fun p->2*p) q) (f2 q))
       (fun q -> f2 q)
       (fun _ -> a)
       p)

  (** val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rec =
    peano_rect

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView

  (** val coq_PeanoView_rect :
      'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rect f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rect f f0 p0 p1)

  (** val coq_PeanoView_rec :
      'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rec f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rec f f0 p0 p1)

  (** val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xO _ = function
  | PeanoOne -> PeanoSucc (1, PeanoOne)
  | PeanoSucc (p, q0) ->
    PeanoSucc ((succ ((fun p->2*p) p)), (PeanoSucc (((fun p->2*p) p),
      (peanoView_xO p q0))))

  (** val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xI _ = function
  | PeanoOne -> PeanoSucc ((succ 1), (PeanoSucc (1, PeanoOne)))
  | PeanoSucc (p, q0) ->
    PeanoSucc ((succ ((fun p->1+2*p) p)), (PeanoSucc (((fun p->1+2*p) p),
      (peanoView_xI p q0))))

  (** val peanoView : int -> coq_PeanoView **)

  let rec peanoView p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> peanoView_xI p0 (peanoView p0))
      (fun p0 -> peanoView_xO p0 (peanoView p0))
      (fun _ -> PeanoOne)
      p

  (** val coq_PeanoView_iter :
      'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_iter a f _ = function
  | PeanoOne -> a
  | PeanoSucc (p, q0) -> f p (coq_PeanoView_iter a f p q0)

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val switch_Eq : comparison -> comparison -> comparison **)

  let switch_Eq c = function
  | Eq -> c
  | x -> x

  (** val mask2cmp : mask -> comparison **)

  let mask2cmp = function
  | IsNul -> Eq
  | IsPos _ -> Gt
  | IsNeg -> Lt

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
        'a1 **)

    let max_case_strong n m0 compat hl hr =
      let c = compSpec2Type n m0 (compare n m0) in
      (match c with
       | CompGtT -> compat n (max n m0) __ (hl __)
       | _ -> compat m0 (max n m0) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m0 x x0 x1 =
      max_case_strong n m0 x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m0 =
      max_case n m0 (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
        'a1 **)

    let min_case_strong n m0 compat hl hr =
      let c = compSpec2Type n m0 (compare n m0) in
      (match c with
       | CompGtT -> compat m0 (min n m0) __ (hr __)
       | _ -> compat n (min n m0) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m0 x x0 x1 =
      min_case_strong n m0 x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m0 =
      min_case n m0 (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m0 x x0 =
    Private_Dec.max_case_strong n m0 (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m0 x x0 =
    max_case_strong n m0 (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m0 x x0 =
    Private_Dec.min_case_strong n m0 (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m0 x x0 =
    min_case_strong n m0 (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec
 end

module N =
 struct
  (** val succ : int -> int **)

  let succ = Pervasives.succ

  (** val succ_pos : int -> int **)

  let succ_pos n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Coq_Pos.succ p)
      n

  (** val add : int -> int -> int **)

  let add = (+)

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 0 (n-m)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Coq_Pos.of_succ_nat n'))
      n

  (** val eq_dec : int -> int -> bool **)

  let eq_dec n m0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m0)
      (fun x ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x p0)
        m0)
      n
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m0 -> match l with
               | [] -> default
               | _ :: t0 -> nth m0 t0 default)
    n

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append l0 (a :: l')

module Coq__2 = struct
 (** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)
 let rec map f = function
 | [] -> []
 | a :: t0 -> (f a) :: (map f t0)
end
include Coq__2

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl -> (match l' with
                | [] -> []
                | y :: tl' -> (x, y) :: (combine tl tl'))

(** val zero0 : char **)

let zero0 = '\000'

(** val one0 : char **)

let one0 = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero0)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one0)
        p)
      n
  in loop (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero0)
    (fun p -> ascii_of_pos p)
    n

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' -> N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type 'a exception0 =
| Exc of char list
| Ret of 'a

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

type ident = char list

type kername = char list

type name =
| NAnon
| NNamed of ident

type inductive = { inductive_mind : kername; inductive_ind : int }

module Coq_Nat = Nat

type 'a eq = 'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Eq *)

(** val eq_dec0 : 'a1 eq -> 'a1 -> 'a1 -> bool **)

let eq_dec0 eq0 =
  eq0

(** val inductive_dec : inductive -> inductive -> bool **)

let inductive_dec s1 s2 =
  let { inductive_mind = mind; inductive_ind = i } = s1 in
  let { inductive_mind = mind'; inductive_ind = i' } = s2 in
  let s = string_dec mind mind' in if s then (=) i i' else false

(** val nEq : int eq **)

let nEq =
  N.eq_dec

type cnstr = { cnstrNm : char list; cnstrArity : int }

type ityp = { itypNm : char list; itypCnstrs : cnstr list }

type itypPack = ityp list

type 'm monad = { ret : (__ -> __ -> 'm); bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 monad -> 'a2 -> 'a1 **)

let ret monad0 x =
  let { ret = ret0; bind = _ } = monad0 in Obj.magic ret0 __ x

(** val bind : 'a1 monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad0 x x0 =
  let { ret = _; bind = bind0 } = monad0 in Obj.magic bind0 __ __ x x0

type 'm pMonad = { pret : (__ -> __ -> __ -> 'm);
                   pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) monP = __

(** val pbind : 'a1 pMonad -> ('a1, 'a3) monP -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let pbind pMonad0 pu x x0 =
  let { pret = _; pbind = pbind0 } = pMonad0 in Obj.magic pbind0 __ __ pu x x0

(** val pMonad_Monad : 'a1 monad -> 'a1 pMonad **)

let pMonad_Monad m0 =
  { pret = (fun _ -> Obj.magic (fun _ x -> ret m0 x)); pbind = (fun _ _ ->
    Obj.magic (fun _ c f -> bind m0 c f)) }

type ('t, 'm) monadState = { get : 'm; put : ('t -> 'm) }

(** val get : ('a1, 'a2) monadState -> 'a2 **)

let get x = x.get

(** val put : ('a1, 'a2) monadState -> 'a1 -> 'a2 **)

let put x = x.put

type ('src, 'dst) certicoqTranslation = 'src -> 'dst exception0

module Positive_as_OT = Coq_Pos

type ('term, 'value) cTerm = 'term

(** val monad_option : __ option monad **)

let monad_option =
  { ret = (Obj.magic (fun _ x -> Some x)); bind = (fun _ _ c1 c2 ->
    match c1 with
    | Some v -> c2 v
    | None -> None) }

type ienv = (char list * itypPack) list

type ('t, 'classType) varClass = 't -> 'classType

(** val varClass0 : ('a1, 'a2) varClass -> 'a1 -> 'a2 **)

let varClass0 varClass1 =
  varClass1

type ('nVar, 'opid) nTerm =
| Vterm of 'nVar
| Oterm of 'opid * ('nVar, 'opid) bTerm list
and ('nVar, 'opid) bTerm =
| Bterm of 'nVar list * ('nVar, 'opid) nTerm

(** val getVar : ('a1, 'a2) nTerm -> 'a1 option **)

let getVar = function
| Vterm v -> Some v
| Oterm (_, _) -> None

type dcon = inductive * int

(** val digit2ascii : int -> char **)

let digit2ascii n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> '0')
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> '1')
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> '2')
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> '3')
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> '4')
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> '5')
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> '6')
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> '7')
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> '8')
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> '9')
                      (fun _ ->
                      ascii_of_nat
                        (add
                          (sub n (Pervasives.succ (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ 0))))))))))) (nat_of_ascii 'A')))
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    n

(** val nat2string : int -> int -> char list **)

let rec nat2string modulus x =
  if Coq_Nat.ltb x modulus
  then (digit2ascii x)::[]
  else let m0 = Coq_Nat.div x modulus in
       append (nat2string modulus m0) ((digit2ascii (sub x (mul modulus m0)))::[])

(** val nat2string10 : int -> char list **)

let nat2string10 =
  nat2string (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))

type l5Opid =
| CLambda
| CKLambda
| CLet
| CFix of int * int
| CDCon of dcon * int
| CHalt
| CRet
| CCall
| CMatch of (dcon * int) list

(** val varClassP : (int, bool) varClass **)

let varClassP p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun _ -> false)
    (fun _ -> true)
    (fun _ -> false)
    p

(** val varClassNVar : ('a1, 'a3) varClass -> ('a1 * 'a2, 'a3) varClass **)

let varClassNVar =  (fun f (p:int*bool) -> varClass0 (f (fst p)))

type nVar = int * name

(** val varClassNVar0 : (nVar, bool) varClass **)

let varClassNVar0 =
  varClassNVar varClassP

type ('s, 't) state =
  's -> 't * 's
  (* singleton inductive, whose constructor was mkState *)

(** val runState : ('a1, 'a2) state -> 'a1 -> 'a2 * 'a1 **)

let runState s =
  s

(** val monad_state : ('a1, __) state monad **)

let monad_state =
  { ret = (fun _ v s -> (v, s)); bind = (fun _ _ c1 c2 s ->
    let (v, s0) = runState c1 s in runState (c2 v) s0) }

(** val monadState_state : ('a1, ('a1, __) state) monadState **)

let monadState_state =
  { get = (fun x -> ((Obj.magic x), x)); put = (fun v _ -> ((Obj.magic ()), v)) }

(** val peq : int -> int -> bool **)

let peq =
  Coq_Pos.eq_dec

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

(** val fromN : int -> int -> int list **)

let rec fromN n m0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m' -> n :: (fromN (N.succ n) m'))
    m0

(** val nthN : 'a1 list -> int -> 'a1 option **)

let rec nthN al n =
  match al with
  | [] -> None
  | a :: al' ->
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> Some a)
       (fun _ -> nthN al' (N.sub n 1))
       n)

(** val max_list : int list -> int -> int **)

let rec max_list ls acc =
  match ls with
  | [] -> acc
  | x :: xs -> max_list xs (Coq_Pos.max x acc)

module PTree =
 struct
  type elt = int

  (** val elt_eq : int -> int -> bool **)

  let elt_eq =
    peq

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val get : int -> 'a1 t -> 'a1 option **)

  let rec get i = function
  | Leaf -> None
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> get ii r)
       (fun ii -> get ii l)
       (fun _ -> o)
       i)

  (** val set : int -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec set i v = function
  | Leaf ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> Node (Leaf, None, (set ii v Leaf)))
       (fun ii -> Node ((set ii v Leaf), None, Leaf))
       (fun _ -> Node (Leaf, (Some v), Leaf))
       i)
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> Node (l, o, (set ii v r)))
       (fun ii -> Node ((set ii v l), o, r))
       (fun _ -> Node (l, (Some v), r))
       i)

  (** val remove : int -> 'a1 t -> 'a1 t **)

  let rec remove i m0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun ii ->
      match m0 with
      | Leaf -> Leaf
      | Node (l, o, r) ->
        (match l with
         | Leaf ->
           (match o with
            | Some _ -> Node (l, o, (remove ii r))
            | None ->
              (match remove ii r with
               | Leaf -> Leaf
               | Node (t0, o0, t1) -> Node (Leaf, None, (Node (t0, o0, t1)))))
         | Node (_, _, _) -> Node (l, o, (remove ii r))))
      (fun ii ->
      match m0 with
      | Leaf -> Leaf
      | Node (l, o, r) ->
        (match o with
         | Some _ -> Node ((remove ii l), o, r)
         | None ->
           (match r with
            | Leaf ->
              (match remove ii l with
               | Leaf -> Leaf
               | Node (t0, o0, t1) -> Node ((Node (t0, o0, t1)), None, Leaf))
            | Node (_, _, _) -> Node ((remove ii l), o, r))))
      (fun _ ->
      match m0 with
      | Leaf -> Leaf
      | Node (l, _, r) ->
        (match l with
         | Leaf -> (match r with
                    | Leaf -> Leaf
                    | Node (_, _, _) -> Node (l, None, r))
         | Node (_, _, _) -> Node (l, None, r)))
      i

  (** val bempty : 'a1 t -> bool **)

  let rec bempty = function
  | Leaf -> true
  | Node (l, o, r) -> (match o with
                       | Some _ -> false
                       | None -> (&&) (bempty l) (bempty r))

  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec beq beqA m1 m2 =
    match m1 with
    | Leaf -> bempty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> bempty m1
       | Node (l2, o2, r2) ->
         (&&)
           ((&&)
             (match o1 with
              | Some y1 -> (match o2 with
                            | Some y2 -> beqA y1 y2
                            | None -> false)
              | None -> (match o2 with
                         | Some _ -> false
                         | None -> true)) (beq beqA l1 l2)) (beq beqA r1 r2))

  (** val prev_append : int -> int -> int **)

  let rec prev_append i j =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun i' -> prev_append i' ((fun p->1+2*p) j))
      (fun i' -> prev_append i' ((fun p->2*p) j))
      (fun _ -> j)
      i

  (** val prev : int -> int **)

  let prev i =
    prev_append i 1

  (** val xmap : (int -> 'a1 -> 'a2) -> 'a1 t -> int -> 'a2 t **)

  let rec xmap f m0 i =
    match m0 with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l ((fun p->2*p) i)),
        (match o with
         | Some x -> Some (f (prev i) x)
         | None -> None), (xmap f r ((fun p->1+2*p) i)))

  (** val map : (int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m0 =
    xmap f m0 1

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map1 f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((map1 f l), (option_map f o), (map1 f r))

  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)

  let coq_Node' l x r =
    match l with
    | Leaf ->
      (match x with
       | Some _ -> Node (l, x, r)
       | None -> (match r with
                  | Leaf -> Leaf
                  | Node (_, _, _) -> Node (l, x, r)))
    | Node (_, _, _) -> Node (l, x, r)

  (** val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t **)

  let rec filter1 pred0 = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    let o' = match o with
             | Some x -> if pred0 x then o else None
             | None -> None in
    coq_Node' (filter1 pred0 l) o' (filter1 pred0 r)

  (** val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec xcombine_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)

  (** val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec xcombine_r f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_r f l) (f None o) (xcombine_r f r)

  (** val combine :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec combine f m1 m2 =
    match m1 with
    | Leaf -> xcombine_r f m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xcombine_l f m1
       | Node (l2, o2, r2) -> coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))

  (** val xelements : 'a1 t -> int -> (int * 'a1) list -> (int * 'a1) list **)

  let rec xelements m0 i k =
    match m0 with
    | Leaf -> k
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         xelements l ((fun p->2*p) i) (((prev i),
           x) :: (xelements r ((fun p->1+2*p) i) k))
       | None -> xelements l ((fun p->2*p) i) (xelements r ((fun p->1+2*p) i) k))

  (** val elements : 'a1 t -> (int * 'a1) list **)

  let elements m0 =
    xelements m0 1 []

  (** val xkeys : 'a1 t -> int -> int list **)

  let xkeys m0 i =
    Coq__2.map fst (xelements m0 i [])

  (** val xfold : ('a2 -> int -> 'a1 -> 'a2) -> int -> 'a1 t -> 'a2 -> 'a2 **)

  let rec xfold f i m0 v =
    match m0 with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         let v1 = xfold f ((fun p->2*p) i) l v in
         let v2 = f v1 (prev i) x in xfold f ((fun p->1+2*p) i) r v2
       | None -> let v1 = xfold f ((fun p->2*p) i) l v in xfold f ((fun p->1+2*p) i) r v1)

  (** val fold : ('a2 -> int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m0 v =
    xfold f 1 m0 v

  (** val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold1 f m0 v =
    match m0 with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x -> let v1 = fold1 f l v in let v2 = f v1 x in fold1 f r v2
       | None -> let v1 = fold1 f l v in fold1 f r v1)
 end

module M = PTree

type var = M.elt

type fTag = M.elt

type iTag = M.elt

type cTag = M.elt

type prim = M.elt

(** val findtag : (cTag * 'a1) list -> cTag -> 'a1 option **)

let rec findtag cl c =
  match cl with
  | [] -> None
  | p :: cl' -> let (c', a) = p in if M.elt_eq c' c then Some a else findtag cl' c

type exp =
| Econstr of var * cTag * var list * exp
| Ecase of var * (cTag * exp) list
| Eproj of var * cTag * int * var * exp
| Efun of fundefs * exp
| Eapp of var * fTag * var list
| Eprim of var * prim * var list * exp
| Ehalt of var
and fundefs =
| Fcons of var * fTag * var list * exp * fundefs
| Fnil

type val0 =
| Vconstr of cTag * val0 list
| Vfun of val0 M.t * fundefs * var
| Vint of int

type cTyInfo = (((name * name) * iTag) * int) * int

type iTyInfo = (cTag * int) list

type cEnv = cTyInfo M.t

type iEnv = iTyInfo M.t

(** val add_cloTag : int -> int -> cEnv -> cEnv **)

let add_cloTag c i cenv0 =
  M.set c ((((NAnon, NAnon), i), ((fun p->2*p) 1)), 0) cenv0

type fTyInfo = int * int list

type fEnv = fTyInfo M.t

type l5Term = (nVar, l5Opid) nTerm

type color =
| Red
| Black

module Color =
 struct
  type t = color
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw =
   struct
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    (** val empty : tree **)

    let empty =
      Leaf

    (** val is_empty : tree -> bool **)

    let is_empty = function
    | Leaf -> true
    | Node (_, _, _, _) -> false

    (** val mem : X.t -> tree -> bool **)

    let rec mem x = function
    | Leaf -> false
    | Node (_, l, k, r) ->
      (match X.compare x k with
       | Eq -> true
       | Lt -> mem x l
       | Gt -> mem x r)

    (** val min_elt : tree -> elt option **)

    let rec min_elt = function
    | Leaf -> None
    | Node (_, l, x, _) -> (match l with
                            | Leaf -> Some x
                            | Node (_, _, _, _) -> min_elt l)

    (** val max_elt : tree -> elt option **)

    let rec max_elt = function
    | Leaf -> None
    | Node (_, _, x, r) -> (match r with
                            | Leaf -> Some x
                            | Node (_, _, _, _) -> max_elt r)

    (** val choose : tree -> elt option **)

    let choose =
      min_elt

    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

    let rec fold f t0 base =
      match t0 with
      | Leaf -> base
      | Node (_, l, x, r) -> fold f r (f x (fold f l base))

    (** val elements_aux : X.t list -> tree -> X.t list **)

    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

    (** val elements : tree -> X.t list **)

    let elements =
      elements_aux []

    (** val rev_elements_aux : X.t list -> tree -> X.t list **)

    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

    (** val rev_elements : tree -> X.t list **)

    let rev_elements =
      rev_elements_aux []

    (** val cardinal : tree -> int **)

    let rec cardinal = function
    | Leaf -> 0
    | Node (_, l, _, r) -> Pervasives.succ (add (cardinal l) (cardinal r))

    (** val maxdepth : tree -> int **)

    let rec maxdepth = function
    | Leaf -> 0
    | Node (_, l, _, r) -> Pervasives.succ (Pervasives.max (maxdepth l) (maxdepth r))

    (** val mindepth : tree -> int **)

    let rec mindepth = function
    | Leaf -> 0
    | Node (_, l, _, r) -> Pervasives.succ (Pervasives.min (mindepth l) (mindepth r))

    (** val for_all : (elt -> bool) -> tree -> bool **)

    let rec for_all f = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      if if f x then for_all f l else false then for_all f r else false

    (** val exists_ : (elt -> bool) -> tree -> bool **)

    let rec exists_ f = function
    | Leaf -> false
    | Node (_, l, x, r) ->
      if if f x then true else exists_ f l then true else exists_ f r

    type enumeration =
    | End
    | More of elt * tree * enumeration

    (** val cons : tree -> enumeration -> enumeration **)

    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (_, l, x, r) -> cons l (More (x, r, e))

    (** val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) -> (match X.compare x1 x2 with
                            | Eq -> cont (cons r2 e3)
                            | x -> x)

    (** val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison **)

    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (_, l1, x1, r1) ->
        compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

    (** val compare_end : enumeration -> comparison **)

    let compare_end = function
    | End -> Eq
    | More (_, _, _) -> Lt

    (** val compare : tree -> tree -> comparison **)

    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)

    (** val equal : tree -> tree -> bool **)

    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> true
      | _ -> false

    (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> if mem x1 r2 then subset_l1 s2 else false)

    (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> if mem x1 l2 then subset_r1 s2 else false
       | Gt -> subsetr subset_r1 x1 r2)

    (** val subset : tree -> tree -> bool **)

    let rec subset s1 s2 =
      match s1 with
      | Leaf -> true
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> false
         | Node (_, l2, x2, r2) ->
           (match X.compare x1 x2 with
            | Eq -> if subset l1 l2 then subset r1 r2 else false
            | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
            | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

    type t = tree

    (** val singleton : elt -> tree **)

    let singleton k =
      Node (Black, Leaf, k, Leaf)

    (** val makeBlack : tree -> tree **)

    let makeBlack = function
    | Leaf -> Leaf
    | Node (_, a, x, b) -> Node (Black, a, x, b)

    (** val makeRed : tree -> tree **)

    let makeRed = function
    | Leaf -> Leaf
    | Node (_, a, x, b) -> Node (Red, a, x, b)

    (** val lbal : tree -> X.t -> tree -> tree **)

    let lbal l k r =
      match l with
      | Leaf -> Node (Black, l, k, r)
      | Node (t0, a, x, c) ->
        (match t0 with
         | Red ->
           (match a with
            | Leaf ->
              (match c with
               | Leaf -> Node (Black, l, k, r)
               | Node (t1, b, y, c0) ->
                 (match t1 with
                  | Red ->
                    Node (Red, (Node (Black, a, x, b)), y, (Node (Black, c0, k, r)))
                  | Black -> Node (Black, l, k, r)))
            | Node (t1, a0, x0, b) ->
              (match t1 with
               | Red -> Node (Red, (Node (Black, a0, x0, b)), x, (Node (Black, c, k, r)))
               | Black ->
                 (match c with
                  | Leaf -> Node (Black, l, k, r)
                  | Node (t2, b0, y, c0) ->
                    (match t2 with
                     | Red ->
                       Node (Red, (Node (Black, a, x, b0)), y, (Node (Black, c0, k, r)))
                     | Black -> Node (Black, l, k, r)))))
         | Black -> Node (Black, l, k, r))

    (** val rbal : tree -> X.t -> tree -> tree **)

    let rbal l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, y, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z, d0) ->
               (match t1 with
                | Red -> Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y0, c) ->
            (match t1 with
             | Red -> Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y, d)))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0, z, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val rbal' : tree -> X.t -> tree -> tree **)

    let rbal' l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, z, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z0, d0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c, z0, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y, c) ->
            (match t1 with
             | Red ->
               (match d with
                | Leaf ->
                  Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z, d)))
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0, z0, d0)))
                   | Black ->
                     Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z, d)))))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0, z0, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val lbalS : tree -> X.t -> tree -> tree **)

    let lbalS l k r =
      match l with
      | Leaf ->
        (match r with
         | Leaf -> Node (Red, l, k, r)
         | Node (t0, a, z, c) ->
           (match t0 with
            | Red ->
              (match a with
               | Leaf -> Node (Red, l, k, r)
               | Node (t1, a0, y, b) ->
                 (match t1 with
                  | Red -> Node (Red, l, k, r)
                  | Black ->
                    Node (Red, (Node (Black, l, k, a0)), y, (rbal' b z (makeRed c)))))
            | Black -> rbal' l k (Node (Red, a, z, c))))
      | Node (t0, a, x, b) ->
        (match t0 with
         | Red -> Node (Red, (Node (Black, a, x, b)), k, r)
         | Black ->
           (match r with
            | Leaf -> Node (Red, l, k, r)
            | Node (t1, a0, z, c) ->
              (match t1 with
               | Red ->
                 (match a0 with
                  | Leaf -> Node (Red, l, k, r)
                  | Node (t2, a1, y, b0) ->
                    (match t2 with
                     | Red -> Node (Red, l, k, r)
                     | Black ->
                       Node (Red, (Node (Black, l, k, a1)), y, (rbal' b0 z (makeRed c)))))
               | Black -> rbal' l k (Node (Red, a0, z, c)))))

    (** val rbalS : tree -> X.t -> tree -> tree **)

    let rbalS l k r = match r with
    | Leaf ->
      (match l with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, x, b) ->
         (match t0 with
          | Red ->
            (match b with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, b0, y, c) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (lbal (makeRed a) x b0), y, (Node (Black, c, k, r)))))
          | Black -> lbal (Node (Red, a, x, b)) k r))
    | Node (t0, b, y, c) ->
      (match t0 with
       | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
       | Black ->
         (match l with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a, x, b0) ->
            (match t1 with
             | Red ->
               (match b0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, b1, y0, c0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (lbal (makeRed a) x b1), y0, (Node (Black, c0, k, r)))))
             | Black -> lbal (Node (Red, a, x, b0)) k r)))

    (** val ins : X.t -> tree -> tree **)

    let rec ins x s = match s with
    | Leaf -> Node (Red, Leaf, x, Leaf)
    | Node (c, l, y, r) ->
      (match X.compare x y with
       | Eq -> s
       | Lt ->
         (match c with
          | Red -> Node (Red, (ins x l), y, r)
          | Black -> lbal (ins x l) y r)
       | Gt ->
         (match c with
          | Red -> Node (Red, l, y, (ins x r))
          | Black -> rbal l y (ins x r)))

    (** val add : X.t -> tree -> tree **)

    let add x s =
      makeBlack (ins x s)

    (** val append : tree -> tree -> tree **)

    let rec append l = match l with
    | Leaf -> (fun r -> r)
    | Node (lc, ll, lx, lr) ->
      let rec append_l r = match r with
      | Leaf -> l
      | Node (rc, rl, rx, rr) ->
        (match lc with
         | Red ->
           (match rc with
            | Red ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl', rx, rr)))
                  | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
            | Black -> Node (Red, ll, lx, (append lr r)))
         | Black ->
           (match rc with
            | Red -> Node (Red, (append_l rl), rx, rr)
            | Black ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black, rl', rx,
                      rr)))
                  | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
      in append_l

    (** val del : X.t -> tree -> tree **)

    let rec del x = function
    | Leaf -> Leaf
    | Node (_, a, y, b) ->
      (match X.compare x y with
       | Eq -> append a b
       | Lt ->
         (match a with
          | Leaf -> Node (Red, (del x a), y, b)
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, (del x a), y, b)
             | Black -> lbalS (del x a) y b))
       | Gt ->
         (match b with
          | Leaf -> Node (Red, a, y, (del x b))
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, a, y, (del x b))
             | Black -> rbalS a y (del x b))))

    (** val remove : X.t -> tree -> tree **)

    let remove x t0 =
      makeBlack (del x t0)

    (** val delmin : tree -> elt -> tree -> elt * tree **)

    let rec delmin l x r =
      match l with
      | Leaf -> (x, r)
      | Node (lc, ll, lx, lr) ->
        let (k, l') = delmin ll lx lr in
        (match lc with
         | Red -> (k, (Node (Red, l', x, r)))
         | Black -> (k, (lbalS l' x r)))

    (** val remove_min : tree -> (elt * tree) option **)

    let remove_min = function
    | Leaf -> None
    | Node (_, l, x, r) -> let (k, t1) = delmin l x r in Some (k, (makeBlack t1))

    (** val bogus : tree * elt list **)

    let bogus =
      (Leaf, [])

    (** val treeify_zero : elt list -> tree * elt list **)

    let treeify_zero acc =
      (Leaf, acc)

    (** val treeify_one : elt list -> tree * elt list **)

    let treeify_one = function
    | [] -> bogus
    | x :: acc0 -> ((Node (Red, Leaf, x, Leaf)), acc0)

    (** val treeify_cont :
        (elt list -> tree * elt list) -> (elt list -> tree * elt list) -> elt list ->
        tree * elt list **)

    let treeify_cont f g acc =
      let (l, l0) = f acc in
      (match l0 with
       | [] -> bogus
       | x :: acc0 -> let (r, acc1) = g acc0 in ((Node (Black, l, x, r)), acc1))

    (** val treeify_aux : bool -> int -> elt list -> tree * elt list **)

    let rec treeify_aux pred0 n =
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun n0 -> treeify_cont (treeify_aux false n0) (treeify_aux pred0 n0))
        (fun n0 -> treeify_cont (treeify_aux pred0 n0) (treeify_aux true n0))
        (fun _ -> if pred0 then treeify_zero else treeify_one)
        n

    (** val plength_aux : elt list -> int -> int **)

    let rec plength_aux l p =
      match l with
      | [] -> p
      | _ :: l0 -> plength_aux l0 (Coq_Pos.succ p)

    (** val plength : elt list -> int **)

    let plength l =
      plength_aux l 1

    (** val treeify : elt list -> tree **)

    let treeify l =
      fst (treeify_aux true (plength l) l)

    (** val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list **)

    let rec filter_aux f s acc =
      match s with
      | Leaf -> acc
      | Node (_, l, k, r) ->
        let acc0 = filter_aux f r acc in
        if f k then filter_aux f l (k :: acc0) else filter_aux f l acc0

    (** val filter : (elt -> bool) -> t -> t **)

    let filter f s =
      treeify (filter_aux f s [])

    (** val partition_aux :
        (elt -> bool) -> tree -> X.t list -> X.t list -> X.t list * X.t list **)

    let rec partition_aux f s acc1 acc2 =
      match s with
      | Leaf -> (acc1, acc2)
      | Node (_, sl, k, sr) ->
        let (acc3, acc4) = partition_aux f sr acc1 acc2 in
        if f k
        then partition_aux f sl (k :: acc3) acc4
        else partition_aux f sl acc3 (k :: acc4)

    (** val partition : (elt -> bool) -> t -> t * t **)

    let partition f s =
      let (ok, ko) = partition_aux f s [] [] in ((treeify ok), (treeify ko))

    (** val union_list : elt list -> elt list -> elt list -> elt list **)

    let rec union_list l1 = match l1 with
    | [] -> rev_append
    | x :: l1' ->
      let rec union_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y :: l2' ->
          (match X.compare x y with
           | Eq -> union_list l1' l2' (x :: acc)
           | Lt -> union_l1 l2' (y :: acc)
           | Gt -> union_list l1' l2 (x :: acc))
      in union_l1

    (** val linear_union : tree -> tree -> tree **)

    let linear_union s1 s2 =
      treeify (union_list (rev_elements s1) (rev_elements s2) [])

    (** val inter_list : X.t list -> elt list -> elt list -> elt list **)

    let rec inter_list = function
    | [] -> (fun _ acc -> acc)
    | x :: l1' ->
      let rec inter_l1 l2 acc =
        match l2 with
        | [] -> acc
        | y :: l2' ->
          (match X.compare x y with
           | Eq -> inter_list l1' l2' (x :: acc)
           | Lt -> inter_l1 l2' acc
           | Gt -> inter_list l1' l2 acc)
      in inter_l1

    (** val linear_inter : tree -> tree -> tree **)

    let linear_inter s1 s2 =
      treeify (inter_list (rev_elements s1) (rev_elements s2) [])

    (** val diff_list : elt list -> elt list -> elt list -> elt list **)

    let rec diff_list l1 = match l1 with
    | [] -> (fun _ acc -> acc)
    | x :: l1' ->
      let rec diff_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y :: l2' ->
          (match X.compare x y with
           | Eq -> diff_list l1' l2' acc
           | Lt -> diff_l1 l2' acc
           | Gt -> diff_list l1' l2 (x :: acc))
      in diff_l1

    (** val linear_diff : tree -> tree -> tree **)

    let linear_diff s1 s2 =
      treeify (diff_list (rev_elements s1) (rev_elements s2) [])

    (** val skip_red : tree -> tree **)

    let skip_red t0 = match t0 with
    | Leaf -> t0
    | Node (t1, t', _, _) -> (match t1 with
                              | Red -> t'
                              | Black -> t0)

    (** val skip_black : tree -> tree **)

    let skip_black t0 =
      match skip_red t0 with
      | Leaf -> Leaf
      | Node (t1, t', t2, t3) ->
        (match t1 with
         | Red -> Node (Red, t', t2, t3)
         | Black -> t')

    (** val compare_height : tree -> tree -> tree -> tree -> comparison **)

    let rec compare_height s1x s1 s2 s2x =
      match skip_red s1x with
      | Leaf ->
        (match skip_red s1 with
         | Leaf -> (match skip_red s2x with
                    | Leaf -> Eq
                    | Node (_, _, _, _) -> Lt)
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Eq
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (_, s2x', _, _) -> compare_height Leaf s1' s2' (skip_black s2x'))))
      | Node (_, s1x', _, _) ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2 with
            | Leaf -> (match skip_red s2x with
                       | Leaf -> Gt
                       | Node (_, _, _, _) -> Lt)
            | Node (_, _, _, _) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (_, _, _, _) -> Lt))
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Gt
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> compare_height (skip_black s1x') s1' s2' Leaf
               | Node (_, s2x', _, _) ->
                 compare_height (skip_black s1x') s1' s2' (skip_black s2x'))))

    (** val union : t -> t -> t **)

    let union t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_union t1 t2
      | Lt -> fold add t1 t2
      | Gt -> fold add t2 t1

    (** val diff : t -> t -> t **)

    let diff t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_diff t1 t2
      | Lt -> filter (fun k -> negb (mem k t2)) t1
      | Gt -> fold remove t2 t1

    (** val inter : t -> t -> t **)

    let inter t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_inter t1 t2
      | Lt -> filter (fun k -> mem k t2) t1
      | Gt -> filter (fun k -> mem k t1) t2

    (** val ltb_tree : X.t -> tree -> bool **)

    let rec ltb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match X.compare x y with
       | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
       | _ -> false)

    (** val gtb_tree : X.t -> tree -> bool **)

    let rec gtb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match X.compare x y with
       | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
       | _ -> false)

    (** val isok : tree -> bool **)

    let rec isok = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

    module MX = OrderedTypeFacts(X)

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * 
       tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * 
       tree * elt option * coq_R_max_elt

    module L = MakeListOrdering(X)

    (** val flatten_e : enumeration -> elt list **)

    let rec flatten_e = function
    | End -> []
    | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))

    (** val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, b) -> (match t1 with
                             | Red -> f a x b
                             | Black -> g t0)

    (** val rrcase :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rrcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y, c0) -> (match t2 with
                                       | Red -> f a x b y c0
                                       | Black -> g t0))
          | Node (t2, a0, x0, b) ->
            (match t2 with
             | Red -> f a0 x0 b x c
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y, c0) ->
                  (match t3 with
                   | Red -> f a x b0 y c0
                   | Black -> g t0))))
       | Black -> g t0)

    (** val rrcase' :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rrcase' f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, y, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y0, c0) ->
               (match t2 with
                | Red -> f a y b y0 c0
                | Black -> g t0))
          | Node (t2, a0, x, b) ->
            (match t2 with
             | Red ->
               (match c with
                | Leaf -> f a0 x b y c
                | Node (t3, b0, y0, c0) ->
                  (match t3 with
                   | Red -> f a y b0 y0 c0
                   | Black -> f a0 x b y c))
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y0, c0) ->
                  (match t3 with
                   | Red -> f a y b0 y0 c0
                   | Black -> g t0))))
       | Black -> g t0)
   end

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> int **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)

  (** val mk_opt_t : (elt * Raw.t) option -> (elt * t) option **)

  let mk_opt_t = function
  | Some p -> let (k, s') = p in Some (k, s')
  | None -> None

  (** val remove_min : t_ -> (elt * t) option **)

  let remove_min s =
    mk_opt_t (Raw.remove_min (this s))
 end

module PS = Make(Positive_as_OT)

(** val union_list0 : PS.t -> PS.elt list -> PS.t **)

let union_list0 s l =
  fold_left (fun set0 e -> PS.add e set0) l s

type exp_ctx =
| Hole_c
| Econstr_c of var * cTag * var list * exp_ctx
| Eproj_c of var * cTag * int * var * exp_ctx
| Eprim_c of var * prim * var list * exp_ctx
| Ecase_c of var * (cTag * exp) list * cTag * exp_ctx * (cTag * exp) list
| Efun1_c of fundefs * exp_ctx
| Efun2_c of fundefs_ctx * exp
and fundefs_ctx =
| Fcons1_c of var * cTag * var list * exp_ctx * fundefs
| Fcons2_c of var * cTag * var list * exp * fundefs_ctx

(** val app_ctx_f : exp_ctx -> exp -> exp **)

let rec app_ctx_f c e =
  match c with
  | Hole_c -> e
  | Econstr_c (x, t0, ys, c0) -> Econstr (x, t0, ys, (app_ctx_f c0 e))
  | Eproj_c (x, t0, n, y, c0) -> Eproj (x, t0, n, y, (app_ctx_f c0 e))
  | Eprim_c (x, f, ys, c0) -> Eprim (x, f, ys, (app_ctx_f c0 e))
  | Ecase_c (x, te, t0, c0, te') -> Ecase (x, (app te ((t0, (app_ctx_f c0 e)) :: te')))
  | Efun1_c (fds, c0) -> Efun (fds, (app_ctx_f c0 e))
  | Efun2_c (cfds, e') -> Efun ((app_f_ctx_f cfds e), e')

(** val app_f_ctx_f : fundefs_ctx -> exp -> fundefs **)

and app_f_ctx_f c e =
  match c with
  | Fcons1_c (f, t0, ys, c0, fds) -> Fcons (f, t0, ys, (app_ctx_f c0 e), fds)
  | Fcons2_c (f, t0, ys, e', cfds) -> Fcons (f, t0, ys, e', (app_f_ctx_f cfds e))

(** val comp_ctx_f : exp_ctx -> exp_ctx -> exp_ctx **)

let rec comp_ctx_f c1 c2 =
  match c1 with
  | Hole_c -> c2
  | Econstr_c (x, t0, ys, c) -> Econstr_c (x, t0, ys, (comp_ctx_f c c2))
  | Eproj_c (x, t0, n, y, c) -> Eproj_c (x, t0, n, y, (comp_ctx_f c c2))
  | Eprim_c (x, f, ys, c) -> Eprim_c (x, f, ys, (comp_ctx_f c c2))
  | Ecase_c (x, te, t0, c, te') -> Ecase_c (x, te, t0, (comp_ctx_f c c2), te')
  | Efun1_c (fds, c) -> Efun1_c (fds, (comp_ctx_f c c2))
  | Efun2_c (cfds, e') -> Efun2_c ((comp_f_ctx_f cfds c2), e')

(** val comp_f_ctx_f : fundefs_ctx -> exp_ctx -> fundefs_ctx **)

and comp_f_ctx_f c c2 =
  match c with
  | Fcons1_c (f, t0, ys, c0, fds) -> Fcons1_c (f, t0, ys, (comp_ctx_f c0 c2), fds)
  | Fcons2_c (f, t0, ys, e', cfds) -> Fcons2_c (f, t0, ys, e', (comp_f_ctx_f cfds c2))

type env = val0 M.t

type prims = (val0 list -> val0 option) M.t

type fVSet = PS.t

(** val add_list : fVSet -> fVSet -> PS.elt list -> fVSet **)

let add_list scope fvset ys =
  fold_left (fun fvs y -> if PS.mem y scope then fvs else PS.add y fvs) ys fvset

(** val exp_fv_aux : exp -> fVSet -> fVSet -> fVSet **)

let rec exp_fv_aux e scope fvset =
  match e with
  | Econstr (x, _, ys, e0) ->
    let fvset' = add_list scope fvset ys in exp_fv_aux e0 (PS.add x scope) fvset'
  | Ecase (x, pats) ->
    let fvset' = fold_left (fun fvs p -> exp_fv_aux (snd p) scope fvs) pats fvset in
    if PS.mem x scope then fvset' else PS.add x fvset'
  | Eproj (x, _, _, y, e0) ->
    let fvset' = if PS.mem y scope then fvset else PS.add y fvset in
    exp_fv_aux e0 (PS.add x scope) fvset'
  | Efun (defs, e0) ->
    let (scope', fvset') = fundefs_fv_aux defs scope fvset in exp_fv_aux e0 scope' fvset'
  | Eapp (x, _, xs) ->
    let fvset' = add_list scope fvset xs in
    if PS.mem x scope then fvset' else PS.add x fvset'
  | Eprim (x, _, ys, e0) ->
    let fvset' = add_list scope fvset ys in exp_fv_aux e0 (PS.add x scope) fvset'
  | Ehalt x -> if PS.mem x scope then fvset else PS.add x fvset

(** val fundefs_fv_aux : fundefs -> fVSet -> fVSet -> fVSet * fVSet **)

and fundefs_fv_aux defs scope fvset =
  match defs with
  | Fcons (f, _, ys, e, defs') ->
    let (scope', fvset') = fundefs_fv_aux defs' (PS.add f scope) fvset in
    (scope', (exp_fv_aux e (union_list0 scope' ys) fvset'))
  | Fnil -> (scope, fvset)

(** val fundefs_fv : fundefs -> fVSet **)

let fundefs_fv b =
  snd (fundefs_fv_aux b PS.empty PS.empty)

(** val max_var : exp -> int -> int **)

let rec max_var e z =
  match e with
  | Econstr (x, _, ys, e0) -> max_var e0 (max_list (x :: ys) z)
  | Ecase (x, p) ->
    let rec aux p0 z0 =
      match p0 with
      | [] -> Coq_Pos.max z0 x
      | y :: p1 -> let (_, e0) = y in aux p1 (max_var e0 z0)
    in aux p z
  | Eproj (x, _, _, y, e0) -> max_var e0 (max_list (x :: (y :: [])) z)
  | Efun (defs, e0) -> let z' = max_var_fundefs defs z in max_var e0 z'
  | Eapp (f, _, xs) -> max_list (f :: xs) z
  | Eprim (x, _, ys, e0) -> max_var e0 (max_list (x :: ys) z)
  | Ehalt x -> Coq_Pos.max z x

(** val max_var_fundefs : fundefs -> int -> int **)

and max_var_fundefs defs z =
  match defs with
  | Fcons (f, _, ys, e, defs0) ->
    let z' = max_var e z in max_var_fundefs defs0 (max_list (f :: ys) z')
  | Fnil -> z

(** val var_dec : int -> int -> bool **)

let var_dec =
  M.elt_eq

type svalue =
| SVconstr of cTag * var list
| SVfun of fTag * var list * exp

type ctx_map = svalue M.t

type r_map = var M.t

type c_map = int M.t

type b_map = bool M.t

(** val getd : 'a1 -> int -> 'a1 M.t -> 'a1 **)

let getd d v sub0 =
  match M.get v sub0 with
  | Some e -> e
  | None -> d

(** val term_size : exp -> int **)

let rec term_size = function
| Econstr (_, _, _, e0) -> add (Pervasives.succ 0) (term_size e0)
| Ecase (_, cl) ->
  add (Pervasives.succ 0)
    (fold_right (fun p n -> let (_, e0) = p in add n (term_size e0)) 0 cl)
| Eproj (_, _, _, _, e0) -> add (Pervasives.succ 0) (term_size e0)
| Efun (fds, e0) -> add (add (Pervasives.succ 0) (funs_size fds)) (term_size e0)
| Eprim (_, _, _, e0) -> add (Pervasives.succ 0) (term_size e0)
| _ -> Pervasives.succ 0

(** val funs_size : fundefs -> int **)

and funs_size = function
| Fcons (_, _, _, e, fds') ->
  add (add (Pervasives.succ 0) (funs_size fds')) (term_size e)
| Fnil -> Pervasives.succ 0

(** val set_list : (M.elt * 'a1) list -> 'a1 M.t -> 'a1 M.t **)

let set_list l map0 =
  fold_right (fun xv cmap -> M.set (fst xv) (snd xv) cmap) map0 l

(** val apply_r : M.elt M.t -> int -> M.elt **)

let apply_r sigma y =
  match M.get y sigma with
  | Some v -> v
  | None -> y

(** val apply_r_list : M.elt M.t -> int list -> M.elt list **)

let apply_r_list sigma ys =
  map (apply_r sigma) ys

type tag = int

(** val all_fun_name : fundefs -> var list **)

let rec all_fun_name = function
| Fcons (f, _, _, _, fds') -> f :: (all_fun_name fds')
| Fnil -> []

(** val update_census_list :
    r_map -> var list -> (var -> c_map -> int) -> c_map -> c_map **)

let rec update_census_list sig0 ys fun_delta count =
  match ys with
  | [] -> count
  | y :: ys' ->
    let y' = apply_r sig0 y in
    update_census_list sig0 ys' fun_delta (M.set y' (fun_delta y' count) count)

(** val update_census : r_map -> exp -> (var -> c_map -> int) -> c_map -> c_map **)

let rec update_census sig0 e fun_delta count =
  match e with
  | Econstr (_, _, ys, e0) ->
    let count' = update_census_list sig0 ys fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Ecase (v, cl) ->
    let count' = update_census_list sig0 (v :: []) fun_delta count in
    fold_right (fun p c -> let (_, e0) = p in update_census sig0 e0 fun_delta c) count'
      cl
  | Eproj (_, _, _, y, e0) ->
    let count' = update_census_list sig0 (y :: []) fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Efun (fl, e0) ->
    let count' = update_census_f sig0 fl fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Eapp (f, _, ys) -> update_census_list sig0 (f :: ys) fun_delta count
  | Eprim (_, _, ys, e0) ->
    let count' = update_census_list sig0 ys fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Ehalt v -> update_census_list sig0 (v :: []) fun_delta count

(** val update_census_f : r_map -> fundefs -> (var -> c_map -> int) -> c_map -> c_map **)

and update_census_f sig0 fds fun_delta count =
  match fds with
  | Fcons (_, _, _, e, fds') ->
    let count' = update_census sig0 e fun_delta count in
    update_census_f sig0 fds' fun_delta count'
  | Fnil -> count

(** val init_census : exp -> c_map **)

let init_census e =
  update_census M.empty e (fun v c -> add (getd 0 v c) (Pervasives.succ 0)) M.empty

(** val dec_census : r_map -> exp -> c_map -> c_map **)

let dec_census sig0 e count =
  update_census sig0 e (fun v c -> sub (getd 0 v c) (Pervasives.succ 0)) count

(** val dec_census_list : r_map -> var list -> c_map -> c_map **)

let dec_census_list sig0 ys count =
  update_census_list sig0 ys (fun v c -> sub (getd 0 v c) (Pervasives.succ 0)) count

(** val dec_census_all_case : r_map -> (var * exp) list -> c_map -> c_map **)

let rec dec_census_all_case sig0 cl count =
  match cl with
  | [] -> count
  | p :: cl' ->
    let (_, e) = p in
    let count' = dec_census_all_case sig0 cl' count in dec_census sig0 e count'

(** val dec_census_case : r_map -> (var * exp) list -> var -> c_map -> c_map **)

let rec dec_census_case sig0 cl y count =
  match cl with
  | [] -> count
  | p :: cl' ->
    let (k, e) = p in
    if var_dec k y
    then dec_census_all_case sig0 cl' count
    else let count' = dec_census_case sig0 cl' y count in dec_census sig0 e count'

(** val update_count_inlined : var list -> var list -> c_map -> c_map **)

let rec update_count_inlined ys xs count =
  match ys with
  | [] -> count
  | y :: ys' ->
    (match xs with
     | [] -> count
     | x :: xs' ->
       let cy = getd 0 y count in
       let cx = getd 0 x count in
       update_count_inlined ys' xs'
         (M.set y (sub (add cy cx) (Pervasives.succ 0)) (M.set x 0 count)))

(** val precontractfun :
    r_map -> c_map -> ctx_map -> fundefs -> (fundefs * c_map) * ctx_map **)

let rec precontractfun sig0 count sub0 = function
| Fcons (f, t0, ys, e, fds') ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     let count' = dec_census sig0 e count in precontractfun sig0 count' sub0 fds')
     (fun _ ->
     let (fc', sub') = precontractfun sig0 count sub0 fds' in
     let (fds'', count') = fc' in
     (((Fcons (f, t0, ys, e, fds'')), count'), (M.set f (SVfun (t0, ys, e)) sub')))
     (getd 0 f count))
| Fnil -> ((Fnil, count), sub0)

(** val contractcases :
    ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map) -> __ ->
    ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map -> ctx_map ->
    (var * exp) list -> (((var * exp) list * c_map) * b_map, __) sigT **)

let rec contractcases oes fcon sig0 count inl sub0 = function
| [] -> ExistT ((([], count), inl), __)
| p :: cl' ->
  let (y, e) = p in
  let ExistT (x, _) = fcon sig0 count ((e, sub0), inl) __ in
  let (p0, inl') = x in
  let (e', count') = p0 in
  let ExistT (x0, _) = contractcases oes fcon sig0 count' inl' sub0 cl' in
  let (p1, inl'') = x0 in
  let (cl'', count'') = p1 in ExistT (((((y, e') :: cl''), count''), inl''), __)

(** val postcontractfun :
    ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map) -> __ ->
    ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map -> ctx_map -> fundefs
    -> ((fundefs * c_map) * b_map, __) sigT **)

let rec postcontractfun oes fcon sig0 count inl sub0 = function
| Fcons (f, t0, ys, e, fds') ->
  if getd false f inl
  then postcontractfun oes fcon sig0 count inl sub0 fds'
  else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          let count' = dec_census sig0 e count in
          postcontractfun oes fcon sig0 count' inl sub0 fds')
          (fun _ ->
          let ExistT (x, _) = fcon sig0 count ((e, sub0), inl) __ in
          let (p, inl') = x in
          let (e', count') = p in
          let ExistT (x0, _) = postcontractfun oes fcon sig0 count' inl' sub0 fds' in
          let (p0, inl'') = x0 in
          let (fds'', count'') = p0 in
          ExistT ((((Fcons (f, t0, ys, e', fds'')), count''), inl''), __))
          (getd 0 f count))
| Fnil -> ExistT (((Fnil, count), inl), __)

(** val contract_func :
    (r_map, (c_map, (exp, (ctx_map, b_map) sigT) sigT) sigT) sigT ->
    ((exp * c_map) * b_map, __) sigT **)

let rec contract_func x =
  let sig0 = projT1 x in
  let count = projT1 (projT2 x) in
  let e = projT1 (projT2 (projT2 x)) in
  let sub0 = projT1 (projT2 (projT2 (projT2 x))) in
  let im = projT2 (projT2 (projT2 (projT2 x))) in
  let contract0 = fun sig1 count0 e0 sub1 im0 ->
    contract_func (ExistT (sig1, (ExistT (count0, (ExistT (e0, (ExistT (sub1, im0))))))))
  in
  (match e with
   | Econstr (x0, t0, ys, e') ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        let count' = dec_census_list sig0 ys count in contract0 sig0 count' e' sub0 im)
        (fun _ ->
        let ExistT (x1, _) =
          contract0 sig0 count e' (M.set x0 (SVconstr (t0, ys)) sub0) im
        in
        let (p, im') = x1 in
        let (e'', count') = p in
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           let count'' = dec_census_list sig0 ys count' in
           ExistT (((e'', count''), im'), __))
           (fun _ ->
           let ys' = apply_r_list sig0 ys in
           ExistT ((((Econstr (x0, t0, ys', e'')), count'), im'), __))
           (getd 0 x0 count')))
        (getd 0 x0 count))
   | Ecase (v, cl) ->
     let v' = apply_r sig0 v in
     (match M.get v' sub0 with
      | Some s ->
        (match s with
         | SVconstr (t0, _) ->
           let filtered_var = findtag cl t0 in
           (match filtered_var with
            | Some k ->
              contract0 sig0
                (dec_census_case sig0 cl t0 (dec_census_list sig0 (v :: []) count)) k
                sub0 im
            | None ->
              let filtered_var0 =
                contractcases (((Ecase (v, cl)), sub0), im) (fun rm cm es _ ->
                  contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0 count im
                  sub0 cl
              in
              let ExistT (x0, _) = filtered_var0 in
              let (p, im') = x0 in
              let (cl', count') = p in ExistT ((((Ecase (v', cl')), count'), im'), __))
         | SVfun (_, _, _) ->
           let filtered_var =
             contractcases (((Ecase (v, cl)), sub0), im) (fun rm cm es _ ->
               contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0 count im
               sub0 cl
           in
           let ExistT (x0, _) = filtered_var in
           let (p, im') = x0 in
           let (cl', count') = p in ExistT ((((Ecase (v', cl')), count'), im'), __))
      | None ->
        let filtered_var =
          contractcases (((Ecase (v, cl)), sub0), im) (fun rm cm es _ ->
            contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0 count im sub0 cl
        in
        let ExistT (x0, _) = filtered_var in
        let (p, im') = x0 in
        let (cl', count') = p in ExistT ((((Ecase (v', cl')), count'), im'), __))
   | Eproj (v, t0, n, y, e0) ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        let count' = dec_census_list sig0 (y :: []) count in
        contract0 sig0 count' e0 sub0 im)
        (fun _ ->
        let y' = apply_r sig0 y in
        (match M.get y' sub0 with
         | Some s ->
           (match s with
            | SVconstr (_, ys) ->
              (match nthN ys n with
               | Some yn ->
                 let yn' = apply_r sig0 yn in
                 let count' = M.set y' (sub (getd 0 y' count) (Pervasives.succ 0)) count
                 in
                 let count'' =
                   M.set v 0 (M.set yn' (add (getd 0 v count) (getd 0 yn' count)) count')
                 in
                 contract0 (M.set v yn' sig0) count'' e0 sub0 im
               | None ->
                 let ExistT (x0, _) = contract0 sig0 count e0 sub0 im in
                 let (p, im') = x0 in
                 let (e', count') = p in
                 ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ ->
                    let count'' = dec_census_list sig0 (y :: []) count' in
                    ExistT (((e', count''), im'), __))
                    (fun _ -> ExistT ((((Eproj (v, t0, n, y', e')), count'), im'),
                    __))
                    (getd 0 v count')))
            | SVfun (_, _, _) ->
              let ExistT (x0, _) = contract0 sig0 count e0 sub0 im in
              let (p, im') = x0 in
              let (e', count') = p in
              ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ ->
                 let count'' = dec_census_list sig0 (y :: []) count' in
                 ExistT (((e', count''), im'), __))
                 (fun _ -> ExistT ((((Eproj (v, t0, n, y', e')), count'), im'),
                 __))
                 (getd 0 v count')))
         | None ->
           let ExistT (x0, _) = contract0 sig0 count e0 sub0 im in
           let (p, im') = x0 in
           let (e', count') = p in
           ((fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              let count'' = dec_census_list sig0 (y :: []) count' in
              ExistT (((e', count''), im'), __))
              (fun _ -> ExistT ((((Eproj (v, t0, n, y', e')), count'), im'),
              __))
              (getd 0 v count'))))
        (getd 0 v count))
   | Efun (fl, e0) ->
     let filtered_var = precontractfun sig0 count sub0 fl in
     let (p, sub') = filtered_var in
     let (fl', count') = p in
     let ExistT (x0, _) = contract0 sig0 count' e0 sub' im in
     let (p0, im') = x0 in
     let (e', count'') = p0 in
     let ExistT (x1, _) =
       postcontractfun (((Efun (fl', e0)), sub0), im') (fun rm cm es _ ->
         contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0 count'' im' sub0
         fl'
     in
     let (p1, im'') = x1 in
     let (fl'', count''') = p1 in
     (match fl'' with
      | Fcons (_, _, _, _, _) -> ExistT ((((Efun (fl'', e')), count'''), im''), __)
      | Fnil -> ExistT (((e', count'''), im''), __))
   | Eapp (f, t0, ys) ->
     let f' = apply_r sig0 f in
     let ys' = apply_r_list sig0 ys in
     let filtered_var = getd 0 f' count in
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> ExistT ((((Eapp (f', t0, ys')), count), im), __))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          let filtered_var0 = M.get f' sub0 in
          (match filtered_var0 with
           | Some s ->
             (match s with
              | SVconstr (_, _) -> ExistT ((((Eapp (f', t0, ys')), count), im), __)
              | SVfun (t', xs, m0) ->
                let filtered_var1 =
                  (&&) (Coq_Pos.eqb t' t0)
                    ((&&) (eqb (length ys) (length xs)) (negb (getd false f' im)))
                in
                if filtered_var1
                then let im' = M.set f' true im in
                     let count' = update_count_inlined ys' xs (M.set f' 0 count) in
                     let ExistT (x0, _) =
                       contract0 (set_list (combine xs ys') sig0) count' m0 sub0 im'
                     in
                     ExistT (x0, __)
                else ExistT ((((Eapp (f', t0, ys')), count), im), __))
           | None -> ExistT ((((Eapp (f', t0, ys')), count), im), __)))
          (fun _ -> ExistT ((((Eapp (f', t0, ys')), count), im), __))
          n)
        filtered_var)
   | Eprim (x0, f, ys, e0) ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        let count' = dec_census_list sig0 ys count in contract0 sig0 count' e0 sub0 im)
        (fun _ ->
        let ExistT (x1, _) = contract0 sig0 count e0 sub0 im in
        let (p, im') = x1 in
        let (e', count') = p in
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           let count'' = dec_census_list sig0 ys count' in
           ExistT (((e', count''), im'), __))
           (fun _ ->
           let ys' = apply_r_list sig0 ys in
           ExistT ((((Eprim (x0, f, ys', e')), count'), im'), __))
           (getd 0 x0 count')))
        (getd 0 x0 count))
   | Ehalt v -> ExistT ((((Ehalt (apply_r sig0 v)), count), im), __))

(** val contract :
    r_map -> c_map -> exp -> ctx_map -> b_map -> ((exp * c_map) * b_map, __) sigT **)

let contract sig0 count e sub0 im =
  contract_func (ExistT (sig0, (ExistT (count, (ExistT (e, (ExistT (sub0, im))))))))

(** val shrink_top : exp -> exp **)

let shrink_top e =
  let count = init_census e in
  let ExistT (x, _) = contract M.empty count e M.empty M.empty in
  let (p, _) = x in let (e', _) = p in e'

type l5_conId = dcon

(** val l5_conId_dec : l5_conId -> l5_conId -> bool **)

let l5_conId_dec x y =
  let (i, n) = x in
  let (i0, n0) = y in let h = inductive_dec i i0 in if h then eq_dec0 nEq n n0 else false

type conId_map = (l5_conId * cTag) list

(** val dcon_to_info : cTag -> l5_conId -> conId_map -> cTag **)

let rec dcon_to_info default_tag a = function
| [] -> default_tag
| p :: sig' ->
  let (cId, inf) = p in
  if l5_conId_dec a cId then inf else dcon_to_info default_tag a sig'

(** val dcon_to_tag : cTag -> l5_conId -> conId_map -> cTag **)

let dcon_to_tag =
  dcon_to_info

(** val fromN0 : int -> int -> int list * int **)

let rec fromN0 n m0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], n))
    (fun m' -> let (l, nm) = fromN0 (Coq_Pos.add n 1) m' in ((n :: l), nm))
    m0

(** val ctx_bind_proj : cTag -> int -> int -> var -> int -> exp_ctx * var **)

let rec ctx_bind_proj tg r m0 n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Hole_c, n))
    (fun m' ->
    let (ctx_p', n') = ctx_bind_proj tg r m' n p in
    ((Eproj_c (n', tg, (N.of_nat (add m' p)), r, ctx_p')), (Coq_Pos.succ n')))
    m0

type nEnv = name M.t

(** val n_empty : nEnv **)

let n_empty =
  M.empty

type t_info = fTag

type t_map = t_info M.t

(** val t_empty : t_map **)

let t_empty =
  M.empty

(** val get_f : fTag -> var -> t_map -> fTag **)

let get_f fun_tag n sig0 =
  match M.get n sig0 with
  | Some v -> v
  | None -> fun_tag

type s_map = var M.t

(** val s_empty : var M.t **)

let s_empty =
  M.empty

(** val get_s : nVar -> s_map -> var **)

let get_s a sig0 =
  match M.get (fst a) sig0 with
  | Some v -> v
  | None -> 1

(** val set_s_list : nVar list -> var list -> s_map -> s_map **)

let rec set_s_list lx ly sig0 =
  match lx with
  | [] -> sig0
  | x :: lx' ->
    (match ly with
     | [] -> sig0
     | y :: ly' -> set_s_list lx' ly' (M.set (fst x) y sig0))

type conv_env = (conId_map * t_map) * nEnv

(** val set_nt : var -> (name * t_info) -> conv_env -> conv_env **)

let set_nt x tn = function
| (p, t3) -> let (t1, t2) = p in ((t1, (M.set x (snd tn) t2)), (M.set x (fst tn) t3))

(** val set_t : var -> t_info -> conv_env -> conv_env **)

let set_t x ti = function
| (p, t3) -> let (t1, t2) = p in ((t1, (M.set x ti t2)), t3)

(** val set_n : var -> name -> conv_env -> conv_env **)

let set_n x n = function
| (p, t3) -> (p, (M.set x n t3))

(** val set_t_f_list : fTag -> var list -> nVar list -> conv_env -> conv_env **)

let rec set_t_f_list fun_tag ns ts tgm =
  match ns with
  | [] -> tgm
  | n :: ns' ->
    (match ts with
     | [] -> tgm
     | t0 :: ts' -> set_t_f_list fun_tag ns' ts' (set_nt n ((snd t0), fun_tag) tgm))

(** val convert :
    cTag -> fTag -> fTag -> (nVar, l5Opid) nTerm -> s_map -> s_map -> conv_env -> var ->
    ((exp * var) * conv_env) option **)

let convert default_tag fun_tag kon_tag =
  let rec convert0 e sv sk tgm n =
    match e with
    | Vterm _ -> None
    | Oterm (l, l0) ->
      (match l with
       | CHalt ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Bterm (l2, h) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] ->
                  pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                    (convert_v h sv sk tgm n) (fun r ->
                    let (y, tgm0) = r in
                    let (y0, n') = y in
                    let (ctx_v, vn) = y0 in
                    ret (Obj.magic monad_option) (((app_ctx_f ctx_v (Ehalt vn)),
                      (Coq_Pos.succ n')), tgm0))
                | _ :: _ -> None)
             | _ :: _ -> None))
       | CRet ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Bterm (l2, k) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] -> None
                | b0 :: l3 ->
                  let Bterm (l4, v) = b0 in
                  (match l4 with
                   | [] ->
                     (match l3 with
                      | [] ->
                        pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                          (convert_v k sv sk tgm n) (fun r1 ->
                          let (y, tgm0) = r1 in
                          let (y0, n') = y in
                          let (ctx_k, kn) = y0 in
                          pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                            (convert_v v sv sk tgm0 n') (fun r2 ->
                            let (y1, tgm1) = r2 in
                            let (y2, n'') = y1 in
                            let (ctx_v, vn) = y2 in
                            ret (Obj.magic monad_option)
                              (((app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp (kn, kon_tag,
                                  (vn :: [])))), n''), tgm1)))
                      | _ :: _ -> None)
                   | _ :: _ -> None))
             | _ :: _ -> None))
       | CCall ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Bterm (l2, f) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] -> None
                | b0 :: l3 ->
                  let Bterm (l4, k) = b0 in
                  (match l4 with
                   | [] ->
                     (match l3 with
                      | [] -> None
                      | b1 :: l5 ->
                        let Bterm (l6, v) = b1 in
                        (match l6 with
                         | [] ->
                           (match l5 with
                            | [] ->
                              pbind (pMonad_Monad (Obj.magic monad_option))
                                (Obj.magic __) (getVar (Obj.magic f)) (fun f0 ->
                                pbind (pMonad_Monad (Obj.magic monad_option))
                                  (Obj.magic __) (getVar (Obj.magic k)) (fun k0 ->
                                  pbind (pMonad_Monad (Obj.magic monad_option))
                                    (Obj.magic __) (getVar (Obj.magic v)) (fun v0 ->
                                    let fv =
                                      if varClass0 varClassNVar0 f0 then sv else sk
                                    in
                                    let kv =
                                      if varClass0 varClassNVar0 k0 then sv else sk
                                    in
                                    let vv =
                                      if varClass0 varClassNVar0 v0 then sv else sk
                                    in
                                    let f' = get_s f0 fv in
                                    ret (Obj.magic monad_option) (((Eapp (f',
                                      (get_f fun_tag f' (snd (fst tgm))),
                                      ((get_s k0 kv) :: ((get_s v0 vv) :: [])))), n),
                                      tgm))))
                            | _ :: _ -> None)
                         | _ :: _ -> None))
                   | _ :: _ -> None))
             | _ :: _ -> None))
       | CMatch ls ->
         (match l0 with
          | [] -> None
          | b :: lbt ->
            let Bterm (l1, v) = b in
            (match l1 with
             | [] ->
               pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                 (convert_v v sv sk tgm n) (fun r1 ->
                 let (y, tgm0) = r1 in
                 let (y0, n') = y in
                 let (ctx_v, vn) = y0 in
                 pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                   (fold_left (fun co b0 ->
                     pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __) co
                       (fun c ->
                       let (y1, n'0) = c in
                       let (y2, r) = y1 in
                       let (y3, tgm1) = y2 in
                       let (y4, sk0) = y3 in
                       let (y5, sv0) = y4 in
                       let (cbl, ls0) = y5 in
                       let Bterm (xs, e0) = b0 in
                       (match ls0 with
                        | [] -> None
                        | y6 :: ls' ->
                          let (dcn, _) = y6 in
                          let lxs = length xs in
                          let tg = dcon_to_tag default_tag dcn (fst (fst tgm1)) in
                          let (ctx_p, n'') = ctx_bind_proj tg r lxs n'0 0 in
                          let (names, _) = fromN0 n'0 lxs in
                          let sv' = set_s_list xs names sv0 in
                          pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                            (convert0 e0 sv' sk0 tgm1 n'') (fun r2 ->
                            let (y7, tgm2) = r2 in
                            let (ce, n''') = y7 in
                            ret (Obj.magic monad_option) ((((((((tg,
                              (app_ctx_f ctx_p ce)) :: cbl), ls'), sv0), sk0), tgm2),
                              r), n'''))))) lbt
                     (ret (Obj.magic monad_option) (((((([], ls), sv), sk), tgm0), vn),
                       n'))) (fun r2 ->
                   let (y1, n'') = r2 in
                   let (y2, vn0) = y1 in
                   let (y3, tgm1) = y2 in
                   let (y4, _) = y3 in
                   let (y5, _) = y4 in
                   let (cbls, _) = y5 in
                   ret (Obj.magic monad_option) (((app_ctx_f ctx_v (Ecase (vn0, cbls))),
                     n''), tgm1)))
             | _ :: _ -> None))
       | _ -> None)
  and convert_v v sv sk tgm n =
    match v with
    | Vterm v0 ->
      if varClass0 varClassNVar0 v0
      then ret (Obj.magic monad_option) (((Hole_c, (get_s v0 sv)), n), tgm)
      else ret (Obj.magic monad_option) (((Hole_c, (get_s v0 sk)), n), tgm)
    | Oterm (l, lbt) ->
      (match l with
       | CLambda ->
         (match lbt with
          | [] -> None
          | b :: l0 ->
            let Bterm (l1, e) = b in
            (match l1 with
             | [] -> None
             | x :: l2 ->
               (match l2 with
                | [] -> None
                | k :: l3 ->
                  (match l3 with
                   | [] ->
                     (match l0 with
                      | [] ->
                        let tgm0 = set_nt (Coq_Pos.succ n) ((snd k), kon_tag) tgm in
                        let tgm1 = set_n n (snd x) tgm0 in
                        pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                          (convert0 e (M.set (fst x) n sv)
                            (M.set (fst k) (Coq_Pos.succ n) sk) tgm1
                            (Coq_Pos.add n ((fun p->2*p) 1))) (fun r ->
                          let (y, tgm2) = r in
                          let (e', n') = y in
                          let tgm3 = set_t n' fun_tag tgm2 in
                          let fds = Fcons (n', fun_tag, ((Coq_Pos.succ n) :: (n :: [])),
                            e', Fnil)
                          in
                          ret (Obj.magic monad_option) ((((Efun1_c (fds, Hole_c)), n'),
                            (Coq_Pos.succ n')), tgm3))
                      | _ :: _ -> None)
                   | _ :: _ -> None))))
       | CKLambda ->
         (match lbt with
          | [] -> None
          | b :: l0 ->
            let Bterm (l1, e) = b in
            (match l1 with
             | [] -> None
             | k :: l2 ->
               (match l2 with
                | [] ->
                  (match l0 with
                   | [] ->
                     let tgm0 = set_n n (snd k) tgm in
                     pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
                       (convert0 e sv (M.set (fst k) n sk) tgm0 (Coq_Pos.succ n))
                       (fun r ->
                       let (y, tgm1) = r in
                       let (e', n') = y in
                       let fds = Fcons (n', kon_tag, (n :: []), e', Fnil) in
                       ret (Obj.magic monad_option) ((((Efun1_c (fds, Hole_c)), n'),
                         (Coq_Pos.succ n')), (set_t n' kon_tag tgm1)))
                   | _ :: _ -> None)
                | _ :: _ -> None)))
       | CFix (_, i) ->
         (match lbt with
          | [] -> ret (Obj.magic monad_option) (((Hole_c, 1), n), tgm)
          | b :: _ ->
            let Bterm (fvars, _) = b in
            let convert_fds =
              let rec convert_fds fds sv0 sk0 tgm0 fnames n0 =
                match fds with
                | [] -> ret monad_option ((Fnil, n0), tgm0)
                | b0 :: fds' ->
                  let Bterm (_, v0) = b0 in
                  (match fnames with
                   | [] -> ret monad_option ((Fnil, n0), tgm0)
                   | currn :: fnames' ->
                     (match v0 with
                      | Vterm _ -> ret monad_option ((Fnil, n0), tgm0)
                      | Oterm (l0, l1) ->
                        (match l0 with
                         | CLambda ->
                           (match l1 with
                            | [] -> ret monad_option ((Fnil, n0), tgm0)
                            | b1 :: l2 ->
                              let Bterm (l3, e) = b1 in
                              (match l3 with
                               | [] -> ret monad_option ((Fnil, n0), tgm0)
                               | x :: l4 ->
                                 (match l4 with
                                  | [] -> ret monad_option ((Fnil, n0), tgm0)
                                  | k :: l5 ->
                                    (match l5 with
                                     | [] ->
                                       (match l2 with
                                        | [] ->
                                          pbind (pMonad_Monad monad_option)
                                            (Obj.magic __)
                                            (Obj.magic convert0 e (M.set (fst x) n0 sv0)
                                              (M.set (fst k) (Coq_Pos.succ n0) sk0)
                                              (set_nt (Coq_Pos.succ n0) ((snd k),
                                                kon_tag) (set_n n0 (snd x) tgm0))
                                              (Coq_Pos.add n0 ((fun p->2*p) 1)))
                                            (fun r1 ->
                                            let (y, tgm1) = r1 in
                                            let (ce, n') = y in
                                            pbind (pMonad_Monad monad_option)
                                              (Obj.magic __)
                                              (convert_fds fds' sv0 sk0 tgm1 fnames' n')
                                              (fun r2 ->
                                              let (y0, tgm2) = r2 in
                                              let (cfds, n'') = y0 in
                                              ret monad_option (((Fcons (currn, fun_tag,
                                                ((Coq_Pos.succ n0) :: (n0 :: [])), ce,
                                                cfds)), n''), tgm2)))
                                        | _ :: _ -> ret monad_option ((Fnil, n0), tgm0))
                                     | _ :: _ -> ret monad_option ((Fnil, n0), tgm0)))))
                         | _ -> ret monad_option ((Fnil, n0), tgm0))))
              in convert_fds
            in
            let (nfds, newn) = fromN0 n (length fvars) in
            let sv' = set_s_list fvars nfds sv in
            let tgm0 = set_t_f_list fun_tag nfds fvars tgm in
            pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
              (Obj.magic convert_fds lbt sv' sk tgm0 nfds newn) (fun r ->
              let (y, tgm1) = r in
              let (fds, n') = y in
              ret (Obj.magic monad_option) ((((Efun1_c (fds, Hole_c)), (nth i nfds 1)),
                n'), tgm1)))
       | CDCon (dcn, _) ->
         let convert_v_list =
           let rec convert_v_list lv sv0 sk0 tgm0 n0 =
             match lv with
             | [] -> ret monad_option (((Hole_c, []), n0), tgm0)
             | y :: lv' ->
               let Bterm (_, v0) = y in
               pbind (pMonad_Monad monad_option) (Obj.magic __)
                 (Obj.magic convert_v v0 sv0 sk0 tgm0 n0) (fun r1 ->
                 let (y0, tgm1) = r1 in
                 let (y1, n') = y0 in
                 let (ctx_v, vn) = y1 in
                 pbind (pMonad_Monad monad_option) (Obj.magic __)
                   (convert_v_list lv' sv0 sk0 tgm1 n') (fun r2 ->
                   let (y2, tgm2) = r2 in
                   let (y3, n'') = y2 in
                   let (ctx_lv', ln') = y3 in
                   ret monad_option ((((comp_ctx_f ctx_v ctx_lv'), (vn :: ln')), n''),
                     tgm2)))
           in convert_v_list
         in
         let ctag = dcon_to_info default_tag dcn (fst (fst tgm)) in
         pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
           (Obj.magic convert_v_list lbt sv sk tgm n) (fun r ->
           let (y, tgm0) = r in
           let (y0, n') = y in
           let (lv_ctx, nl) = y0 in
           ret (Obj.magic monad_option)
             ((((comp_ctx_f lv_ctx (Econstr_c (n', ctag, nl, Hole_c))), n'),
             (Coq_Pos.succ n')), (set_t n' ctag tgm0)))
       | _ -> None)
  in convert0

type ienv0 = (char list * itypPack) list

(** val convert_cnstrs :
    char list -> cTag list -> cnstr list -> inductive -> int -> iTag -> cEnv ->
    conId_map -> cEnv * conId_map **)

let rec convert_cnstrs tyname cct itC ind nCon niT ce dcm =
  match cct with
  | [] -> (ce, dcm)
  | cn :: cct' ->
    (match itC with
     | [] -> (ce, dcm)
     | cst :: icT' ->
       let { cnstrNm = cname; cnstrArity = ccn } = cst in
       convert_cnstrs tyname cct' icT' ind (N.add nCon 1) niT
         (M.set cn (((((NNamed cname), (NNamed tyname)), niT), (N.of_nat ccn)), nCon) ce)
         (((ind, nCon), cn) :: dcm))

(** val convert_typack :
    ityp list -> char list -> int -> ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
    (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let rec convert_typack typ idBundle n ice = match ice with
| (p, dcm) ->
  let (p0, niT) = p in
  let (p1, ncT) = p0 in
  let (ie, ce) = p1 in
  (match typ with
   | [] -> ice
   | y :: typ' ->
     let { itypNm = itN; itypCnstrs = itC } = y in
     let (cct, ncT') = fromN0 ncT (length itC) in
     let (ce', dcm') =
       convert_cnstrs itN cct itC { inductive_mind = idBundle; inductive_ind = n } 0 niT
         ce dcm
     in
     let ityi =
       combine cct
         (map (fun c -> let { cnstrNm = _; cnstrArity = n0 } = c in N.of_nat n0) itC)
     in
     convert_typack typ' idBundle (add n (Pervasives.succ 0)) (((((M.set niT ityi ie),
       ce'), ncT'), (Coq_Pos.succ niT)), dcm'))

(** val convert_env' :
    ienv0 -> ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
    (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let rec convert_env' g ice =
  match g with
  | [] -> ice
  | p :: g' -> let (id0, ty) = p in convert_env' g' (convert_typack ty id0 0 ice)

(** val convert_env :
    cTag -> iTag -> ienv0 -> (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let convert_env default_tag default_itag g =
  let default_iEnv = M.set default_itag ((default_tag, 0) :: []) M.empty in
  let default_cEnv = M.set default_tag ((((NAnon, NAnon), default_itag), 0), 0) M.empty
  in
  convert_env' g ((((default_iEnv, default_cEnv), (Coq_Pos.succ default_tag)),
    (Coq_Pos.succ default_itag)), [])

(** val convert_top :
    cTag -> iTag -> fTag -> fTag -> (ienv0 * (nVar, l5Opid) nTerm) ->
    (((((cEnv * nEnv) * fEnv) * cTag) * iTag) * exp) option **)

let convert_top default_tag default_itag fun_tag kon_tag ee =
  let (p, dcm) = convert_env default_tag default_itag (fst ee) in
  let (p0, itag) = p in
  let (p1, ctag) = p0 in
  let (_, cG) = p1 in
  pbind (pMonad_Monad (Obj.magic monad_option)) (Obj.magic __)
    (Obj.magic convert default_tag fun_tag kon_tag (snd ee) s_empty s_empty ((dcm,
      t_empty), n_empty) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1))))))) (fun r ->
    let (y, tgm) = r in
    let (er, _) = y in
    let (_, nM) = tgm in
    let fenv =
      M.set fun_tag (((fun p->2*p) 1), (0 :: (1 :: [])))
        (M.set kon_tag (1, (0 :: [])) M.empty)
    in
    ret (Obj.magic monad_option) (((((cG, nM), fenv), ctag), itag), er))

(** val get_next : int -> int list -> (int * int) * int list **)

let rec get_next curr = function
| [] -> ((curr, (Coq_Pos.succ curr)), [])
| hd :: l' ->
  if Coq_Pos.eqb curr hd
  then get_next (Coq_Pos.succ curr) l'
  else ((curr, (Coq_Pos.succ curr)), (hd :: l'))

(** val get_n_next : int -> int list -> int -> (int list * int) * int list **)

let rec get_n_next curr l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (([], curr), l))
    (fun n' ->
    let (p, l0) = get_next curr l in
    let (x, curr0) = p in
    let (p0, l1) = get_n_next curr0 l0 n' in
    let (xs, curr1) = p0 in (((x :: xs), curr1), l1))
    n

(** val freshen_term : exp -> int M.t -> int -> int list -> (exp * int) * int list **)

let rec freshen_term e sigma curr l =
  match e with
  | Econstr (x, t0, ys, e0) ->
    let (p, l0) = get_next curr l in
    let (x', curr0) = p in
    let ys' = apply_r_list sigma ys in
    let (p0, l1) = freshen_term e0 (M.set x x' sigma) curr0 l0 in
    let (e', curr1) = p0 in (((Econstr (x', t0, ys', e')), curr1), l1)
  | Ecase (v, cl) ->
    let (p, l0) =
      let rec alpha_list br curr0 l0 =
        match br with
        | [] -> (([], curr0), l0)
        | h :: br' ->
          let (t0, e0) = h in
          let (p, l1) = freshen_term e0 sigma curr0 l0 in
          let (e', curr1) = p in
          let (p0, l2) = alpha_list br' curr1 l1 in
          let (br'', curr2) = p0 in ((((t0, e') :: br''), curr2), l2)
      in alpha_list cl curr l
    in
    let (cl', curr0) = p in (((Ecase ((apply_r sigma v), cl')), curr0), l0)
  | Eproj (x, t0, n, y, e0) ->
    let (p, l0) = get_next curr l in
    let (x', curr0) = p in
    let y' = apply_r sigma y in
    let (p0, l1) = freshen_term e0 (M.set x x' sigma) curr0 l0 in
    let (e', curr1) = p0 in (((Eproj (x', t0, n, y', e')), curr1), l1)
  | Efun (fds, e0) ->
    let f_names = all_fun_name fds in
    let (p, l0) = get_n_next curr l (length f_names) in
    let (f_names', curr0) = p in
    let sigma' = set_list (combine f_names f_names') sigma in
    let (p0, l1) = freshen_fun fds sigma' curr0 l0 in
    let (fds', curr1) = p0 in
    let (p1, l2) = freshen_term e0 sigma' curr1 l1 in
    let (e', curr2) = p1 in (((Efun (fds', e')), curr2), l2)
  | Eapp (f, t0, ys) ->
    let f' = apply_r sigma f in
    let ys' = apply_r_list sigma ys in (((Eapp (f', t0, ys')), curr), l)
  | Eprim (x, t0, ys, e0) ->
    let (p, l0) = get_next curr l in
    let (x', curr0) = p in
    let ys' = apply_r_list sigma ys in
    let (p0, l1) = freshen_term e0 (M.set x x' sigma) curr0 l0 in
    let (e', curr1) = p0 in (((Eprim (x', t0, ys', e')), curr1), l1)
  | Ehalt x -> let x' = apply_r sigma x in (((Ehalt x'), curr), l)

(** val freshen_fun :
    fundefs -> int M.t -> int -> int list -> (fundefs * int) * int list **)

and freshen_fun fds sigma curr l =
  match fds with
  | Fcons (f, t0, xs, e, fds0) ->
    let f' = apply_r sigma f in
    let (p, l0) = get_n_next curr l (length xs) in
    let (xs', curr0) = p in
    let sigma' = set_list (combine xs xs') sigma in
    let (p0, l1) = freshen_term e sigma' curr0 l0 in
    let (e', curr1) = p0 in
    let (p1, l2) = freshen_fun fds0 sigma curr1 l1 in
    let (fds', curr2) = p1 in (((Fcons (f', t0, xs', e', fds')), curr2), l2)
  | Fnil -> ((Fnil, curr), l)

type 'st inlineHeuristic = { update_funDef : (fundefs -> r_map -> 'st -> 'st * 'st);
                             update_inFun : (var -> tag -> var list -> exp -> r_map ->
                                            'st -> 'st);
                             update_App : (var -> tag -> var list -> 'st -> 'st * bool) }

(** val update_funDef : 'a1 inlineHeuristic -> fundefs -> r_map -> 'a1 -> 'a1 * 'a1 **)

let update_funDef x = x.update_funDef

(** val update_inFun :
    'a1 inlineHeuristic -> var -> tag -> var list -> exp -> r_map -> 'a1 -> 'a1 **)

let update_inFun x = x.update_inFun

(** val update_App :
    'a1 inlineHeuristic -> var -> tag -> var list -> 'a1 -> 'a1 * bool **)

let update_App x = x.update_App

type 't freshM = (int, 't) state

type r_map0 = var M.t

(** val freshen_exp : exp -> exp freshM **)

let freshen_exp e =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun curr ->
    let (p, _) = freshen_term e M.empty curr [] in
    let (e', n) = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put n) (fun _ -> ret (Obj.magic monad_state) e'))

(** val add_fundefs :
    fundefs -> ((tag * var list) * exp) M.t -> ((tag * var list) * exp) M.t **)

let rec add_fundefs fds del0 =
  match fds with
  | Fcons (f, t0, xs, e, fds0) -> M.set f ((t0, xs), e) (add_fundefs fds0 del0)
  | Fnil -> del0

(** val beta_contract_fds :
    'a1 inlineHeuristic -> fundefs -> ('a1 -> exp -> __ -> exp freshM) -> fundefs ->
    r_map0 -> 'a1 -> fundefs freshM **)

let rec beta_contract_fds iH fds fcon fdc sig0 s =
  match fdc with
  | Fcons (f, t0, xs, e, fdc') ->
    let s' = iH.update_inFun f t0 xs e sig0 s in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic fcon s' e __)
      (fun e' ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (beta_contract_fds iH fds fcon fdc' sig0 s) (fun fds' ->
        ret (Obj.magic monad_state) (Fcons (f, t0, xs, e', fds'))))
  | Fnil -> ret (Obj.magic monad_state) Fnil

(** val beta_contract_func :
    'a1 inlineHeuristic -> (int * exp, (var M.t, (((tag * var list) * exp) M.t, 'a1)
    sigT) sigT) sigT -> exp freshM **)

let rec beta_contract_func iH x =
  let de = projT1 x in
  let sig0 = projT1 (projT2 x) in
  let del0 = projT1 (projT2 (projT2 x)) in
  let s = projT2 (projT2 (projT2 x)) in
  let beta_contract0 = fun de0 sig1 del1 s0 ->
    beta_contract_func iH (ExistT (de0, (ExistT (sig1, (ExistT (del1, s0))))))
  in
  let (d, e) = de in
  let d0 = Obj.magic d in
  let e0 = Obj.magic e in
  (match e0 with
   | Econstr (x0, t0, ys, e1) ->
     let ys' = apply_r_list sig0 ys in
     Obj.magic pbind (pMonad_Monad monad_state) __
       (Obj.magic beta_contract0 (d0, e1) sig0 del0 s) (fun e' ->
       ret monad_state (Econstr (x0, t0, ys', e')))
   | Ecase (v, cl) ->
     let v' = apply_r sig0 v in
     Obj.magic pbind (pMonad_Monad monad_state) __
       (let rec beta_list br s0 =
          match br with
          | [] -> ret monad_state []
          | h :: br' ->
            let (t0, e1) = h in
            pbind (pMonad_Monad monad_state) (Obj.magic __)
              (Obj.magic beta_contract0 (d0, e1) sig0 del0 s0) (fun e' ->
              pbind (pMonad_Monad monad_state) (Obj.magic __) (beta_list br' s0)
                (fun br'' -> ret monad_state ((t0, e') :: br'')))
        in beta_list cl s) (fun cl' -> ret monad_state (Ecase (v', cl')))
   | Eproj (x0, t0, n, y, e1) ->
     let y' = apply_r sig0 y in
     Obj.magic pbind (pMonad_Monad monad_state) __
       (Obj.magic beta_contract0 (d0, e1) sig0 del0 s) (fun e' ->
       ret monad_state (Eproj (x0, t0, n, y', e')))
   | Efun (fds, e1) ->
     let del' = add_fundefs fds del0 in
     let (s1, s2) = iH.update_funDef fds sig0 s in
     Obj.magic pbind (pMonad_Monad monad_state) __
       (Obj.magic beta_contract0 (d0, e1) sig0 del' s1) (fun e' ->
       pbind (pMonad_Monad monad_state) (Obj.magic __)
         (Obj.magic beta_contract_fds iH fds (fun s0 e2 _ ->
           beta_contract0 (d0, e2) sig0 del' s0) fds sig0 s2) (fun fds' ->
         ret monad_state (Efun (fds', e'))))
   | Eapp (f, t0, ys) ->
     let f' = apply_r sig0 f in
     let ys' = apply_r_list sig0 ys in
     let (s0, inl) = iH.update_App f' t0 ys' s in
     let filtered_var = ((inl, (M.get f' del0)), d0) in
     let (p, n) = filtered_var in
     let (b, o) = p in
     if b
     then (match o with
           | Some p0 ->
             let (p1, e1) = p0 in
             let (_, xs) = p1 in
             ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic ret monad_state (Eapp (f', t0, ys')))
                (fun d' ->
                let xs0 = Obj.magic xs in
                let e2 = Obj.magic e1 in
                let d'0 = Obj.magic d' in
                let sig' = set_list (combine xs0 ys') sig0 in
                Obj.magic pbind (pMonad_Monad (Obj.magic monad_state)) __
                  (freshen_exp e2) (fun e' -> beta_contract0 (d'0, e') sig' del0 s0))
                n)
           | None -> Obj.magic ret monad_state (Eapp (f', t0, ys')))
     else Obj.magic ret monad_state (Eapp (f', t0, ys'))
   | Eprim (x0, t0, ys, e1) ->
     Obj.magic pbind (pMonad_Monad monad_state) __
       (Obj.magic beta_contract0 (d0, e1) sig0 del0 s) (fun e' ->
       let ys' = apply_r_list sig0 ys in ret monad_state (Eprim (x0, t0, ys', e')))
   | Ehalt x0 -> let x' = apply_r sig0 x0 in Obj.magic ret monad_state (Ehalt x'))

(** val beta_contract :
    'a1 inlineHeuristic -> (int * exp) -> var M.t -> ((tag * var list) * exp) M.t -> 'a1
    -> exp freshM **)

let beta_contract iH de sig0 del0 s =
  beta_contract_func iH (ExistT (de, (ExistT (sig0, (ExistT (del0, s))))))

(** val beta_contract_top : 'a1 inlineHeuristic -> exp -> int -> 'a1 -> exp **)

let beta_contract_top iH e d s =
  let n = Coq_Pos.add (max_var e 1) 1 in
  let (e', _) = runState (beta_contract iH (d, e) M.empty M.empty s) n in e'

(** val combineInlineHeuristic :
    (bool -> bool -> bool) -> 'a1 inlineHeuristic -> 'a2 inlineHeuristic -> ('a1 * 'a2)
    inlineHeuristic **)

let combineInlineHeuristic deci iH1 iH2 =
  { update_funDef = (fun fds sigma s ->
    let (s1, s2) = s in
    let (s11, s12) = iH1.update_funDef fds sigma s1 in
    let (s21, s22) = iH2.update_funDef fds sigma s2 in ((s11, s21), (s12, s22)));
    update_inFun = (fun f t0 xs e sigma s ->
    let (s1, s2) = s in
    let s1' = iH1.update_inFun f t0 xs e sigma s1 in
    let s2' = iH2.update_inFun f t0 xs e sigma s2 in (s1', s2')); update_App =
    (fun f t0 ys s ->
    let (s1, s2) = s in
    let (s1', b1) = iH1.update_App f t0 ys s1 in
    let (s2', b2) = iH2.update_App f t0 ys s2 in ((s1', s2'), (deci b1 b2))) }

(** val postUncurryIH : int M.t inlineHeuristic **)

let postUncurryIH =
  { update_funDef = (fun _ _ s -> (s, s)); update_inFun = (fun _ _ _ _ _ s -> s);
    update_App = (fun f _ ys s ->
    let o = M.get f s in
    (match o with
     | Some y ->
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (s, false))
          (fun n ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match ys with
            | [] -> (s, false)
            | k :: _ ->
              ((M.set f 0 (M.set k (Pervasives.succ (Pervasives.succ 0)) s)), true))
            (fun n0 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (s, true))
              (fun _ -> (s, false))
              n0)
            n)
          y)
     | None -> (s, false))) }

(** val inlineSmallIH : int -> bool M.t inlineHeuristic **)

let inlineSmallIH bound =
  { update_funDef = (fun fds sigma s ->
    let s' =
      let rec upd fds0 sigma0 s0 =
        match fds0 with
        | Fcons (f, _, _, e, fdc') ->
          if ltb (term_size e) bound
          then upd fdc' sigma0 (M.set f true s0)
          else upd fdc' sigma0 s0
        | Fnil -> s0
      in upd fds sigma s
    in
    (s', s')); update_inFun = (fun f _ _ _ _ s -> M.remove f s); update_App =
    (fun f _ _ s ->
    match M.get f s with
    | Some b -> if b then ((M.remove f s), true) else (s, false)
    | None -> (s, false)) }

(** val inlineSmallOrUncurried : int -> (bool M.t * int M.t) inlineHeuristic **)

let inlineSmallOrUncurried bound =
  combineInlineHeuristic (||) (inlineSmallIH bound) postUncurryIH

(** val inline_uncurry_contract : exp -> int M.t -> int -> int -> exp **)

let inline_uncurry_contract e s bound d =
  beta_contract_top (inlineSmallOrUncurried bound) e d (M.empty, s)

type st = int * int M.t

(** val eq_var : int -> int -> bool **)

let eq_var =
  Coq_Pos.eqb

(** val occurs_in_vars : var -> var list -> bool **)

let rec occurs_in_vars k = function
| [] -> false
| x :: xs1 -> (||) (eq_var k x) (occurs_in_vars k xs1)

(** val occurs_in_exp : var -> exp -> bool **)

let rec occurs_in_exp k = function
| Econstr (z, _, xs, e1) ->
  (||) ((||) (eq_var z k) (occurs_in_vars k xs)) (occurs_in_exp k e1)
| Ecase (x, arms) ->
  (||) (eq_var k x)
    (let rec occurs_in_arms = function
     | [] -> false
     | p :: arms1 -> let (_, e0) = p in (||) (occurs_in_exp k e0) (occurs_in_arms arms1)
     in occurs_in_arms arms)
| Eproj (z, _, _, x, e1) -> (||) ((||) (eq_var z k) (eq_var k x)) (occurs_in_exp k e1)
| Efun (fds, e0) -> (||) (occurs_in_fundefs k fds) (occurs_in_exp k e0)
| Eapp (x, _, xs) -> (||) (eq_var k x) (occurs_in_vars k xs)
| Eprim (z, _, xs, e1) ->
  (||) ((||) (eq_var z k) (occurs_in_vars k xs)) (occurs_in_exp k e1)
| Ehalt x -> eq_var x k

(** val occurs_in_fundefs : var -> fundefs -> bool **)

and occurs_in_fundefs k = function
| Fcons (z, _, zs, e, fds1) ->
  (||) ((||) ((||) (eq_var z k) (occurs_in_vars k zs)) (occurs_in_exp k e))
    (occurs_in_fundefs k fds1)
| Fnil -> false

type arrityMap = fTag M.t

type localMap = bool M.t

type stateType = (((((var * bool) * arrityMap) * fEnv) * fTag) * localMap) * st

type 't uncurryM = (stateType, 't) state

(** val markToInline : int -> var -> var -> unit uncurryM **)

let markToInline n f k =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, s0) = s in
    let (p0, lm) = p in
    let (p1, ft) = p0 in
    let (p2, fenv) = p1 in
    let (p3, aenv) = p2 in
    let (y, b) = p3 in
    (Obj.magic monadState_state).put ((((((y, b), aenv), fenv), ft), lm),
      ((Pervasives.max (fst s0) n),
      (M.set f (Pervasives.succ 0)
        (M.set k (Pervasives.succ (Pervasives.succ 0)) (snd s0))))))

(** val copyVar : var -> var uncurryM **)

let copyVar _ =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, s0) = s in
    let (p0, lm) = p in
    let (p1, ft) = p0 in
    let (p2, fenv) = p1 in
    let (p3, aenv) = p2 in
    let (y, b) = p3 in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put (((((((Coq_Pos.add y 1), b), aenv), fenv), ft),
        lm), s0)) (fun _ -> ret (Obj.magic monad_state) y))

(** val mark_as_uncurried : var -> unit uncurryM **)

let mark_as_uncurried x =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, s0) = s in
    let (p0, lm) = p in
    let (p1, ft) = p0 in
    let (p2, fenv) = p1 in
    let (p3, aenv) = p2 in
    let (y, b) = p3 in
    (Obj.magic monadState_state).put ((((((y, b), aenv), fenv), ft), (M.set x true lm)),
      s0))

(** val copyVars : var list -> var list uncurryM **)

let rec copyVars = function
| [] -> ret (Obj.magic monad_state) []
| x :: xs' ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic copyVar x)
    (fun y ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (copyVars xs')
      (fun ys -> ret (Obj.magic monad_state) (y :: ys)))

(** val click : unit uncurryM **)

let click =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, s0) = s in
    let (p0, lm) = p in
    let (p1, ft) = p0 in
    let (p2, fenv) = p1 in
    let (p3, aenv) = p2 in
    let (y, _) = p3 in
    (Obj.magic monadState_state).put ((((((y, true), aenv), fenv), ft), lm), s0))

(** val already_uncurried : var -> bool uncurryM **)

let already_uncurried f =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, _) = s in
    let (_, lm) = p in
    (match M.get f lm with
     | Some b -> ret (Obj.magic monad_state) b
     | None -> ret (Obj.magic monad_state) false))

(** val get_fTag : int -> fTag uncurryM **)

let get_fTag n =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun s ->
    let (p, s0) = s in
    let (p0, lm) = p in
    let (p1, ft) = p0 in
    let (p2, fenv) = p1 in
    let (p3, aenv) = p2 in
    let (y, b) = p3 in
    let p4 = N.succ_pos n in
    (match M.get p4 aenv with
     | Some t3 -> ret (Obj.magic monad_state) t3
     | None ->
       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
         ((Obj.magic monadState_state).put ((((((y, b), (M.set p4 ft aenv)),
           (M.set ft (n, (fromN 0 (N.to_nat n))) fenv)), (Coq_Pos.succ ft)), lm), s0))
         (fun _ -> ret (Obj.magic monad_state) ft)))

(** val uncurry_exp : exp -> exp uncurryM **)

let rec uncurry_exp = function
| Econstr (x, ct, vs, e1) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_exp e1)
    (fun e1' -> ret (Obj.magic monad_state) (Econstr (x, ct, vs, e1')))
| Ecase (x, arms) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (let rec uncurry_list = function
     | [] -> ret (Obj.magic monad_state) []
     | h :: t0 ->
       let (s, e0) = h in
       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_exp e0)
         (fun e' ->
         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_list t0)
           (fun t' -> ret (Obj.magic monad_state) ((s, e') :: t')))
     in uncurry_list arms) (fun arms' -> ret (Obj.magic monad_state) (Ecase (x, arms')))
| Eproj (x, ct, n, y, e1) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_exp e1)
    (fun e1' -> ret (Obj.magic monad_state) (Eproj (x, ct, n, y, e1')))
| Efun (fds, e1) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic uncurry_fundefs fds) (fun fds' ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_exp e1)
      (fun e1' -> ret (Obj.magic monad_state) (Efun (fds', e1'))))
| Eprim (x, p, xs, e1) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_exp e1)
    (fun e1' -> ret (Obj.magic monad_state) (Eprim (x, p, xs, e1')))
| x -> ret (Obj.magic monad_state) x

(** val uncurry_fundefs : fundefs -> fundefs uncurryM **)

and uncurry_fundefs = function
| Fcons (f, f_ft, fvs, fe, fds1) ->
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (uncurry_fundefs fds1)
    (fun fds1' ->
    match fvs with
    | [] ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic uncurry_exp fe) (fun fe' ->
        ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))
    | fk :: fvs0 ->
      (match fe with
       | Efun (f0, e) ->
         (match f0 with
          | Fcons (g, gt, gvs, ge, f1) ->
            (match f1 with
             | Fcons (_, _, _, _, _) ->
               pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                 (Obj.magic uncurry_exp fe) (fun fe' ->
                 ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))
             | Fnil ->
               (match e with
                | Eapp (fk', fk_ft, l) ->
                  (match l with
                   | [] ->
                     pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                       (Obj.magic uncurry_exp fe) (fun fe' ->
                       ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))
                   | g' :: l0 ->
                     (match l0 with
                      | [] ->
                        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                          (Obj.magic uncurry_exp ge) (fun ge' ->
                          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                            (Obj.magic already_uncurried g) (fun g_unc ->
                            if (&&)
                                 ((&&)
                                   ((&&) ((&&) (eq_var fk fk') (eq_var g g'))
                                     (negb (occurs_in_exp g ge)))
                                   (negb (occurs_in_exp fk ge))) (negb g_unc)
                            then pbind (pMonad_Monad (Obj.magic monad_state))
                                   (Obj.magic __) (Obj.magic copyVars gvs) (fun gvs' ->
                                   pbind (pMonad_Monad (Obj.magic monad_state))
                                     (Obj.magic __) (Obj.magic copyVars fvs0)
                                     (fun fvs' ->
                                     pbind (pMonad_Monad (Obj.magic monad_state))
                                       (Obj.magic __) (Obj.magic copyVar f) (fun f' ->
                                       pbind (pMonad_Monad (Obj.magic monad_state))
                                         (Obj.magic __) (Obj.magic mark_as_uncurried g)
                                         (fun _ ->
                                         pbind (pMonad_Monad (Obj.magic monad_state))
                                           (Obj.magic __) (Obj.magic click) (fun _ ->
                                           let fp_numargs = length (app gvs' fvs') in
                                           pbind (pMonad_Monad (Obj.magic monad_state))
                                             (Obj.magic __)
                                             (Obj.magic markToInline fp_numargs f g)
                                             (fun _ ->
                                             pbind
                                               (pMonad_Monad (Obj.magic monad_state))
                                               (Obj.magic __)
                                               (Obj.magic get_fTag (N.of_nat fp_numargs))
                                               (fun fp_ft ->
                                               ret (Obj.magic monad_state) (Fcons (f,
                                                 f_ft, (fk :: fvs'), (Efun ((Fcons (g,
                                                 gt, gvs', (Eapp (f', fp_ft,
                                                 (app gvs' fvs'))), Fnil)), (Eapp (fk,
                                                 fk_ft, (g :: []))))), (Fcons (f',
                                                 fp_ft, (app gvs fvs0), ge', fds1')))))))))))
                            else ret (Obj.magic monad_state) (Fcons (f, f_ft,
                                   (fk :: fvs0), (Efun ((Fcons (g, gt, gvs, ge', Fnil)),
                                   (Eapp (fk', fk_ft, (g' :: []))))), fds1'))))
                      | _ :: _ ->
                        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                          (Obj.magic uncurry_exp fe) (fun fe' ->
                          ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))))
                | _ ->
                  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                    (Obj.magic uncurry_exp fe) (fun fe' ->
                    ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))))
          | Fnil ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (Obj.magic uncurry_exp fe) (fun fe' ->
              ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1'))))
       | _ ->
         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
           (Obj.magic uncurry_exp fe) (fun fe' ->
           ret (Obj.magic monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))))
| Fnil -> ret (Obj.magic monad_state) Fnil

(** val uncurry :
    exp -> arrityMap -> fEnv -> fTag -> localMap -> int -> st ->
    ((((((exp * arrityMap) * fEnv) * fTag) * localMap) * var) * st) option **)

let uncurry e aenv fenv ft lm freshvar s =
  let (e0, s0) =
    runState (uncurry_exp e) ((((((freshvar, false), aenv), fenv), ft), lm), s)
  in
  let (p, s1) = s0 in
  let (p0, lm0) = p in
  let (p1, ft0) = p0 in
  let (p2, fenv0) = p1 in
  let (p3, aenv0) = p2 in
  let (maxvar, b) = p3 in
  if b then Some ((((((e0, aenv0), fenv0), ft0), lm0), maxvar), s1) else None

(** val uncurry_fuel' :
    int -> exp -> arrityMap -> fEnv -> fTag -> localMap -> int -> st -> (exp * st) * fEnv **)

let rec uncurry_fuel' n e aenv fenv ft lm freshvar s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((e, s), fenv))
    (fun m0 ->
    match uncurry e aenv fenv ft lm freshvar s with
    | Some p ->
      let (p0, s') = p in
      let (p1, freshvar0) = p0 in
      let (p2, lm') = p1 in
      let (p3, ft') = p2 in
      let (p4, fenv') = p3 in
      let (e', aenv') = p4 in uncurry_fuel' m0 e' aenv' fenv' ft' lm' freshvar0 s'
    | None -> ((e, s), fenv))
    n

(** val uncurry_fuel : int -> exp -> fEnv -> (exp * st) * fEnv **)

let uncurry_fuel n e fenv =
  let max_ft = M.fold (fun cm ft _ -> Coq_Pos.max cm ft) fenv 1 in
  let freshvar = Coq_Pos.add (max_var e 1) 1 in
  uncurry_fuel' n e M.empty fenv (Coq_Pos.succ max_ft) M.empty freshvar (0, M.empty)

(** val erase_fundefs :
    exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) -> exp * fundefs **)

let rec erase_fundefs e defs f =
  match e with
  | Econstr (x, tag0, ys, e') ->
    erase_fundefs e' defs (fun p ->
      let (e0, defs0) = p in f ((Econstr (x, tag0, ys, e0)), defs0))
  | Ecase (x, tes) ->
    fold_left (fun f0 te p ->
      let (c, e0) = te in
      let (e1, defs1) = p in
      erase_fundefs e0 defs1 (fun p2 ->
        let (e2, defs2) = p2 in
        (match e1 with
         | Ecase (x', tes') -> f0 ((Ecase (x', ((c, e2) :: tes'))), defs2)
         | _ -> f0 ((Ecase (x, ((c, e2) :: []))), defs2)))) tes f ((Ecase (x, [])), defs)
  | Eproj (x, tag0, n, y, e') ->
    erase_fundefs e' defs (fun p ->
      let (e0, defs0) = p in f ((Eproj (x, tag0, n, y, e0)), defs0))
  | Efun (fdefs, e') ->
    erase_fundefs e' defs (fun p ->
      let (e'', defs'') = p in erase_nested_fundefs fdefs e'' defs'' f)
  | Eprim (x, prim0, ys, e') ->
    erase_fundefs e' defs (fun p ->
      let (e'0, defs') = p in f ((Eprim (x, prim0, ys, e'0)), defs'))
  | x -> f (x, defs)

(** val erase_nested_fundefs :
    fundefs -> exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) -> exp * fundefs **)

and erase_nested_fundefs defs e hdefs f =
  match defs with
  | Fcons (g, t0, xs, e', defs0) ->
    erase_nested_fundefs defs0 e hdefs (fun p1 ->
      let (e1, defs1) = p1 in
      erase_fundefs e' defs1 (fun p2 ->
        let (e2, defs2) = p2 in f (e1, (Fcons (g, t0, xs, e2, defs2)))))
  | Fnil -> f (e, hdefs)

(** val exp_hoist : exp -> exp **)

let exp_hoist e =
  let (e0, defs) = erase_fundefs e Fnil id in
  (match defs with
   | Fcons (_, _, _, _, _) -> Efun (defs, e0)
   | Fnil -> e0)

type varInfo =
| FVar of int
| MRFun of var
| BoundVar

type varInfoMap = varInfo M.t

type state_contents = { next_var : var; nect_cTag : cTag; next_iTag : iTag; cenv : 
                        cEnv; name_env : name M.t }

(** val cenv : state_contents -> cEnv **)

let cenv x = x.cenv

(** val name_env : state_contents -> name M.t **)

let name_env x = x.name_env

type 't ccstate = (state_contents, 't) state

(** val get_name_entry : var -> name ccstate **)

let get_name_entry x =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var = _; nect_cTag = _; next_iTag = _; cenv = _; name_env = names } = p in
    (match PTree.get x names with
     | Some name0 -> ret (Obj.magic monad_state) name0
     | None -> ret (Obj.magic monad_state) NAnon))

(** val set_name_entry : var -> name -> unit ccstate **)

let set_name_entry x name0 =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var = n; nect_cTag = c; next_iTag = i; cenv = e; name_env = names } = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var = n; nect_cTag = c; next_iTag = i;
        cenv = e; name_env = (M.set x name0 names) }) (fun _ ->
      ret (Obj.magic monad_state) ()))

(** val add_name : var -> char list -> unit ccstate **)

let add_name fresh _ =
  set_name_entry fresh (NNamed ('e'::('n'::('v'::[]))))

(** val add_name_suff : var -> var -> char list -> unit ccstate **)

let add_name_suff fresh old suff =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic get_name_entry old) (fun oldn ->
    match oldn with
    | NAnon -> set_name_entry fresh (NNamed (append ('a'::('n'::('o'::('n'::[])))) suff))
    | NNamed s -> set_name_entry fresh (NNamed (append s suff)))

(** val clo_env_suffix : char list **)

let clo_env_suffix =
  '_'::('e'::('n'::('v'::[])))

(** val clo_suffix : char list **)

let clo_suffix =
  '_'::('c'::('l'::('o'::[])))

(** val code_suffix : char list **)

let code_suffix =
  '_'::('c'::('o'::('d'::('e'::[]))))

(** val proj_suffix : char list **)

let proj_suffix =
  '_'::('p'::('r'::('o'::('j'::[]))))

(** val get_name : var -> char list -> var ccstate **)

let get_name old_var suff =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var = n; nect_cTag = c; next_iTag = i; cenv = e; name_env = names } = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var = (Coq_Pos.add n 1); nect_cTag = c;
        next_iTag = i; cenv = e; name_env = names }) (fun _ ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic add_name_suff n old_var suff) (fun _ -> ret (Obj.magic monad_state) n)))

(** val get_name_no_suff : char list -> var ccstate **)

let get_name_no_suff name0 =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var = n; nect_cTag = c; next_iTag = i; cenv = e; name_env = names } = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var = (Coq_Pos.add n 1); nect_cTag = c;
        next_iTag = i; cenv = e; name_env = names }) (fun _ ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic add_name n name0) (fun _ -> ret (Obj.magic monad_state) n)))

(** val make_record_cTag : int -> cTag ccstate **)

let make_record_cTag n =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var = x; nect_cTag = c; next_iTag = i; cenv = e; name_env = names } = p in
    let inf = ((((NAnon, NAnon), i), n), 0) in
    let e' = M.set c inf e in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var = x; nect_cTag = (Coq_Pos.add c 1);
        next_iTag = (Coq_Pos.add i 1); cenv = e'; name_env = names }) (fun _ ->
      ret (Obj.magic monad_state) c))

(** val get_var :
    cTag -> var -> varInfoMap -> cTag -> var -> (var * (exp -> exp)) ccstate **)

let get_var clo_tag x map0 c _UU0393_ =
  match PTree.get x map0 with
  | Some entry ->
    (match entry with
     | FVar pos ->
       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
         (Obj.magic get_name x proj_suffix) (fun y ->
         ret (Obj.magic monad_state) (y, (fun e -> Eproj (y, c, pos, _UU0393_, e))))
     | MRFun code_ptr ->
       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
         (Obj.magic get_name x clo_suffix) (fun y ->
         ret (Obj.magic monad_state) (y, (fun e -> Econstr (y, clo_tag,
           (code_ptr :: (_UU0393_ :: [])), e))))
     | BoundVar -> ret (Obj.magic monad_state) (x, id))
  | None -> ret (Obj.magic monad_state) (x, id)

(** val get_vars :
    cTag -> var list -> varInfoMap -> cTag -> var -> (var list * (exp -> exp)) ccstate **)

let rec get_vars clo_tag xs map0 c _UU0393_ =
  match xs with
  | [] -> ret (Obj.magic monad_state) ([], id)
  | x :: xs0 ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (Obj.magic get_var clo_tag x map0 c _UU0393_) (fun t1 ->
      let (y, f) = t1 in
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (get_vars clo_tag xs0 map0 c _UU0393_) (fun t2 ->
        let (ys, f') = t2 in ret (Obj.magic monad_state) ((y :: ys), (fun e -> f (f' e)))))

(** val add_params : int list -> varInfoMap -> varInfoMap **)

let rec add_params args mapfv =
  match args with
  | [] -> mapfv
  | x :: xs -> M.set x BoundVar (add_params xs mapfv)

(** val make_env :
    cTag -> fVSet -> varInfoMap -> varInfoMap -> cTag -> var -> var ->
    ((cTag * varInfoMap) * (exp -> exp)) ccstate **)

let make_env clo_tag fv _ mapfv_old c_old _UU0393__new _UU0393__old =
  let fvs = PS.elements fv in
  let (map_new', n) =
    let rec add_fvs l n map0 =
      match l with
      | [] -> (map0, n)
      | x :: xs -> add_fvs xs (N.add n 1) (PTree.set x (FVar n) map0)
    in add_fvs fvs 0 PTree.empty
  in
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic get_vars clo_tag fvs mapfv_old c_old _UU0393__old) (fun t1 ->
    let (fv', g') = t1 in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (Obj.magic make_record_cTag n) (fun c_new ->
      ret (Obj.magic monad_state) ((c_new, map_new'), (fun e ->
        g' (Econstr (_UU0393__new, c_new, fv', e))))))

(** val make_full_closure :
    cTag -> fundefs -> varInfoMap -> varInfoMap -> var ->
    ((varInfoMap * varInfoMap) * (exp -> exp)) ccstate **)

let rec make_full_closure clo_tag defs mapfv_new mapfv_old _UU0393_ =
  match defs with
  | Fcons (f, _, _, _, defs') ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (Obj.magic get_name f code_suffix) (fun code_ptr ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (make_full_closure clo_tag defs' mapfv_new mapfv_old _UU0393_) (fun t0 ->
        let (p, g') = t0 in
        let (mapfv_new', mapfv_old') = p in
        let mapfv_new'' = PTree.set f (MRFun code_ptr) mapfv_new' in
        let mapfv_old'' = PTree.set f BoundVar mapfv_old' in
        ret (Obj.magic monad_state) ((mapfv_new'', mapfv_old''), (fun e -> Econstr (f,
          clo_tag, (code_ptr :: (_UU0393_ :: [])), (g' e))))))
  | Fnil -> ret (Obj.magic monad_state) ((mapfv_new, mapfv_old), id)

(** val exp_closure_conv :
    cTag -> exp -> varInfoMap -> cTag -> var -> (exp * (exp -> exp)) ccstate **)

let exp_closure_conv clo_tag =
  let rec exp_closure_conv0 e mapfv c _UU0393_ =
    match e with
    | Econstr (x, tag0, ys, e') ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_vars clo_tag ys mapfv c _UU0393_) (fun t1 ->
        let (ys', f) = t1 in
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) c _UU0393_) (fun ef ->
          ret (Obj.magic monad_state) ((Econstr (x, tag0, ys', (snd ef (fst ef)))), f)))
    | Ecase (x, pats) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (let rec mapM_cc = function
         | [] -> ret (Obj.magic monad_state) []
         | y0 :: xs ->
           let (y, e0) = y0 in
           pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
             (exp_closure_conv0 e0 mapfv c _UU0393_) (fun ef ->
             pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (mapM_cc xs)
               (fun xs' -> ret (Obj.magic monad_state) ((y, (snd ef (fst ef))) :: xs')))
         in mapM_cc pats) (fun pats' ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (Obj.magic get_var clo_tag x mapfv c _UU0393_) (fun t1 ->
          let (x', f1) = t1 in ret (Obj.magic monad_state) ((Ecase (x', pats')), f1)))
    | Eproj (x, tag0, n, y, e') ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag y mapfv c _UU0393_) (fun t1 ->
        let (y', f) = t1 in
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) c _UU0393_) (fun ef ->
          ret (Obj.magic monad_state) ((Eproj (x, tag0, n, y', (snd ef (fst ef)))), f)))
    | Efun (defs, e0) ->
      let fv = fundefs_fv defs in
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_name_no_suff ('e'::('n'::('v'::[])))) (fun _UU0393_' ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (Obj.magic make_env clo_tag fv PTree.empty mapfv c _UU0393_' _UU0393_)
          (fun t1 ->
          let (p, g1) = t1 in
          let (c', mapfv_new) = p in
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (Obj.magic make_full_closure clo_tag defs mapfv_new mapfv _UU0393_')
            (fun t2 ->
            let (p0, g2) = t2 in
            let (mapfv_new', mapfv_old') = p0 in
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (exp_closure_conv0 e0 mapfv_old' c _UU0393_) (fun ef ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (fundefs_closure_conv defs mapfv_new' c') (fun defs' ->
                ret (Obj.magic monad_state) ((Efun (defs', (g2 (snd ef (fst ef))))), g1))))))
    | Eapp (f, ft, xs) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag f mapfv c _UU0393_) (fun t1 ->
        let (f', g1) = t1 in
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (Obj.magic get_vars clo_tag xs mapfv c _UU0393_) (fun t2 ->
          let (xs', g2) = t2 in
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (Obj.magic get_name f code_suffix) (fun ptr ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (Obj.magic get_name f clo_env_suffix) (fun _UU0393_0 ->
              ret (Obj.magic monad_state) ((Eproj (ptr, clo_tag, 0, f', (Eproj
                (_UU0393_0, clo_tag, 1, f', (Eapp (ptr, ft, (_UU0393_0 :: xs'))))))),
                (fun e0 -> g1 (g2 e0)))))))
    | Eprim (x, prim0, ys, e') ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_vars clo_tag ys mapfv c _UU0393_) (fun t1 ->
        let (ys', f) = t1 in
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) c _UU0393_) (fun ef ->
          ret (Obj.magic monad_state) ((Eprim (x, prim0, ys', (snd ef (fst ef)))), f)))
    | Ehalt x ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag x mapfv c _UU0393_) (fun t1 ->
        let (x', f) = t1 in ret (Obj.magic monad_state) ((Ehalt x'), f))
  and fundefs_closure_conv defs mapfv c =
    match defs with
    | Fcons (f, tag0, ys, e, defs') ->
      let mapfv' = add_params ys mapfv in
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic get_name f clo_env_suffix) (fun _UU0393_ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (exp_closure_conv0 e mapfv' c _UU0393_) (fun ef ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (fundefs_closure_conv defs' mapfv c) (fun defs'' ->
            let code_ptr =
              match PTree.get f mapfv with
              | Some entry -> (match entry with
                               | MRFun ptr -> ptr
                               | _ -> f)
              | None -> f
            in
            ret (Obj.magic monad_state) (Fcons (code_ptr, tag0, (_UU0393_ :: ys),
              (snd ef (fst ef)), defs'')))))
    | Fnil -> ret (Obj.magic monad_state) Fnil
  in exp_closure_conv0

(** val closure_conversion_hoist :
    cTag -> exp -> cTag -> iTag -> cEnv -> name M.t -> (cEnv * name M.t) * exp **)

let closure_conversion_hoist clo_tag e ctag itag cenv' nmap =
  let _UU0393_ = Coq_Pos.add (max_var e 1) 1 in
  let next = Coq_Pos.add _UU0393_ 1 in
  let state1 = { next_var = next; nect_cTag = ctag; next_iTag = itag; cenv = cenv';
    name_env = nmap }
  in
  let (p, s) = runState (exp_closure_conv clo_tag e PTree.empty 1 _UU0393_) state1 in
  let (e0, f) = p in ((s.cenv, s.name_env), (exp_hoist (f e0)))

type varInfo0 = var
  (* singleton inductive, whose constructor was FreeVar *)

type funInfo =
| Fun of var * fTag * var list

type varInfoMap0 = varInfo0 PTree.t

type funInfoMap = funInfo PTree.t

type state_contents0 = { next_var0 : var; next_fTag : fTag }

type 't state0 = (state_contents0, 't) state

(** val get_name0 : var state0 **)

let get_name0 =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var0 = n; next_fTag = f } = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var0 = (Coq_Pos.add n 1); next_fTag = f })
      (fun _ -> ret (Obj.magic monad_state) n))

(** val get_names : int -> var list state0 **)

let rec get_names n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ret (Obj.magic monad_state) [])
    (fun n0 ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic get_name0)
      (fun x ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (get_names n0)
        (fun xs -> ret (Obj.magic monad_state) (x :: xs))))
    n

(** val get_tag : fTag state0 **)

let get_tag =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun p ->
    let { next_var0 = n; next_fTag = f } = p in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      ((Obj.magic monadState_state).put { next_var0 = n; next_fTag = (Coq_Pos.add f 1) })
      (fun _ -> ret (Obj.magic monad_state) f))

(** val rename : varInfoMap0 -> var -> var **)

let rename map0 x =
  match M.get x map0 with
  | Some inf -> inf
  | None -> x

(** val rename_lst : varInfoMap0 -> var list -> var list **)

let rename_lst map0 xs =
  map (rename map0) xs

(** val add_functions : fundefs -> var list -> funInfoMap -> funInfoMap state0 **)

let rec add_functions b fvs m0 =
  match b with
  | Fcons (f, _, _, _, b0) ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (add_functions b0 fvs m0) (fun m' ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic get_name0)
        (fun f' ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic get_tag)
          (fun ft' -> ret (Obj.magic monad_state) (M.set f (Fun (f', ft', fvs)) m'))))
  | Fnil -> ret (Obj.magic monad_state) m0

(** val add_free_vars : var list -> varInfoMap0 -> (var list * varInfoMap0) state0 **)

let rec add_free_vars fvs m0 =
  match fvs with
  | [] -> ret (Obj.magic monad_state) ([], m0)
  | y :: ys ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (add_free_vars ys m0)
      (fun p ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (Obj.magic get_name0)
        (fun y' ->
        let (ys', m') = p in ret (Obj.magic monad_state) ((y' :: ys'), (M.set y y' m'))))

(** val fundefs_true_fv_aux : funInfoMap -> fundefs -> fVSet -> PS.t -> fVSet * PS.t **)

let fundefs_true_fv_aux funmap =
  let rec exp_true_fv_aux e scope fvset =
    match e with
    | Econstr (x, _, ys, e0) ->
      let fvset' = add_list scope fvset ys in exp_true_fv_aux e0 (PS.add x scope) fvset'
    | Ecase (x, pats) ->
      let fvset' = fold_left (fun fvs p -> exp_true_fv_aux (snd p) scope fvs) pats fvset
      in
      if PS.mem x scope then fvset' else PS.add x fvset'
    | Eproj (x, _, _, y, e0) ->
      let fvset' = if PS.mem y scope then fvset else PS.add y fvset in
      exp_true_fv_aux e0 (PS.add x scope) fvset'
    | Efun (defs, e0) ->
      let (scope', fvset') = fundefs_true_fv_aux0 defs scope fvset in
      exp_true_fv_aux e0 scope' fvset'
    | Eapp (x, _, xs) ->
      let fvset' =
        match PTree.get x funmap with
        | Some inf -> let Fun (f', _, fvs) = inf in union_list0 fvset (f' :: fvs)
        | None -> if PS.mem x scope then fvset else PS.add x fvset
      in
      add_list scope fvset' xs
    | Eprim (x, _, ys, e0) ->
      let fvset' = add_list scope fvset ys in exp_true_fv_aux e0 (PS.add x scope) fvset'
    | Ehalt x -> if PS.mem x scope then fvset else PS.add x fvset
  and fundefs_true_fv_aux0 defs scope fvset =
    match defs with
    | Fcons (f, _, ys, e, defs') ->
      let (scope', fvset') = fundefs_true_fv_aux0 defs' (PS.add f scope) fvset in
      (scope', (exp_true_fv_aux e (union_list0 scope' ys) fvset'))
    | Fnil -> (scope, fvset)
  in fundefs_true_fv_aux0

(** val fundefs_true_fv : funInfoMap -> fundefs -> PS.t **)

let fundefs_true_fv funmap b =
  snd (fundefs_true_fv_aux funmap b PS.empty PS.empty)

(** val exp_lambda_lift : exp -> varInfoMap0 -> funInfoMap -> exp state0 **)

let rec exp_lambda_lift e fvm fm =
  match e with
  | Econstr (x, t0, ys, e0) ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (exp_lambda_lift e0 fvm fm) (fun e' ->
      ret (Obj.magic monad_state) (Econstr (x, t0, (rename_lst fvm ys), e')))
  | Ecase (x, p) ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (let rec mapM_ll = function
       | [] -> ret (Obj.magic monad_state) []
       | y :: p0 ->
         let (c, e0) = y in
         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
           (exp_lambda_lift e0 fvm fm) (fun e' ->
           pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (mapM_ll p0)
             (fun p' -> ret (Obj.magic monad_state) ((c, e') :: p')))
       in mapM_ll p) (fun p' -> ret (Obj.magic monad_state) (Ecase ((rename fvm x), p')))
  | Eproj (x, t0, n, y, e0) ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (exp_lambda_lift e0 fvm fm) (fun e' ->
      ret (Obj.magic monad_state) (Eproj (x, t0, n, (rename fvm y), e')))
  | Efun (b, e0) ->
    let fvs = PS.elements (fundefs_true_fv fm b) in
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (Obj.magic add_functions b fvs fm) (fun fm' ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (Obj.magic fundefs_lambda_lift b fvm fm') (fun b' ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (exp_lambda_lift e0 fvm fm') (fun e' ->
          ret (Obj.magic monad_state) (Efun (b', e')))))
  | Eapp (f, ft, xs) ->
    (match PTree.get f fm with
     | Some inf ->
       let Fun (f', ft', fvs) = inf in
       ret (Obj.magic monad_state) (Eapp ((rename fvm f'), ft',
         (rename_lst fvm (app xs fvs))))
     | None ->
       ret (Obj.magic monad_state) (Eapp ((rename fvm f), ft, (rename_lst fvm xs))))
  | Eprim (x, f, ys, e0) ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
      (exp_lambda_lift e0 fvm fm) (fun e' ->
      ret (Obj.magic monad_state) (Eprim (x, f, (rename_lst fvm ys), e')))
  | Ehalt x -> ret (Obj.magic monad_state) (Ehalt (rename fvm x))

(** val fundefs_lambda_lift : fundefs -> varInfoMap0 -> funInfoMap -> fundefs state0 **)

and fundefs_lambda_lift b fvm fm =
  match b with
  | Fcons (f, ft, xs, e, b0) ->
    (match M.get f fm with
     | Some inf ->
       let Fun (f', ft', fvs) = inf in
       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
         (Obj.magic add_free_vars fvs fvm) (fun p ->
         let (ys, fvm') = p in
         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
           (Obj.magic get_names (length xs)) (fun xs' ->
           pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
             (Obj.magic exp_lambda_lift e fvm' fm) (fun e' ->
             pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
               (fundefs_lambda_lift b0 fvm fm) (fun b' ->
               ret (Obj.magic monad_state) (Fcons (f', ft', (app xs ys), e', (Fcons (f,
                 ft, xs', (Eapp (f', ft', (app xs' (rename_lst fvm fvs)))), b'))))))))
     | None -> ret (Obj.magic monad_state) (Fcons (f, ft, xs, e, b0)))
  | Fnil -> ret (Obj.magic monad_state) Fnil

(** val lambda_lift : exp -> fTag -> exp **)

let lambda_lift e ftag =
  let next = Coq_Pos.add (max_var e 1) 1 in
  let state1 = { next_var0 = next; next_fTag = ftag } in
  let (e0, _) = runState (exp_lambda_lift e PTree.empty PTree.empty) state1 in e0

type dropping_fun =
| Dropping of var list list * bool list list

(** val bool_drop : dropping_fun -> bool list list **)

let rec bool_drop = function
| Dropping (_, bss) -> bss

(** val get_vars0 : fundefs -> var list list **)

let rec get_vars0 = function
| Fcons (_, _, xs, _, b') -> xs :: (get_vars0 b')
| Fnil -> []

(** val get_funs : fundefs -> var list **)

let rec get_funs = function
| Fcons (f, _, _, _, b') -> f :: (get_funs b')
| Fnil -> []

(** val get_bool_false : var list -> bool list **)

let rec get_bool_false = function
| [] -> []
| _ :: ys' -> false :: (get_bool_false ys')

(** val get_bool_true : var list -> bool list **)

let rec get_bool_true = function
| [] -> []
| _ :: ys' -> true :: (get_bool_true ys')

(** val get_bools : fundefs -> bool list list **)

let rec get_bools = function
| Fcons (_, _, ys, _, b') -> (get_bool_false ys) :: (get_bools b')
| Fnil -> []

(** val get_drop_initial : fundefs -> dropping_fun **)

let rec get_drop_initial b =
  let yss = get_vars0 b in let bss = get_bools b in Dropping (yss, bss)

(** val replace_nth : int -> 'a1 list -> 'a1 -> 'a1 list **)

let rec replace_nth n ys x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match ys with
              | [] -> ys
              | _ :: ys' -> x :: ys')
    (fun n' -> match ys with
               | [] -> ys
               | y :: ys' -> y :: (replace_nth n' ys' x))
    n

(** val find_fun : var -> var list -> int -> bool * int **)

let rec find_fun x funs n =
  match funs with
  | [] -> (false, n)
  | f :: funs' ->
    if peq f x then (true, n) else find_fun x funs' (add n (Pervasives.succ 0))

(** val add_escaping : var -> dropping_fun -> var list -> dropping_fun **)

let rec add_escaping x drop funs =
  let (b, n) = find_fun x funs 0 in
  if b
  then let Dropping (yss, bss) = drop in
       let ys = nth n yss [] in
       let bs = get_bool_true ys in
       let bss' = replace_nth n bss bs in Dropping (yss, bss')
  else drop

(** val add_escapings' : var list -> dropping_fun -> var list -> dropping_fun **)

let rec add_escapings' xs drop funs =
  match xs with
  | [] -> drop
  | x :: xs' -> add_escapings' xs' (add_escaping x drop funs) funs

(** val add_var_helper : var -> var list -> bool list -> bool list **)

let rec add_var_helper x ys bs =
  match ys with
  | [] -> bs
  | y :: ys' ->
    (match bs with
     | [] -> bs
     | b :: bs' -> if peq x y then true :: bs' else b :: (add_var_helper x ys' bs'))

(** val add_var : var -> dropping_fun -> int -> dropping_fun **)

let rec add_var x drop n =
  let Dropping (yss, bss) = drop in
  let ys = nth n yss [] in
  let bs = nth n bss [] in
  let bs' = add_var_helper x ys bs in
  let bss' = replace_nth n bss bs' in Dropping (yss, bss')

(** val add_vars : var list -> dropping_fun -> int -> dropping_fun **)

let rec add_vars xs drop n =
  match xs with
  | [] -> drop
  | x :: xs' -> add_vars xs' (add_var x drop n) n

(** val add_fun_args : int -> var list -> bool list -> dropping_fun -> dropping_fun **)

let rec add_fun_args n xs bs drop =
  match xs with
  | [] -> drop
  | x :: xs' ->
    (match bs with
     | [] -> drop
     | b :: bs' ->
       if eqb0 b true
       then let drop' = add_var x drop n in add_fun_args n xs' bs' drop'
       else add_fun_args n xs' bs' drop)

(** val add_fun_vars :
    var -> var list -> var list -> dropping_fun -> int -> dropping_fun **)

let rec add_fun_vars f funs xs drop m0 =
  let (b, n) = find_fun f funs 0 in
  if b
  then let bss = bool_drop drop in let bs = nth n bss [] in add_fun_args m0 xs bs drop
  else add_vars xs drop m0

(** val escaping_fun_exp : exp -> dropping_fun -> var list -> dropping_fun **)

let rec escaping_fun_exp e drop funs =
  match e with
  | Econstr (_, _, ys, e') -> escaping_fun_exp e' (add_escapings' ys drop funs) funs
  | Ecase (_, p) ->
    let rec mapM_LD l drop0 =
      match l with
      | [] -> drop0
      | p0 :: l' ->
        let (_, e') = p0 in
        let drop' = escaping_fun_exp e' drop0 funs in mapM_LD l' drop'
    in mapM_LD p drop
  | Eproj (_, _, _, _, e') -> escaping_fun_exp e' drop funs
  | Eapp (_, _, ys) -> add_escapings' ys drop funs
  | Eprim (_, _, _, e') -> escaping_fun_exp e' drop funs
  | _ -> drop

(** val escaping_fun_fundefs : fundefs -> dropping_fun -> var list -> dropping_fun **)

let rec escaping_fun_fundefs b drop funs =
  match b with
  | Fcons (_, _, _, e, b') ->
    let drop' = escaping_fun_exp e drop funs in escaping_fun_fundefs b' drop' funs
  | Fnil -> drop

(** val live_expr : fundefs -> dropping_fun -> var list -> int -> exp -> dropping_fun **)

let rec live_expr b drop funs n = function
| Econstr (_, _, ys, e') -> let drop' = add_vars ys drop n in live_expr b drop' funs n e'
| Ecase (x, p) ->
  let drop' = add_var x drop n in
  let rec mapM_LD l drop0 =
    match l with
    | [] -> drop0
    | p0 :: l' ->
      let (_, e') = p0 in let drop'0 = live_expr b drop0 funs n e' in mapM_LD l' drop'0
  in mapM_LD p drop'
| Eproj (_, _, _, y, e') -> let drop' = add_var y drop n in live_expr b drop' funs n e'
| Efun (_, _) -> drop
| Eapp (f, _, ys) -> let drop' = add_var f drop n in add_fun_vars f funs ys drop' n
| Eprim (_, f, ys, e') ->
  let drop' = add_var f drop n in
  let drop'' = add_vars ys drop' n in live_expr b drop'' funs n e'
| Ehalt x -> add_var x drop n

(** val live : fundefs -> dropping_fun -> var list -> int -> dropping_fun **)

let rec live b drop funs n =
  match b with
  | Fcons (_, _, _, e, b') ->
    let drop' = live_expr b drop funs n e in
    live b' drop' funs (add n (Pervasives.succ 0))
  | Fnil -> drop

(** val check_list_equality : bool list -> bool list -> bool **)

let rec check_list_equality l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | hd1 :: tl1 ->
    (match l2 with
     | [] -> false
     | hd2 :: tl2 -> if eqb0 hd1 hd2 then check_list_equality tl1 tl2 else false)

(** val check_list_list_equality : bool list list -> bool list list -> bool **)

let rec check_list_list_equality l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | hd1 :: tl1 ->
    (match l2 with
     | [] -> false
     | hd2 :: tl2 ->
       if check_list_equality hd1 hd2 then check_list_list_equality tl1 tl2 else false)

(** val drop_equality : dropping_fun -> dropping_fun -> bool **)

let rec drop_equality drop1 drop2 =
  let Dropping (_, bss1) = drop1 in
  let Dropping (_, bss2) = drop2 in check_list_list_equality bss1 bss2

(** val num_vars : fundefs -> int -> int **)

let rec num_vars b n =
  match b with
  | Fcons (_, _, xs, _, b') -> num_vars b' (add n (length xs))
  | Fnil -> n

(** val find_drop_helper : fundefs -> dropping_fun -> var list -> int -> dropping_fun **)

let rec find_drop_helper b prev_drop funs n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> prev_drop)
    (fun n' ->
    let curr_drop = live b prev_drop funs 0 in
    if drop_equality prev_drop curr_drop
    then prev_drop
    else find_drop_helper b curr_drop funs n')
    n

(** val find_drop : exp -> dropping_fun **)

let rec find_drop = function
| Efun (b, e') ->
  let funs = get_funs b in
  let initial_drop = get_drop_initial b in
  let drop' = escaping_fun_exp e' (escaping_fun_fundefs b initial_drop funs) funs in
  let n = num_vars b 0 in find_drop_helper b drop' funs n
| _ -> Dropping (([] :: []), ([] :: []))

(** val drop_args : var list -> bool list -> var list **)

let rec drop_args ys bs =
  match ys with
  | [] -> ys
  | y :: ys' ->
    (match bs with
     | [] -> ys
     | b :: bs' -> if eqb0 b true then y :: (drop_args ys' bs') else drop_args ys' bs')

(** val dropper_expr : dropping_fun -> var list -> exp -> exp **)

let rec dropper_expr drop funs e = match e with
| Econstr (x, t0, ys, e') -> Econstr (x, t0, ys, (dropper_expr drop funs e'))
| Ecase (x, p) ->
  let p' =
    let rec mapM_LD l = match l with
    | [] -> l
    | p0 :: l' -> let (c', e') = p0 in (c', (dropper_expr drop funs e')) :: (mapM_LD l')
    in mapM_LD p
  in
  Ecase (x, p')
| Eproj (x, t0, m0, y, e') -> Eproj (x, t0, m0, y, (dropper_expr drop funs e'))
| Efun (_, _) -> e
| Eapp (f, t0, ys) ->
  let (b, n) = find_fun f funs 0 in
  if b
  then let bss = bool_drop drop in
       let ys' = drop_args ys (nth n bss []) in Eapp (f, t0, ys')
  else Eapp (f, t0, ys)
| Eprim (x, f, ys, e') -> Eprim (x, f, ys, (dropper_expr drop funs e'))
| Ehalt x -> Ehalt x

(** val dropper_fundefs : fundefs -> dropping_fun -> var list -> int -> fundefs **)

let rec dropper_fundefs b drop funs n =
  let Dropping (_, bss) = drop in
  (match b with
   | Fcons (f, ft, ys, e, b') ->
     let ys' = drop_args ys (nth n bss []) in
     let e' = dropper_expr drop funs e in
     Fcons (f, ft, ys', e', (dropper_fundefs b' drop funs (add n (Pervasives.succ 0))))
   | Fnil -> b)

(** val dropper : exp -> exp **)

let rec dropper e = match e with
| Efun (b, e') ->
  let funs = get_funs b in
  let drop = find_drop e in
  let b' = dropper_fundefs b drop funs 0 in
  let e'' = dropper_expr drop funs e' in Efun (b', e'')
| _ -> e

(** val print : char list -> unit **)

let print = (fun s-> print_string (String.concat "" (List.map (String.make 1) s)))

type l6env = ((prims * cEnv) * nEnv) * fEnv

type l6term = env * exp

type l6val = val0

(** val default_cTag : int **)

let default_cTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))

(** val default_iTag : int **)

let default_iTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))

(** val bogus_cloTag : int **)

let bogus_cloTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val bogus_cloiTag : int **)

let bogus_cloiTag =
  (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val fun_fTag : int **)

let fun_fTag =
  (fun p->1+2*p) 1

(** val kon_fTag : int **)

let kon_fTag =
  (fun p->2*p) 1

(** val certiL5_t0_L6 :
    ((ienv * l5Term, ienv * l5Term) cTerm, (l6env * l6term, l6val) cTerm)
    certicoqTranslation **)

let certiL5_t0_L6 v =
  match convert_top default_cTag default_iTag fun_fTag kon_fTag v with
  | Some r ->
    let (p, e) = r in
    let (p0, next_iTag0) = p in
    let (p1, next_cTag) = p0 in
    let (p2, fenv) = p1 in
    let (cenv0, nenv) = p2 in
    let (p3, _) =
      uncurry_fuel (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (shrink_top e) fenv
    in
    let (e0, s0) = p3 in
    let (_, s) = s0 in
    let e1 =
      inline_uncurry_contract e0 s (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))
    in
    let e2 = shrink_top e1 in
    let e3 = lambda_lift e2 next_iTag0 in
    let (p4, t') =
      closure_conversion_hoist bogus_cloTag e3 next_cTag next_iTag0 cenv0 nenv
    in
    let (cenv', nenv') = p4 in
    Ret ((((M.empty, (add_cloTag bogus_cloTag bogus_cloiTag cenv')), nenv'), M.empty),
    (M.empty, (shrink_top t')))
  | None ->
    Exc
      ('f'::('a'::('i'::('l'::('e'::('d'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('n'::('g'::(' '::('f'::('r'::('o'::('m'::(' '::('L'::('5'::(' '::('t'::('o'::(' '::('L'::('6'::[])))))))))))))))))))))))))))))))

type nEnv0 = name M.t

(** val show_pos : int -> char list **)

let show_pos x =
  nat2string10 (Coq_Pos.to_nat x)

(** val show_binnat : int -> char list **)

let show_binnat x =
  nat2string10 (N.to_nat x)

(** val sep : 'a1 -> 'a1 list -> 'a1 list **)

let rec sep s = function
| [] -> []
| h :: t0 -> (match t0 with
              | [] -> h :: []
              | _ :: _ -> h :: (s :: (sep s t0)))

type string_tree =
| Emp
| Str of char list
| App of string_tree * string_tree

(** val show_tree_c : string_tree -> char list -> char list **)

let rec show_tree_c t0 acc =
  match t0 with
  | Emp -> acc
  | Str s -> append s acc
  | App (t1, t2) -> show_tree_c t1 (show_tree_c t2 acc)

(** val show_tree : string_tree -> char list **)

let show_tree t0 =
  show_tree_c t0 []

(** val show_var : nEnv0 -> int -> string_tree **)

let show_var nenv x =
  match M.get x nenv with
  | Some n ->
    (match n with
     | NAnon -> App ((Str ('x'::[])), (Str (show_pos x)))
     | NNamed s -> App ((App ((Str s), (Str ('_'::[])))), (Str (show_pos x))))
  | None -> App ((Str ('x'::[])), (Str (show_pos x)))

(** val show_con : cEnv -> cTag -> string_tree **)

let show_con cenv0 tg =
  match M.get tg cenv0 with
  | Some c ->
    let (p, _) = c in
    let (p0, _) = p in
    let (p1, _) = p0 in
    let (n0, _) = p1 in
    (match n0 with
     | NAnon -> App ((Str ('c'::('o'::('n'::('_'::[]))))), (Str (show_pos tg)))
     | NNamed s -> Str s)
  | None -> App ((Str ('c'::('o'::('n'::('_'::[]))))), (Str (show_pos tg)))

(** val show_ftag : bool -> fTag -> string_tree **)

let show_ftag ftag_flag tg =
  if ftag_flag
  then App ((App ((Str ('<'::[])), (Str (show_pos tg)))), (Str ('>'::[])))
  else Str []

(** val show_vars : nEnv0 -> int list -> string_tree **)

let show_vars nenv xs =
  App ((App ((Str ('('::[])),
    (fold_right (fun x y -> App (x, y)) (Str [])
      (sep (Str (','::[])) (map (show_var nenv) xs))))), (Str (')'::[])))

type 't m = (string_tree, 't) state

(** val emit : string_tree -> unit m **)

let emit s =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
    (Obj.magic monadState_state).get (fun st0 ->
    (Obj.magic monadState_state).put (App (st0, s)))

(** val tab : int -> unit m **)

let rec tab n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ret (Obj.magic monad_state) ())
    (fun n0 ->
    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (emit (Str (' '::[])))
      (fun _ -> tab n0))
    n

(** val chr_newline : char **)

let chr_newline =
  '\n'

(** val newline : unit m **)

let newline =
  emit (Str (chr_newline::[]))

(** val emit_exp : nEnv0 -> cEnv -> bool -> int -> exp -> unit m **)

let rec emit_exp nenv cenv0 ftag_flag indent e =
  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (tab indent) (fun _ ->
    match e with
    | Econstr (x, tg, xs, e0) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('l'::('e'::('t'::(' '::[])))))) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_var nenv x)) (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (emit (Str (' '::(':'::('='::(' '::[])))))) (fun _ ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (emit (show_con cenv0 tg)) (fun _ ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (emit (show_vars nenv xs)) (fun _ ->
                pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                  (emit (Str (' '::('i'::('n'::(' '::[])))))) (fun _ ->
                  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) newline
                    (fun _ -> emit_exp nenv cenv0 ftag_flag indent e0)))))))
    | Ecase (x, arms) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('c'::('a'::('s'::('e'::(' '::[]))))))) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_var nenv x)) (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (emit (Str (' '::('o'::('f'::(' '::('{'::[]))))))) (fun _ ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) newline
              (fun _ ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (let rec iter0 = function
                 | [] -> ret (Obj.magic monad_state) ()
                 | p :: tail ->
                   let (tg, e0) = p in
                   pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                     (tab indent) (fun _ ->
                     pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                       (emit (Str ('|'::(' '::[])))) (fun _ ->
                       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                         (emit (show_con cenv0 tg)) (fun _ ->
                         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                           (emit (Str (' '::('='::('>'::(' '::[])))))) (fun _ ->
                           pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                             newline (fun _ ->
                             pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                               (emit_exp nenv cenv0 ftag_flag
                                 (add (Pervasives.succ (Pervasives.succ 0)) indent) e0)
                               (fun _ -> iter0 tail))))))
                 in iter0 arms) (fun _ ->
                pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (tab indent)
                  (fun _ ->
                  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                    (emit (Str ('}'::[]))) (fun _ -> newline)))))))
    | Eproj (x, tg, n, y, e0) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('l'::('e'::('t'::(' '::[])))))) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_var nenv x)) (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (emit (Str
              (' '::(':'::('='::(' '::('p'::('r'::('o'::('j'::('_'::[])))))))))))
            (fun _ ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (emit (Str (show_binnat n))) (fun _ ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (emit (Str (' '::[]))) (fun _ ->
                pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                  (emit (Str (show_pos tg))) (fun _ ->
                  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                    (emit (Str (' '::[]))) (fun _ ->
                    pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                      (emit (show_var nenv y)) (fun _ ->
                      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                        (emit (Str (' '::('i'::('n'::(' '::[])))))) (fun _ ->
                        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                          newline (fun _ -> emit_exp nenv cenv0 ftag_flag indent e0))))))))))
    | Efun (fds, e0) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('l'::('e'::('t'::('r'::('e'::('c'::(' '::('['::[]))))))))))
        (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) newline (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (let rec iter0 = function
             | Fcons (x, tg, xs, e1, fds') ->
               pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                 (tab (add (Pervasives.succ (Pervasives.succ 0)) indent)) (fun _ ->
                 pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                   (emit (Str ('f'::('u'::('n'::(' '::[])))))) (fun _ ->
                   pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                     (emit (show_var nenv x)) (fun _ ->
                     pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                       (emit (show_ftag ftag_flag tg)) (fun _ ->
                       pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                         (emit (show_vars nenv xs)) (fun _ ->
                         pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                           (emit (Str (' '::(':'::('='::(' '::[])))))) (fun _ ->
                           pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                             newline (fun _ ->
                             pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                               (emit_exp nenv cenv0 ftag_flag
                                 (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0)))) indent) e1) (fun _ ->
                               iter0 fds'))))))))
             | Fnil -> ret (Obj.magic monad_state) ()
             in iter0 fds) (fun _ ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) (tab indent)
              (fun _ ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (emit (Str (']'::(' '::('i'::('n'::[])))))) (fun _ ->
                pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) newline
                  (fun _ -> emit_exp nenv cenv0 ftag_flag indent e0))))))
    | Eapp (x, ft, ys) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (show_var nenv x)) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_ftag ftag_flag ft)) (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (emit (show_vars nenv ys)) (fun _ -> newline)))
    | Eprim (x, p, ys, e0) ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('l'::('e'::('t'::(' '::[])))))) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_var nenv x)) (fun _ ->
          pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
            (emit (Str
              (' '::(':'::('='::(' '::('p'::('r'::('i'::('m'::('_'::[])))))))))))
            (fun _ ->
            pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
              (emit (Str (show_pos p))) (fun _ ->
              pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                (emit (show_vars nenv ys)) (fun _ ->
                pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
                  (emit (Str (' '::('i'::('n'::(' '::[])))))) (fun _ ->
                  pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __) newline
                    (fun _ -> emit_exp nenv cenv0 ftag_flag indent e0)))))))
    | Ehalt x ->
      pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
        (emit (Str ('h'::('a'::('l'::('t'::(' '::[]))))))) (fun _ ->
        pbind (pMonad_Monad (Obj.magic monad_state)) (Obj.magic __)
          (emit (show_var nenv x)) (fun _ -> newline)))

(** val show_exp : nEnv0 -> cEnv -> bool -> exp -> char list **)

let show_exp nenv cenv0 ftag_flag x =
  chr_newline::(show_tree (snd (runState (emit_exp nenv cenv0 ftag_flag 0 x) Emp)))

(** val concat : char list -> char list -> char list **)

let concat = List.append

(** val comp_L6 :
    (ienv * l5Term, ienv * l5Term) cTerm exception0 -> (l6env * l6term, l6val) cTerm
    exception0 **)

let comp_L6 = function
| Exc s -> Exc s
| Ret v -> certiL5_t0_L6 v

(** val test1_L5 : (ienv * l5Term, ienv * l5Term) cTerm exception0 **)

let test1_L5 =
  Ret
    (((('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[])))))))))))))))))))))),
    ({ itypNm = ('n'::('a'::('t'::[]))); itypCnstrs = ({ cnstrNm = ('O'::[]);
    cnstrArity = 0 } :: ({ cnstrNm = ('S'::[]); cnstrArity = (Pervasives.succ
    0) } :: [])) } :: [])) :: []), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Oterm (CLambda, ((Bterm (((((fun p->2*p) 1), (NNamed
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('N'::('a'::('t'::('.'::('a'::('d'::('d'::[])))))))))))))))))) :: ((((fun p->1+2*p)
    1), (NNamed ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda,
    ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []),
    (Oterm (CRet, ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: ((Bterm ([], (Oterm (CLambda, ((Bterm (((((fun p->2*p)
    ((fun p->2*p) 1)), (NNamed
    ('T'::('o'::('p'::('#'::('T'::('E'::('S'::('T'::('_'::('L'::('6'::('#'::('s'::('i'::('m'::('p'::('l'::('e'::('_'::('t'::('e'::('s'::('t'::[]))))))))))))))))))))))))) :: ((((fun p->1+2*p)
    1), (NNamed ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda,
    ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm
    (((fun p->2*p) ((fun p->2*p) 1)), (NNamed
    ('T'::('o'::('p'::('#'::('T'::('E'::('S'::('T'::('_'::('L'::('6'::('#'::('s'::('i'::('m'::('p'::('l'::('e'::('_'::('t'::('e'::('s'::('t'::[])))))))))))))))))))))))))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Oterm (CLambda, ((Bterm (((((fun p->2*p) ((fun p->2*p) 1)), (NNamed
    ('x'::[]))) :: ((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: [])), (Oterm (CRet,
    ((Bterm ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: ((Bterm ([], (Oterm (CLambda, ((Bterm (((((fun p->2*p)
    ((fun p->1+2*p) 1)), (NNamed ('y'::[]))) :: ((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->2*p) 1), (NNamed
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('N'::('a'::('t'::('.'::('a'::('d'::('d'::[]))))))))))))))))))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Vterm (((fun p->2*p) ((fun p->2*p) 1)), (NNamed
    ('x'::[])))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Oterm ((CDCon (({ inductive_mind =
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[]))))))))))))))))))))));
    inductive_ind = 0 }, 1), (Pervasives.succ 0))), ((Bterm ([], (Oterm ((CDCon
    (({ inductive_mind =
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[]))))))))))))))))))))));
    inductive_ind = 0 }, 0), 0)), [])))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Vterm
    (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Oterm ((CFix ((Pervasives.succ 0), 0)), ((Bterm (((((fun p->2*p) 1), (NNamed
    ('a'::('d'::('d'::[]))))) :: []), (Oterm (CLambda, ((Bterm (((((fun p->2*p)
    ((fun p->2*p) 1)), (NNamed ('n'::[]))) :: ((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm
    (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([], (Oterm (CLambda, ((Bterm
    (((((fun p->2*p) ((fun p->1+2*p) 1)), (NNamed ('m'::[]))) :: ((((fun p->1+2*p) 1),
    (NNamed ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Vterm (((fun p->2*p) ((fun p->2*p) 1)), (NNamed
    ('n'::[])))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed ('k'::('m'::('d'::[]))))) :: []),
    (Oterm ((CMatch ((({ inductive_mind =
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[]))))))))))))))))))))));
    inductive_ind = 0 }, 0), 0) :: ((({ inductive_mind =
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[]))))))))))))))))))))));
    inductive_ind = 0 }, 1), (Pervasives.succ 0)) :: []))), ((Bterm ([], (Vterm
    (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed ('k'::('m'::('d'::[])))))))) :: ((Bterm
    ([], (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1),
    (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->2*p) ((fun p->1+2*p) 1)),
    (NNamed ('m'::[])))))) :: [])))))) :: []))))) :: ((Bterm ([], (Vterm
    (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: [])))))) :: ((Bterm (((((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1))), NAnon) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: ((Bterm ([], (Oterm (CLambda, ((Bterm (((((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1))), (NNamed ('p'::[]))) :: ((((fun p->1+2*p) 1),
    (NNamed ('k'::[]))) :: [])), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed
    ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet, ((Bterm ([], (Vterm
    (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->2*p)
    1), (NNamed ('a'::('d'::('d'::[])))))))) :: [])))))) :: []))))) :: ((Bterm ([],
    (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Vterm (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))), (NNamed
    ('p'::[])))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Vterm (((fun p->2*p) ((fun p->1+2*p) 1)), (NNamed
    ('m'::[])))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('x'::('0'::('k'::('d'::('c'::('o'::('n'::[]))))))))) :: []), (Oterm (CRet, ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([], (Oterm
    ((CDCon (({ inductive_mind =
    ('C'::('o'::('q'::('.'::('I'::('n'::('i'::('t'::('.'::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::('s'::('.'::('n'::('a'::('t'::[]))))))))))))))))))))));
    inductive_ind = 0 }, 1), (Pervasives.succ 0))), ((Bterm ([], (Vterm (((fun p->1+2*p)
    ((fun p->2*p) 1)), (NNamed
    ('x'::('0'::('k'::('d'::('c'::('o'::('n'::[])))))))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[])))))) :: []), (Oterm (CRet, ((Bterm ([], (Oterm
    (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []), (Oterm (CRet,
    ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed ('k'::[])))))) :: ((Bterm ([],
    (Vterm (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))),
    NAnon)))) :: [])))))) :: []))))) :: ((Bterm ([], (Oterm (CKLambda, ((Bterm
    (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm ([], (Vterm
    (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: [])))))) :: []))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) ((fun p->1+2*p) 1)), (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[])))))))) :: []), (Oterm (CCall, ((Bterm ([],
    (Vterm (((fun p->1+2*p) ((fun p->2*p) 1)), (NNamed
    ('k'::('a'::('p'::('f'::[]))))))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) 1),
    (NNamed ('k'::[])))))) :: ((Bterm ([], (Vterm (((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (NNamed
    ('k'::('a'::('p'::('A'::('r'::('g'::[]))))))))))) :: []))))))) :: []))))) :: [])))))) :: []))))) :: [])))))) :: []))))) :: ((Bterm
    ([], (Oterm (CKLambda, ((Bterm (((((fun p->1+2*p) 1), (NNamed ('k'::[]))) :: []),
    (Oterm (CHalt, ((Bterm ([], (Vterm (((fun p->1+2*p) 1), (NNamed
    ('k'::[])))))) :: []))))) :: []))))) :: [])))))

(** val compL6_and_print_twice :
    (ienv * l5Term, ienv * l5Term) cTerm exception0 -> unit **)

let compL6_and_print_twice testL5 =
  match comp_L6 testL5 with
  | Exc _ ->
    print
      ('F'::('a'::('i'::('l'::('e'::('d'::(' '::('d'::('u'::('r'::('i'::('n'::('g'::(' '::('c'::('o'::('m'::('p'::('_'::('L'::('6'::[])))))))))))))))))))))
  | Ret c ->
    let (l, l0) = c in
    let (p, _) = l in
    let (p0, cenv0) = p in
    let (_, cenv') = p0 in
    let (_, t0) = l0 in
    let x =
      'B'::('e'::('f'::('o'::('r'::('e'::(' '::('d'::('r'::('o'::('p'::('p'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))
    in
    let y = concat x (show_exp cenv0 cenv' true t0) in
    let z =
      concat y
        ('A'::('f'::('t'::('e'::('r'::(' '::('d'::('r'::('o'::('p'::('p'::('i'::('n'::('g'::('\\'::('n'::[]))))))))))))))))
    in
    let w = concat z (show_exp cenv0 cenv' true (dropper t0)) in print w

(** val out1 : unit **)

let out1 =
  compL6_and_print_twice test1_L5

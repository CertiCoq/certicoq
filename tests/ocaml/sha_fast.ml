
type unit0 =
| Tt

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> True
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> False
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> True
             | Npos _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.coq_lxor p q)

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> False
    | Npos p -> Coq_Pos.testbit p n0
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> True
    | _ -> False

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> False
  | Zpos p -> (match p with
               | XO _ -> False
               | _ -> True)
  | Zneg p -> (match p with
               | XO _ -> False
               | _ -> True)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> False
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> False

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

(** val z_le_gt_dec : z -> z -> sumbool **)

let z_le_gt_dec =
  z_le_dec

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

type string =
| EmptyString
| String of ascii * string

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n0 z0 =
  match n0 with
  | O -> z0
  | S n1 -> XO (shift_nat n1 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val zeq : z -> z -> sumbool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> sumbool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> sumbool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : sumbool -> bool **)

let proj_sumbool = function
| Left -> True
| Right -> False

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  match b with
  | True -> Z.succ_double x
  | False -> Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ ->
    Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
    (fun x0 ->
    match match Z.odd x0 with
          | True -> proj_sumbool (zlt Z0 n0)
          | False -> False with
    | True -> Zneg XH
    | False -> Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x i =
  match n0 with
  | O -> Nil
  | S m ->
    (match Z.odd x with
     | True -> Cons (i, (z_one_bits m (Z.div2 x) (Z.add i (Zpos XH))))
     | False -> z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> False
| XO q -> p_is_power2 q
| XH -> True

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p -> (match p_is_power2 p with
             | True -> Some (Z.log2 x)
             | False -> None)
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    (match zeq r Z0 with
     | Left -> Z0
     | Right -> Z.sub modulus r)

  (** val unsigned : int -> z **)

  let unsigned n0 =
    n0

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in
    (match zlt x half_modulus with
     | Left -> x
     | Right -> Z.sub x modulus)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> sumbool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    match zeq (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val lt : int -> int -> bool **)

  let lt x y =
    match zlt (signed x) (signed y) with
    | Left -> True
    | Right -> False

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    match zlt (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    match lt x zero with
    | True -> one
    | False -> zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    match zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus with
    | Left -> zero
    | Right -> one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    match zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0 with
    | Left -> one
    | Right -> zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    match match lt x zero with
          | True -> negb (eq (coq_and x (sub (shl one y) one)) zero)
          | False -> False with
    | True -> one
    | False -> zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    match eq x zero with
    | True -> one
    | False -> zero

  (** val divmodu2 : int -> int -> int -> (int, int) prod option **)

  let divmodu2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo))
          (unsigned d)
      in
      (match zle q max_unsigned with
       | Left -> Some (Pair ((repr q), (repr r)))
       | Right -> None)

  (** val divmods2 : int -> int -> int -> (int, int) prod option **)

  let divmods2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
          (signed d)
      in
      (match match proj_sumbool (zle min_signed q) with
             | True -> proj_sumbool (zle q max_signed)
             | False -> False with
       | True -> Some (Pair ((repr q), (repr r)))
       | False -> None)

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | Nil -> zero
  | Cons (a, b) -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (match match proj_sumbool (zlt (Z.add x1 sz1) modulus) with
           | True -> proj_sumbool (zlt (Z.add x2 sz2) modulus)
           | False -> False with
     | True ->
       (match proj_sumbool (zle (Z.add x1 sz1) x2) with
        | True -> True
        | False -> proj_sumbool (zle (Z.add x2 sz2) x1))
     | False -> False)

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 = shl (repr (Z.sub (two_p width) (Zpos XH))) (repr pos) in
    coq_or (shl (zero_ext width p) (repr pos)) (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_8 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S O)))))))
 end

module Byte = Make(Wordsize_8)

(** val str_to_bytes : string -> Byte.int list **)

let rec str_to_bytes = function
| EmptyString -> Nil
| String (c, s) ->
  Cons ((Byte.repr (Z.of_N (n_of_ascii c))), (str_to_bytes s))

(** val shr0 : z -> Int.int -> Int.int **)

let shr0 b x =
  Int.shru x (Int.repr b)

(** val intlist_to_bytelist : Int.int list -> Byte.int list **)

let rec intlist_to_bytelist = function
| Nil -> Nil
| Cons (i, r) ->
  Cons ((Byte.repr (Int.unsigned (shr0 (Zpos (XO (XO (XO (XI XH))))) i))),
    (Cons ((Byte.repr (Int.unsigned (shr0 (Zpos (XO (XO (XO (XO XH))))) i))),
    (Cons ((Byte.repr (Int.unsigned (shr0 (Zpos (XO (XO (XO XH)))) i))),
    (Cons ((Byte.repr (Int.unsigned i)), (intlist_to_bytelist r))))))))

(** val bytes_to_Int :
    Byte.int -> Byte.int -> Byte.int -> Byte.int -> Int.int **)

let bytes_to_Int a b c d =
  Int.coq_or
    (Int.coq_or
      (Int.coq_or
        (Int.shl (Int.repr (Byte.unsigned a))
          (Int.repr (Zpos (XO (XO (XO (XI XH)))))))
        (Int.shl (Int.repr (Byte.unsigned b))
          (Int.repr (Zpos (XO (XO (XO (XO XH))))))))
      (Int.shl (Int.repr (Byte.unsigned c))
        (Int.repr (Zpos (XO (XO (XO XH))))))) (Int.repr (Byte.unsigned d))

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f al bl =
  match al with
  | Nil -> Nil
  | Cons (a, al') ->
    (match bl with
     | Nil -> Nil
     | Cons (b, bl') -> Cons ((f a b), (map2 f al' bl')))

(** val k256 : Int.int list **)

let k256 =
  map Int.repr (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO
    (XO (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI (XO (XI (XI (XO (XO
    (XI (XO (XO (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XI
    (XO (XI (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO (XI
    (XI (XO (XO (XI (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XI (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI (XI
    (XO (XI (XI (XO (XI (XO (XI (XO (XI (XO (XO (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI
    (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XI
    (XI (XO (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XI
    (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO
    (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO
    (XI (XI (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO
    (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI
    (XO (XI (XO (XO XH))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI
    (XI (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO
    (XO (XO (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI
    (XI (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI
    (XO (XI (XO (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI
    (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI
    (XI (XI (XO (XI (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XI
    (XI (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO
    (XI (XI (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO (XI
    (XO (XO (XI (XO (XO (XI (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XO (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO
    (XO (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI
    (XI (XI (XI XH)))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XI (XI
    (XO (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XO
    (XI (XO (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI
    (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO
    (XO (XI (XO (XI (XO (XO XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XO (XI (XI (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO
    (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO
    (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XI
    (XI (XI (XI (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI
    (XI (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO
    (XO (XO (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO
    (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO
    (XI (XI (XI (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO
    (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XI (XO (XI
    (XI (XO (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO
    (XO (XI (XO (XI (XO (XO (XI (XI (XO (XI XH))))))))))))))))))))))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XO
    (XO (XI (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO
    (XI (XO (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XI (XI
    (XI (XI (XO (XO XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO
    (XO (XI (XI (XI (XO (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI
    (XI (XO (XO (XO (XO (XI (XI (XI (XO XH)))))))))))))))))))))))))))))),
    (Cons ((Zpos (XO (XO (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI
    (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO
    (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO
    (XI (XI (XO (XO (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XI
    (XO (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI
    (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XI (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XI
    (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO
    (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO
    (XO (XI (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO (XO (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO
    (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO
    (XO (XO (XO (XI (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI
    (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XI
    (XO (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO
    (XI (XI (XI (XO (XO (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI
    (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XO (XI
    (XO (XI (XI (XO (XI (XO (XI XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI
    (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XO (XO (XO XH))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XI
    (XO (XI (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO
    (XI (XO (XI (XI (XO (XO (XI XH))))))))))))))))))))))))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI
    (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI XH))))))))))))))))))))))))))))),
    (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XI (XO (XI (XI (XI (XO (XI (XI (XI
    (XO (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XO
    XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI
    (XO (XI (XO (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI
    (XO (XO (XI (XO (XI XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XI
    (XI (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI
    (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI XH)))))))))))))))))))))))))))))),
    (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XO
    (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO
    (XI (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XI
    (XI (XI (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XO (XO (XI
    (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI
    (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI
    (XO (XO (XI (XO (XI (XI XH))))))))))))))))))))))))))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO
    (XI (XO (XO (XI (XO (XI (XO (XO (XO (XI (XI (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO
    (XO (XO (XO (XO (XO (XI (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI
    (XO (XO (XI (XO (XO (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO
    (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI
    (XO (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XI (XI (XI (XO (XO (XI (XI (XO (XI (XI (XO
    (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO
    XH)))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI
    (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XI (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XI (XI (XI (XO
    (XI (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XO (XO (XO (XI
    XH)))))))))))))))))))))))))))))))),
    Nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ch : Int.int -> Int.int -> Int.int -> Int.int **)

let ch x y z0 =
  Int.xor (Int.coq_and x y) (Int.coq_and (Int.not x) z0)

(** val maj : Int.int -> Int.int -> Int.int -> Int.int **)

let maj x y z0 =
  Int.xor (Int.xor (Int.coq_and x z0) (Int.coq_and y z0)) (Int.coq_and x y)

(** val rotr : z -> Int.int -> Int.int **)

let rotr b x =
  Int.ror x (Int.repr b)

(** val sigma_0 : Int.int -> Int.int **)

let sigma_0 x =
  Int.xor (Int.xor (rotr (Zpos (XO XH)) x) (rotr (Zpos (XI (XO (XI XH)))) x))
    (rotr (Zpos (XO (XI (XI (XO XH))))) x)

(** val sigma_1 : Int.int -> Int.int **)

let sigma_1 x =
  Int.xor
    (Int.xor (rotr (Zpos (XO (XI XH))) x) (rotr (Zpos (XI (XI (XO XH)))) x))
    (rotr (Zpos (XI (XO (XO (XI XH))))) x)

(** val sigma_2 : Int.int -> Int.int **)

let sigma_2 x =
  Int.xor
    (Int.xor (rotr (Zpos (XI (XI XH))) x)
      (rotr (Zpos (XO (XI (XO (XO XH))))) x)) (shr0 (Zpos (XI XH)) x)

(** val sigma_3 : Int.int -> Int.int **)

let sigma_3 x =
  Int.xor
    (Int.xor (rotr (Zpos (XI (XO (XO (XO XH))))) x)
      (rotr (Zpos (XI (XI (XO (XO XH))))) x))
    (shr0 (Zpos (XO (XI (XO XH)))) x)

type registers = Int.int list

(** val init_registers : registers **)

let init_registers =
  map Int.repr (Cons ((Zpos (XI (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO
    (XO (XI (XI (XI (XI (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO
    (XO (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XI (XO
    (XI (XI (XO (XI (XI (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI (XI (XO (XI (XI (XO (XO (XI (XI (XI (XI
    (XO (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI
    XH)))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI
    (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO
    (XI (XO (XI (XO (XO (XI (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XI (XO
    XH))))))))))))))))))))))))))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO
    (XO (XI (XO (XO (XO (XI (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO
    (XI (XI (XO (XI (XI (XO (XO XH)))))))))))))))))))))))))))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XI (XI
    (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI
    XH))))))))))))))))))))))))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI
    (XI (XO (XI (XI (XO XH))))))))))))))))))))))))))))))), Nil))))))))))))))))

(** val rnd_function : registers -> Int.int -> Int.int -> registers **)

let rnd_function x k w =
  match x with
  | Nil -> Nil
  | Cons (a, l) ->
    (match l with
     | Nil -> Nil
     | Cons (b, l0) ->
       (match l0 with
        | Nil -> Nil
        | Cons (c, l1) ->
          (match l1 with
           | Nil -> Nil
           | Cons (d, l2) ->
             (match l2 with
              | Nil -> Nil
              | Cons (e, l3) ->
                (match l3 with
                 | Nil -> Nil
                 | Cons (f, l4) ->
                   (match l4 with
                    | Nil -> Nil
                    | Cons (g, l5) ->
                      (match l5 with
                       | Nil -> Nil
                       | Cons (h, l6) ->
                         (match l6 with
                          | Nil ->
                            let t1 =
                              Int.add
                                (Int.add
                                  (Int.add (Int.add h (sigma_1 e)) (ch e f g))
                                  k) w
                            in
                            let t2 = Int.add (sigma_0 a) (maj a b c) in
                            Cons ((Int.add t1 t2), (Cons (a, (Cons (b, (Cons
                            (c, (Cons ((Int.add d t1), (Cons (e, (Cons (f,
                            (Cons (g, Nil)))))))))))))))
                          | Cons (_, _) -> Nil))))))))

(** val zeros : z -> Int.int list **)

let rec zeros n0 =
  match Z.gtb n0 Z0 with
  | True -> Cons (Int.zero, (zeros (Z.sub n0 (Zpos XH))))
  | False -> Nil

(** val padlen : z -> Int.int list **)

let padlen n0 =
  let p = Z.add (Z.div n0 (Zpos (XO (XO XH)))) (Zpos (XI XH)) in
  let q =
    Z.sub
      (Z.mul
        (Z.div (Z.add p (Zpos (XI (XI (XI XH))))) (Zpos (XO (XO (XO (XO
          XH)))))) (Zpos (XO (XO (XO (XO XH)))))) p
  in
  app (zeros q) (Cons
    ((Int.repr (Z.div (Z.mul n0 (Zpos (XO (XO (XO XH))))) Int.modulus)),
    (Cons ((Int.repr (Z.mul n0 (Zpos (XO (XO (XO XH)))))), Nil))))

(** val generate_and_pad' : Byte.int list -> z -> Int.int list **)

let rec generate_and_pad' n0 len =
  match n0 with
  | Nil ->
    Cons
      ((bytes_to_Int (Byte.repr (Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))))
         Byte.zero Byte.zero Byte.zero), (padlen len))
  | Cons (h1, l) ->
    (match l with
     | Nil ->
       Cons
         ((bytes_to_Int h1
            (Byte.repr (Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))))
            Byte.zero Byte.zero), (padlen (Z.add len (Zpos XH))))
     | Cons (h2, l0) ->
       (match l0 with
        | Nil ->
          Cons
            ((bytes_to_Int h1 h2
               (Byte.repr (Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))))
               Byte.zero), (padlen (Z.add len (Zpos (XO XH)))))
        | Cons (h3, l1) ->
          (match l1 with
           | Nil ->
             Cons
               ((bytes_to_Int h1 h2 h3
                  (Byte.repr (Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))))),
               (padlen (Z.add len (Zpos (XI XH)))))
           | Cons (h4, t) ->
             Cons ((bytes_to_Int h1 h2 h3 h4),
               (generate_and_pad' t (Z.add len (Zpos (XO (XO XH)))))))))

(** val generate_and_pad_alt : Byte.int list -> Int.int list **)

let generate_and_pad_alt n0 =
  generate_and_pad' n0 Z0

(** val wnext : Int.int list -> Int.int **)

let wnext = function
| Nil -> Int.zero
| Cons (_, l) ->
  (match l with
   | Nil -> Int.zero
   | Cons (x2, l0) ->
     (match l0 with
      | Nil -> Int.zero
      | Cons (_, l1) ->
        (match l1 with
         | Nil -> Int.zero
         | Cons (_, l2) ->
           (match l2 with
            | Nil -> Int.zero
            | Cons (_, l3) ->
              (match l3 with
               | Nil -> Int.zero
               | Cons (_, l4) ->
                 (match l4 with
                  | Nil -> Int.zero
                  | Cons (x7, l5) ->
                    (match l5 with
                     | Nil -> Int.zero
                     | Cons (_, l6) ->
                       (match l6 with
                        | Nil -> Int.zero
                        | Cons (_, l7) ->
                          (match l7 with
                           | Nil -> Int.zero
                           | Cons (_, l8) ->
                             (match l8 with
                              | Nil -> Int.zero
                              | Cons (_, l9) ->
                                (match l9 with
                                 | Nil -> Int.zero
                                 | Cons (_, l10) ->
                                   (match l10 with
                                    | Nil -> Int.zero
                                    | Cons (_, l11) ->
                                      (match l11 with
                                       | Nil -> Int.zero
                                       | Cons (_, l12) ->
                                         (match l12 with
                                          | Nil -> Int.zero
                                          | Cons (x15, l13) ->
                                            (match l13 with
                                             | Nil -> Int.zero
                                             | Cons (x16, _) ->
                                               Int.add
                                                 (Int.add (sigma_3 x2) x7)
                                                 (Int.add (sigma_2 x15) x16))))))))))))))))

(** val generate_word : Int.int list -> nat -> Int.int list **)

let rec generate_word msg = function
| O -> msg
| S n' -> generate_word (Cons ((wnext msg), msg)) n'

(** val rnd_64 : registers -> Int.int list -> Int.int list -> registers **)

let rec rnd_64 x k w =
  match k with
  | Nil -> x
  | Cons (k1, k') ->
    (match w with
     | Nil -> x
     | Cons (w1, w') -> rnd_64 (rnd_function x k1 w1) k' w')

(** val process_block : registers -> Int.int list -> registers **)

let process_block r block =
  map2 Int.add r
    (rnd_64 r k256
      (rev
        (generate_word block (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))

(** val grab_and_process_block :
    nat -> registers -> Int.int list -> Int.int list -> (registers, Int.int
    list) prod **)

let rec grab_and_process_block n0 r firstrev msg =
  match n0 with
  | O -> Pair ((process_block r firstrev), msg)
  | S n' ->
    (match msg with
     | Nil -> Pair (r, Nil)
     | Cons (m1, msg') ->
       grab_and_process_block n' r (Cons (m1, firstrev)) msg')

(** val process_msg : registers -> Int.int list -> registers **)

let rec process_msg r = function
| Nil -> r
| Cons (i, l) ->
  let Pair (r0, l0) =
    grab_and_process_block (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))) r Nil (Cons (i, l))
  in
  process_msg r0 l0

(** val sHA_256' : Byte.int list -> Byte.int list **)

let sHA_256' str =
  intlist_to_bytelist (process_msg init_registers (generate_and_pad_alt str))

(** val test : string **)

let test =
  String ((Ascii (True, True, False, False, False, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, True, False, False, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, True, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, False, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, True, False, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, False, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, True, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, True, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, False, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, True, False, False, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, False, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, False, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, False, True, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, True, False, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, False, True, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, False, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, False, False)),
    (String ((Ascii (False, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val sha_fast : unit0 -> Byte.int list **)

let sha_fast _ =
  sHA_256' (str_to_bytes test)

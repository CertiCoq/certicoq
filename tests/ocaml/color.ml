
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

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

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

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

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

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f x =
  g (f x)

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Left
  | S n0 -> (match m with
             | O -> Right
             | S n1 -> le_lt_dec n0 n1)

(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val lt_dec : nat -> nat -> sumbool **)

let lt_dec n m =
  le_dec (S n) m

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
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

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | Nil -> l'
  | Cons (a, l0) -> rev_append l0 (Cons (a, l'))

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| Nil -> Nil
| Cons (x, l0) -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

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
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
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
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val succ : z -> z **)

  let succ x =
    add x (Zpos XH)

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> True
    | _ -> False

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module PositiveOrderedTypeBits =
 struct
  type t = positive

  (** val compare : t -> t -> positive compare0 **)

  let rec compare p y =
    match p with
    | XI p0 -> (match y with
                | XI p1 -> compare p0 p1
                | _ -> GT)
    | XO p0 -> (match y with
                | XO p1 -> compare p0 p1
                | _ -> LT)
    | XH -> (match y with
             | XI _ -> LT
             | XO _ -> GT
             | XH -> EQ)

  (** val eq_dec : positive -> positive -> sumbool **)

  let eq_dec x y =
    match Pos.compare x y with
    | Eq -> Left
    | _ -> Right
 end

module type S =
 sig
  module E :
   OrderedType

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> sumbool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val compare : t -> t -> t compare0

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module PositiveSet =
 struct
  module E = PositiveOrderedTypeBits

  type elt = positive

  type tree =
  | Leaf
  | Node of tree * bool * tree

  type t = tree

  (** val empty : t **)

  let empty =
    Leaf

  (** val is_empty : t -> bool **)

  let rec is_empty = function
  | Leaf -> True
  | Node (l, b, r) ->
    (match match negb b with
           | True -> is_empty l
           | False -> False with
     | True -> is_empty r
     | False -> False)

  (** val mem : elt -> t -> bool **)

  let rec mem i = function
  | Leaf -> False
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> mem i0 r
     | XO i0 -> mem i0 l
     | XH -> o)

  (** val add : elt -> t -> t **)

  let rec add i = function
  | Leaf ->
    (match i with
     | XI i0 -> Node (Leaf, False, (add i0 Leaf))
     | XO i0 -> Node ((add i0 Leaf), False, Leaf)
     | XH -> Node (Leaf, True, Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> Node (l, o, (add i0 r))
     | XO i0 -> Node ((add i0 l), o, r)
     | XH -> Node (l, True, r))

  (** val singleton : elt -> t **)

  let singleton i =
    add i empty

  (** val node : t -> bool -> t -> t **)

  let node l b r =
    match b with
    | True -> Node (l, b, r)
    | False ->
      (match l with
       | Leaf ->
         (match r with
          | Leaf -> Leaf
          | Node (_, _, _) -> Node (l, False, r))
       | Node (_, _, _) -> Node (l, False, r))

  (** val remove : elt -> t -> t **)

  let rec remove i = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> node l o (remove i0 r)
     | XO i0 -> node (remove i0 l) o r
     | XH -> node l False r)

  (** val union : t -> t -> t **)

  let rec union m m' =
    match m with
    | Leaf -> m'
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> m
       | Node (l', o', r') ->
         Node ((union l l'), (match o with
                              | True -> True
                              | False -> o'), (union r r')))

  (** val inter : t -> t -> t **)

  let rec inter m m' =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> Leaf
       | Node (l', o', r') ->
         node (inter l l') (match o with
                            | True -> o'
                            | False -> False) (inter r r'))

  (** val diff : t -> t -> t **)

  let rec diff m m' =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> m
       | Node (l', o', r') ->
         node (diff l l') (match o with
                           | True -> negb o'
                           | False -> False) (diff r r'))

  (** val equal : t -> t -> bool **)

  let rec equal m m' =
    match m with
    | Leaf -> is_empty m'
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> is_empty m
       | Node (l', o', r') ->
         (match match eqb o o' with
                | True -> equal l l'
                | False -> False with
          | True -> equal r r'
          | False -> False))

  (** val subset : t -> t -> bool **)

  let rec subset m m' =
    match m with
    | Leaf -> True
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> is_empty m
       | Node (l', o', r') ->
         (match match match negb o with
                      | True -> True
                      | False -> o' with
                | True -> subset l l'
                | False -> False with
          | True -> subset r r'
          | False -> False))

  (** val rev_append : elt -> elt -> elt **)

  let rec rev_append y x =
    match y with
    | XI y0 -> rev_append y0 (XI x)
    | XO y0 -> rev_append y0 (XO x)
    | XH -> x

  (** val rev : elt -> elt **)

  let rev x =
    rev_append x XH

  (** val xfold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> elt -> 'a1 **)

  let rec xfold f m v i =
    match m with
    | Leaf -> v
    | Node (l, b, r) ->
      (match b with
       | True -> xfold f r (f (rev i) (xfold f l v (XO i))) (XI i)
       | False -> xfold f r (xfold f l v (XO i)) (XI i))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f m i =
    xfold f m i XH

  (** val xforall : (elt -> bool) -> t -> elt -> bool **)

  let rec xforall f m i =
    match m with
    | Leaf -> True
    | Node (l, o, r) ->
      (match match match negb o with
                   | True -> True
                   | False -> f (rev i) with
             | True -> xforall f r (XI i)
             | False -> False with
       | True -> xforall f l (XO i)
       | False -> False)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f m =
    xforall f m XH

  (** val xexists : (elt -> bool) -> t -> elt -> bool **)

  let rec xexists f m i =
    match m with
    | Leaf -> False
    | Node (l, o, r) ->
      (match match match o with
                   | True -> f (rev i)
                   | False -> False with
             | True -> True
             | False -> xexists f r (XI i) with
       | True -> True
       | False -> xexists f l (XO i))

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f m =
    xexists f m XH

  (** val xfilter : (elt -> bool) -> t -> elt -> t **)

  let rec xfilter f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      node (xfilter f l (XO i))
        (match o with
         | True -> f (rev i)
         | False -> False) (xfilter f r (XI i))

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f m =
    xfilter f m XH

  (** val xpartition : (elt -> bool) -> t -> elt -> (t, t) prod **)

  let rec xpartition f m i =
    match m with
    | Leaf -> Pair (Leaf, Leaf)
    | Node (l, o, r) ->
      let Pair (lt, lf) = xpartition f l (XO i) in
      let Pair (rt, rf) = xpartition f r (XI i) in
      (match o with
       | True ->
         let fi = f (rev i) in Pair ((node lt fi rt), (node lf (negb fi) rf))
       | False -> Pair ((node lt False rt), (node lf False rf)))

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f m =
    xpartition f m XH

  (** val xelements : t -> elt -> elt list -> elt list **)

  let rec xelements m i a =
    match m with
    | Leaf -> a
    | Node (l, b, r) ->
      (match b with
       | True -> xelements l (XO i) (Cons ((rev i), (xelements r (XI i) a)))
       | False -> xelements l (XO i) (xelements r (XI i) a))

  (** val elements : t -> elt list **)

  let elements m =
    xelements m XH Nil

  (** val cardinal : t -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, b, r) ->
    (match b with
     | True -> S (Coq__1.add (cardinal l) (cardinal r))
     | False -> Coq__1.add (cardinal l) (cardinal r))

  (** val omap : (elt -> elt) -> elt option -> elt option **)

  let omap f = function
  | Some i -> Some (f i)
  | None -> None

  (** val choose : t -> elt option **)

  let rec choose = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match o with
     | True -> Some XH
     | False ->
       (match choose l with
        | Some i -> Some (XO i)
        | None -> omap (fun x -> XI x) (choose r)))

  (** val min_elt : t -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match min_elt l with
     | Some i -> Some (XO i)
     | None ->
       (match o with
        | True -> Some XH
        | False -> omap (fun x -> XI x) (min_elt r)))

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match max_elt r with
     | Some i -> Some (XI i)
     | None ->
       (match o with
        | True -> Some XH
        | False -> omap (fun x -> XO x) (max_elt l)))

  (** val compare_bool : bool -> bool -> comparison **)

  let compare_bool a b =
    match a with
    | True -> (match b with
               | True -> Eq
               | False -> Gt)
    | False -> (match b with
                | True -> Lt
                | False -> Eq)

  (** val compare_fun : t -> t -> comparison **)

  let rec compare_fun m m' =
    match m with
    | Leaf -> (match is_empty m' with
               | True -> Eq
               | False -> Lt)
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> (match is_empty m with
                  | True -> Eq
                  | False -> Gt)
       | Node (l', o', r') ->
         (match compare_bool o o' with
          | Eq ->
            (match compare_fun l l' with
             | Eq -> compare_fun r r'
             | x -> x)
          | x -> x))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s s' =
    match equal s s' with
    | True -> Left
    | False -> Right

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    match compare_fun s s' with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT
 end

module type Coq_S =
 sig
  module E :
   OrderedType

  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

(** val append : positive -> positive -> positive **)

let rec append i j =
  match i with
  | XI ii -> XI (append ii j)
  | XO ii -> XO (append ii j)
  | XH -> j

module PositiveMap =
 struct
  module E = PositiveOrderedTypeBits

  module ME = KeyOrderedType(E)

  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val is_empty : 'a1 t -> bool **)

  let rec is_empty = function
  | Leaf -> True
  | Node (l, o, r) ->
    (match o with
     | Some _ -> False
     | None -> (match is_empty l with
                | True -> is_empty r
                | False -> False))

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match i with
     | XI ii -> find ii r
     | XO ii -> find ii l
     | XH -> o)

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem i = function
  | Leaf -> False
  | Node (l, o, r) ->
    (match i with
     | XI ii -> mem ii r
     | XO ii -> mem ii l
     | XH -> (match o with
              | Some _ -> True
              | None -> False))

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add i v = function
  | Leaf ->
    (match i with
     | XI ii -> Node (Leaf, None, (add ii v Leaf))
     | XO ii -> Node ((add ii v Leaf), None, Leaf)
     | XH -> Node (Leaf, (Some v), Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI ii -> Node (l, o, (add ii v r))
     | XO ii -> Node ((add ii v l), o, r)
     | XH -> Node (l, (Some v), r))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove i m =
    match i with
    | XI ii ->
      (match m with
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
    | XO ii ->
      (match m with
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
    | XH ->
      (match m with
       | Leaf -> Leaf
       | Node (l, _, r) ->
         (match l with
          | Leaf ->
            (match r with
             | Leaf -> Leaf
             | Node (_, _, _) -> Node (l, None, r))
          | Node (_, _, _) -> Node (l, None, r)))

  (** val xelements : 'a1 t -> key -> (key, 'a1) prod list **)

  let rec xelements m i =
    match m with
    | Leaf -> Nil
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         app (xelements l (append i (XO XH))) (Cons ((Pair (i, x)),
           (xelements r (append i (XI XH)))))
       | None ->
         app (xelements l (append i (XO XH))) (xelements r (append i (XI XH))))

  (** val elements : 'a1 t -> (key, 'a1) prod list **)

  let elements m =
    xelements m XH

  (** val cardinal : 'a1 t -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, o, r) ->
    (match o with
     | Some _ -> S (Coq__1.add (cardinal l) (cardinal r))
     | None -> Coq__1.add (cardinal l) (cardinal r))

  (** val xfind : key -> key -> 'a1 t -> 'a1 option **)

  let rec xfind i j m =
    match i with
    | XI ii ->
      (match j with
       | XI jj -> xfind ii jj m
       | XO _ -> None
       | XH -> find i m)
    | XO ii ->
      (match j with
       | XI _ -> None
       | XO jj -> xfind ii jj m
       | XH -> find i m)
    | XH -> (match j with
             | XH -> find i m
             | _ -> None)

  (** val xmapi : (key -> 'a1 -> 'a2) -> 'a1 t -> key -> 'a2 t **)

  let rec xmapi f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmapi f l (append i (XO XH))), (option_map (f i) o),
        (xmapi f r (append i (XI XH))))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    xmapi f m XH

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    mapi (fun _ -> f) m

  (** val xmap2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec xmap2_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((xmap2_l f l), (f o None), (xmap2_l f r))

  (** val xmap2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec xmap2_r f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((xmap2_r f l), (f None o), (xmap2_r f r))

  (** val _map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec _map2 f m1 m2 =
    match m1 with
    | Leaf -> xmap2_r f m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xmap2_l f m1
       | Node (l2, o2, r2) ->
         Node ((_map2 f l1 l2), (f o1 o2), (_map2 f r1 r2)))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f =
    _map2 (fun o1 o2 ->
      match o1 with
      | Some _ -> f o1 o2
      | None -> (match o2 with
                 | Some _ -> f o1 o2
                 | None -> None))

  (** val xfoldi :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> key -> 'a2 **)

  let rec xfoldi f m v i =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         xfoldi f r (f i x (xfoldi f l v (append i (XO XH))))
           (append i (XI XH))
       | None ->
         xfoldi f r (xfoldi f l v (append i (XO XH))) (append i (XI XH)))

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    xfoldi f m i XH

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m1 m2 =
    match m1 with
    | Leaf -> is_empty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> is_empty m1
       | Node (l2, o2, r2) ->
         (match match match o1 with
                      | Some v1 ->
                        (match o2 with
                         | Some v2 -> cmp v1 v2
                         | None -> False)
                      | None -> (match o2 with
                                 | Some _ -> False
                                 | None -> True) with
                | True -> equal cmp l1 l2
                | False -> False with
          | True -> equal cmp r1 r2
          | False -> False))
 end

module E = PositiveOrderedTypeBits

module Coq0_S = PositiveSet

module M = PositiveMap

type node0 = E.t

type nodeset = Coq0_S.t

type 'x nodemap = 'x M.t

type graph = nodeset nodemap

(** val adj : graph -> node0 -> nodeset **)

let adj g i =
  match M.find i g with
  | Some a -> a
  | None -> Coq0_S.empty

(** val subset_nodes : (node0 -> nodeset -> sumbool) -> graph -> Coq0_S.t **)

let subset_nodes p_dec g =
  M.fold (fun n adj0 s ->
    match p_dec n adj0 with
    | Left -> Coq0_S.add n s
    | Right -> s) g Coq0_S.empty

(** val low_deg_dec : nat -> node0 -> nodeset -> sumbool **)

let low_deg_dec k _ adj0 =
  lt_dec (Coq0_S.cardinal adj0) k

(** val remove_node : node0 -> graph -> graph **)

let remove_node n g =
  M.map (Coq0_S.remove n) (M.remove n g)

(** val select : nat -> graph -> node0 list **)

let rec select k g =
  match Coq0_S.choose (subset_nodes (low_deg_dec k) g) with
  | Some e -> Cons (e, (select k (remove_node e g)))
  | None -> Nil

type coloring = node0 M.t

(** val colors_of : coloring -> Coq0_S.t -> Coq0_S.t **)

let colors_of f s =
  Coq0_S.fold (fun n s0 ->
    match M.find n f with
    | Some c -> Coq0_S.add c s0
    | None -> s0) s Coq0_S.empty

(** val color1 : Coq0_S.t -> graph -> node0 -> coloring -> coloring **)

let color1 palette g n f =
  match Coq0_S.choose (Coq0_S.diff palette (colors_of f (adj g n))) with
  | Some c -> M.add n c f
  | None -> f

(** val color : Coq0_S.t -> graph -> coloring **)

let color palette g =
  fold_right (color1 palette g) M.empty (select (Coq0_S.cardinal palette) g)

type graph_description = (z, (z, z list) prod list) prod

(** val iota' : z -> z list -> z list **)

let rec iota' i al =
  match Z.gtb i Z0 with
  | True -> iota' (Z.pred i) (Cons ((Z.pred i), al))
  | False -> rev_append Nil al

(** val iota : z -> z list **)

let iota i =
  iota' i Nil

(** val clique : z -> (z, z) prod list **)

let rec clique k =
  match Z.gtb k Z0 with
  | True ->
    app (clique (Z.sub k (Zpos XH)))
      (map (fun i -> Pair ((Z.sub k (Zpos XH)), i))
        (iota (Z.sub k (Zpos XH))))
  | False -> Nil

(** val zzlist_to_poslist :
    (z, z) prod list -> (positive, positive) prod list **)

let zzlist_to_poslist =
  map (fun ij -> Pair ((Z.to_pos (Z.succ (fst ij))),
    (Z.to_pos (Z.succ (snd ij)))))

(** val translate_adj_list : (z, z list) prod -> (z, z) prod list **)

let translate_adj_list = function
| Pair (i, al) -> map (fun j -> Pair (i, j)) al

(** val parse_graph : graph_description -> (positive, positive) prod list **)

let parse_graph = function
| Pair (k, l) ->
  zzlist_to_poslist (concat (Cons ((clique k), (map translate_adj_list l))))

(** val make_palette : graph_description -> Coq0_S.t **)

let make_palette g =
  fold_right Coq0_S.add Coq0_S.empty
    (map (compose Z.to_pos Z.succ) (iota (fst g)))

(** val add_edge : (E.t, E.t) prod -> graph -> graph **)

let add_edge e g =
  M.add (fst e) (Coq0_S.add (snd e) (adj g (fst e)))
    (M.add (snd e) (Coq0_S.add (fst e) (adj g (snd e))) g)

(** val mk_graph : (E.t, E.t) prod list -> graph **)

let mk_graph el =
  fold_right add_edge M.empty el

(** val run : graph_description -> (z, z) prod **)

let run g =
  let result = M.elements (color (make_palette g) (mk_graph (parse_graph g)))
  in
  Pair ((Z.add (fst g) (Z.of_nat (length (snd g)))),
  (Z.of_nat (length result)))

(** val g16 : graph_description **)

let g16 =
  Pair ((Zpos (XO (XO (XO (XO XH))))), (Cons ((Pair ((Zpos (XO (XO (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XO (XO XH)))), (Cons (Z0, (Cons ((Zpos
    (XO (XI XH))), (Cons ((Zpos (XI (XI XH))), (Cons ((Zpos XH), (Cons ((Zpos
    (XO XH)), Nil)))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XO (XO XH)))), (Cons (Z0, (Cons ((Zpos (XO
    (XI XH))), (Cons ((Zpos (XI (XI XH))), (Cons ((Zpos XH), Nil)))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XO XH)))), (Cons (Z0, (Cons ((Zpos (XI (XI XH))), (Cons ((Zpos (XO (XI
    XH))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XO
    XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XO XH)))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI
    XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI
    (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO
    (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO
    (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XO XH)))), (Cons (Z0, (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI XH))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XO
    XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XI
    (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI XH)))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI
    XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI XH)))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI
    XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO
    (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))), (Cons
    ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO
    (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons (Z0, (Cons ((Zpos
    (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XO (XO (XO XH)))), (Cons ((Zpos (XI (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XO
    XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XO
    XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO
    (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI
    XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XI
    (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XI XH)))))), (Cons
    ((Zpos (XI (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI
    XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO
    (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI XH)), (Cons ((Zpos (XO XH)), (Cons ((Zpos
    (XO (XI XH))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons (Z0, (Cons ((Zpos (XO (XI (XI
    (XO (XO XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))),
    (Cons ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XO (XO
    (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI XH)))))),
    (Cons ((Zpos (XO (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI
    (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO
    (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI
    (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO XH))))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO XH))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XO
    (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO XH))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO XH))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO
    (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO XH))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XI
    (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XI
    (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XO
    (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO
    (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI
    (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI XH))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI XH))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI
    (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))), (Cons
    ((Zpos (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI XH)),
    (Cons ((Zpos (XO XH)), (Cons ((Zpos (XO (XI XH))), (Cons ((Zpos (XI (XI
    XH))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), Nil)))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI
    (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO
    XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI
    XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI
    (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons
    ((Zpos (XO (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI
    XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI
    (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO XH))))))),
    (Cons ((Zpos (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), Nil)))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XI (XO
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI
    (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO
    XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI
    XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI
    (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons
    ((Zpos (XO (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI
    XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI
    (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XO (XI (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XO (XO (XO XH)))))), Nil)))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO
    (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    Nil)))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI
    (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), Nil)))))))))))))), (Cons
    ((Pair ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI
    (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XI
    (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XO
    (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XI
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XO
    (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XI (XO XH)))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI
    (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI
    (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XO (XO
    (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI
    (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XO
    (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XI
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XO
    (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (Cons
    ((Pair ((Zpos (XO (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI
    (XI (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO XH)))))), Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XO (XI XH)))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XO (XO (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XI
    (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI
    (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO
    (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO
    XH))))))), Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO
    (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI XH)))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO
    (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI XH)),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))),
    Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XO (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI
    XH)))))), Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XI
    (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XO
    (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO
    (XO (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XI
    (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XI (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI
    XH)))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI
    (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI
    XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XI (XI (XI
    XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO
    (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI
    (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XI (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO
    (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), Nil)))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XO
    (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO
    (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))),
    Nil)))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XO (XO
    (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XO (XI (XI (XI
    (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XI XH)))))), Nil)))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XO (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI
    (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO
    (XO (XO (XI XH)))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI
    (XO (XO (XO (XI XH)))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XI (XO (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))), (Cons ((Zpos (XI
    (XO (XO (XO (XI XH)))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))),
    (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI
    (XO (XI (XI (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XO (XO XH))))))), Nil)))))))))))))))))))))))))))))))))), (Cons
    ((Pair ((Zpos (XI (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO
    (XI (XO (XI (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XO (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO XH)))))), Nil)))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO
    (XO (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI
    XH)))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO
    (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI
    (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XO (XI (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI XH)))))), (Cons ((Zpos (XO (XI (XO (XI (XI XH)))))),
    Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XO (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XO (XI (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI
    (XI (XO (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    Nil)))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO XH))))))),
    Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO
    (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO
    (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO
    XH)))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO XH))))))),
    Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XO (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XI (XO (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XO (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XI (XI (XO (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XO (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XO (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XI (XO (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XI (XI (XO (XO XH)))))),
    Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO XH)))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), Nil)))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XI (XI
    (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XI (XI
    (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), Nil)))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XO (XI XH))))))), Nil)))))))))))))))))), (Cons
    ((Pair ((Zpos (XI (XO (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XO (XO (XO (XO (XI XH))))))), Nil)))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XO (XO (XO (XI XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), Nil)))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XO (XO
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), Nil)))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO
    (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI
    (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XI XH))))))), (Cons
    ((Zpos (XI (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO
    (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI XH))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI
    (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))), (Cons
    ((Zpos (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO
    XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))),
    Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XO (XO
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XI XH))))))),
    Nil)))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XI XH))))))),
    Nil)))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XO (XI (XO
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), Nil)))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XI (XO
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), Nil)))))))))))))))))))), (Cons ((Pair
    ((Zpos (XI (XO (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), Nil)))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI
    (XI (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XI XH))))))),
    Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XI (XI (XO (XI XH))))))), Nil)))))))))))))))))))))), (Cons
    ((Pair ((Zpos (XO (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XI XH))))))), Nil)))))))))))))))))))), (Cons ((Pair ((Zpos (XI
    (XO (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO
    (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), Nil)))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XI XH))))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XI XH))))))),
    (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO
    (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XI XH))))))),
    (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI
    (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XI (XI (XI XH))))))),
    (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI
    XH))))))), Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XO
    (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))),
    Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XO (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XI
    XH))))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XI
    (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XI (XI XH))))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XI (XI (XI (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))),
    Nil)))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), Nil)))))))))))))))))))))), (Cons
    ((Pair ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XI (XI (XI XH))))))),
    (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO
    (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO
    XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI
    XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))),
    Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI
    (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XI XH))))))),
    Nil)))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XI (XI
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XI (XI (XI XH))))))),
    Nil)))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XI (XI (XI
    (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XI
    (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XI XH))))))), Nil)))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO
    XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), Nil)))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), Nil)))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XI (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO
    (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XO (XO (XO XH)))))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO (XO
    (XO XH)))))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI
    (XO (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XI (XI XH))))))), Nil)))))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO
    (XO (XI (XI XH))))))), Nil)))))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XO
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XO (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO
    (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI
    (XO (XI XH))))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XI (XO (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), Nil)))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI
    (XO (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XI
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XO (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XI
    (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    Nil)))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XI (XO
    (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))),
    Nil)))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XI (XI (XI (XO
    (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XI
    (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XO (XI (XO (XO XH)))))))),
    (Cons ((Zpos (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))),
    Nil)))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XO (XO
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))),
    Nil)))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XO
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XI (XO (XO
    XH)))))))), Nil)))))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos
    (XO (XI (XO (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XO (XO (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI (XO (XO
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XO (XO
    (XI (XO (XO XH)))))))), Nil)))))))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XO (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI
    (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XO (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XI (XO
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos
    (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO (XO XH)))))),
    (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos (XO (XI (XI
    (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO
    (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons
    ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO
    (XI (XO (XO XH)))))))), Nil)))))))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO
    XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XO (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO
    (XI (XI (XI XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))),
    (Cons ((Zpos (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO (XI XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO
    (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))),
    Nil)))))))))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XI
    (XI (XO (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO
    XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI (XO (XO XH))))))),
    (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XO (XO
    (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO XH)))))))), (Cons
    ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XI (XI
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO (XO (XO (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI XH))))))), (Cons ((Zpos
    (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos (XI (XI (XO (XI (XO (XI
    XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XI (XO XH))))))), Nil)))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XO (XO (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XI (XI
    (XO (XO XH))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons
    ((Zpos (XO (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO
    (XO XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))),
    (Cons ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO
    (XO (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))),
    Nil)))))))))))))))))))))))))))))))), (Cons ((Pair ((Zpos (XI (XO (XO (XI
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons
    ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI
    XH)))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI
    (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XO XH))))))), (Cons ((Zpos (XO (XI (XO (XI (XI (XO
    (XO XH)))))))), Nil)))))))))))))))))))))))))))))))))), (Cons ((Pair
    ((Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XI
    (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))), (Cons ((Zpos
    (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XI (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO
    (XI (XO (XO (XO XH)))))), (Cons ((Zpos (XO (XI (XI (XO (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))), (Cons
    ((Zpos (XI (XI (XI (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XO (XO (XO
    (XO (XO (XO (XO XH)))))))), (Cons ((Zpos (XI (XO (XO (XI (XI (XI
    XH))))))), (Cons ((Zpos (XO (XI (XO (XO (XI (XI XH))))))), (Cons ((Zpos
    (XI (XI (XO (XI (XO (XI XH))))))), (Cons ((Zpos (XO (XO (XI (XO (XO (XI
    XH))))))), (Cons ((Zpos (XI (XO (XI (XI (XI (XO XH))))))), (Cons ((Zpos
    (XI (XO (XI (XI (XO (XO XH))))))), Nil)))))))))))))))))))))))))))))))))),
    (Cons ((Pair ((Zpos (XI (XI (XO (XI (XI (XO (XO XH)))))))), (Cons ((Zpos
    (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XO (XI (XO (XO XH)))))),
    (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), (Cons ((Zpos (XO (XO (XI (XI
    (XI (XO (XO XH)))))))), (Cons ((Zpos (XI XH)), (Cons ((Zpos (XO XH)),
    Nil)))))))))))))), (Cons ((Pair ((Zpos (XO (XO (XI (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI
    (XO (XI (XO (XO XH)))))), (Cons ((Zpos (XI (XI (XO (XI (XI (XO (XO
    XH)))))))), (Cons ((Zpos (XO (XI (XI (XO (XI XH)))))), Nil)))))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val main : (z, z) prod **)

let main =
  run g16

(** val color0 : unit0 -> (z, z) prod **)

let color0 _ =
  main

open Basics
open Datatypes
open Equalities
open List0

module MakeRaw =
 functor (X:DecidableType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : elt -> t -> bool **)

  let rec mem x = function
  | [] -> false
  | y :: l -> if X.eq_dec x y then true else mem x l

  (** val add : elt -> t -> t **)

  let rec add x s = match s with
  | [] -> x :: []
  | y :: l -> if X.eq_dec x y then s else y :: (add x l)

  (** val singleton : elt -> t **)

  let singleton x =
    x :: []

  (** val remove : elt -> t -> t **)

  let rec remove x = function
  | [] -> []
  | y :: l -> if X.eq_dec x y then l else y :: (remove x l)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f =
    fold_left (flip f)

  (** val union : t -> t -> t **)

  let union s =
    fold add s

  (** val diff : t -> t -> t **)

  let diff s s' =
    fold remove s' s

  (** val inter : t -> t -> t **)

  let inter s s' =
    fold (fun x s0 -> if mem x s' then add x s0 else s0) s []

  (** val subset : t -> t -> bool **)

  let subset s s' =
    is_empty (diff s s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    (&&) (subset s s') (subset s' s)

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | [] -> []
  | x :: l -> if f x then x :: (filter f l) else filter f l

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | [] -> true
  | x :: l -> if f x then for_all f l else false

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | [] -> false
  | x :: l -> if f x then true else exists_ f l

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition f l in
    if f x then ((x :: s1), s2) else (s1, (x :: s2))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements s =
    s

  (** val choose : t -> elt option **)

  let choose = function
  | [] -> None
  | x :: _ -> Some x

  (** val isok : elt list -> bool **)

  let rec isok = function
  | [] -> true
  | a :: l0 -> (&&) (negb (mem a l0)) (isok l0)
 end

module Make =
 functor (X:DecidableType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

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

  (** val cardinal : t -> nat **)

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
 end

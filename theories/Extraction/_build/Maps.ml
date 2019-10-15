open Coqlib0
open Datatypes
open List0

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

  let rec remove i m =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun ii ->
      match m with
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
      match m with
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
      match m with
      | Leaf -> Leaf
      | Node (l, _, r) ->
        (match l with
         | Leaf ->
           (match r with
            | Leaf -> Leaf
            | Node (_, _, _) -> Node (l, None, r))
         | Node (_, _, _) -> Node (l, None, r)))
      i

  (** val bempty : 'a1 t -> bool **)

  let rec bempty = function
  | Leaf -> true
  | Node (l, o, r) ->
    (match o with
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
              | Some y1 ->
                (match o2 with
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

  let rec xmap f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l ((fun p->2*p) i)),
        (match o with
         | Some x -> Some (f (prev i) x)
         | None -> None), (xmap f r ((fun p->1+2*p) i)))

  (** val map : (int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    xmap f m 1

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map1 f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((map1 f l), (Coqlib0.option_map f o), (map1 f r))

  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)

  let coq_Node' l x r =
    match l with
    | Leaf ->
      (match x with
       | Some _ -> Node (l, x, r)
       | None ->
         (match r with
          | Leaf -> Leaf
          | Node (_, _, _) -> Node (l, x, r)))
    | Node (_, _, _) -> Node (l, x, r)

  (** val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t **)

  let rec filter1 pred = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    let o' = match o with
             | Some x -> if pred x then o else None
             | None -> None
    in
    coq_Node' (filter1 pred l) o' (filter1 pred r)

  (** val xcombine_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec xcombine_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)

  (** val xcombine_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

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
       | Node (l2, o2, r2) ->
         coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))

  (** val xelements : 'a1 t -> int -> (int * 'a1) list -> (int * 'a1) list **)

  let rec xelements m i k =
    match m with
    | Leaf -> k
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         xelements l ((fun p->2*p) i) (((prev i),
           x) :: (xelements r ((fun p->1+2*p) i) k))
       | None ->
         xelements l ((fun p->2*p) i) (xelements r ((fun p->1+2*p) i) k))

  (** val elements : 'a1 t -> (int * 'a1) list **)

  let elements m =
    xelements m 1 []

  (** val xkeys : 'a1 t -> int -> int list **)

  let xkeys m i =
    List0.map fst (xelements m i [])

  (** val xfold : ('a2 -> int -> 'a1 -> 'a2) -> int -> 'a1 t -> 'a2 -> 'a2 **)

  let rec xfold f i m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         let v1 = xfold f ((fun p->2*p) i) l v in
         let v2 = f v1 (prev i) x in xfold f ((fun p->1+2*p) i) r v2
       | None ->
         let v1 = xfold f ((fun p->2*p) i) l v in
         xfold f ((fun p->1+2*p) i) r v1)

  (** val fold : ('a2 -> int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m v =
    xfold f 1 m v

  (** val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold1 f m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x -> let v1 = fold1 f l v in let v2 = f v1 x in fold1 f r v2
       | None -> let v1 = fold1 f l v in fold1 f r v1)
 end

module PMap =
 struct
  type 'a t = 'a * 'a PTree.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init x =
    (x, PTree.empty)

  (** val get : int -> 'a1 t -> 'a1 **)

  let get i m =
    match PTree.get i (snd m) with
    | Some x -> x
    | None -> fst m

  (** val set : int -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)

  let set i x m =
    ((fst m), (PTree.set i x (snd m)))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    ((f (fst m)), (PTree.map1 f (snd m)))
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> int

  val eq : t -> t -> bool
 end

module IMap =
 functor (X:INDEXED_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> bool **)

  let elt_eq =
    X.eq

  type 'x t = 'x PMap.t

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init =
    PMap.init

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get i m =
    PMap.get (X.index i) m

  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)

  let set i v m =
    PMap.set (X.index i) v m

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    PMap.map
 end

module ZIndexed =
 struct
  type t = int

  (** val index : int -> int **)

  let index z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> (fun p->2*p) p)
      (fun p -> (fun p->1+2*p) p)
      z

  (** val eq : int -> int -> bool **)

  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

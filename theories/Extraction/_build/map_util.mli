open Maps

module M :
 sig
  type elt = int

  val elt_eq : int -> int -> bool

  type 'a tree = 'a PTree.tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val get : int -> 'a1 t -> 'a1 option

  val set : int -> 'a1 -> 'a1 t -> 'a1 t

  val remove : int -> 'a1 t -> 'a1 t

  val bempty : 'a1 t -> bool

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val prev_append : int -> int -> int

  val prev : int -> int

  val xmap : (int -> 'a1 -> 'a2) -> 'a1 t -> int -> 'a2 t

  val map : (int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t

  val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t

  val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xelements : 'a1 t -> int -> (int * 'a1) list -> (int * 'a1) list

  val elements : 'a1 t -> (int * 'a1) list

  val xkeys : 'a1 t -> int -> int list

  val xfold : ('a2 -> int -> 'a1 -> 'a2) -> int -> 'a1 t -> 'a2 -> 'a2

  val fold : ('a2 -> int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

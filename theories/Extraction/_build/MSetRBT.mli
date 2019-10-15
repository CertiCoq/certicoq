open BinPos
open Datatypes
open List0
open MSetInterface
open Nat0
open Orders
open OrdersFacts

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : X.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : X.t list -> tree -> X.t list

    val elements : tree -> X.t list

    val rev_elements_aux : X.t list -> tree -> X.t list

    val rev_elements : tree -> X.t list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> X.t -> tree -> bool

    val subsetr : (tree -> bool) -> X.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> X.t -> tree -> tree

    val rbal : tree -> X.t -> tree -> tree

    val rbal' : tree -> X.t -> tree -> tree

    val lbalS : tree -> X.t -> tree -> tree

    val rbalS : tree -> X.t -> tree -> tree

    val ins : X.t -> tree -> tree

    val add : X.t -> tree -> tree

    val append : tree -> tree -> tree

    val del : X.t -> tree -> tree

    val remove : X.t -> tree -> tree

    val delmin : tree -> elt -> tree -> elt * tree

    val remove_min : tree -> (elt * tree) option

    val bogus : tree * elt list

    val treeify_zero : elt list -> tree * elt list

    val treeify_one : elt list -> tree * elt list

    val treeify_cont :
      (elt list -> tree * elt list) -> (elt list -> tree * elt list) -> elt
      list -> tree * elt list

    val treeify_aux : bool -> int -> elt list -> tree * elt list

    val plength_aux : elt list -> int -> int

    val plength : elt list -> int

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list

    val filter : (elt -> bool) -> t -> t

    val partition_aux :
      (elt -> bool) -> tree -> X.t list -> X.t list -> X.t list * X.t list

    val partition : (elt -> bool) -> t -> t * t

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : X.t list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : X.t -> tree -> bool

    val gtb_tree : X.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1

    val rrcase' :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt * Raw.t) option -> (elt * t) option

  val remove_min : t_ -> (elt * t) option
 end

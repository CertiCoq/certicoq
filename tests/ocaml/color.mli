
type unit0 =
| Tt

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val eqb : bool -> bool -> bool

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

val le_lt_dec : nat -> nat -> sumbool

val le_gt_dec : nat -> nat -> sumbool

val le_dec : nat -> nat -> sumbool

val lt_dec : nat -> nat -> sumbool

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : nat -> positive
 end

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val succ : z -> z

  val pred : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val gtb : z -> z -> bool

  val of_nat : nat -> z

  val to_pos : z -> positive
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

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

module PositiveOrderedTypeBits :
 sig
  type t = positive

  val compare : t -> t -> positive compare0

  val eq_dec : positive -> positive -> sumbool
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

module PositiveSet :
 sig
  module E :
   sig
    type t = positive

    val compare : t -> t -> positive compare0

    val eq_dec : positive -> positive -> sumbool
   end

  type elt = positive

  type tree =
  | Leaf
  | Node of tree * bool * tree

  type t = tree

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val node : t -> bool -> t -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val rev_append : elt -> elt -> elt

  val rev : elt -> elt

  val xfold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> elt -> 'a1

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val xforall : (elt -> bool) -> t -> elt -> bool

  val for_all : (elt -> bool) -> t -> bool

  val xexists : (elt -> bool) -> t -> elt -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val xfilter : (elt -> bool) -> t -> elt -> t

  val filter : (elt -> bool) -> t -> t

  val xpartition : (elt -> bool) -> t -> elt -> (t, t) prod

  val partition : (elt -> bool) -> t -> (t, t) prod

  val xelements : t -> elt -> elt list -> elt list

  val elements : t -> elt list

  val cardinal : t -> nat

  val omap : (elt -> elt) -> elt option -> elt option

  val choose : t -> elt option

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare_bool : bool -> bool -> comparison

  val compare_fun : t -> t -> comparison

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> t compare0
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

val append : positive -> positive -> positive

module PositiveMap :
 sig
  module E :
   sig
    type t = positive

    val compare : t -> t -> positive compare0

    val eq_dec : positive -> positive -> sumbool
   end

  module ME :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = positive
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : positive -> positive -> sumbool

      val lt_dec : positive -> positive -> sumbool

      val eqb : positive -> positive -> bool
     end
   end

  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val mem : key -> 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val xelements : 'a1 t -> key -> (key, 'a1) prod list

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val xfind : key -> key -> 'a1 t -> 'a1 option

  val xmapi : (key -> 'a1 -> 'a2) -> 'a1 t -> key -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val xmap2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xmap2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val _map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xfoldi : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> key -> 'a2

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module E :
 OrderedType with type t = positive

module Coq0_S :
 S with module E = E with type elt = PositiveSet.elt with type t = PositiveSet.t

module M :
 Coq_S with module E = E with type 'a t = 'A PositiveMap.t

type node0 = E.t

type nodeset = Coq0_S.t

type 'x nodemap = 'x M.t

type graph = nodeset nodemap

val adj : graph -> node0 -> nodeset

val subset_nodes : (node0 -> nodeset -> sumbool) -> graph -> Coq0_S.t

val low_deg_dec : nat -> node0 -> nodeset -> sumbool

val remove_node : node0 -> graph -> graph

val select : nat -> graph -> node0 list

type coloring = node0 M.t

val colors_of : coloring -> Coq0_S.t -> Coq0_S.t

val color1 : Coq0_S.t -> graph -> node0 -> coloring -> coloring

val color : Coq0_S.t -> graph -> coloring

type graph_description = (z, (z, z list) prod list) prod

val iota' : z -> z list -> z list

val iota : z -> z list

val clique : z -> (z, z) prod list

val zzlist_to_poslist : (z, z) prod list -> (positive, positive) prod list

val translate_adj_list : (z, z list) prod -> (z, z) prod list

val parse_graph : graph_description -> (positive, positive) prod list

val make_palette : graph_description -> Coq0_S.t

val add_edge : (E.t, E.t) prod -> graph -> graph

val mk_graph : (E.t, E.t) prod list -> graph

val run : graph_description -> (z, z) prod

val g16 : graph_description

val main : (z, z) prod

val color0 : unit0 -> (z, z) prod

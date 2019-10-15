open Datatypes
open MSetWeakList
open Nat0
open PeanoNat
open String0
open Utils

val compare_bool : bool -> bool -> comparison

val bool_lt : bool -> bool -> bool

module Level :
 sig
  type t =
  | Coq_lProp
  | Coq_lSet
  | Level of char list
  | Var of nat

  val t_rect : 'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t -> 'a1

  val t_rec : 'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t -> 'a1

  val set : t

  val prop : t

  val is_prop : t -> bool

  val compare : t -> t -> comparison
 end

module LevelDecidableType :
 sig
  type t = Level.t

  val eq_dec : t -> t -> bool
 end

module LevelSet :
 sig
  module Raw :
   sig
    type elt = Level.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = Level.t

    val eq_dec : Level.t -> Level.t -> bool
   end

  type elt = Level.t

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
 end

type universe_level = Level.t

module Universe :
 sig
  module Expr :
   sig
    type t = Level.t * bool

    type super_result =
    | SuperSame of bool
    | SuperDiff of comparison

    val super : t -> t -> super_result
   end

  type t = Expr.t list

  val level : t -> Level.t option

  val merge_univs : nat -> t -> t -> t

  val sup : t -> t -> t

  val sort_of_product : t -> t -> t
 end

type universe = Universe.t

module ConstraintType :
 sig
  type t =
  | Lt
  | Le
  | Eq

  val t_rect : 'a1 -> 'a1 -> 'a1 -> t -> 'a1

  val t_rec : 'a1 -> 'a1 -> 'a1 -> t -> 'a1
 end

type univ_constraint = (universe_level * ConstraintType.t) * universe_level

module UnivConstraintDec :
 sig
  type t = univ_constraint

  val eq_dec : t -> t -> bool
 end

module ConstraintSet :
 sig
  module Raw :
   sig
    type elt = univ_constraint

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = univ_constraint

    val eq_dec : univ_constraint -> univ_constraint -> bool
   end

  type elt = univ_constraint

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
 end

type constraints = ConstraintSet.t

type 'a constrained = 'a * constraints

module Instance :
 sig
  type t = Level.t list
 end

type universe_instance = Instance.t

module UContext :
 sig
  type t = Instance.t constrained
 end

module Variance :
 sig
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

module CumulativityInfo :
 sig
  type t = UContext.t * Variance.t list
 end

type universe_context =
| Monomorphic_ctx of UContext.t
| Polymorphic_ctx of UContext.t
| Cumulative_ctx of CumulativityInfo.t

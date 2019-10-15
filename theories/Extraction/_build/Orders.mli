open Datatypes

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

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

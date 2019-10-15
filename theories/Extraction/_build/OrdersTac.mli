open Datatypes
open Orders

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

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

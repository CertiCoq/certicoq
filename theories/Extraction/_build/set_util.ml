open Datatypes
open List0
open MSetRBT
open POrderedType

module PS = Make(Positive_as_OT)

(** val union_list : PS.t -> PS.elt list -> PS.t **)

let union_list s l =
  fold_left (fun set e -> PS.add e set) l s

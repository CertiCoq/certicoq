
type coq_Decidable =
  bool
  (* singleton inductive, whose constructor was Build_Decidable *)

val coq_Decidable_witness : coq_Decidable -> bool

val decide : coq_Decidable -> bool

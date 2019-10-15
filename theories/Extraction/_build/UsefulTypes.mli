open DecidableClass

val coq_DecConj : coq_Decidable -> coq_Decidable -> coq_Decidable

type 't coq_Deq = 't -> 't -> coq_Decidable

val deceq : 'a1 coq_Deq -> 'a1 -> 'a1 -> coq_Decidable

type coq_DecidableSumbool = bool

val decAsSumbool : coq_DecidableSumbool -> coq_Decidable

type 't coq_DeqSumbool = 't -> 't -> coq_DecidableSumbool

val deceqSumbool : 'a1 coq_DeqSumbool -> 'a1 -> 'a1 -> coq_DecidableSumbool

val deqAsSumbool : 'a1 coq_DeqSumbool -> 'a1 coq_Deq

val deq_prod : 'a1 coq_Deq -> 'a2 coq_Deq -> ('a1 * 'a2) coq_Deq

val opExtract : 'a1 -> 'a1 option -> 'a1

val xor : bool -> bool -> bool

val ascii_dec_bool : char -> char -> bool

val string_eq_bool : char list -> char list -> bool

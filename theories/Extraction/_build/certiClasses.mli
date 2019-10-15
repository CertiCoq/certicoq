open Datatypes
open ExceptionMonad

type ('term, 'value) bigStepResult =
| Result of 'value
| OutOfTime of 'term
| Error of char list * 'term option

type coq_Opt = nat
  (* singleton inductive, whose constructor was Flag *)

type ('src, 'dst) coq_CerticoqTranslation =
  coq_Opt -> 'src -> 'dst coq_exception

val translate :
  ('a1, 'a2) coq_CerticoqTranslation -> coq_Opt -> 'a1 -> 'a2 coq_exception

type ('src, 'dst) coq_CerticoqTotalTranslation = coq_Opt -> 'src -> 'dst

val translateT :
  ('a1, 'a2) coq_CerticoqTotalTranslation -> coq_Opt -> 'a1 -> 'a2

val liftTotal :
  ('a1, 'a2) coq_CerticoqTotalTranslation -> ('a1, 'a2)
  coq_CerticoqTranslation

val composeTranslation :
  ('a1, 'a2) coq_CerticoqTranslation -> ('a2, 'a3) coq_CerticoqTranslation ->
  ('a1, 'a3) coq_CerticoqTranslation

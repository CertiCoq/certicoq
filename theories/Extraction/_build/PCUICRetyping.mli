open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICChecker
open PCUICLiftSubst
open Monad_utils
open Univ0
open Utils

val type_of_as_sort :
  coq_Fuel -> global_context -> (context -> term -> term typing_result) ->
  context -> term -> universe typing_result

val type_of :
  coq_Fuel -> global_context -> context -> term -> term typing_result

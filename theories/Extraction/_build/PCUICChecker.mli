open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICTyping
open PCUICUnivSubst
open Monad_utils
open Univ0
open Utils

type __ = Obj.t

module RedFlags :
 sig
  type t = { beta : bool; iota : bool; zeta : bool; delta : bool;
             fix_ : bool; cofix_ : bool }

  val beta : t -> bool

  val iota : t -> bool

  val zeta : t -> bool

  val delta : t -> bool

  val fix_ : t -> bool

  val default : t
 end

val zip : (term * term list) -> term

val reduce_stack :
  RedFlags.t -> global_declarations -> context -> nat -> term -> term list ->
  (term * term list) option

val fix_decls : term mfixpoint -> context_decl list

val lookup_env : global_context -> ident -> global_decl option

type type_error =
| UnboundRel of nat
| UnboundVar of char list
| UnboundMeta of nat
| UnboundEvar of nat
| UndeclaredConstant of char list
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotConvertible of context * term * term * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| NotEnoughFuel of nat

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

val typing_monad : __ typing_result coq_Monad

val monad_exc : (type_error, __ typing_result) coq_MonadExc

val hnf_stack :
  coq_Fuel -> global_declarations -> context -> term -> (term * term list)
  typing_result

val reduce_to_sort :
  coq_Fuel -> global_declarations -> context -> term -> universe typing_result

val reduce_to_prod :
  coq_Fuel -> global_declarations -> context -> term -> (term * term)
  typing_result

val reduce_to_ind :
  coq_Fuel -> global_declarations -> context -> term -> ((inductive * Level.t
  list) * term list) typing_result

val lookup_constant_type :
  global_context -> ident -> universe_instance -> term typing_result

val lookup_ind_decl :
  global_context -> ident -> nat -> ((one_inductive_body
  list * universe_context) * one_inductive_body) typing_result

val lookup_ind_type :
  global_context -> ident -> nat -> Level.t list -> term typing_result

val lookup_constructor_decl :
  global_context -> ident -> nat -> nat -> ((one_inductive_body
  list * universe_context) * term) typing_result

val lookup_constructor_type :
  global_context -> ident -> nat -> nat -> universe_instance -> term
  typing_result

val try_suc : Universe.t -> Universe.t

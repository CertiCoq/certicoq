open BinNat
open BinPos
open Datatypes
open Monad0
open Nat0
open StateMonad
open Cps
open State

val eq_var : int -> int -> bool

val occurs_in_vars : var -> var list -> bool

val occurs_in_exp : var -> exp -> bool

val occurs_in_fundefs : var -> fundefs -> bool

type coq_St = nat * nat M.t

type arityMap = fTag M.t

type localMap = bool M.t

type stateType = ((bool * arityMap) * localMap) * coq_St

type 't uncurryM = (stateType, 't) compM

val markToInline : nat -> var -> var -> unit uncurryM

val mark_as_uncurried : var -> unit uncurryM

val click : unit uncurryM

val has_clicked : bool uncurryM

val already_uncurried : var -> bool uncurryM

val get_fTag : int -> fTag uncurryM

val uncurry_exp : exp -> exp uncurryM

val uncurry_fundefs : fundefs -> fundefs uncurryM

val uncurry : exp -> exp option uncurryM

val uncurry_fuel' : nat -> exp -> exp uncurryM

val uncurry_fuel : nat -> exp -> comp_data -> (exp * nat M.t) * comp_data

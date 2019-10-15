open Datatypes
open MSetWeakList
open Nat0
open PeanoNat
open String0
open Utils

(** val compare_bool : bool -> bool -> comparison **)

let compare_bool b1 b2 =
  if b1 then if b2 then Eq else Gt else if b2 then Lt else Eq

(** val bool_lt : bool -> bool -> bool **)

let bool_lt b1 b2 =
  match compare_bool b1 b2 with
  | Lt -> true
  | _ -> false

module Level =
 struct
  type t =
  | Coq_lProp
  | Coq_lSet
  | Level of char list
  | Var of nat

  (** val t_rect :
      'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t -> 'a1 **)

  let t_rect f f0 f1 f2 = function
  | Coq_lProp -> f
  | Coq_lSet -> f0
  | Level x -> f1 x
  | Var x -> f2 x

  (** val t_rec :
      'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t -> 'a1 **)

  let t_rec f f0 f1 f2 = function
  | Coq_lProp -> f
  | Coq_lSet -> f0
  | Level x -> f1 x
  | Var x -> f2 x

  (** val set : t **)

  let set =
    Coq_lSet

  (** val prop : t **)

  let prop =
    Coq_lProp

  (** val is_prop : t -> bool **)

  let is_prop = function
  | Coq_lProp -> true
  | _ -> false

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lProp -> (match l2 with
                    | Coq_lProp -> Eq
                    | _ -> Lt)
    | Coq_lSet -> (match l2 with
                   | Coq_lProp -> Gt
                   | Coq_lSet -> Eq
                   | _ -> Lt)
    | Level s1 ->
      (match l2 with
       | Level s2 -> string_compare s1 s2
       | Var _ -> Lt
       | _ -> Gt)
    | Var n -> (match l2 with
                | Var m -> compare n m
                | _ -> Gt)
 end

module LevelDecidableType =
 struct
  type t = Level.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | Level.Coq_lProp -> (match y with
                          | Level.Coq_lProp -> true
                          | _ -> false)
    | Level.Coq_lSet -> (match y with
                         | Level.Coq_lSet -> true
                         | _ -> false)
    | Level.Level x0 ->
      (match y with
       | Level.Level s0 -> string_dec x0 s0
       | _ -> false)
    | Level.Var x0 ->
      (match y with
       | Level.Var n0 -> Nat.eq_dec x0 n0
       | _ -> false)
 end

module LevelSet = Make(LevelDecidableType)

type universe_level = Level.t

module Universe =
 struct
  module Expr =
   struct
    type t = Level.t * bool

    type super_result =
    | SuperSame of bool
    | SuperDiff of comparison

    (** val super : t -> t -> super_result **)

    let super x y =
      match Level.compare (fst x) (fst y) with
      | Eq -> SuperSame (bool_lt (snd x) (snd y))
      | x0 ->
        let (l, b) = x in
        if b
        then SuperDiff x0
        else let (l', b0) = y in
             if b0
             then SuperDiff x0
             else (match l with
                   | Level.Coq_lProp ->
                     (match l' with
                      | Level.Coq_lProp -> SuperSame false
                      | _ -> SuperSame true)
                   | _ ->
                     (match l' with
                      | Level.Coq_lProp -> SuperSame false
                      | _ -> SuperDiff x0))
   end

  type t = Expr.t list

  (** val level : t -> Level.t option **)

  let level = function
  | [] -> None
  | t0 :: l0 ->
    let (l, b) = t0 in
    if b then None else (match l0 with
                         | [] -> Some l
                         | _ :: _ -> None)

  (** val merge_univs : nat -> t -> t -> t **)

  let rec merge_univs fuel l1 l2 =
    match fuel with
    | O -> l1
    | S fuel0 ->
      (match l1 with
       | [] -> l2
       | h1 :: t1 ->
         (match l2 with
          | [] -> l1
          | h2 :: t2 ->
            (match Expr.super h1 h2 with
             | Expr.SuperSame b ->
               if b then merge_univs fuel0 t1 l2 else merge_univs fuel0 l1 t2
             | Expr.SuperDiff c ->
               (match c with
                | Lt -> h1 :: (merge_univs fuel0 t1 l2)
                | _ -> h2 :: (merge_univs fuel0 l1 t2)))))

  (** val sup : t -> t -> t **)

  let sup u1 u2 =
    merge_univs (add (add (Datatypes.length u1) (Datatypes.length u2)) (S O))
      u1 u2

  (** val sort_of_product : t -> t -> t **)

  let sort_of_product domsort rangsort = match rangsort with
  | [] -> sup domsort rangsort
  | t0 :: l ->
    let (t1, b) = t0 in
    (match t1 with
     | Level.Coq_lProp ->
       if b
       then sup domsort rangsort
       else (match l with
             | [] -> rangsort
             | _ :: _ -> sup domsort rangsort)
     | _ -> sup domsort rangsort)
 end

type universe = Universe.t

module ConstraintType =
 struct
  type t =
  | Lt
  | Le
  | Eq

  (** val t_rect : 'a1 -> 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rect f f0 f1 = function
  | Lt -> f
  | Le -> f0
  | Eq -> f1

  (** val t_rec : 'a1 -> 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rec f f0 f1 = function
  | Lt -> f
  | Le -> f0
  | Eq -> f1
 end

type univ_constraint = (universe_level * ConstraintType.t) * universe_level

module UnivConstraintDec =
 struct
  type t = univ_constraint

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let (x0, x1) = x in
    let (p, u) = y in
    let (x2, x3) = x0 in
    let (u0, t0) = p in
    if LevelDecidableType.eq_dec x2 u0
    then (match x3 with
          | ConstraintType.Lt ->
            (match t0 with
             | ConstraintType.Lt ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match u with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match u with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match u with
                   | Level.Level s0 -> string_dec x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match u with
                   | Level.Var n0 -> Nat.eq_dec x4 n0
                   | _ -> false))
             | _ -> false)
          | ConstraintType.Le ->
            (match t0 with
             | ConstraintType.Le ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match u with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match u with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match u with
                   | Level.Level s0 -> string_dec x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match u with
                   | Level.Var n0 -> Nat.eq_dec x4 n0
                   | _ -> false))
             | _ -> false)
          | ConstraintType.Eq ->
            (match t0 with
             | ConstraintType.Eq ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match u with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match u with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match u with
                   | Level.Level s0 -> string_dec x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match u with
                   | Level.Var n0 -> Nat.eq_dec x4 n0
                   | _ -> false))
             | _ -> false))
    else false
 end

module ConstraintSet = Make(UnivConstraintDec)

type constraints = ConstraintSet.t

type 'a constrained = 'a * constraints

module Instance =
 struct
  type t = Level.t list
 end

type universe_instance = Instance.t

module UContext =
 struct
  type t = Instance.t constrained
 end

module Variance =
 struct
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

module CumulativityInfo =
 struct
  type t = UContext.t * Variance.t list
 end

type universe_context =
| Monomorphic_ctx of UContext.t
| Polymorphic_ctx of UContext.t
| Cumulative_ctx of CumulativityInfo.t

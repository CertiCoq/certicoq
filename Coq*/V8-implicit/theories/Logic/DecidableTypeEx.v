(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: DecidableTypeEx.v 8933 2006-06-09 14:08:38Z herbelin $ *)

Require Import DecidableType OrderedType OrderedTypeEx.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Examples of Decidable Type structures. *)

(** A particular case of [DecidableType] where 
    the equality is the usual one of Coq. *)

Module Type UsualDecidableType.
 Parameter t : Set.
 Definition eq := @eq t.
 Definition eq_refl x := @refl_equal t x.
 Definition eq_sym x y := @sym_eq t x y.
 Definition eq_trans x y z := @trans_eq t x y z.
 Parameter eq_dec : forall x y, { eq x y }+{~eq x y }.
End UsualDecidableType.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** An OrderedType can be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType. 
 Module OF := OrderedTypeFacts O.
 Definition t := O.t.
 Definition eq := O.eq. 
 Definition eq_refl := O.eq_refl. 
 Definition eq_sym := O.eq_sym. 
 Definition eq_trans := O.eq_trans. 
 Definition eq_dec := OF.eq_dec. 
End OT_as_DT.

(** (Usual) Decidable Type for [nat], [positive], [N], [Z] *)

Module Nat_as_DT <: UsualDecidableType := OT_as_DT (Nat_as_OT).
Module Positive_as_DT <: UsualDecidableType := OT_as_DT (Positive_as_OT).
Module N_as_DT <: UsualDecidableType := OT_as_DT (N_as_OT).
Module Z_as_DT <: UsualDecidableType := OT_as_DT (Z_as_OT).

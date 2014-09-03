(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: pmlize.mli 5920 2004-07-16 20:01:26Z herbelin $ *)

open Past
open Penv
open Names

(* translation of imperative programs into intermediate functional programs *)

val trans : Prename.t -> typed_program -> cc_term


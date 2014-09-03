(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: alpha.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

(* Alphabetic order. *)

val compare_char : char -> char -> int
val compare_string : string -> string -> int

(* Alphabetic normalization. *)

val norm_char : char -> char
val norm_string : string -> string

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: vernacinterp.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

(*i*)
open Tacexpr
(*i*)

(* Interpretation of extended vernac phrases. *)
 
val disable_drop : exn -> exn

val vinterp_add : string -> (raw_generic_argument list -> unit -> unit) -> unit
val overwriting_vinterp_add : 
  string -> (raw_generic_argument list -> unit -> unit) -> unit

val vinterp_init : unit -> unit
val call : string * raw_generic_argument list -> unit

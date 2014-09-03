(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: dyn.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

(* Dynamics. Use with extreme care. Not for kids. *)

type t

val create : string -> ('a -> t) * (t -> 'a)
val tag : t -> string

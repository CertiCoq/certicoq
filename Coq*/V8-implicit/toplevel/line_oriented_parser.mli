(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: line_oriented_parser.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

val line_oriented_channel_to_option: string -> in_channel -> int -> char option

val flush_until_end_of_stream : 'a Stream.t -> unit

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: reserve.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

open Util
open Names
open Rawterm

val declare_reserved_type : identifier located -> rawconstr -> unit
val find_reserved_type : identifier -> rawconstr
val anonymize_if_reserved : name -> rawconstr -> rawconstr

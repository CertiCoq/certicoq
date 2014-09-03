(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: g_rtauto.ml4 7734 2005-12-26 14:06:51Z herbelin $*)

(*i camlp4deps: "parsing/grammar.cma"  i*)

TACTIC EXTEND rtauto
  [ "rtauto" ] -> [ Refl_tauto.rtauto_tac ]
END


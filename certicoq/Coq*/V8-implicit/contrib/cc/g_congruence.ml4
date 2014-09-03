(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id: g_congruence.ml4 9151 2006-09-19 13:32:22Z corbinea $ *)

open Cctac
open Tactics
open Tacticals

(* Tactic registration *)
      
TACTIC EXTEND cc
 [ "congruence" ] -> [ congruence_tac 0 [] ]
 |[ "congruence" integer(n) ] -> [ congruence_tac n [] ]
 |[ "congruence" "with" ne_constr_list(l) ] -> [ congruence_tac 0 l ]
 |[ "congruence" integer(n) "with" ne_constr_list(l) ] -> 
   [ congruence_tac n l ]
END

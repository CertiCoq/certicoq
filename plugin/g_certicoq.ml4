(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Stdarg
open Pp
open Certicoq
open Ltac_plugin

open Tacarg
open Vernacexpr
open Pcoq
open Genarg



VERNAC ARGUMENT EXTEND cargs
| [ "-anf" ] -> [ ANF ]
| [ "-time" ] -> [ TIME ]
| [ "-o1" ] -> [ OPT(1) ]
| [ "-debug" ] -> [ DEBUG ]
| [ "-args" "0" ] -> [ ARGS(0) ]
| [ "-args" "1" ] -> [ ARGS(1) ]
| [ "-args" "2" ] -> [ ARGS(2) ]
| [ "-args" "3" ] -> [ ARGS(3) ]
| [ "-args" "4" ] -> [ ARGS(4) ]
| [ "-args" "5" ] -> [ ARGS(5) ]
| [ "-args" "6" ] -> [ ARGS(6) ]
| [ "-args" "7" ] -> [ ARGS(7) ]
| [ "-args" "8" ] -> [ ARGS(8) ]
| [ "-args" "9" ] -> [ ARGS(9) ]
| [ "-args" "10" ] -> [ ARGS(10) ]
| [ "-args" "11" ] -> [ ARGS(11) ]
| [ "-args" "12" ] -> [ ARGS(12) ]
END

(* ZOE: TODO Now this is really ugly. However the more elegant:
| [ "-args" int(n) ] -> [ ARGS(n) ]
doesn't seem to work because int() is not found. It seems that  in other developments similar things work:
http://www.lix.polytechnique.fr/~barras/darcs/V8-implicit/_darcs/pristine/contrib/extraction/g_extraction.ml4
https://gitlab.informatik.uni-bremen.de/fritjof/coq/blob/fca82378cd2824534383f1f5bc09d08fade1dc17/plugins/ltac/g_ltac.ml4
I will look further into it *)

VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" cargs_list(l) global(gr) ] -> [
    let gr = Nametab.global gr in
    match Certicoq.make_options l with
    | Res opts -> Certicoq.compile opts gr
    | Error s -> Feedback.msg_error (Pp.str s ++ Pp.str "\n" ++ Pp.str Certicoq.options_help)
  ]
(* | [ "CertiCoq" "Show" "L6" "Opt" int(n) global(gr) ] -> [ *)
(*     let gr = Nametab.global gr in *)
(*     Certicoq.show_l6 (coq_nat_of_int n) gr *)
(*   ] *)
END

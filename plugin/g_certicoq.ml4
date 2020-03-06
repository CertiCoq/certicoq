(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Pp
open Certicoq
open Ltac_plugin
open Stdarg
open Pcoq.Prim

VERNAC ARGUMENT EXTEND cargs 
| [ "-anf" ] -> [ ANF ]
| [ "-time" ] -> [ TIME ]
| [ "-o1" ] -> [ OPT(1) ]
| [ "-debug" ] -> [ DEBUG ]
| [ "-args" natural(n) ] -> [ ARGS(n) ]
| [ "-fvargs" natural(n) ] -> [ FVARGS(n) ]
(* Zoe: -fvargs only for my convenience in parameterizing lambda lifting and
   measuring performance. Not intended for user purposes. *)
| [ "-ext" string(s) ] -> [ EXT(s) ]
END

VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" cargs_list(l) global(gr) ] -> [
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l in
    Certicoq.compile_with_glue opts gr
  ]
| [ "CertiCoq" "Show" "IR" cargs_list(l) global(gr) ] -> [
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l in
    Certicoq.show_ir opts gr
  ]
| [ "CertiCoq" "-help" ] -> [
    Feedback.msg_info (str help_msg)
  ]
END

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
END

VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" cargs_list(l) global(gr) ] -> [
    let gr = Nametab.global gr in
    match Certicoq.make_options l with
    | Res opts -> Certicoq.compile_with_glue opts gr
    | Error s -> Feedback.msg_error (Pp.str s ++ Pp.str "\n" ++ Pp.str Certicoq.options_help)
  ]
| [ "CertiCoq" "Show" "IR" cargs_list(l) global(gr) ] -> [
    let gr = Nametab.global gr in
    match Certicoq.make_options l with
    | Res opts -> Certicoq.show_ir opts gr
    | Error s -> Feedback.msg_error (Pp.str s ++ Pp.str "\n" ++ Pp.str Certicoq.options_help)
  ]
END

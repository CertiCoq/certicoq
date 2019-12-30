(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Stdarg
open Pp

VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" string_list(l) global(gr) ] -> [
    (* Zoe: Ideally use a custom data type instead of string *)
    let gr = Nametab.global gr in
    match Certicoq.parse_options l with
    | Res opts -> Certicoq.compile opts gr
    | Error s -> Feedback.msg_error (Pp.str s ++ Pp.str "\n" ++ Pp.str Certicoq.options_help)
  ]
| [ "CertiCoq" "Compile" global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile Certicoq.default_options gr
  ]
(* | [ "CertiCoq" "Show" "L6" "Opt" int(n) global(gr) ] -> [ *)
(*     let gr = Nametab.global gr in *)
(*     Certicoq.show_l6 (coq_nat_of_int n) gr *)
(*   ] *)
END

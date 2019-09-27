(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Stdarg

VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile O gr
  ]
| [ "CertiCoq" "Compile" "Opt" global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile (S O) gr
  ]
END

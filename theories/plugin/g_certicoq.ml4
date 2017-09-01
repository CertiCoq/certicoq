(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Constrarg

VERNAC COMMAND EXTEND Certicoq_compile CLASSIFIED AS QUERY
| [ "Certicoq" "Compile" global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile gr
  ]
END

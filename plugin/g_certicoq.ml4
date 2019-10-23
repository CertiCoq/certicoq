(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "certicoq_plugin"

open Stdarg

let rec coq_nat_of_int x =
  match x with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (coq_nat_of_int (pred n))


VERNAC COMMAND EXTEND CertiCoq_Compile CLASSIFIED AS QUERY
| [ "CertiCoq" "Compile" global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile true O gr
  ]
| [ "CertiCoq" "Compile" "Opt" int(n) global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile true (coq_nat_of_int n) gr
  ]
| [ "CertiCoq" "Compile" "ANF" "Opt" int(n) global(gr) ] -> [
    let gr = Nametab.global gr in
    Certicoq.compile false (coq_nat_of_int n) gr
  ]
END

From CertiCoq.Plugin Require Import Loader.
From Coq Require Import PrimFloat.

CertiCoq Register [ 
  Coq.Floats.PrimFloat.compare => "prim_float_compare",
  Coq.Floats.PrimFloat.eqb => "prim_float_eqb",
  Coq.Floats.PrimFloat.ltb => "prim_float_ltb",
  Coq.Floats.PrimFloat.leb => "prim_float_leb",
  Coq.Floats.PrimFloat.frshiftexp => "prim_float_frshiftexp" with tinfo,
  Coq.Floats.PrimFloat.ldshiftexp => "prim_float_ldshiftexp" with tinfo,
  Coq.Floats.PrimFloat.normfr_mantissa => "prim_float_normfr_mantissa",
  Coq.Floats.PrimFloat.classify => "prim_float_classify",
  Coq.Floats.PrimFloat.abs => "prim_float_abs" with tinfo,
  Coq.Floats.PrimFloat.sqrt => "prim_float_sqrt" with tinfo,
  Coq.Floats.PrimFloat.opp => "prim_float_opp" with tinfo,
  Coq.Floats.PrimFloat.div => "prim_float_div" with tinfo,
  Coq.Floats.PrimFloat.mul => "prim_float_mul" with tinfo,
  Coq.Floats.PrimFloat.add => "prim_float_add" with tinfo,
  Coq.Floats.PrimFloat.sub => "prim_float_sub" with tinfo,
  Coq.Floats.PrimFloat.of_uint63 => "prim_float_of_uint63" with tinfo,
  Coq.Floats.PrimFloat.next_up => "prim_float_next_up" with tinfo,
  Coq.Floats.PrimFloat.next_down => "prim_float_next_down" with tinfo ]
Include [ "prim_floats.h" as library ].

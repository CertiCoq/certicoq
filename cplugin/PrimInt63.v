From CertiCoq.VanillaPlugin Require Import Loader.
From Coq.Numbers.Cyclic.Int63 Require Import PrimInt63.

CertiCoq Register [ 
  Coq.Numbers.Cyclic.Int63.PrimInt63.add => "prim_int63_add",
  Coq.Numbers.Cyclic.Int63.PrimInt63.eqb => "prim_int63_eqb",
  Coq.Numbers.Cyclic.Int63.PrimInt63.land => "prim_int63_land", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsr => "prim_int63_lsr", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsl => "prim_int63_lsl", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.head0 => "prim_int63_head0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.tail0 => "prim_int63_tail0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.compare => "prim_int63_compare", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.subc => "prim_int63_subc" with tinfo,
  Coq.Numbers.Cyclic.Int63.PrimInt63.sub => "prim_int63_sub", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addc => "prim_int63_addc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "prim_int63_addcarryc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "prim_int63_subcarryc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mulc => "prim_int63_mulc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mul => "prim_int63_mul", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "prim_int63_diveucl_21" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl => "prim_int63_diveucl" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mod => "prim_int63_mod", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "prim_int63_addmuldiv", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.leb => "prim_int63_leb", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.ltb => "prim_int63_ltb", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.div => "prim_int63_div", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lor => "prim_int63_lor", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lxor => "prim_int63_lxor"
]
Include [ Library "prim_int63.h" ].

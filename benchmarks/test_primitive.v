From MetaCoq.Template Require Import bytestring MCString.
From CertiCoq.Plugin Require Import CertiCoq.
From Coq Require Import Uint63.
Open Scope bs.

CertiCoq Generate Glue -file "basics" [ nat, list, bool ].

Definition cst := (5 + 1)%uint63.

CertiCoq Compile cst
Extract Constants [ 
    Coq.Numbers.Cyclic.Int63.PrimInt63.add => "prim_int63_add" ]
Include [ "prim_int63.h" ].

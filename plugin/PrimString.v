From CertiCoq.Plugin Require Import Loader.
From Coq Require Import PString.

CertiCoq Register [
    Coq.Strings.PrimString.compare => "prim_string_compare",
      Coq.Strings.PrimString.get => "prim_string_get",
      Coq.Strings.PrimString.length => "prim_string_length"
  ]
  Include [ Library "prim_string.h" ].


From CertiCoq.VanillaPlugin Require Import Loader.
From Corelib Require Import PrimString.

CertiCoq Register [
  Corelib.Strings.PrimString.compare => "prim_string_compare",
  Corelib.Strings.PrimString.get => "prim_string_get",
  Corelib.Strings.PrimString.length => "prim_string_length"
]
Include [ Library "prim_string.h" ].


(** Naive conversion to continuation-passing style for a core language including
    mutually recursive functions, data constructors, and pattern matching.
*)
Require Import Arith BinNat String List Omega Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

Require L3.term.

Require Import simpleCPS.






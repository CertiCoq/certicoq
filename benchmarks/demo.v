Require Import Arith.
  

From CertiCoq.Plugin Require Import CertiCoq.


Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).

CertiCoq Compile demo1.

Definition demo2 := (negb, List.hd_error).

CertiCoq Compile demo2.
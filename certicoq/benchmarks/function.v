Require Import Recdef.
Require Import ZArith.


Function sqrt' (n x0 x diff: Z) {measure Z.to_nat diff} : Z :=
 (if diff =? 0
 then x
 else let y := Z.div2 (x + Z.div n x)
          in if y =? x0 then Z.min x0 x
              else sqrt' n x y (y-x0))%Z.
Proof.
Admitted.

Definition sqrt n := sqrt' n 0 n n.

Definition test n := Z.to_nat (sqrt (Z.of_nat n)).

Extraction "sqrt.ml" test .


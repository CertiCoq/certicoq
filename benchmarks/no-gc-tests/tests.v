Require Import Arith List String.

From CertiCoq.Plugin Require Import CertiCoq.

Import ListNotations.

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 10).

(* Demo 3 *)

Definition demo3 := List.fold_left plus (List.repeat 1 10) 0.

Eval compute in "Compiling demo1"%string.

CertiCoq Compile -no-gc demo1.

CertiCoq Generate Glue -file "glue_demo1" [ list, bool ].

Eval compute in "Compiling demo2"%string.

CertiCoq Compile -no-gc demo2.

CertiCoq Generate Glue -file "glue_demo2" [ list, bool ].

Eval compute in "Compiling demo3"%string.

CertiCoq Compile -no-gc demo3.

CertiCoq Generate Glue -file "glue_demo3" [ nat ].

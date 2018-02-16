Require Import Arith.
From CertiCoq Require Import CertiCoq.

Definition foo := 3 + 4.

CertiCoq Compile foo.

Require Import vs.
CertiCoq Compile main.

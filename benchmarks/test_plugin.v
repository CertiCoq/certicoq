Require Import Arith.
From CertiCoq.Plugin Require Import CertiCoq.
Unset Template Cast Propositions.

Definition foo := 3 + 4.

CertiCoq Compile foo.

Require Import Binom.

CertiCoq Compile main.

Require Import CertiCoq.Benchmarks.vs.
CertiCoq Compile main.

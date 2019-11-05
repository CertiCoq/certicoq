Require Import Arith.
From CertiCoq.Plugin Require Import CertiCoq.
Unset Template Cast Propositions.
Require Import List.
Import ListNotations.
Definition foo := 3 + 4.

MetaCoq Check foo.
MetaCoq Erase foo.
CertiCoq Compile foo.

MetaCoq Erase (map negb [true; false]).

Definition test := map negb [true; false].
CertiCoq Compile test.

Require Import Binom.
(* Universe issues: template polymorphism not implemented yet *)
(* MetaCoq SafeCheck main. *)
(* MetaCoq Check main. *)
Time MetaCoq Erase main.

Time CertiCoq Compile main.

Require Import CertiCoq.Benchmarks.vs.
MetaCoq Erase main.
CertiCoq Compile main.

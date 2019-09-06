Require Import Arith.
From CertiCoq.Plugin Require Import CertiCoq.
Unset Template Cast Propositions.
Require Import List.
Import ListNotations.
Definition foo := 3 + 4.

MetaCoq Check foo.
MetaCoq Erase foo.
CertiCoq Compile foo.

Definition bool_list := map negb [true; false].
Set Printing Universes.
(* Universe issues: undeclared universes from sections *)
(* MetaCoq SafeCheck bool_list.*)

Require Import Binom.
(* Universe issues: template polymorphism not implemented yet *)

(* MetaCoq Erase main. *)
(* CertiCoq Compile main. *)

(* Require Import CertiCoq.Benchmarks.vs. *)
(* CertiCoq Compile main. *)

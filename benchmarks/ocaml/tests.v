Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

(* The same benchmarks as CertiCoq benchmarks, but slightly modified
   to suspend computations with unit so we can run multiple times *)

Definition demo1 (_ : unit) := List.app (List.repeat true 5) (List.repeat false 3).
Definition demo2 (_ : unit) := List.map negb [true; false; true].
Definition demo3 (_ : unit) := andb. 

Extraction "demo1" demo1.
Extraction "demo2" demo2.

Definition list_sum (_ : unit) := List.fold_left plus (List.repeat 1 100) 0.

Extraction "list_sum" list_sum.

Definition vs_easy (_ : unit) :=
  match vs.main with
  | Valid => true
  | _ => false
  end.

Definition vs_hard (_ : unit) :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

(* Modified by hand *)
(* Extraction "vs_easy" vs_easy. *)
(* Extraction "vs_hard" vs_hard. *)

Definition binom (_ : unit) := Binom.main.

Extraction "binom" binom.

Definition color (_ : unit) := Color.main.

Extraction "color" color.

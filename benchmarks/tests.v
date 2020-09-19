Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

CertiCoq -help.

(* Zoe : Currently not working *) 
(* Definition test := "The message". *)
(* Definition sha := sha256.SHA_256 (sha256.str_to_bytes test). *)

(* CertiCoq Compile -ext "_cps" sha. *)
(* CertiCoq Compile -direct demo1. *)
(* CertiCoq Compile -O 2 -ext "_cps_opt" demo1. *)
(* CertiCoq Compile -direct -O 2 -ext "_opt" demo1. *)

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).
Definition demo2 := List.map negb [true; false; true].
Definition demo3 := andb. 

(* CertiCoq Show IR -debug -direct demo1. *)

CertiCoq Compile -ext "_cps" demo1.
CertiCoq Compile -direct demo1.
CertiCoq Compile -O 2 -ext "_cps_opt" demo1.
CertiCoq Compile -direct -O 2 -ext "_opt" demo1.

CertiCoq Compile -ext "_cps" demo2.
CertiCoq Compile -direct demo2.
CertiCoq Compile -O 2 -ext "_cps_opt" demo2.
CertiCoq Compile -direct -O 2 -ext "_opt" demo2.

CertiCoq Compile -ext "_cps" demo3.
CertiCoq Compile -direct demo3.
CertiCoq Compile -O 2 -ext "_cps_opt" demo3.
CertiCoq Compile -direct -O 2 -ext "_opt" demo3.

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* CertiCoq Show IR -debug -direct list_sum. *)
(* CertiCoq Show IR -debug -O 2 -ext "_cps_opt" list_sum. *)

CertiCoq Compile -ext "_cps" list_sum.
CertiCoq Compile -direct list_sum.
CertiCoq Compile -O 2 -ext "_cps_opt" list_sum.
CertiCoq Compile -direct -O 2 -ext "_opt" list_sum.

Definition vs_easy :=
  match vs.main with
  | Valid => true
  | _ => false
  end.

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

CertiCoq Compile -direct -time vs_easy.
CertiCoq Compile -ext "_cps" -time vs_easy.
CertiCoq Compile -O 2 -ext "_cps_opt" vs_easy.
CertiCoq Compile -direct -O 2 -ext "_opt" vs_easy.

CertiCoq Compile -ext "_cps" vs_hard.
CertiCoq Compile -direct vs_hard.
CertiCoq Compile -O 2 -ext "_cps_opt" vs_hard.
CertiCoq Compile -direct -O 2 -ext "_opt" vs_hard.

Definition binom := Binom.main.

CertiCoq Compile -ext "_cps" binom. (* returns nat *)
CertiCoq Compile -direct binom.  (* returns nat *)
CertiCoq Compile -O 2 -ext "_cps_opt" binom.
CertiCoq Compile -direct -O 2 -ext "_opt" binom.

Definition color := Color.main.

CertiCoq Compile -ext "_cps" color.
CertiCoq Compile -direct color.
CertiCoq Compile -O 2 -ext "_cps_opt" color.
CertiCoq Compile -direct -O 2 -ext "_opt" color.

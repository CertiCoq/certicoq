Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.


(* Definition vs_easy := *)
(*   match vs.main with *)
(*   | Valid => true *)
(*   | _ => false *)
(*   end. *)

(* CertiCoq Show IR -debug -O 2 -ext "_cps_opt" vs_easy. *)

(* CertiCoq Show IR -debug -ext "_cps" vs_easy. *)

(* CertiCoq Show IR -debug -direct vs_easy. *)

(* CertiCoq Show IR -debug -direct -O 2 -ext "_opt" vs_easy. *)

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).
Definition demo2 := List.map negb [true; false; true].
Definition demo3 := andb. 

(* CertiCoq Show IR -debug -direct demo1. *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* CertiCoq Show IR -debug -direct list_sum. *)
(* CertiCoq Show IR -debug -direct -O 2 -ext "_opt" list_sum. *)

Eval compute in "Compiling demo1".

CertiCoq Compile -ext "_cps" demo1.
CertiCoq Compile -direct demo1.
CertiCoq Compile -O 2 -ext "_cps_opt" demo1.
CertiCoq Compile -direct -O 2 -ext "_opt" demo1.

Eval compute in "Compiling demo2".

CertiCoq Compile -ext "_cps" demo2.
CertiCoq Compile -direct demo2.
CertiCoq Compile -O 2 -ext "_cps_opt" demo2.
CertiCoq Compile -direct -O 2 -ext "_opt" demo2.

Eval compute in "Compiling demo3".

CertiCoq Compile -ext "_cps" demo3.
CertiCoq Compile -direct demo3.
CertiCoq Compile -O 2 -ext "_cps_opt" demo3.
CertiCoq Compile -direct -O 2 -ext "_opt" demo3.

Eval compute in "Compiling list_sum".

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

Eval compute in "Compiling vs_easy".

CertiCoq Compile -direct -time_anf vs_easy.
CertiCoq Compile -ext "_cps" -time_anf vs_easy.
CertiCoq Compile -O 2 -ext "_cps_opt" vs_easy.
CertiCoq Compile -direct -O 2 -ext "_opt" vs_easy.

Eval compute in "Compiling vs_hard".

CertiCoq Compile -ext "_cps" vs_hard.
CertiCoq Compile -direct vs_hard.
CertiCoq Compile -O 2 -ext "_cps_opt" vs_hard.
CertiCoq Compile -direct -O 2 -ext "_opt" vs_hard.

Definition binom := Binom.main.

Eval compute in "Compiling binom".

CertiCoq Compile -ext "_cps" binom. (* returns nat *)
CertiCoq Compile -direct binom.  (* returns nat *)
CertiCoq Compile -O 2 -ext "_cps_opt" binom.
CertiCoq Compile -direct -O 2 -ext "_opt" binom.

Definition color := Color.main.

Eval compute in "Compiling color".

CertiCoq Compile -time -ext "_cps" color.
CertiCoq Compile -time -direct color.
CertiCoq Compile -time -O 2 -ext "_cps_opt" color.
CertiCoq Compile -time -direct -O 2 -ext "_opt" color.


(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.".

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

Eval compute in "Compiling sha".

CertiCoq Compile -ext "_cps" sha.
CertiCoq Compile -direct sha.
CertiCoq Compile -O 2 -ext "_cps_opt" sha.
CertiCoq Compile -direct -O 2 -ext "_opt" sha.

Eval compute in "Compiling sha_fast".

CertiCoq Compile -ext "_cps" sha_fast.
CertiCoq Compile -direct sha_fast.
CertiCoq Compile -O 2 -ext "_cps_opt" sha_fast.
CertiCoq Compile -direct -O 2 -ext "_opt" sha_fast.

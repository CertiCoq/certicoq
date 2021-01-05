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

(* Demo 1 *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

(* Demo 3 *)

Definition demo3 := andb.

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* Veristar *)

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

(* Binom *)

Definition binom := Binom.main.

(* Color *)
Definition color := Color.main.

(* Sha *)

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.".

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

(* CertiCoq Show IR -time_anf binom. *)
(* CertiCoq Show IR -time_anf -O 1 -ext "_opt" binom. *)
(* CertiCoq Show IR -config 2 -direct -time_anf -ext "_inl" vs_easy. *)
(* CertiCoq Show IR -config 2 -direct -O 1 -time_anf -ext "_opt_no_inl" vs_easy. *)

Eval compute in "Compiling demo1".

CertiCoq Compile -dev 1 -direct -time_anf vs_easy.

CertiCoq Compile -dev 1 -ext "_cps" demo1.
CertiCoq Compile -dev 1 -direct demo1.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" demo1.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" demo1.

Eval compute in "Compiling demo2".

CertiCoq Compile -dev 1 -ext "_cps" demo2.
CertiCoq Compile -dev 1 -direct demo2.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" demo2.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" demo2.

Eval compute in "Compiling demo3".

CertiCoq Compile -dev 1 -ext "_cps" demo3.
CertiCoq Compile -dev 1 -direct demo3.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" demo3.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" demo3.

Eval compute in "Compiling list_sum".

CertiCoq Compile -dev 1 -ext "_cps" list_sum.
CertiCoq Compile -dev 1 -direct list_sum.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" list_sum.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" list_sum.


Eval compute in "Compiling vs_easy".

CertiCoq Compile -dev 1 -direct -time_anf vs_easy.
CertiCoq Compile -dev 1 -ext "_cps" -time_anf vs_easy.
CertiCoq Compile -dev 1 -time -O 1 -ext "_cps_opt" vs_easy.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" vs_easy.

Eval compute in "Compiling vs_hard".

CertiCoq Compile -dev 1 -ext "_cps" vs_hard.
CertiCoq Compile -dev 1 -direct vs_hard.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" vs_hard.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" vs_hard.


Eval compute in "Compiling binom".

CertiCoq Compile -dev 1 -ext "_cps" binom.
CertiCoq Compile -dev 1 -direct binom.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" binom.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" binom.


Eval compute in "Compiling color".

CertiCoq Compile -dev 1 -time -ext "_cps" color.
CertiCoq Compile -dev 1 -time -direct color.
CertiCoq Compile -dev 1 -time -O 1 -ext "_cps_opt" color.
CertiCoq Compile -dev 1 -time -direct -O 1 -ext "_opt" color.

(* Don't compile slow sha *)
(* Eval compute in "Compiling sha". *)

(* CertiCoq Compile -dev 1 -ext "_cps" sha. *)
(* CertiCoq Compile -dev 1 -direct sha. *)
(* CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" sha. *)
(* CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" sha. *)

Eval compute in "Compiling sha_fast".

CertiCoq Compile -dev 1 -ext "_cps" sha_fast.
CertiCoq Compile -dev 1 -direct sha_fast.
CertiCoq Compile -dev 1 -O 1 -ext "_cps_opt" sha_fast.
CertiCoq Compile -dev 1 -direct -O 1 -ext "_opt" sha_fast.

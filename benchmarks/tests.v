Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

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
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0 =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment example_ent in
       loop n res
     end) 100  Valid.

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

Goal True. idtac "---------- all manual ----------". Abort.
Goal True. idtac "vs_easy:". Abort.
CertiCoq Compile -O 0 -time -dev 1 vs_easy.
Goal True. idtac "vs_hard:". Abort.
CertiCoq Compile -O 0 -time -dev 1 vs_hard.
Goal True. idtac "binom:". Abort.
CertiCoq Compile -O 0 -time -dev 1 binom.
Goal True. idtac "color:". Abort.
CertiCoq Compile -O 0 -time -dev 1 color.
Goal True. idtac "sha:". Abort.
CertiCoq Compile -O 0 -time -dev 1 sha.

Goal True. idtac "---------- shrink proto ----------". Abort.
Goal True. idtac "vs_easy:". Abort.
CertiCoq Compile -O 0 -time -dev 2 vs_easy.
Goal True. idtac "vs_hard:". Abort.
CertiCoq Compile -O 0 -time -dev 2 vs_hard.
Goal True. idtac "binom:". Abort.
CertiCoq Compile -O 0 -time -dev 2 binom.
Goal True. idtac "color:". Abort.
CertiCoq Compile -O 0 -time -dev 2 color.
Goal True. idtac "sha:". Abort.
CertiCoq Compile -O 0 -time -dev 2 sha.

Goal True. idtac "---------- uncurry proto ----------". Abort.
Goal True. idtac "vs_easy:". Abort.
CertiCoq Compile -O 0 -time -dev 0 vs_easy.
Goal True. idtac "vs_hard:". Abort.
CertiCoq Compile -O 0 -time -dev 0 vs_hard.
Goal True. idtac "binom:". Abort.
CertiCoq Compile -O 0 -time -dev 0 binom.
Goal True. idtac "color:". Abort.
CertiCoq Compile -O 0 -time -dev 0 color.
Goal True. idtac "sha:". Abort.
CertiCoq Compile -O 0 -time -dev 0 sha.

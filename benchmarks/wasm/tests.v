Require Import Arith List String Uint63 BinNat.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import CertiCoq.Benchmarks.lib.coind.
Require Import CertiCoq.Benchmarks.lib.coqprime.
Require Import CertiCoq.Benchmarks.lib.BernsteinYangTermination.
Require Import CertiCoq.Benchmarks.lib.stack_machine.

From MetaCoq.Utils Require Import bytestring MCString.
From CertiCoq.Plugin Require Import CertiCoq.

Open Scope bs.

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

(* Lazy factorial. Needs coinductive types *)

Definition lazy_factorial := string_of_Z (coind.lfact 150).

(* Sha *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%string.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).


(*******************************************************************)
(* from https://github.com/AU-COBRA/coq-rust-extraction/blob/master/tests/theories/InternalFix.v *)

Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
            match m with
            | O => ack p 1
            | S q => ack p (ackn q)
            end
          in ackn m
  end.
Definition ack_3_9 := ack 3 9.

Fixpoint even n :=
  match n with
  | O => true
  | S m => odd m
  end
  with odd n :=
    match n with
    | O => false
    | S k => even k
    end.
Definition even_10000 := even 10000.

Definition bernstein_yang := W 10.

Eval compute in "Compiling ack".
CertiCoq Compile Wasm ack_3_9.

Eval compute in "Compiling even_10000".
CertiCoq Compile Wasm even_10000.

Eval compute in "Bernstein yang termination".
CertiCoq Compile Wasm bernstein_yang.
(* bernstein_yang only for compilation, runs out of memory when executing binary *)

(*******************************************************************)
Eval compute in "Compiling demo1".
CertiCoq Compile Wasm demo1.

(* CertiCoq Compile -O 0 -cps -ext "_cps" demo1. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo1. *)
(* CertiCoq Generate Glue -file "glue_demo1" [ list, bool ]. *)

Eval compute in "Compiling demo2".
CertiCoq Compile Wasm demo2.

(* CertiCoq Compile -O 0 -cps -ext "_cps" demo2. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo2. *)
(* CertiCoq Generate Glue -file "glue_demo2" [ list, bool ]. *)

(*
Eval compute in "Compiling demo3".

CertiCoq Compile Wasm -cps -debug demo3.
(* CertiCoq Compile -O 0 -cps -ext "_cps" demo3. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo3. *)
*)
(* CertiCoq Generate Glue -file "glue_demo3" [ list, bool ]. *)

Eval compute in "Compiling list_sum".
CertiCoq Compile Wasm list_sum.
(* CertiCoq Compile -O 0 -cps -ext "_cps" list_sum. *)
(* CertiCoq Compile -cps -ext "_cps_opt" list_sum. *)
(* CertiCoq Generate Glue -file "glue_list_sum" [ nat ]. *)

(* Eval compute in "Compiling list_sum_primitive".
CertiCoq Compile Wasm -debug list_sum_primitive. *)
(* Eval compute in "Compiling lazy factorial (using unsafe passes)". *)

(* CertiCoq Compile -unsafe-erasure -O 1 lazy_factorial. *)
(* CertiCoq Compile -unsafe-erasure -ext "_opt" lazy_factorial. *)
(* CertiCoq Compile -unsafe-erasure -args 1000 -config 9 -O 1 -ext "_opt_ll" lazy_factorial. *) 
(* (1* CertiCoq Compile -O 0 -cps -ext "_cps" demo1. *1) *)
(* (1* CertiCoq Compile -cps -ext "_cps_opt" demo1. *1) *)
(* CertiCoq Generate Glue -file "glue_lazy_factorial" [ ]. *)

Eval compute in "Compiling vs_easy".
CertiCoq Compile Wasm vs_easy.
(* CertiCoq Compile Wasm -cps -time -debug vs_easy. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" -time_anf vs_easy. *)
(* CertiCoq Compile -time -cps -ext "_cps_opt" vs_easy. *)
(* CertiCoq Generate Glue -file "glue_vs_easy" [ list, bool, vs.space_atom, vs.clause ]. *)

Eval compute in "Compiling vs_hard".
CertiCoq Compile Wasm vs_hard.
(* CertiCoq Compile Wasm -cps -time -debug vs_hard. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" vs_hard. *)
(* CertiCoq Compile -cps -ext "_cps_opt" vs_hard. *)
(* CertiCoq Generate Glue -file "glue_vs_hard" [ list, bool ]. *)


Eval compute in "Compiling binom".
CertiCoq Compile Wasm binom.
(* CertiCoq Show IR -file "binom" binom. *)
(* CertiCoq Compile Wasm -cps -time -debug binom. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" binom. *)
(* CertiCoq Compile -cps -ext "_cps_opt" binom. *)
(* CertiCoq Generate Glue -file "glue_binom" [ nat ]. *)


Eval compute in "Compiling color".
CertiCoq Compile Wasm color.

(* CertiCoq Compile -O 0 -time -cps -ext "_cps" color. *)
(* CertiCoq Compile -time -cps -ext "_cps_opt" color. *)
(* CertiCoq Generate Glue -file "glue_color" [ prod, Z ]. *)

(* Don't compile slow sha *)
(* Eval compute in "Compiling sha". *)

(* CertiCoq Compile -cps -ext "_cps" sha. *)
(* CertiCoq Compile sha. *)
(* CertiCoq Compile -O 1 -cps -ext "_cps_opt" sha. *)
(* CertiCoq Compile -O 1 -ext "_opt" sha. *)
(* CertiCoq Generate Glue -file "glue_sha" [ ]. *)

Eval compute in "Compiling sha_fast".
CertiCoq Compile Wasm sha_fast.
(* CertiCoq Compile Wasm -cps -time -debug sha_fast. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" sha_fast. *)
(* CertiCoq Compile -cps -ext "_cps_opt" sha_fast. *)
(* CertiCoq Generate Glue -file "glue_sha_fast" [ ]. *)

(* Eval compute in "Compiling parse_wasm_module". *)
(* CertiCoq Compile Wasm -time -debug test_module. *)

Definition sm_gauss_nat :=
  let n := 1000 in
  match (s_execute' (gauss_sum_sintrs_nat n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)
  | _ => None
  end.

Definition sm_gauss_N :=
  let n := 1000%N in
  match (s_execute' (gauss_sum_sintrs_N n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)%N
  | _ => None
  end.

Definition sm_gauss_PrimInt :=
  let n := 1000%uint63 in
  match (s_execute' (gauss_sum_sintrs_PrimInt n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)%uint63
  | _ => None
  end.

Eval compute in "Compiling sm_gauss".
CertiCoq Compile Wasm sm_gauss_nat.
CertiCoq Compile Wasm sm_gauss_N.
CertiCoq Compile Wasm sm_gauss_PrimInt.

Definition coqprime := check_cert3.
Eval compute in "Compiling coqprime".
CertiCoq Compile Wasm coqprime.

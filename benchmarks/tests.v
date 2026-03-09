From Stdlib Require Import Arith List String.
Require Import CertiRocq.Benchmarks.lib.vs.
Require Import CertiRocq.Benchmarks.lib.Binom.
Require Import CertiRocq.Benchmarks.lib.Color.
Require Import CertiRocq.Benchmarks.lib.sha256.
Require Import CertiRocq.Benchmarks.lib.coind.
From MetaRocq.Utils Require Import bytestring MRString.
From CertiRocq.Plugin Require Import CertiRocq.

Definition foo := 0.

Open Scope bs.

Import ListNotations.
Import VeriStar.

CertiRocq -help.


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

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%string.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

Eval compute in "Compiling demo1".

CertiRocq Compile -O 0 demo1.
CertiRocq Compile -ext "_opt" demo1.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo1.
(* CertiRocq Compile -O 0 -cps -ext "_cps" demo1. *)
(* CertiRocq Compile -cps -ext "_cps_opt" demo1. *)
CertiRocq Generate Glue -file "glue_demo1" [ list, bool ].

Eval compute in "Compiling demo2".

CertiRocq Compile -O 0 demo2.
CertiRocq Compile -ext "_opt" demo2.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo2.
(* CertiRocq Compile -O 0 -cps -ext "_cps" demo2. *)
(* CertiRocq Compile -cps -ext "_cps_opt" demo2. *)
CertiRocq Generate Glue -file "glue_demo2" [ list, bool ].

Eval compute in "Compiling demo3".

CertiRocq Compile -O 0 demo3.
CertiRocq Compile -ext "_opt" demo3.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo3.
(* CertiRocq Compile -O 0 -cps -ext "_cps" demo3. *)
(* CertiRocq Compile -cps -ext "_cps_opt" demo3. *)
CertiRocq Generate Glue -file "glue_demo3" [ list, bool ].

Eval compute in "Compiling list_sum".

CertiRocq Compile -O 0 list_sum.
CertiRocq Compile -ext "_opt" list_sum.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" list_sum.
(* CertiRocq Compile -O 0 -cps -ext "_cps" list_sum. *)
(* CertiRocq Compile -cps -ext "_cps_opt" list_sum. *)
CertiRocq Generate Glue -file "glue_list_sum" [ nat ].

Eval compute in "Compiling lazy factorial (using unsafe passes)".

CertiRocq Compile -unsafe-erasure -O 1 lazy_factorial.
CertiRocq Compile -unsafe-erasure -ext "_opt" lazy_factorial.
CertiRocq Compile -unsafe-erasure -args 1000 -config 9 -O 1 -ext "_opt_ll" lazy_factorial.
(* CertiRocq Compile -O 0 -cps -ext "_cps" demo1. *)
(* CertiRocq Compile -cps -ext "_cps_opt" demo1. *)
CertiRocq Generate Glue -file "glue_lazy_factorial" [ ].

Eval compute in "Compiling vs_easy".

CertiRocq Compile -O 0 -time_anf vs_easy.
CertiRocq Compile -ext "_opt" vs_easy.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" vs_easy.
(* CertiRocq Compile -O 0 -cps -ext "_cps" -time_anf vs_easy. *)
(* CertiRocq Compile -time -cps -ext "_cps_opt" vs_easy. *)
CertiRocq Generate Glue -file "glue_vs_easy" [ list, bool, vs.space_atom, vs.clause ].

Eval compute in "Compiling vs_hard".

CertiRocq Compile -O 0 vs_hard.
CertiRocq Compile -ext "_opt" vs_hard.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" vs_hard.
(* CertiRocq Compile -O 0 -cps -ext "_cps" vs_hard. *)
(* CertiRocq Compile -cps -ext "_cps_opt" vs_hard. *)
CertiRocq Generate Glue -file "glue_vs_hard" [ list, bool ].


Eval compute in "Compiling binom".

CertiRocq Compile -O 0 binom.
CertiRocq Compile -ext "_opt" binom.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" binom.
(* CertiRocq Compile -O 0 -cps -ext "_cps" binom. *)
(* CertiRocq Compile -cps -ext "_cps_opt" binom. *)
CertiRocq Generate Glue -file "glue_binom" [ nat ].


Eval compute in "Compiling color".
From Stdlib Require Import ZArith.

CertiRocq Compile -O 0 -time color.
CertiRocq Compile -time -ext "_opt" color.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" color.
(* CertiRocq Compile -O 0 -time -cps -ext "_cps" color. *)
(* CertiRocq Compile -time -cps -ext "_cps_opt" color. *)
CertiRocq Generate Glue -file "glue_color" [ prod, Z ].

(* Don't compile slow sha *)
(* Eval compute in "Compiling sha". *)

(* CertiRocq Compile -cps -ext "_cps" sha. *)
(* CertiRocq Compile sha. *)
(* CertiRocq Compile -O 1 -cps -ext "_cps_opt" sha. *)
(* CertiRocq Compile -O 1 -ext "_opt" sha. *)
(* CertiRocq Generate Glue -file "glue_sha" [ ]. *)

Eval compute in "Compiling sha_fast".

CertiRocq Compile -O 0 sha_fast.
CertiRocq Compile -ext "_opt" sha_fast.
CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" sha_fast.
(* CertiRocq Compile -O 0 -cps -ext "_cps" sha_fast. *)
(* CertiRocq Compile -cps -ext "_cps_opt" sha_fast. *)
CertiRocq Generate Glue -file "glue_sha_fast" [ ].

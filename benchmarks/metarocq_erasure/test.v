From MetaRocq.Template Require Import All Loader.
From CertiRocq.Benchmarks.metacoq_erasure Require Import Loader.
(* Set MetaRocq Debug. *)
Set MetaRocq Timing.
From Stdlib Require Import List.
Import ListNotations.

(* CertiRocq Erase (List.map negb [true; false]). *)

From MetaRocq.ErasurePlugin Require Import Erasure.
CertiRocq Erase @erase_and_print_template_program.

(* From MetaRocq.SafeChecker Require Import PCUICSafeChecker. *)
(* CertiRocq Erase @typecheck_program. *)

(*
From Stdlib Require Import Arith List String.
Require Import CertiRocq.Benchmarks.lib.vs.
Require Import CertiRocq.Benchmarks.lib.Binom.
Require Import CertiRocq.Benchmarks.lib.Color.
Require Import CertiRocq.Benchmarks.lib.sha256.

Import ListNotations.
Import VeriStar.

(* Demo 1 *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

CertiRocq Erase demo1.

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

CertiRocq Erase demo2.

(* Demo 3 *)

Definition demo3 := andb.

CertiRocq Erase demo3.

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

CertiRocq Erase list_sum.

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

Time CertiRocq Erase vs_easy.

 (* (clause_list2set (pure_clauses (map order_eqv_clause (cnf example_ent)))). *)

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

Time CertiRocq Erase vs_hard.

(* Binom *)

Definition binom := Binom.main.

CertiRocq Erase binom.

(* Color *)
Definition color := Color.main.

CertiRocq Erase color.
(* Sha *)

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%bs.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes (String.to_string test)).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes (String.to_string test)).

CertiRocq Erase sha_fast.
*)

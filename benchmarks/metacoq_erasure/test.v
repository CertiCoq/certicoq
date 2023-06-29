From MetaCoq.Template Require Import All Loader.
From CertiCoq.Benchmarks.metacoq_erasure Require Import Loader.
(* Set MetaCoq Debug. *)
Set MetaCoq Timing.
From Coq Require Import List.
Import ListNotations.

(* CertiCoq Erase (List.map negb [true; false]). *)

From MetaCoq.ErasurePlugin Require Import Erasure.
CertiCoq Erase @erase_and_print_template_program.

(* From MetaCoq.SafeChecker Require Import PCUICSafeChecker. *)
(* CertiCoq Erase @typecheck_program. *)

(*
Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

Import ListNotations.
Import VeriStar.
 
(* Demo 1 *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

CertiCoq Erase demo1.

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

CertiCoq Erase demo2.

(* Demo 3 *)

Definition demo3 := andb.

CertiCoq Erase demo3.

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

CertiCoq Erase list_sum.

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

Time CertiCoq Erase vs_easy.

 (* (clause_list2set (pure_clauses (map order_eqv_clause (cnf example_ent)))). *)

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

Time CertiCoq Erase vs_hard.

(* Binom *)

Definition binom := Binom.main.

CertiCoq Erase binom.

(* Color *)
Definition color := Color.main.

CertiCoq Erase color.
(* Sha *)

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%bs.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes (String.to_string test)).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes (String.to_string test)).

CertiCoq Erase sha_fast.
*)

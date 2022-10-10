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


(* CertiCoq Show IR -time_anf vs_easy. *)
(* CertiCoq Show IR -time_anf -O 1 -ext "_optc0" vs_easy. *)
(* CertiCoq Show IR -config 2 -time_anf -ext "_inl" vs_easy. *)
(* CertiCoq Show IR -config 2 -O 1 -time_anf -ext "_opt_no_inl" vs_easy. *)

Eval compute in "Compiling demo1".

CertiCoq Compile -O 1 -ext "_cps_opt" demo1.
CertiCoq Compile -O 1 -ext "_opt" demo1.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" demo1.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" demo1.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" demo1.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" demo1.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" demo1.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" demo1.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" demo1.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" demo1.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" demo1.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" demo1.

Eval compute in "Compiling demo2".

CertiCoq Compile -O 1 -ext "_cps_opt" demo2.
CertiCoq Compile -O 1 -ext "_opt" demo2.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" demo2.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" demo2.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" demo2.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" demo2.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" demo2.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" demo2.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" demo2.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" demo2.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" demo2.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" demo2.

Eval compute in "Compiling list_sum".

CertiCoq Compile -O 1 -ext "_cps_opt" list_sum.
CertiCoq Compile -O 1 -ext "_opt" list_sum.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" list_sum.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" list_sum.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" list_sum.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" list_sum.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" list_sum.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" list_sum.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" list_sum.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" list_sum.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" list_sum.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" list_sum.


Eval compute in "Compiling vs_easy".

CertiCoq Compile -O 1 -ext "_cps_opt" vs_easy.
CertiCoq Compile -O 1 -ext "_opt" vs_easy.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" vs_easy.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" vs_easy.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" vs_easy.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" vs_easy.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" vs_easy.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" vs_easy.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" vs_easy.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" vs_easy.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" vs_easy.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" vs_easy.

Eval compute in "Compiling vs_hard".

CertiCoq Compile -O 1 -ext "_cps_opt" vs_hard.
CertiCoq Compile -O 1 -ext "_opt" vs_hard.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" vs_hard.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" vs_hard.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" vs_hard.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" vs_hard.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" vs_hard.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" vs_hard.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" vs_hard.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" vs_hard.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" vs_hard.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" vs_hard.


Eval compute in "Compiling binom".

CertiCoq Compile -O 1 -ext "_cps_opt" binom.
CertiCoq Compile -O 1 -ext "_opt" binom.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" binom.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" binom.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" binom.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" binom.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" binom.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" binom.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" binom.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" binom.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" binom.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" binom.

Eval compute in "Compiling color".

CertiCoq Compile -O 1 -ext "_cps_opt" color.
CertiCoq Compile -O 1 -ext "_opt" color.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" color.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" color.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" color.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" color.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" color.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" color.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" color.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" color.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" color.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" color.

Eval compute in "Compiling sha_fast".

CertiCoq Compile -O 1 -ext "_cps_opt" sha_fast.
CertiCoq Compile -O 1 -ext "_opt" sha_fast.

CertiCoq Compile -config 1 -O 1 -ext "_cps_opt1" sha_fast.
CertiCoq Compile -config 1 -O 1 -ext "_opt1" sha_fast.

CertiCoq Compile -config 2 -O 1 -ext "_cps_opt2" sha_fast.
CertiCoq Compile -config 2 -O 1 -ext "_opt2" sha_fast.

CertiCoq Compile -config 3 -O 1 -ext "_cps_opt3" sha_fast.
CertiCoq Compile -config 3 -O 1 -ext "_opt3" sha_fast.

CertiCoq Compile -config 4 -O 1 -ext "_cps_opt4" sha_fast.
CertiCoq Compile -config 4 -O 1 -ext "_opt4" sha_fast.

CertiCoq Compile -config 5 -O 1 -ext "_cps_opt5" sha_fast.
CertiCoq Compile -config 5 -O 1 -ext "_opt5" sha_fast.


(* OLD 

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S n' => odd n'
  end
with
odd (n : nat) : bool :=
  let del (x : nat) := x in 
  match n with
  | 0 => false
  | S n' => even n'
  end.


Definition filter_odd := List.app (filter even (seq 0 2)) (filter odd (seq 0 2)).

CertiCoq Show IR -anf -debug filter_odd. 
CertiCoq Compile -ext "_cps" filter_odd.
CertiCoq Compile -o1 -ext "_cps_opt" filter_odd.
CertiCoq Compile -anf filter_odd.
CertiCoq Compile -anf -o1 -ext "_opt" filter_odd.

Definition repeat {A} (x : A) (n : nat) : list A :=
  (fix rep (x : A) (n : nat) acc :=
     match n with
     | 0 => acc
     | S k => rep x k (x :: acc)
     end) x n [].


Definition list_sum := List.fold_left plus (repeat 10 (100)) 0.

CertiCoq Compile -ext "_cps" list_sum.
CertiCoq Compile -o1 -ext "_cps_opt" list_sum.
CertiCoq Compile -anf list_sum.
CertiCoq Compile -anf -o1 -ext "_opt" list_sum.

Fixpoint loop_add n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop_add n f
  end.

(* Problem: if function is not closed it will end up in the closure of the wrapper.
   This should not happen because its environment is a sub-environment of
   its own environment. But that means that it should be created on the spot.
   Not sure what is better.
   ==> Then maybe lifted and wrappers should be defined in the same rec.
   So that the big environment is shared when it is needed
 *)

Definition clos_loop (u : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | x::xs =>
       (* this gets inlined *)
       let clos z := k1 + k2 + k3 + z in
       (clos x) + list_add k1 k2 k3 xs
     end) 0 0 0 (List.repeat 0 1).

(* Definition clos_loop (u : unit) : nat := *)
(*   (fix list_add k1 k2 k3 l : nat := *)
(*      match l with *)
(*      | [] => 0 *)
(*      | x::xs => *)
(*        let clos z := x + k1 + k2 + k3 in *)
(*        (clos x) + list_add k1 k2 k3 xs *)
(*      end) 0 0 0 (List.repeat 0 (100*1000)). *)

Definition clos := loop_add 1 clos_loop.

CertiCoq Compile -ext "_cps" clos.
CertiCoq Compile -o1 -ext "_cps_opt" clos.
CertiCoq Compile -anf clos.
CertiCoq Compile -anf -o1 -ext "_opt" clos.
(* CertiCoq Show IR -debug clos. *)

(* CertiCoq Show IR -anf -debug clos. *)
(* CertiCoq Show IR -anf -debug -o1 -ext "_opt" clos. *)


Definition addxy (x y w : nat) (l : list nat) := 
  let f := (fix aux l :=
     match l with
     | [] => []
     | z :: zs => (z + x + y + w) :: aux zs
     end) in
  f l. 

Definition rec_clos := addxy 1 2 3 (List.repeat 0 (100*500)).

CertiCoq Compile -ext "_cps" rec_clos.
CertiCoq Compile -o1 -ext "_cps_opt" rec_clos.
CertiCoq Compile -anf rec_clos.
CertiCoq Compile -anf -o1 -ext "_opt" rec_clos.


Definition intxy (x y w : nat) (l : list nat):= 
  let f := (fix aux l acc :=
     match l with
     | [] => acc  
     | z :: zs => aux zs (z :: x :: y :: w :: acc)
     end) in
  f l [].

Definition intxy' (x y w : nat) (l : list nat) := 
  let f := (fix aux l :=
     match l with
     | [] => []  
     | z :: zs => z :: x :: y :: w :: aux zs
     end) in
  f l.

Definition rec_clos2 := intxy 1 2 3 (repeat 0 (100*500)).

CertiCoq Compile -ext "_cps" rec_clos2.
CertiCoq Compile -o1 -ext "_cps_opt" rec_clos2.
CertiCoq Compile -anf rec_clos2.
CertiCoq Compile -anf -o1 -ext "_opt" rec_clos2.
CertiCoq Show IR -anf rec_clos2.
CertiCoq Show IR -anf -o1 -ext "_opt" rec_clos2.


(* Fixpoint ack (m : nat) := *)
(*   fix aux (n : nat) := *)
(*     match m with *)
(*     | 0 => n + 1 *)
(*     | S m => *)
(*       match n with *)
(*       | 0 => ack m 1 *)
(*       | S n => ack m (aux n) *)
(*       end *)
(*     end. *)

(* Fixpoint merge (l1 l2:list nat) acc : list nat := *)
(*   match l1, l2 with *)
(*   | nil, _ => l2 *)
(*   | _, nil => l1 *)
(*   | x1::l1', x2::l2' => *)
(*     if leb x1 x2 then x1 :: merge l1' l2 *)
(*     else *)
(*       x2 :: (fix merge_aux (l2:list nat) := *)
(*                match l2 with *)
(*                | nil => l1 *)
(*                | x2::l2' => *)
(*                  if leb x1 x2 then x1::merge l1' l2 *)
(*                  else x2:: merge_aux l2' *)
(*                end) l2' *)
(*          end. *)




(* TODO: Eventually move somewhere else and also add the option to print help.
Valid options:
-anf    : to use direct-style compilation
-time   : to time phases
-o1     : to use optimizing pipeline
-debug  : to print debug messages 
-args X : to use X arguments in the C generated code (+1 for the thread_info)


To print the backend IR (aka LambdaANF) you can use the command
CertiCoq Show IR <global_id>.
*)

(* 
Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).
Definition demo2 := List.map negb [true; false; true].
Definition demo3 := andb. 
 
CertiCoq Compile -ext "_cps" demo1.
CertiCoq Compile -anf demo1.
CertiCoq Compile -anf -o1 -ext "_opt" demo1.

CertiCoq Compile -ext "_cps" demo2.
CertiCoq Compile -anf demo2.
CertiCoq Compile -anf -o1 -ext "_opt" demo2.

(* Also works for CPS, when choosing another number of arguments, e.g. -args 1 *)
CertiCoq Compile -ext "_cps" demo3.
CertiCoq Compile -anf demo3.
CertiCoq Compile -anf -o1 -ext "_opt" demo3.

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

CertiCoq Compile -ext "_cps" list_sum.
CertiCoq Compile -anf list_sum.
CertiCoq Compile -anf -o1 -ext "_opt" list_sum.


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

CertiCoq Compile -ext "_cps" vs_easy.
CertiCoq Compile -anf vs_easy.
CertiCoq Compile -anf -o1 -ext "_opt" vs_easy.

(* Zoe: Compiling with the CPS pipeline takes much longer for vs_easy.
   The overhead seems to come from the C translation: (maybe has to do with dbg/error messages?)

Timing for CPS:
Debug: Time elapsed in L1g:  8.835582
Debug: Time elapsed in LambdaBoxMut:  0.000454
Debug: Time elapsed in LambdaBoxMut_eta:  0.000620
Debug: Time elapsed in LambdaBoxLocal:  0.014821
Debug: Time elapsed in LambdaBoxLocal_2:  0.003420
Debug: Time elapsed in LambdaBoxLocal_5:  0.000780
Debug: Time elapsed in L5:  0.005000
Debug: Time elapsed in LambdaANF CPS:  0.105993
Debug: Time elapsed in LambdaANF Pipeline:  8.532707
Debug: Time elapsed in Codegen:  87.985509

Timing for ANF:
Debug: Time elapsed in L1g:  8.543669
Debug: Time elapsed in LambdaBoxMut:  0.000457
Debug: Time elapsed in LambdaBoxMut_eta:  0.000640
Debug: Time elapsed in LambdaBoxLocal:  0.013329
Debug: Time elapsed in LambdaANF ANF:  0.020384
Debug: Time elapsed in LambdaANF Pipeline:  0.148308
Debug: Time elapsed in Codegen:  2.394216 *)

CertiCoq Compile -ext "_cps" vs_hard.
CertiCoq Compile -anf vs_hard.
CertiCoq Compile -anf -o1 -ext "_opt" vs_hard.

Definition binom := Binom.main.

CertiCoq Compile -ext "_cps" binom. (* returns nat *)
CertiCoq Compile -anf binom.  (* returns nat *)
CertiCoq Compile -anf -o1 -ext "_opt" binom.  (* returns nat *)

Definition color := Color.main.

CertiCoq Compile -ext "_cps" color.
CertiCoq Compile -anf color.
CertiCoq Compile -anf -o1 -ext "_opt" color.
*)
*)

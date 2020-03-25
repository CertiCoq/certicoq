Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
(* Require Import CertiCoq.Benchmarks.lib.sha256. *)

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

CertiCoq -help.

Fixpoint loop_add n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop_add n f
  end.


(* XXX lambda lifting is lifting the same argument more than once *)
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


Definition addxy (x y : nat) (l : list nat) := 
  let f := (fix aux l :=
     match l with
     | [] => []
     | z :: zs => (z + x + y) :: aux zs
     end) in
  f l. 

Definition rec_clos := addxy 1 2 (List.repeat 0 (100*500)).

CertiCoq Compile -ext "_cps" rec_clos.
CertiCoq Compile -o1 -ext "_cps_opt" rec_clos.
CertiCoq Compile -anf rec_clos.
CertiCoq Compile -anf -o1 -ext "_opt" rec_clos.



Definition intxy (x y : nat) (l : list nat):= 
  let f := (fix aux l acc :=
     match l with
     | [] => acc  
     | z :: zs => aux zs (z :: x :: y :: acc)
     end) in
  f l [].

Definition rec_clos2 := intxy 1 2 (List.repeat 0 (100*500)).

CertiCoq Compile -ext "_cps" rec_clos2.
CertiCoq Compile -o1 -args 1 -ext "_cps_opt" rec_clos2.
CertiCoq Compile -anf -args 1 rec_clos2.
CertiCoq Compile -anf -o1 -ext "_opt" rec_clos2.



(* TODO: Eventually move somewhere else and also add the option to print help.
Valid options:
-anf    : to use direct-style compilation
-time   : to time phases
-o1     : to use optimizing pipeline
-debug  : to print debug messages 
-args X : to use X arguments in the C generated code (+1 for the thread_info)


To print the backend IR (aka L6) you can use the command
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
Debug: Time elapsed in L2k:  0.000454
Debug: Time elapsed in L2k_eta:  0.000620
Debug: Time elapsed in L4:  0.014821
Debug: Time elapsed in L4_2:  0.003420
Debug: Time elapsed in L4_5:  0.000780
Debug: Time elapsed in L5:  0.005000
Debug: Time elapsed in L6 CPS:  0.105993
Debug: Time elapsed in L6 Pipeline:  8.532707
Debug: Time elapsed in L7:  87.985509

Timing for ANF:
Debug: Time elapsed in L1g:  8.543669
Debug: Time elapsed in L2k:  0.000457
Debug: Time elapsed in L2k_eta:  0.000640
Debug: Time elapsed in L4:  0.013329
Debug: Time elapsed in L6 ANF:  0.020384
Debug: Time elapsed in L6 Pipeline:  0.148308
Debug: Time elapsed in L7:  2.394216 *)

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
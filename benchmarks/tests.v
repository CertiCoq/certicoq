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
(* CertiCoq Show IR -debug -direct -O 2 -ext "_opt" list_sum. *)

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

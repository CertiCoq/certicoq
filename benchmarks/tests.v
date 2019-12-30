Require Import Arith List.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Import ListNotations.

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).

CertiCoq Compile demo1.
CertiCoq Compile ANF Opt 0 demo1.

Definition demo2 := List.map negb [true; false; true].

CertiCoq Compile demo2.
CertiCoq Compile ANF Opt 0 demo2.

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

CertiCoq Compile list_sum.
CertiCoq Compile ANF Opt 0 list_sum.

Import VeriStar.

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

CertiCoq Compile vs_easy. (* XXX this takes too long and needs investigation *)
CertiCoq Compile ANF Opt 0 vs_easy.

CertiCoq Compile vs_hard.
CertiCoq Compile ANF Opt 0 vs_hard.

CertiCoq Compile Binom.main. (* returns nat *)
CertiCoq Compile ANF Opt 0 Binom.main.  (* returns nat *)

CertiCoq Compile Color.main.
CertiCoq Compile ANF Opt 0 Color.main.



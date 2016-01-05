Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Bool.
Require Maps.
Require Recdef.
Import Nnat.


Require Import CpdtTactics.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.




Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStrippedL1" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4.
Add LoadPath "../L5_CPS" as CPS.
From CPS Require Export cpseval. 

Require Import cps.
Require Import cps_util.
Require Import shrink_cps.

Require Import L5_to_L6 closure_conversion.


Definition compile_to_L6 (ee: exceptionMonad.exception cps) : option exp :=
  match ee with
    | exceptionMonad.Ret e =>
      Some (convert_top 1%positive 1%positive 1%positive e)
    | _ => None
  end.

Print exceptionMonad.

Definition shrink_once_L6 (oe: option exp): option exp :=
  match oe with
    | Some e => Some (shrink_top e)
    | None => None
  end.

Definition closure_convert_L6 (oe: option exp): option exp :=
  match oe with
    | Some e => Some (closure_conversion e)
    | None => None
  end.

Quote Recursively Definition p0L1 := 0%nat.
Definition p0L5 := Eval compute in compile p0L1.
Definition p0L6 := compile_to_L6 p0L5.
Definition p0L6s := Eval compute in shrink_once_L6 p0L6.
Definition p0L6scc := Eval compute in closure_convert_L6 p0L6.
Print p0L6s.
(* Print p0L6scc. *)

Definition sabry (x:nat): (nat -> nat) :=
  fun (y:nat) => x.

Definition feil:nat := sabry (0%nat) (1%nat).

Quote Recursively Definition pFeilL1 := feil.
Definition pFeilL5 := Eval compute in compile pFeilL1.
Definition pFeilL6 := Eval compute in compile_to_L6 pFeilL5.
Definition pFeilL6s := Eval compute in shrink_once_L6 pFeilL6.
Definition pFeilL6ss := Eval compute in shrink_once_L6 pFeilL6s.
Definition pFeilL6sss := Eval compute in shrink_once_L6 pFeilL6ss.
Print pFeilL6s.
Print pFeilL6ss.
Print pFeilL6sss.

Fixpoint idn (n:nat) : nat := n.
Quote Recursively Definition pIdnL1 := idn.
Definition pIdnL5 := Eval compute in compile pIdnL1.
Definition pIdnL6 := Eval compute in compile_to_L6 pIdnL5.
Definition pIdnL6s := Eval compute in shrink_once_L6 pIdnL6.
Print Assumptions closure_convert_L6.
Definition pIdnL6cc := Eval compute in
      shrink_once_L6 (closure_convert_L6 pIdnL6s).
Print pIdnL6cc.
Print pIdnL6s.


Definition predn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => n end.
Quote Recursively Definition pPredL1 := predn.
Definition pPredL5 := Eval compute in compile pPredL1.
Definition pPredL6 := Eval compute in compile_to_L6 pPredL5.
Definition pPredL6s := Eval compute in shrink_once_L6 (pPredL6).
Definition pPredL6cc := Eval compute in
      (closure_convert_L6 pPredL6s).
Print pPredL6s.
Print pPredL6cc.

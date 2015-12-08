Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Bool.
Require Maps.
Require Recdef.
Import Nnat.
Require Import CpdtTactics.



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
Require Import L5_to_L6.




Definition compile_to_L6 (ee: exceptionMonad.exception cps) : option exp :=
  match ee with
    | exceptionMonad.Ret e => Some (convert_top e)
    | _ => None
  end.

Print exceptionMonad.

Definition shrink_once_L6 (oe: option exp): option exp :=
  match oe with
    | Some e => Some (shrink_top e)
    | None => None
  end.

Quote Recursively Definition p0l1 := 0%nat.
Print p0l1.
Definition p0l5 := Eval compute in compile p0l1.
Print p0l5.
Definition p0l6 := Eval compute in compile_to_L6 p0l5.
Print p0l6.
Definition p0l6s := Eval compute in shrink_once_L6 p0l6.
Print p0l6s.
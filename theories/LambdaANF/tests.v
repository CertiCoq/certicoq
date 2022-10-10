Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Import String.
Require Maps.
Require Coq.funind.Recdef.
Import Nnat.


Require Import CpdtTactics.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.




(* Add LoadPath "../common" as Common. *)
(* Add LoadPath "../L1_MalechaQuoted" as L1. *)
(* Add LoadPath "../L2_typeStripped" as L2. *)
(* Add LoadPath "../LambdaBoxMut_flattenedApp" as LambdaBoxMut. *)
(* Add LoadPath "../LambdaBoxLocal" as LambdaBoxLocal. *)
(* Add LoadPath "../L5_LambdaANF" as LambdaANF. *)

(* 
This file has been moved to certicoq/oldL5. was it needed? If so, please
revert the commit 7625.

Require Export LambdaANF.cpseval
*)
Require Import cps.
Require Import cps_util.
Require Import shrink_cps.
Require Import cps_show.

Require Import L5_to_LambdaANF closure_conversion uncurry.

Definition compile_L1_to_LambdaBoxLocal := LambdaBoxMut_to_LambdaBoxLocal.program_exp.

Check L5a.compile_L1_to_L5a.

Definition emap {A B} (f:A->B) (en: exceptionMonad.exception A) :
  exceptionMonad.exception B :=
  match en with
  | exceptionMonad.Exc s => exceptionMonad.Exc s
  | exceptionMonad.Ret e => exceptionMonad.Ret (f e)
  end.

Definition show_exn (x : exceptionMonad.exception exp) : string :=
  match x with
  | exceptionMonad.Exc s => s
  | exceptionMonad.Ret e => show_exp e
  end.

Definition compile_L1_to_LambdaANF (e:Ast.program) :=
    match L5a.compile_L1_to_L5a e with
    | exceptionMonad.Exc s => exceptionMonad.Exc s
    | exceptionMonad.Ret e => exceptionMonad.Ret (convert_top (L5a.Halt_c e))
    end.

Quote Recursively Definition p0L1 := 0%nat.
Eval compute in compile_L1_to_LambdaANF p0L1.

Definition uncurry_LambdaANF := emap (fun x => match uncurry x with
                                        | None => x
                                        | Some y => y
                                        end).
Definition shrink_once_LambdaANF := emap shrink_top.
Definition closure_convert_LambdaANF := emap closure_conversion.
Definition compile_uncurry (e:Ast.program) :=
  uncurry_LambdaANF (compile_L1_to_LambdaANF e).

Eval compute in compile_uncurry p0L1.

Quote Recursively Definition P1L1 := (fun x:nat => x).
Definition P1LambdaANF := Eval compute in compile_L1_to_LambdaANF P1L1.
Definition P1LambdaANFs := Eval compute in shrink_once_LambdaANF P1LambdaANF.
Eval compute in show_exn P1LambdaANF.
Eval compute in show_exn P1LambdaANFs.
Definition P1LambdaANFu := Eval compute in uncurry_LambdaANF P1LambdaANF.
Eval compute in show_exn P1LambdaANFu.
Definition P1LambdaANFsu := Eval compute in uncurry_LambdaANF P1LambdaANFs.
Eval compute in show_exn P1LambdaANFsu.

Quote Recursively Definition P2L1 := (fun (x y:nat) => x).
Definition P2LambdaANF := Eval compute in compile_L1_to_LambdaANF P2L1.
Eval compute in show_exn P2LambdaANF.
Definition P2LambdaANFs := Eval compute in shrink_once_LambdaANF P2LambdaANF.
Eval compute in show_exn P2LambdaANFs.
Definition P2LambdaANFsu := Eval compute in uncurry_LambdaANF P2LambdaANFs.
Eval compute in show_exn P2LambdaANFsu.
Definition P2LambdaANFu := Eval compute in uncurry_LambdaANF P2LambdaANF.
Print P2LambdaANFu.

Definition P3 := (fun f:nat => 0%nat).
Quote Recursively Definition P3L1 := P3.
Definition P3LambdaANF := Eval compute in compile_L1_to_LambdaANF P3L1.
Eval compute in show_exn P3LambdaANF.
Definition P3LambdaANFs := Eval compute in shrink_once_LambdaANF P3LambdaANF.
Eval compute in show_exn P3LambdaANFs.

Definition P4 := (0,1)%nat.
Quote Recursively Definition P4L1 := P4.
Definition P4LambdaBoxLocal := Eval compute in compile_L1_to_LambdaBoxLocal P4L1.
Print P4LambdaBoxLocal.
Definition P4LambdaANF := Eval compute in compile_L1_to_LambdaANF P4L1.
Eval compute in show_exn P4LambdaANF.
(* This doesn't shrink correctly. *)
Definition P4LambdaANFs := Eval compute in shrink_once_LambdaANF P3LambdaANF.
Eval compute in show_exn P4LambdaANFs.

Definition P5 :=
  (fun x => match x with | 0 => 0 | S n => n end)%nat.
Quote Recursively Definition P5L1 := P5.
Definition P5LambdaANF := Eval compute in compile_L1_to_LambdaANF P5L1.
Eval compute in show_exn P5LambdaANF.
(* This doesn't shrink correctly. *)
Definition P5LambdaANFs := Eval compute in shrink_once_LambdaANF P5LambdaANF.
Eval compute in show_exn P5LambdaANFs.
(*
Definition p0L5 := Eval compute in compile p0L1.
Print p0L5.
Check compile.
Check (compile : Ast.program -> exceptionMonad.exception cps).
Definition p0LambdaANF := compile_to_LambdaANF p0L5.
Definition p0LambdaANFs := Eval compute in shrink_once_LambdaANF p0LambdaANF.
Definition p0LambdaANFscc := Eval compute in closure_convert_LambdaANF p0LambdaANF.
Print p0LambdaANFs.
*)
(* Print p0LambdaANFscc. *)

Definition sabry (x:nat): (nat -> nat) :=
  fun (y:nat) => x.

Quote Recursively Definition pSabryL1 := sabry.
Definition pSabryLambdaANF := Eval compute in compile_L1_to_LambdaANF pSabryL1.
Print pSabryLambdaANF.
Definition pSabryLambdaANFu := Eval compute in compile_uncurry pSabryL1.
Print pSabryLambdaANFu.
Definition pSabryLambdaANFs := Eval compute in shrink_once_LambdaANF pSabryLambdaANFu.
Print pSabryLambdaANFs.
Definition feil:nat := sabry (0%nat) (1%nat).

Quote Recursively Definition pFeilL1 := feil.
Definition pFeilL5 := Eval compute in compile pFeilL1.
Definition pFeilLambdaANF := Eval compute in compile_to_LambdaANF pFeilL5.
Definition pFeilLambdaANFs := Eval compute in shrink_once_LambdaANF pFeilLambdaANF.
Definition pFeilLambdaANFss := Eval compute in shrink_once_LambdaANF pFeilLambdaANFs.
Definition pFeilLambdaANFsss := Eval compute in shrink_once_LambdaANF pFeilLambdaANFss.
Print pFeilLambdaANFs.
Print pFeilL5.
Print pFeilLambdaANFsss.

Fixpoint idn (n:nat) : nat := n.
Quote Recursively Definition pIdnL1 := idn.
Definition pIdnL5 := Eval compute in compile pIdnL1.
Definition pIdnLambdaANF := Eval compute in compile_to_LambdaANF pIdnL5.

Definition pIdnLambdaANFs := Eval compute in shrink_once_LambdaANF pIdnLambdaANF.
(* Definition pIdnLambdaANFcc := Eval compute in
      closure_convert_LambdaANF pIdnLambdaANFs. 
Print pIdnLambdaANFcc. *)
Print pIdnLambdaANF.
Print pIdnLambdaANFs.


(* Can all administrative redexes be reduces in one round of shrink? *)
Definition predn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => n end.
Quote Recursively Definition pPredL1 := predn.
Print pPredL1.
Definition pPredL5 := Eval compute in compile pPredL1.
Definition pPredLambdaANF := Eval compute in compile_to_LambdaANF pPredL5.
Print pPredLambdaANF.
Definition pPredLambdaANFs := Eval compute in shrink_once_LambdaANF (pPredLambdaANF).
Definition pPredLambdaANFcc := Eval compute in
      (closure_convert_LambdaANF pPredLambdaANFs).
Print pPredLambdaANFs.
Print pPredLambdaANFcc.

Transparent N.add.
Quote Recursively Definition p_add01 := (Nat.add 0%nat 1).
Print p_add01.
Definition pAdd01L5 := Eval compute in compile p_add01.
Definition pAdd01LambdaANF := Eval compute in compile_to_LambdaANF pAdd01L5.
Definition pAdd01LambdaANFs := Eval compute in shrink_once_LambdaANF (pAdd01LambdaANF).
Print pAdd01LambdaANFs.

Inductive Alph : Set :=
| A : Alph
| B : Alph
| C : nat -> Alph
| D : nat -> Alph ->  nat -> Alph.

Fixpoint foo (a:Alph) (b:Alph) : nat :=
  match a with
    | A => 0
    | D x z y => foo z a
    | _ => 2
  end.

Fixpoint foo2 (a:Alph*Alph) : nat :=
  match a with
     | (A, x) => 0
     | (y, D _ _ _) => 1
     | (B, x) => 2
     |  _ => 3
  end.


Quote Recursively Definition pFooL1 := foo.
Print pFooL1.
Definition pFooL5 := Eval compute in compile pFooL1.
Definition pFooLambdaANF := Eval compute in compile_to_LambdaANF pFooL5.
Definition pFooLambdaANFs := Eval compute in shrink_once_LambdaANF (pFooLambdaANF).
Print pFooLambdaANFs.


(* Reflect back at Nat ? 

Write to certicoq: 

(0) test in tests.v ...

(1) AXIOMS REJECTED by malecha_L1 even if in Prop <---| High priority due to prop axioms 



TEST SHRINK REDUCER
 extract shrink to ocaml and test efficiency

 translate to C and test efficiency
*)
Quote Recursively Definition pShrink := convert_top.
Set Printing Depth 100.
Print pShrink.
Definition pShrinkL5 := Eval compute in compile pShrink.      
Print pShrinkL5.
Definition pShrinkLambdaANF := Eval compute in compile_to_LambdaANF pShrinkL5.
Definition pShrinkLambdaANFs := Eval compute in shrink_once_LambdaANF pShrinkLambdaANF.
Print pShrinkLambdaANFs.



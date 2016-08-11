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
(* Add LoadPath "../L3_flattenedApp" as L3. *)
(* Add LoadPath "../L4_deBruijn" as L4. *)
(* Add LoadPath "../L5_CPS" as CPS. *)
Require Export CPS.cpseval.

Require Import cps.
Require Import cps_util.
Require Import shrink_cps.
Require Import cps_show.

Require Import L5_to_L6 closure_conversion uncurry.

Definition compile_L1_to_L4 := L3_to_L4.program_exp.

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

Definition compile_L1_to_L6 (e:Ast.program) :=
    match L5a.compile_L1_to_L5a e with
    | exceptionMonad.Exc s => exceptionMonad.Exc s
    | exceptionMonad.Ret e => exceptionMonad.Ret (convert_top (L5a.Halt_c e))
    end.

Quote Recursively Definition p0L1 := 0%nat.
Eval compute in compile_L1_to_L6 p0L1.

Definition uncurry_L6 := emap (fun x => match uncurry x with
                                        | None => x
                                        | Some y => y
                                        end).
Definition shrink_once_L6 := emap shrink_top.
Definition closure_convert_L6 := emap closure_conversion.
Definition compile_uncurry (e:Ast.program) :=
  uncurry_L6 (compile_L1_to_L6 e).

Eval compute in compile_uncurry p0L1.

Quote Recursively Definition P1L1 := (fun x:nat => x).
Definition P1L6 := Eval compute in compile_L1_to_L6 P1L1.
Definition P1L6s := Eval compute in shrink_once_L6 P1L6.
Eval compute in show_exn P1L6.
Eval compute in show_exn P1L6s.
Definition P1L6u := Eval compute in uncurry_L6 P1L6.
Eval compute in show_exn P1L6u.
Definition P1L6su := Eval compute in uncurry_L6 P1L6s.
Eval compute in show_exn P1L6su.

Quote Recursively Definition P2L1 := (fun (x y:nat) => x).
Definition P2L6 := Eval compute in compile_L1_to_L6 P2L1.
Eval compute in show_exn P2L6.
Definition P2L6s := Eval compute in shrink_once_L6 P2L6.
Eval compute in show_exn P2L6s.
Definition P2L6su := Eval compute in uncurry_L6 P2L6s.
Eval compute in show_exn P2L6su.
Definition P2L6u := Eval compute in uncurry_L6 P2L6.
Print P2L6u.

Definition P3 := (fun f:nat => 0%nat).
Quote Recursively Definition P3L1 := P3.
Definition P3L6 := Eval compute in compile_L1_to_L6 P3L1.
Eval compute in show_exn P3L6.
Definition P3L6s := Eval compute in shrink_once_L6 P3L6.
Eval compute in show_exn P3L6s.

Definition P4 := (0,1)%nat.
Quote Recursively Definition P4L1 := P4.
Definition P4L4 := Eval compute in compile_L1_to_L4 P4L1.
Print P4L4.
Definition P4L6 := Eval compute in compile_L1_to_L6 P4L1.
Eval compute in show_exn P4L6.
(* This doesn't shrink correctly. *)
Definition P4L6s := Eval compute in shrink_once_L6 P3L6.
Eval compute in show_exn P4L6s.

Definition P5 :=
  (fun x => match x with | 0 => 0 | S n => n end)%nat.
Quote Recursively Definition P5L1 := P5.
Definition P5L6 := Eval compute in compile_L1_to_L6 P5L1.
Eval compute in show_exn P5L6.
(* This doesn't shrink correctly. *)
Definition P5L6s := Eval compute in shrink_once_L6 P5L6.
Eval compute in show_exn P5L6s.
(*
Definition p0L5 := Eval compute in compile p0L1.
Print p0L5.
Check compile.
Check (compile : Ast.program -> exceptionMonad.exception cps).
Definition p0L6 := compile_to_L6 p0L5.
Definition p0L6s := Eval compute in shrink_once_L6 p0L6.
Definition p0L6scc := Eval compute in closure_convert_L6 p0L6.
Print p0L6s.
*)
(* Print p0L6scc. *)

Definition sabry (x:nat): (nat -> nat) :=
  fun (y:nat) => x.

Quote Recursively Definition pSabryL1 := sabry.
Definition pSabryL6 := Eval compute in compile_L1_to_L6 pSabryL1.
Print pSabryL6.
Definition pSabryL6u := Eval compute in compile_uncurry pSabryL1.
Print pSabryL6u.
Definition pSabryL6s := Eval compute in shrink_once_L6 pSabryL6u.
Print pSabryL6s.
Definition feil:nat := sabry (0%nat) (1%nat).

Quote Recursively Definition pFeilL1 := feil.
Definition pFeilL5 := Eval compute in compile pFeilL1.
Definition pFeilL6 := Eval compute in compile_to_L6 pFeilL5.
Definition pFeilL6s := Eval compute in shrink_once_L6 pFeilL6.
Definition pFeilL6ss := Eval compute in shrink_once_L6 pFeilL6s.
Definition pFeilL6sss := Eval compute in shrink_once_L6 pFeilL6ss.
Print pFeilL6s.
Print pFeilL5.
Print pFeilL6sss.

Fixpoint idn (n:nat) : nat := n.
Quote Recursively Definition pIdnL1 := idn.
Definition pIdnL5 := Eval compute in compile pIdnL1.
Definition pIdnL6 := Eval compute in compile_to_L6 pIdnL5.

Definition pIdnL6s := Eval compute in shrink_once_L6 pIdnL6.
(* Definition pIdnL6cc := Eval compute in
      closure_convert_L6 pIdnL6s. 
Print pIdnL6cc. *)
Print pIdnL6.
Print pIdnL6s.


(* Can all administrative redexes be reduces in one round of shrink? *)
Definition predn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => n end.
Quote Recursively Definition pPredL1 := predn.
Print pPredL1.
Definition pPredL5 := Eval compute in compile pPredL1.
Definition pPredL6 := Eval compute in compile_to_L6 pPredL5.
Print pPredL6.
Definition pPredL6s := Eval compute in shrink_once_L6 (pPredL6).
Definition pPredL6cc := Eval compute in
      (closure_convert_L6 pPredL6s).
Print pPredL6s.
Print pPredL6cc.

Transparent N.add.
Quote Recursively Definition p_add01 := (Nat.add 0%nat 1).
Print p_add01.
Definition pAdd01L5 := Eval compute in compile p_add01.
Definition pAdd01L6 := Eval compute in compile_to_L6 pAdd01L5.
Definition pAdd01L6s := Eval compute in shrink_once_L6 (pAdd01L6).
Print pAdd01L6s.

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
Definition pFooL6 := Eval compute in compile_to_L6 pFooL5.
Definition pFooL6s := Eval compute in shrink_once_L6 (pFooL6).
Print pFooL6s.


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
Definition pShrinkL6 := Eval compute in compile_to_L6 pShrinkL5.
Definition pShrinkL6s := Eval compute in shrink_once_L6 pShrinkL6.
Print pShrinkL6s.



Require Export Common.certiClasses.
Require Export L2.instances.
Require Export L1g.instances.
Require Export L2_5.instances.
Require Export L4.instances.
Require Export L6.instances.

Set Template Cast Propositions.

Quote Recursively Definition p := (3+4).
                                  
Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Require Import Common.Common.
Require Import String.
Open Scope string_scope.



Eval compute in (ctranslateTo certiL4 p).

Time Eval compute in (ctranslateTo certiL5a p).


Eval compute in (cTerm certiL6).
Eval compute in (ctranslateTo certiL6 p).

(* 
To debug typeclass resolution problems, try:
Typeclasses eauto := 5. (* or a small number to limit the search depth *)
Typeclasses eauto := debug. (* if your ide doesn't show debug messages, use coqc *)
Print Instances CerticoqTranslation.
Print Instances CerticoqTotalTranslation.
Print Instances CerticoqLanguage.
*)

Quote Recursively Definition swap := 
(fun  (p: nat  * bool) =>
match p with
(x,y) => (y,x)
end).



Ltac computeExtract certiL4 f:=
(let t:= eval compute in (translateTo (cTerm certiL4) f) in 
match t with
|Ret ?xx => exact xx
end).



Definition swap4 : (cTerm certiL4).
computeExtract certiL4 swap.
Defined.

Definition swap4a : cTerm certiL4_2.
computeExtract certiL4_2 swap.
Defined.

Print swap4.

Quote Recursively Definition prev := (fun x => 
 match x with
 | 0 => 0
| S n => n
end)%nat.

(*
Local Opaque L4_2_to_L5.Match_e.
Local Opaque L4_2_to_L5.Fix_e.
Local Opaque L4_2_to_L5.Con_e.
Local Opaque L4_2_to_L5.Lam_e.
Local Opaque L4_2_to_L5.Let_e.
Local Opaque L4_2_to_L5.App_e.
*)

Definition prev4 : cTerm certiL4.
computeExtract certiL4 prev.
Defined.

Definition prev4a : cTerm certiL4_2.
computeExtract certiL4_2 prev.
Defined.

Definition prev5 : cTerm certiL5.
(let t:= eval vm_compute in (translateTo (cTerm certiL5) prev) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition prev5a : cTerm certiL5a.
(let t:= eval vm_compute in (translateTo (cTerm certiL5a) prev) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Print prev4.
Print prev4a.
Print prev5.
Print prev5a.

Print prev.

Require Import L3.instances.
Eval compute in (cTerm certiL3).

Definition prev3 := ltac:(computeExtract certiL3 prev).

Require Import L3_to_L4.
Definition prev3Ienv := L4.L3_to_L4.inductive_env (AstCommon.env prev3).
Eval vm_compute in prev3Ienv.

Require Import NPeano.
Require Import Recdef.
Set Implicit Arguments.
Require Import Omega.

Function Gcd (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (b mod S k)  (S k)
end
.
Proof.
- intros m n k Heq. subst. apply Nat.mod_upper_bound.
  omega.
- exact lt_wf.
Defined.

Set Template Cast Propositions.

Quote Recursively Definition pgcd :=
Gcd.

Eval compute in (cTerm certiL2).
Let pcgd2 : cTerm certiL2.
let T:= eval vm_compute in (L2.compile.program_Program pgcd) in exact T.
Defined.

Let pcgd4a : cTerm certiL4_2.
(let t:= eval vm_compute in (certiClasses.translate (cTerm certiL2) (cTerm certiL4_2) pcgd2) in 
match t with
|Ret ?xx => exact xx
end).
Defined.
Require Import List.
Import ListNotations.

(* the Gcd_terminate function is in the environment. Below,
we project that part of the environment.
The environment is too big, because it contains even the
definitions that were used in the erased proof. *)
Eval vm_compute in (nth_error (AstCommon.env pcgd2) 1).
(* Eval vm_compute in (nth_error (AstCommon.env pcgd3) 1). *)

Require Import SquiggleEq.terms.

Require Import  ExtLib.Data.String.

(*
Definition pgcd4astr : string.
let t:= eval vm_compute in (print4 pcgd4a) in exact t.
Defined.
Eval compute in pgcd4astr.
*)


Definition p6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) p) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Require Import L6_to_Clight Maps.

Definition compile_L6 (t : cTerm certiL6) : L5_to_L6.nEnv * Clight.program :=
  let '((_, cenv, _, nenv), prog) := t in
  let p := stripNameState (compile prog cenv nenv) in
  (fst p, stripOption (snd p)).

Open Scope positive_scope.

Definition p7 := compile_L6 p6.

Require Import L6.cps L6.cps_show.

Inductive blah : Type :=
| blah1 : blah -> blah
| blah2 : blah -> blah
| blah3 : blah
| blah4 : blah
.

Definition blahFun (b : blah) : blah :=
  match b with
  | blah1 b' => b'
  | blah2 b' => blah1 b'
  | blah3 => blah4
  | blah4 => blah1 blah3
  end.

Quote Recursively Definition blahProg := (blahFun (blah2 (blahFun blah4))).

Definition blahProg6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) blahProg) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition blahProg7 := compile_L6 blahProg6.

Definition show_exn {A:Type} (x : exceptionMonad.exception (cTerm certiL6)) : string :=
  match x with
  | exceptionMonad.Exc s => s
  | exceptionMonad.Ret ((p,cenv,g, nenv), e) => show_exp nenv cenv e
  end.

Eval compute in (show_exn (Ret p6)).

Quote Recursively Definition test_fun := (fun x : nat => (x + 4)%nat).
Definition test_fun6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) test_fun) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Definition swap6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) swap) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition swap7 := compile_L6 swap6.


Quote Recursively Definition three := 3.

Definition three6 : cTerm certiL6. 
(let t:= eval vm_compute in (translateTo (cTerm certiL6) three) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition three7 := compile_L6 three6.


Require Import L6.cps.

Quote Recursively Definition cpsTerm := (Efun
                                         (Fcons f t'
                                                (y :: z :: nil)
                                                (Eapp y t'' (z :: nil))
                                                Fnil)
                                         (Eproj b t 2%N x
                                                (Eproj c t 4%N x
                                                       (Eapp f t' (b :: c :: nil))))).

Definition cpsTerm6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) cpsTerm) in 
match t with
|Ret ?xx => exact xx
end).
Defined.
Definition cpsTerm7 := compile_L6 cpsTerm6.

(*
Add LoadPath "../benchmarks".
Require Import Color.
 *)

(*
Add LoadPath "../benchmarks".
Require Import vs.

Quote Recursively Definition vs := vs.main.
Definition vs6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) vs) in 
match t with
|Ret ?xx => exact xx
end).
Defined.
Definition vs6' := Eval vm_compute in (L6_translation vs6).


Print vs6.
Print vs6'.

Definition vs7 := compile_L6 vs6.
*)

(*
Quote Recursively Definition comp_fEnv := L6_to_Clight.compute_fEnv.
Definition comp_fEnv6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) comp_fEnv) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Definition comp_fEnv6' := Eval vm_compute in (L6_translation comp_fEnv6).
Print comp_fEnv6'.
Definition comp_fEnv7 := compile_L6 comp_fEnv6.




Quote Recursively Definition make_args := L6_to_Clight.compute_fEnv.
Definition comp_fEnv6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) comp_fEnv) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Definition comp_fEnv6' := Eval vm_compute in (L6_translation comp_fEnv6).
Print comp_fEnv6'.
Definition comp_fEnv7 := compile_L6 comp_fEnv6.
 *)

Require Import runtime.runtime.

Definition printProg := fun prog file => L6_to_Clight.print_Clight_dest_names (snd prog) (M.elements (fst prog)) file.

Definition test := printProg p7 "output/threePlusFour.c".
(*Definition test := printProg blahProg7 "output/blah.c".*)








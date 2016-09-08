Require Export Common.certiClasses.
Require Export L2.instances.
Require Export L4.instances.
(*Require Export L6.instances.*)


Quote Recursively Definition p := (3 + 4).

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Print Instances CerticoqTranslation.
Print Instances CerticoqTotalTranslation.
Print Instances CerticoqLanguage.

Require Import Common.Common.
Eval compute in (translateTo (cTerm certiL4) p).

Time Eval compute in (translateTo (cTerm certiL5a) p).

(* Fix the type of [certiL5a_t0_L6]. It should return (cTerm certiL6) which 
also contains an environment. 
To debug typeclass resolution problems, try:
Typeclasses eauto := 5. (* or a small number to limit the search depth *)
Typeclasses eauto := debug. (* if your ide doesn't show debug messages, use coqc *)

Eval vm_compute in (translateTo (* (cTerm certiL6) *) cps.exp p).


*)


Quote Recursively Definition swap := 
(fun  (p: nat  * bool) =>
match p with
(x,y) => (y,x)
end).

Open Scope string_scope.
Print swap.

Ltac computeExtract certiL4 f:=
(let t:= eval compute in (translateTo (cTerm certiL4) f) in 
match t with
|Ret ?xx => exact xx
end).


Definition swap4 : (cTerm certiL4).
computeExtract certiL4 swap.
Defined.

Definition swap4a : cTerm certiL4a.
computeExtract certiL4a swap.
Defined.

Print swap4.

Quote Recursively Definition prev := (fun x => 
 match x with
 | 0 => 0
| S n => n
end).

(*
Local Opaque L4a_to_L5.Match_e.
Local Opaque L4a_to_L5.Fix_e.
Local Opaque L4a_to_L5.Con_e.
Local Opaque L4a_to_L5.Lam_e.
Local Opaque L4a_to_L5.Let_e.
Local Opaque L4a_to_L5.App_e.
*)

Definition prev4 : cTerm certiL4.
computeExtract certiL4 prev.
Defined.

Definition prev4a : cTerm certiL4a.
computeExtract certiL4a prev.
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






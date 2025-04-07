From MetaCoq.Utils Require Import bytestring MCString. 
From MetaCoq.Common Require Import Primitive.
From CertiCoq.Plugin Require Import CertiCoq.
From Coq Require Import Uint63 ZArith.
Open Scope bs.

Set CertiCoq Build Directory "_build".

Definition cst := coq_msg_info (Primitive.string_of_prim_int ((1 << 63))%uint63).
Set Warnings "-primitive-turned-into-axiom".
CertiCoq Run cst.

(* CertiCoq Compile test. *)

From Bignums Require Import BigN.
Local Open Scope bigN_scope.
From MetaCoq.ErasurePlugin Require Import Loader.

(* From MetaCoq.Erasure Require Import Loader. *)
 
Definition testd := diveucl_21 9305446873517 1793572051078448654 4930380657631323783. 
Definition testmul := head0 3221225472.
Eval compute in testmul.

(* MetaCoq Erase -time -typed testmul. *)

CertiCoq Eval -time -debug -typed-erasure testmul.
(* 
Result: 549755813886, 0
Calling prim_int63_eqb on 0 and 0: 1, 1 
Calling prim_int63_eqb on 549755813886 and 0: 0, 0 
Calling prim_int63_addmuldiv
Calling addmuldiv with 1, 0 and 0: 0 *)
(* Definition testd := diveucl_21 4 0 4611686018427387904. *)
(* Eval compute in testd. *)
Definition cst_small : BigN.t * BigN.t := BigN.div_eucl (6) 3.
Time Eval vm_compute in cst_small.
Time Eval compute in cst_small.
CertiCoq Eval -time -typed-erasure -unsafe-erasure cst_small. (* Execution: 0.001s *)
CertiCoq Show IR -time -typed-erasure -unsafe-erasure cst_small. (* Execution: 0.001s *)

From Coq Require Import StreamMemo.

CertiCoq Show IR -time -typed-erasure -unsafe-erasure memo_make. (* Execution: 0.001s *)

Definition cst_big : bool := 
  let x := BigN.div_eucl (2 ^ 129 + (2 ^ 39 - 2)) 3 in 
  BigN.eqb (fst x) (fst x).

Time Eval vm_compute in cst_big. (* 0s *)

(*CertiCoq Eval -time -typed-erasure -unsafe-erasure cst_big.*) (* Execution: 0.001s, slow compilation *)
(* CertiCoq Eval -time -unsafe-erasure cst_big. *)

Definition cst_big2 : bool := 
  let x := BigN.div_eucl (2 ^ 64500000 + (2 ^ 39 - 2)) 3 in 
  BigN.eqb (fst x) (fst x).

(*Time Eval vm_compute in cst_big2. (* 14 s *) *)
(* Time CertiCoq Eval -debug -time -typed-erasure -unsafe-erasure cst_big2. *)
 (* 69s *)

Require Import Cyclic63.
Open Scope uint63_scope.
Definition test := (addmuldiv 32 3 5629499534213120)%uint63.
Eval compute in test.

Definition string_of_zn2z {A} (sofa : A -> string) (c : zn2z A) : string :=
  match c with
  | W0 => "W0"
  | WW x y => "WW " ++ sofa x ++ " " ++ sofa y
  end.

Definition string_of_carry {A} (sofa : A -> string) (c : carry A) : string :=
  match c with
  | C0 x => "(C0 " ++ sofa x ++ ")"
  | C1 x => "(C1 " ++ sofa x ++ ")"
  end.

Definition string_of_bool b :=
  if (b : bool) then "true" else "false".

Definition string_of_primpair (x : int * int) :=
  let (l, r) := x in
  "(" ++ Primitive.string_of_prim_int l ++ ", " ++ Primitive.string_of_prim_int r ++ ")".

Definition result := coq_msg_info (Primitive.string_of_prim_int test).
(* Definition result := ("(" ++ Primitive.string_of_prim_int (fst cst_big) ++ ", " ++ *)
    (* Primitive.string_of_prim_int (snd cst_big) ++ ")")%bs. *)
Time Eval vm_compute in result.

CertiCoq Run result.

From MetaCoq Require Import bytestring MCString Primitive.
From CertiCoq.Plugin Require Import CertiCoq.
From Coq Require Import Uint63 ZArith.
Open Scope bs.

Definition cst := coq_msg_info (Primitive.string_of_prim_int ((1 << 63))%uint63).
Set Warnings "-primitive-turned-into-axiom".
CertiCoq Run cst.

(* CertiCoq Compile test. *)

From Bignums Require Import BigN.
Local Open Scope bigN_scope.
From MetaCoq Require Import Loader.

(* From MetaCoq.Erasure Require Import Loader. *)
 
(* Definition testd := diveucl_21 9305446873517 1793572051078448654 4930380657631323783. *)
(* Definition testmul := head0 3221225472. *)
(* Eval compute in testmul. *)
(* 
Result: 549755813886, 0
Calling prim_int63_eqb on 0 and 0: 1, 1 
Calling prim_int63_eqb on 549755813886 and 0: 0, 0 
Calling prim_int63_addmuldiv
Calling addmuldiv with 1, 0 and 0: 0 *)
(* Definition testd := diveucl_21 4 0 4611686018427387904. *)
(* Eval compute in testd. *)
Definition cst_big : BigN.t * BigN.t := BigN.div_eucl (2 ^ 129 + (2 ^ 39 - 2)) 3.
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
Time Eval native_compute in result.

CertiCoq Run result.

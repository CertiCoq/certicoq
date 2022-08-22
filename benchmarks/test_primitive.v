From MetaCoq.Template Require Import bytestring MCString.
From CertiCoq.Plugin Require Import CertiCoq.
From Coq Require Import Uint63 ZArith.
Open Scope bs.

Cd "runs".

Axiom (coq_msg_info : string -> unit).
Axiom (coq_user_error : string -> unit).
Axiom (coq_msg_debug : string -> unit).

Definition cst := coq_msg_info (Primitive.string_of_prim_int ((1 << 65))%uint63).

CertiCoq Run cst
Extract Constants [ 
  coq_msg_info => "print_msg_info",
  Coq.Numbers.Cyclic.Int63.PrimInt63.add => "prim_int63_add",
  Coq.Numbers.Cyclic.Int63.PrimInt63.eqb => "prim_int63_eqb",
  Coq.Numbers.Cyclic.Int63.PrimInt63.land => "prim_int63_land", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsr => "prim_int63_lsr", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsl => "prim_int63_lsl", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.head0 => "prim_int63_head0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.tail0 => "prim_int63_tail0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.compare => "prim_int63_compare", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.subc => "prim_int63_subc" with tinfo,
  Coq.Numbers.Cyclic.Int63.PrimInt63.sub => "prim_int63_sub", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addc => "prim_int63_addc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "prim_int63_addcarryc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "prim_int63_subcarryc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mulc => "prim_int63_mulc" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mul => "prim_int63_mul", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "prim_int63_diveucl_21" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl => "prim_int63_diveucl" with tinfo, 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mod => "prim_int63_mod", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "prim_int63_addmuldiv", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.leb => "prim_int63_leb", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.ltb => "prim_int63_ltb", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.div => "prim_int63_div", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lor => "prim_int63_lor", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lxor => "prim_int63_lxor" ]
Include [ "prim_int63.h" ].

(* CertiCoq Compile test. *)

From Bignums Require Import BigN.
Local Open Scope bigN_scope.
From MetaCoq.Template Require Import Loader.

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

CertiCoq Run result
Extract Constants [ 
    coq_msg_info => "print_msg_info",
    Coq.Numbers.Cyclic.Int63.PrimInt63.add => "prim_int63_add",
    Coq.Numbers.Cyclic.Int63.PrimInt63.eqb => "prim_int63_eqb",
    Coq.Numbers.Cyclic.Int63.PrimInt63.land => "prim_int63_land", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.lsr => "prim_int63_lsr", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.lsl => "prim_int63_lsl", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.head0 => "prim_int63_head0", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.tail0 => "prim_int63_tail0", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.compare => "prim_int63_compare", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.subc => "prim_int63_subc" with tinfo,
    Coq.Numbers.Cyclic.Int63.PrimInt63.sub => "prim_int63_sub", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.addc => "prim_int63_addc" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "prim_int63_addcarryc" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "prim_int63_subcarryc" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.mulc => "prim_int63_mulc" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.mul => "prim_int63_mul", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "prim_int63_diveucl_21" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl => "prim_int63_diveucl" with tinfo, 
    Coq.Numbers.Cyclic.Int63.PrimInt63.mod => "prim_int63_mod", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "prim_int63_addmuldiv", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.leb => "prim_int63_leb", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.ltb => "prim_int63_ltb", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.div => "prim_int63_div", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.lor => "prim_int63_lor", 
    Coq.Numbers.Cyclic.Int63.PrimInt63.lxor => "prim_int63_lxor"
]
Include [ "prim_int63.h" ].

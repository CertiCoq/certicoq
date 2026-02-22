From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Primitive.

From Stdlib Require Import PrimFloat PrimInt63.
From CertiCoq.CertiCoqC Require Import CertiCoqC.

(* Set MetaRocq Debug. *)
Set MetaRocq Timing.
From Stdlib Require Import List.
Import ListNotations.

Require Import compcert.common.AST.

Class Show (A : Type) := show : A -> string.

#[export] Instance nat_show : Show nat := string_of_nat.
Local Open Scope bs.
Definition string_of_bool b :=
  if (b : bool) then "true" else "false".
#[export] Instance bool_show : Show bool := string_of_bool.

#[export] Instance list_show {A} {SA : Show A} : Show (list A) := string_of_list show.

#[export] Instance float_show : Show PrimFloat.float := string_of_float.
#[export] Instance prim_int_show : Show PrimInt63.int := string_of_prim_int.
#[export] Instance Z_show : Show BinNums.Z := string_of_Z.
From Stdlib Require Import ZArith.

From MetaRocq.ErasurePlugin Require Import Loader.
From CertiCoq.Common Require Import Pipeline_utils.
From CertiCoq.CertiCoqC Require Import CertiCoqC.
From CertiCoq.CertiCoqC Require Import Loader.

Definition certicoqc (opts : Options) (p : Template.Ast.Env.program) :=
  let () := coq_msg_info "certicoqc called" in
  compile opts p.

Set Warnings "-primitive-turned-into-axiom".

(* Definition demo1 := show [1; 0; 1].

CertiCoqC Eval demo1.

Definition demo2 := if false then false else true.
CertiCoqC Eval demo2. *)

(* Time CertiCoqC Compile -build_dir "tests" -time -O 1 demo1. *)

From Stdlib Require Import Strings.PrimString.

Time CertiCoqC Compile -build_dir "tests" -time -O 1 certicoqc.

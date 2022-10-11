From MetaCoq.Template Require Import All Loader Primitive bytestring.
From Coq Require Import PrimFloat PrimInt63.
From CertiCoq.CertiCoqC Require Import CertiCoqC.

(* Set MetaCoq Debug. *)
Set MetaCoq Timing.
From Coq Require Import List.
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
Require Import ZArith.
 
From CertiCoq.CertiCoqC Require Import compile.
From CertiCoq.Common Require Import Pipeline_utils.

Definition certicoqc (opts : Options) (p : Template.Ast.Env.program) := 
  let () := coq_msg_info "certicoqc called" in
  compile opts p.

Set Warnings "-primitive-turned-into-axiom".
Time CertiCoqC Compile -build_dir "tests" -time -O 1 certicoqc.

From MetaCoq.Template Require Import All Loader.
From CertiCoq.CertiCoqC Require Import Loader.
From CertiCoq Require Import CertiCoq.

(* Set MetaCoq Debug. *)
Set MetaCoq Timing.
From Coq Require Import List.
Import ListNotations.

Require Import compcert.common.AST.

Cd "tests".

From MetaCoq.Erasure Require Import Erasure.

(* Time CertiCoqC Compile erase_and_print_template_program. *)
(*Extract Constants [
  (* coq_msg_debug => "print_msg_debug", *)
  (* coq_msg_info => "print_msg_info", *)
   ] 
Include [ "print.h" ].
*)
(* 32sec *)
(*Cd "../mltests".
Time CertiCoq Compile erase_and_print_template_program.
(* 12sec *) *)

From CertiCoq.CertiCoqC Require Import compile.

Time CertiCoqC Compile -time -O 1 compile.certicoqc
 Extract Constants [ 
  (* coq_msg_debug => "print_msg_debug", *)
   coq_msg_info => "print_msg_info" ] 
Include [ "print.h" ].

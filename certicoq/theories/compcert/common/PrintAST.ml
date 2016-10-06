(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Useful functions for pretty-printers *)

open Printf
open Camlcoq
open AST

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"
  | Tlong -> "long"
  | Tsingle -> "single"
  | Tany32 -> "any32"
  | Tany64 -> "any64"

let name_of_chunk = function
  | Mint8signed -> "int8s"
  | Mint8unsigned -> "int8u"
  | Mint16signed -> "int16s"
  | Mint16unsigned -> "int16u"
  | Mint32 -> "int32"
  | Mint64 -> "int64"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"
  | Many32 -> "any32"
  | Many64 -> "any64"

let rec implode = function
    []       -> ""
  | charlist -> (Char.escaped (List.hd charlist)) ^
                (implode (List.tl charlist))

let name_of_external = function
  | EF_external(name, sg) -> sprintf "extern %S" (implode name)
  | EF_builtin(name, sg) -> sprintf "builtin %S" (implode name)
  | EF_vload chunk -> sprintf "volatile load %s" (name_of_chunk chunk)
  | EF_vstore chunk -> sprintf "volatile store %s" (name_of_chunk chunk)
  | EF_malloc -> "malloc"
  | EF_free -> "free"
  | EF_memcpy(sz, al) ->
      sprintf "memcpy size %s align %s " (Z.to_string sz) (Z.to_string al)
  | EF_annot(text, targs) -> sprintf "annot %S" (implode text)
  | EF_annot_val(text, targ) ->  sprintf "annot_val %S" (implode text)
  | EF_inline_asm (text, blah1, blah2) -> sprintf "inline_asm %S" (implode text)

(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Pp
open Printer
open Metacoq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils
module MLCompiler : Certicoq.CompilerInterface with 
  type name_env = BasicAst.name Cps.M.t
  = struct
  type name_env = BasicAst.name Cps.M.t
  let compile = Certicoqc_plugin_wrapper.compile
  let printProg prog names (dest : string) (import : string list) =
    PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest import

  let generate_glue = Glue.generate_glue
  let generate_ffi = Ffi.generate_ffi
end

module CCompile = Certicoq.CompileFunctor (MLCompiler)
include CCompile
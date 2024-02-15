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
  let printProg prog names (dest : string) (imports : import list) =
    let imports' = List.map (fun i -> match i with
      | FromRelativePath s -> "#include \"" ^ s ^ "\""
      | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
      | FromAbsolutePath s ->
          failwith "Import with absolute path should have been filled") imports in
    PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

  let generate_glue = Glue.generate_glue
  let generate_ffi = Ffi.generate_ffi
end

module CCompile = Certicoq.CompileFunctor (MLCompiler)
include CCompile

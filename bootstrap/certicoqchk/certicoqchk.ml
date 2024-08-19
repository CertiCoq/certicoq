(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2022                                                 *)
(**********************************************************************)

open Pp
open Printer
open Metacoq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils

let quote gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  let term = Metacoq_template_plugin.Ast_quoter.quote_term_rec ~bypass:true env sigma (EConstr.to_constr sigma c) in
  term

let check gr = 
  (* Quote Coq term *)
  let p = quote gr in
  let b = Certicoqchk_plugin_wrapper.check (Obj.magic p) (* Go through a type equality *) in
  if b then () else CErrors.user_err Pp.(str"The program does not typecheck")

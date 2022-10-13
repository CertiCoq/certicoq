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

let debug = true

let debug_msg (flag : bool) (s : string) =
  if flag then
    Feedback.msg_debug (str s)
  else ()

let quote gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = Metacoq_template_plugin.Ast_quoter.quote_term_rec ~bypass:true env (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.. checking." time);
  term

let check gr = 
  (* Quote Coq term *)
  let p = quote gr in
  let b = Certicoqchk_plugin_wrapper.check (Obj.magic p) (* Go through a type equality *) in
  match b with
  | Datatypes.Coq_true -> () 
  | Datatypes.Coq_false -> CErrors.user_err Pp.(str"The program does not typecheck")
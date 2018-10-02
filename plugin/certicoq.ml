(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017      Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)

open Pp
open Printer
open Term_quoter
open ExceptionMonad   
open AstCommon

let pr_char c = str (Char.escaped c)
   
let pr_char_list =
  prlist_with_sep mt pr_char
   
let compile gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma gr in
  let const = match gr with
    | Globnames.ConstRef c -> c
    | _ -> CErrors.user_err ~hdr:"template-coq"
       (Printer.pr_global gr ++ str" is not a constant definition") in
  Feedback.msg_debug (str"Quoting");
  let term = quote_term_rec env (EConstr.to_constr sigma c) in
  Feedback.msg_debug (str"Finished quoting.. compiling to L7.");
  match AllInstances.compile_template_L7 term with
  | Ret ((nenv, header), prg) ->
     Feedback.msg_debug (str"Finished compiling, printing to file.");
     let str = quote_string (Names.string_of_kn (Names.Constant.canonical const) ^ ".c") in
     let hstr = quote_string (Names.string_of_kn (Names.Constant.canonical const) ^ ".h") in
     AllInstances.printProg (nenv,prg) str;
     AllInstances.printProg (nenv,header) hstr
  | Exc s ->
     CErrors.user_err ~hdr:"template-coq" (str "Could not compile: " ++ pr_char_list s)

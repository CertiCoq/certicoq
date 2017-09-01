(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017      Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)

open Pp
open Printer
open Template_coq
open ExceptionMonad   
open AstCommon

let pr_char c = str (Char.escaped c)
   
let pr_char_list =
  prlist_with_sep mt pr_char
   
let compile gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let Sigma.Sigma (c, sigma, _) = Evarutil.new_global (Sigma.Unsafe.of_evar_map sigma) gr in
  let const = match gr with
    | Globnames.ConstRef c -> c
    | _ -> CErrors.errorlabstrm "template-coq"
       (Printer.pr_global gr ++ str" is not a constant definition") in
  Feedback.msg_debug (str"Quoting");
  let term = quote_term_rec env c in
  Feedback.msg_debug (str"Finished quoting.. compiling to L7.");
  match AllInstances.compile_template_L7 (Obj.magic term) with
  | Ret (nenv, prg) ->
     Feedback.msg_debug (str"Finished compiling, printing to file.");
     let str = quote_string (Names.string_of_kn (Names.Constant.canonical const) ^ ".c") in
     AllInstances.printProg (nenv,prg) str
  | Exc s ->
     CErrors.errorlabstrm "template-coq" (str "Could not compile: " ++ pr_char_list s)

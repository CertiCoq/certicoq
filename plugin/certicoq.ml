(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Pp
open Printer
open Ast_quoter
open ExceptionMonad
open AstCommon

(** Various Utils *)

let pr_char c = str (Char.escaped c)

let pr_char_list =
  prlist_with_sep mt pr_char

let string_of_chars (chars : char list) : string =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let rec coq_nat_of_int x =
  match x with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (coq_nat_of_int (pred n))

let debug_msg (flag : bool) (s : string) =
  if flag then
    Feedback.msg_debug (str s)
  else ()

(** Compilation Command Arguments *)

type command_args =
 | ANF
 | TIME
 | OPT of int
 | DEBUG
 | ARGS of int

type options =
  { cps       : bool;
    time      : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
  }

let default_options : options =
  { cps    = true;
    time   = false;
    olevel = 0;
    debug  = false;
    args   = 5;
  }

let help_msg : string =
  "Usage:\n\
To compile an program named <gid> type:\n\
   CertiCoq Compile [options] <gid>.\n\n\
To show this help message type:\n\
   CertiCoq -help.\n\n\
To produce an .ir file with the last IR (lambda-anf) of the compiler type:\n\
   CertiCoq Show IR [options] <global_identifier>.\n\n
Valid options:\n\
-direct :  Produce direct-style code (as opposed to he default which is continuation-passing style)\n\
-time   :  Time each compilation phase\n\
-o1     :  Perform more aggressive optimizations (currently unboxing of closure environments)\n\
-bebug  :  Show debugging information\n\
-args X :  Specify how many arguments are used in the C translation (on top of the thread_info argument)\n\
\n\
To show this help message type:\n\
CertiCoq -help.\n"


let make_options (l : command_args list) : options =
  let rec aux (o : options) l =
    match l with
    | [] -> o
    | ANF     :: xs -> aux {o with cps = false} xs
    | TIME    :: xs -> aux {o with time = true} xs
    | OPT n   :: xs -> aux {o with olevel = n} xs
    | DEBUG   :: xs -> aux {o with debug = true} xs
    | ARGS n  :: xs -> aux {o with args = n} xs
  in aux default_options l

let make_pipeline_options (opts : options) =
  let cps    = opts.cps in
  let args = coq_nat_of_int opts.args in
  let olevel = coq_nat_of_int opts.olevel in
  let timing = opts.time in
  let debug  = opts.debug in
  Pipeline.make_opts cps args olevel timing debug

(** Main Compilation Functions *)

(* Quote Coq term *)
let quote opts gr =
  let debug = opts.debug in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma gr in
  let const = match gr with
    | Globnames.ConstRef c -> c
    | _ -> CErrors.user_err ~hdr:"template-coq"
       (Printer.pr_global gr ++ str" is not a constant definition") in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = quote_term_rec env (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.. compiling to L7." time);
  (term, const)

(* Compile Quoted term with CertiCoq *)
let compile opts term const =
  let debug = opts.debug in
  let options = make_pipeline_options opts in

  let p = Pipeline.compile options term in
  match p with
  | (CompM.Ret ((nenv, header), prg), dbg) ->
    debug_msg debug "Finished compiling, printing to file.";
    let time = Unix.gettimeofday() in
    (* Zoe: Make suffix appear only in testing/debugging mode *)
    let suff = if opts.cps then "_cps" else "" ^ if opts.olevel <> 0 then "_opt" else "" in
    let cstr = Quoted.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".c") in
    let hstr = Quoted.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".h") in
    Pipeline.printProg (nenv,prg) cstr;
    Pipeline.printProg (nenv,header) hstr;
    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str (Printf.sprintf "Printed to file in %f s.." time));
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg)
  | (CompM.Err s, dbg) ->
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg);
    CErrors.user_err ~hdr:"pipeline" (str "Could not compile: " ++ (pr_char_list s) ++ str "\n")

(* Generate glue code for the compiled program *)
let generate_glue opts term const =
  let debug = opts.debug in
  let options = make_pipeline_options opts in

  let time = Unix.gettimeofday() in
  (match Pipeline.make_glue options term with
  | CompM.Ret (((nenv, header), prg), logs) ->
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Generated glue code in %f s.." time);
    (match logs with [] -> () | _ ->
      debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_chars logs))));
    let time = Unix.gettimeofday() in
    let cstr = Quoted.string_to_list ("glue." ^ Names.KerName.to_string (Names.Constant.canonical const) ^ ".c") in
    let hstr = Quoted.string_to_list ("glue." ^ Names.KerName.to_string (Names.Constant.canonical const) ^ ".h") in
    Pipeline.printProg (nenv, prg) cstr;
    Pipeline.printProg (nenv, header) hstr;

    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Printed glue code to file in %f s.." time)
  | CompM.Err s ->
    CErrors.user_err ~hdr:"glue-code" (str "Could not generate glue code: " ++ pr_char_list s))


let compile_with_glue opts gr =
  let (term, const) = quote opts gr in
  compile opts term const;
  generate_glue opts term const

let compile_only opts gr =
  let (term, const) = quote opts gr in
  compile opts term const

let generate_glue_only opts gr =
  let (term, const) = quote opts gr in
  generate_glue opts term const

let print_to_file (s : string) (file : string) =
  let f = open_out file in
  Printf.fprintf f "%s\n" s;
  close_out f

let show_ir opts gr =
  let (term, const) = quote opts gr in
  let debug = opts.debug in
  let options = make_pipeline_options opts in
  let p = Pipeline.show_IR options term in
  match p with
  | (Ret prg, dbg) ->
    debug_msg debug "Finished compiling, printing to file.";
    let time = Unix.gettimeofday() in
    let suff = if opts.cps then "_cps" else "" ^ if opts.olevel <> 0 then "_opt" else "" in
    let file = (Names.KerName.to_string (Names.Constant.canonical const)) ^ suff ^ ".ir" in
    print_to_file (string_of_chars prg) file;
    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str (Printf.sprintf "Printed to file in %f s.." time));
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg)
  | (CompM.Err s, dbg) ->
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg);
    CErrors.user_err ~hdr:"show-ir" (str "Could not compile: " ++ (pr_char_list s) ++ str "\n")


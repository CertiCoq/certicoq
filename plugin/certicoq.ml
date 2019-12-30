(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017      Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)

open Pp
open Printer
open Ast_quoter
open ExceptionMonad
open AstCommon


type options =
  { cps  : bool;
    time : bool;
    opt  : int; }

let default_options : options =
  { cps  = true;
    time = false;
    opt  = 0;
  }

type 'a error = Res of 'a | Error of string


let options_help : string =
  "List of valid options: \"direct\", \"-o1\", \"time\"\n"


let parse_options (l : string list) : options error =
  let rec aux (o : options) l =
    match l with
    | [] -> Res o
    | "anf" :: xs -> aux {o with cps = false} xs
    | "time" :: xs -> aux {o with time = true} xs
    | "-o1" :: xs -> aux {o with opt = 1} xs
    | x :: xs -> Error ("Unsupported option " ^ x)
  in aux default_options l

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

(*
let pcuic_size' a p =
  match p with
  | Coq_tRel n -> a+1
  | Coq_tMeta n -> a+1
  | Coq_tVar id -> a+1
  | Coq_tEvar -> a+1
  | Coq_tSort -> a+1
  | Coq_tProd n t1 t2 ->  pcuic_size (pcuic_size (a+1) t1) t2
| Coq_tLambda n t b -> pcuic_size (a+1) 1
| Coq_tLetIn n t1 ty t2 -> pcuic_size (pcuic_size (a+1) t1) t2
| Coq_tApp t1 t2 ->  of term * term
| Coq_tConst of kername * universe_instance
| Coq_tInd of inductive * universe_instance
| Coq_tConstruct of inductive * nat * universe_instance
| Coq_tCase of (inductive * nat) * term * term * (nat * term) list
| Coq_tProj of projection * term
| Coq_tFix of term mfixpoint * nat
| Coq_tCoFix of term mfixpoint * nat
| _ -> "unimplemented" *)

let compile opts gr =
  (* get opts *)
  let cps = opts.cps in
  let olevel = coq_nat_of_int opts.opt in
  let timing = opts.time in
  
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma gr in
  let const = match gr with
    | Globnames.ConstRef c -> c
    | _ -> CErrors.user_err ~hdr:"template-coq"
       (Printer.pr_global gr ++ str" is not a constant definition") in
  Feedback.msg_debug (str"Quoting");
  let time = Unix.gettimeofday() in
  let term = quote_term_rec env (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  Feedback.msg_debug (str(Printf.sprintf "Finished quoting in %f s.. compiling to L7." time));
  let fuel = coq_nat_of_int 10000 in
  let nenv = 
    let p = Pipeline.compile cps olevel timing term in
    match p with
    | (Ret ((nenv, header), prg), inf) ->
      Feedback.msg_debug (str"Finished compiling, printing to file.");
      let time = Unix.gettimeofday() in
      (* Zoe: Make suffix appear only in testing/debugging mode *)
      let suff = if cps then "_cps" else "" ^ if olevel <> O then "_opt" else "" in
      let cstr = Quoted.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".c") in
      let hstr = Quoted.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".h") in
      Pipeline.printProg (nenv,prg) cstr;
      Pipeline.printProg (nenv,header) hstr;
      let time = (Unix.gettimeofday() -. time) in
      Feedback.msg_debug (str(Printf.sprintf "Printed to file in %f s.." time))
    | (Err s, inf) ->
      CErrors.user_err ~hdr:"template-coq" (str "Could not compile: " ++ pr_char_list s)
  in
  let time = Unix.gettimeofday() in
  (match Pipeline.make_glue term with
  | Ret (((nenv, header), prg), logs) ->
    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str (Printf.sprintf "Generated glue code in %f s.." time));
    (match logs with [] -> () | _ ->
      Feedback.msg_debug (str (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_chars logs)))));
    let time = Unix.gettimeofday() in
    let cstr = Quoted.string_to_list ("glue." ^ Names.KerName.to_string (Names.Constant.canonical const) ^ ".c") in
    let hstr = Quoted.string_to_list ("glue." ^ Names.KerName.to_string (Names.Constant.canonical const) ^ ".h") in
    Pipeline.printProg (nenv, prg) cstr;
    Pipeline.printProg (nenv, header) hstr;

    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str(Printf.sprintf "Printed glue code to file in %f s.." time))
  | Exc s ->
    CErrors.user_err ~hdr:"template-coq" (str "Could not generate glue code: " ++ pr_char_list s))

(* For emitting L6 code *)
(* let show_l6 olevel gr = *)
(*   let env = Global.env () in *)
(*   let sigma = Evd.from_env env in *)
(*   let sigma, c = Evarutil.new_global sigma gr in *)
(*   let const = match gr with *)
(*     | Globnames.ConstRef c -> c *)
(*     | _ -> CErrors.user_err ~hdr:"template-coq" *)
(*        (Printer.pr_global gr ++ str" is not a constant definition") in *)
(*   Feedback.msg_debug (str"Quoting"); *)
(*   let time = Unix.gettimeofday() in *)
(*   let term = quote_term_rec env (EConstr.to_constr sigma c) in *)
(*   let time = (Unix.gettimeofday() -. time) in *)
(*   Feedback.msg_debug (str(Printf.sprintf "Finished quoting in %f s.. compiling to L7." time)); *)
(*   let fuel = coq_nat_of_int 10000 in *)
(*   let p = AllInstances.emit_L6_anf fuel olevel term in *)
(*   match p with *)
(*   | Ret str -> *)
(*      let l6f = (Names.KerName.to_string (Names.Constant.canonical const) ^ ".l6") in *)
(*      let f = open_out l6f in *)
(*      Printf.fprintf f "%s" (string_of_chars str); *)
(*      close_out f; *)
(*   | Exc s -> *)
(*      CErrors.user_err ~hdr:"template-coq" (str "Could not compile: " ++ pr_char_list s) *)

(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Printer
open Metacoq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils

external get_unboxed_ordinal : Obj.t -> int = "get_unboxed_ordinal"
external get_boxed_ordinal : Obj.t -> int = "get_boxed_ordinal"

module Value = struct
  open Printf

type t = Obj.t

let compare = compare
let equal = (==)
let hash = Hashtbl.hash

type tag =
  | Lazy
  | Closure
  | Object
  | Infix
  | Forward
  | Block
  | Abstract
  | String
  | Double
  | Double_array
  | Custom
  | Int
  | Out_of_heap
  | Unaligned

type custom =
  | Custom_nativeint of nativeint
  | Custom_int32 of int32
  | Custom_int64 of int64
  | Custom_bigarray
  | Custom_channel
  | Custom_unknown
  | Not_custom

(* external bits : t -> nativeint = "inspect_bits" *)

let hex_digits = "0123456789ABCDEF"

let dec_of_bits v =
  sprintf "%nd" v

let hex_of_bits v =
  let (lsr) = Nativeint.shift_right in
  let (land) = Nativeint.logand in
  let ndig = Nativeint.size / 4 in
  let b = Buffer.create (2 + ndig + 1) in
  Buffer.add_string b "0x";
  for i = ndig - 1 downto 0 do
    let d = (v lsr (i * 4)) land 0xFn in
    Buffer.add_char b hex_digits.[Nativeint.to_int d]
  done;
  Buffer.contents b

let bin_of_bits v =
  let (lsr) = Nativeint.shift_right in
  let (land) = Nativeint.logand in
  let ndig = Nativeint.size in
  let b = Buffer.create (2 + ndig + 1) in
  (* three seems reasonable, prefix and maybe null? *)
  Buffer.add_string b "0b";
  for i = Sys.word_size - 1 downto 0 do
    let d = (v lsr i) land 1n in
    Buffer.add_string b (if d = 1n then "1" else "0")
  done;
  Buffer.contents b

(* let bits_to_string ?(base=`Hex) v =
  let bs = bits v in
  match base with
  | `Dec -> dec_of_bits bs
  | `Hex -> hex_of_bits bs
  | `Bin -> bin_of_bits bs *)

(* external custom_identifier : t -> string = "inspect_custom_id"

external custom_has_finalize : t -> bool = "inspect_custom_has_finalize"
external custom_has_compare : t -> bool = "inspect_custom_has_compare"
external custom_has_hash : t -> bool = "inspect_custom_has_hash"
external custom_has_serialize : t -> bool = "inspect_custom_has_serialize"
external custom_has_deserialize : t -> bool = "inspect_custom_has_deserialize" *)

(* let custom_ops_info r =
  sprintf "%c%c%c%c%c"
    (if custom_has_finalize r    then 'F' else '-')
    (if custom_has_compare r     then 'C' else '-')
    (if custom_has_hash r        then 'H' else '-')
    (if custom_has_serialize r   then 'S' else '-')
    (if custom_has_deserialize r then 'D' else '-') *)

let nativeint_id = "_n"
let int32_id = "_i"
let int64_id = "_j"
let bigarray_id = "_bigarray"
let channel_id = "_chan"

module TagSet =
struct
  include Set.Make(struct type t = tag let compare = compare end)

  let of_list tlist =
    List.fold_left (fun s t -> add t s) empty tlist

  let all =
    of_list [
      Lazy;
      Closure;
      Object;
      Infix;
      Forward;
      Block;
      Abstract;
      String;
      Double;
      Double_array;
      Custom;
      Int;
      Out_of_heap;
      Unaligned;
    ]
end

(* Make sure the known custom identifiers are in sync. *)
let _ =
  let rnat = Obj.repr 0n and ri32 = Obj.repr 0l and ri64 = Obj.repr 0L in
    assert (Obj.tag rnat = Obj.custom_tag);
    assert (Obj.tag ri32 = Obj.custom_tag);
    assert (Obj.tag ri64 = Obj.custom_tag);
    (* assert (nativeint_id = custom_identifier rnat);
    assert (int32_id = custom_identifier ri32);
    assert (int64_id = custom_identifier ri64);
    (* assert (bigarray_id = custom_identifier ...); *)
    assert (channel_id = custom_identifier (Obj.repr stdout)); *)
    ()

let custom_value r =
  if Obj.tag r = Obj.custom_tag then (
    
	Custom_unknown
  )
  else
    Not_custom

let custom_is_int r =
  match custom_value r with
    | Custom_nativeint _ -> false
    | Custom_int32 _ -> true
    | Custom_int64 _ ->	true
    | _ -> false

(* Matching an integer value should be faster than a series of if
   statements.
   That's why all these assertions are here, to make sure
   that the integer literals used in the match statement actually
   correspond to the tags defined by the Obj module. *)
let _ =
  assert (Obj.lazy_tag = 246);
  assert (Obj.closure_tag = 247);
  assert (Obj.object_tag = 248);
  assert (Obj.infix_tag = 249);
  assert (Obj.forward_tag = 250);
  assert (Obj.no_scan_tag = 251);
  assert (Obj.abstract_tag = 251);
  assert (Obj.string_tag = 252);
  assert (Obj.double_tag = 253);
  assert (Obj.double_array_tag = 254);
  assert (Obj.custom_tag = 255);
  assert (Obj.int_tag = 1000);
  assert (Obj.out_of_heap_tag = 1001);
  assert (Obj.unaligned_tag = 1002);
  ()

(* Slower and safer.
let value_tag r =
  match tag r with
    | x when x = lazy_tag -> Lazy
    | x when x = closure_tag -> Closure
    | x when x = object_tag -> Object
    | x when x = infix_tag -> Infix
    | x when x = forward_tag -> Forward
    | x when x < no_scan_tag -> Block
    | x when x = abstract_tag -> Abstract
    | x when x = string_tag -> String
    | x when x = double_tag -> Double
    | x when x = double_array_tag -> Double_array
    | x when x = custom_tag -> Custom
    | x when x = int_tag -> Int
    | x when x = out_of_heap_tag -> Out_of_heap
    | x when x = unaligned_tag -> Unaligned
    | x -> failwith (sprintf "OCaml value with unknown tag = %d" x)
*)

(* Faster but more dangerous *)
let tag r =
  match Obj.tag r with
    | x when x < 246 -> Block
    | 246 -> Lazy
    | 247 -> Closure
    | 248 -> Object
    | 249 -> Infix
    | 250 -> Forward
    | 251 -> Abstract
    | 252 -> String
    | 253 -> Double
    | 254 -> Double_array
    | 255 -> Custom
    | 1000 -> Int
    | 1001 -> Out_of_heap
    | 1002 -> Unaligned
    | x -> failwith (sprintf "OCaml value with unknown tag = %d" x)

(* Slower? and safer
let is_in_heap r =
  let x = Obj.tag r in
    not (x = Obj.int_tag || x = Obj.out_of_heap_tag || x = Obj.unaligned_tag)
*)

(* Faster but more dangerous *)
let is_in_heap r =
  let x = Obj.tag r in
    x < 1000 || 1002 < x

let heap_words r =
  if is_in_heap r then Obj.size r else 0

let mnemonic r =
  match tag r with
    | Lazy -> "LAZY"
    | Closure -> "CLOS"
    | Object -> "OBJ"
    | Infix -> "INFX"
    | Forward -> "FWD"
    | Block -> "BLK"
    | Abstract -> "ABST"
    | String -> "STR"
    | Double -> "DBL"
    | Double_array -> "DBLA"
    | Custom -> "CUST"
    | Int -> "INT"
    | Out_of_heap -> "OADR"
    | Unaligned -> "UADR"

let mnemonic_unknown =
  "????"

let abbrev r =
  match tag r with
    | Lazy
    | Closure
    | Object
    | Infix
    | Forward
    | Block
    | Double_array
    | String
    | Abstract     -> sprintf "%s#%d" (mnemonic r) (heap_words r)
    | Double       -> sprintf "%g" (Obj.magic r : float)
    | Custom       -> (
	match custom_value r with
	  | Custom_nativeint n -> sprintf "%ndn" n
	  | Custom_int32 i     -> sprintf "%ldl" i
	  | Custom_int64 i     -> sprintf "%LdL" i
	  | Custom_bigarray    -> "Bigarray"
	  | Custom_channel     -> "Channel"
	  | Custom_unknown     -> sprintf "Unknown"
	  | Not_custom         -> failwith "Value.description: should be a custom value"
      )
    | Int          -> string_of_int (Obj.magic r : int)
    | Out_of_heap  -> "Out_of_heap"
    | Unaligned    -> "Unaligned"

let description r =
  match tag r with
    | Lazy         -> "Lazy: #" ^ string_of_int (Obj.size r)
    | Closure      -> "Closure: #" ^ string_of_int (Obj.size r)
    | Object       -> "Object: #" ^ string_of_int (Obj.size r)
    | Infix        -> "Infix: #" ^ string_of_int (Obj.size r)
    | Forward      -> "Forward: #" ^ string_of_int (Obj.size r)
    | Block        -> sprintf "Block(%d): #%d" (Obj.tag r) (Obj.size r)
    | Abstract     -> "Abstract: #" ^ string_of_int (Obj.size r)
    | String       ->
        let len = String.length (Obj.magic r : string) in
        sprintf "String: %d char%s" len (if len > 1 then "s" else "")
    | Double       -> sprintf "Double: %g" (Obj.magic r : float)
    | Double_array -> sprintf "Double_array: %d floats" (Array.length (Obj.magic r : float array))
    | Custom       -> (
	match custom_value r with
	  | Custom_nativeint n -> sprintf "Nativeint: %nd" n
	  | Custom_int32 i     -> sprintf "Int32: %ld" i
	  | Custom_int64 i     -> sprintf "Int64: %Ld" i
	  | Custom_bigarray    -> "Bigarray"
	  | Custom_channel     -> "Channel"
	  | Custom_unknown     -> sprintf "Custom:"
	  | Not_custom         -> failwith "Value.description: should be a custom value"
      )
    | Int          -> sprintf "Int: %d" (Obj.magic r : int)
    | Out_of_heap  -> sprintf "Out_of_heap "
    | Unaligned    -> sprintf "Unaligned "

end

(** Various Utils *)

let pr_string s = Pp.str (Caml_bytestring.caml_string_of_bytestring s)

(* remove duplicates but preserve order, keep the leftmost element *)
let nub (xs : 'a list) : 'a list = 
  List.fold_right (fun x xs -> if List.mem x xs then xs else x :: xs) xs []

let rec coq_nat_of_int x =
  match x with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (coq_nat_of_int (pred n))

let debug_msg (flag : bool) (s : string) =
  if flag then
    Feedback.msg_debug (Pp.str s)
  else ()

(* Separate registration of primitive extraction *)

type prim = ((Kernames.kername * Kernames.ident) * bool)
let global_registers = 
  Summary.ref (([], []) : prim list * import list) ~name:"CertiCoq Registration"

let global_registers_name = "certicoq-registration"

let cache_registers (prims, imports) =
  let (prims', imports') = !global_registers in
  global_registers := (prims @ prims', imports @ imports')
let global_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_registers_name
    ~cache:(fun r -> cache_registers r)
    ~subst:None) (*(fun (msub, r) -> r)) *)

let register (prims : prim list) (imports : import list) : unit =
  let curlib = Sys.getcwd () in
  let newr = (prims, List.map (fun i -> 
    match i with
    | FromAbsolutePath s -> FromRelativePath (Filename.concat curlib s)
    | _ -> i) imports) in
  (* Feedback.msg_debug Pp.(str"Prims: " ++ prlist_with_sep spc (fun ((x, y), wt) -> str (string_of_bytestring y)) (fst newr)); *)
  Lib.add_leaf (global_registers_input newr)

let get_global_prims () = fst !global_registers
let get_global_includes () = snd !global_registers

(* Support for dynamically-linked certicoq-compiled programs *)
type certicoq_run_function = Ast0.Env.global_env -> typ:Ast0.term -> Obj.t

let certicoq_run_functions = 
  Summary.ref ~name:"CertiCoq Run Functions Table" 
    (CString.Map.empty : certicoq_run_function CString.Map.t)

let certicoq_run_functions_name = "certicoq-run-functions-registration"

let cache_certicoq_run_function (s, fn) =
  let fns = !certicoq_run_functions in
  certicoq_run_functions := CString.Map.add s fn fns

let certicoq_run_function_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge certicoq_run_functions_name
    ~cache:(fun r -> cache_certicoq_run_function r)
    ~subst:None)

let register_certicoq_run s fn =
  Lib.add_leaf (certicoq_run_function_input (s, fn))

let run_certicoq_run s = 
  try CString.Map.find s !certicoq_run_functions
  with Not_found -> CErrors.user_err Pp.(str"Could not find certicoq run function associated to " ++ str s)

(** Coq FFI: message channels and raising user errors. *)

let coq_msg_info s =
  let s = Caml_bytestring.caml_string_of_bytestring s in
  Feedback.msg_info (Pp.str s)
  
let _ = Callback.register "coq_msg_info" coq_msg_info

let coq_msg_debug s = 
  Feedback.msg_debug Pp.(str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "coq_msg_debug" coq_msg_debug

let coq_msg_notice s = 
  Feedback.msg_notice Pp.(str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "coq_msg_notice" coq_msg_notice
  
let coq_user_error s =
  CErrors.user_err Pp.(str (Caml_bytestring.caml_string_of_bytestring s))

let _ = Callback.register "coq_user_error" coq_user_error 

(** Compilation Command Arguments *)

type command_args =
 | BYPASS_QED
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int
 | ANFCONFIG of int (* To measure different ANF configurations *)
 | BUILDDIR of string (* Directory name to be prepended to the file name *)
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int    (* For development purposes *)
 | PREFIX of string (* Prefix to add to the generated FFI fns, avoids clashes with C fns *)
 | FILENAME of string (* Name of the generated file *)

type options =
  { bypass_qed : bool;
    cps       : bool;
    time      : bool;
    time_anf  : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    anf_conf  : int;
    build_dir : string;
    filename  : string;
    ext       : string;
    dev       : int;
    prefix    : string;
    prims     : ((Kernames.kername * Kernames.ident) * bool) list;
  }

let default_options : options =
  { bypass_qed = false;
    cps       = false;
    time      = false;
    time_anf  = false;
    olevel    = 1;
    debug     = false;
    args      = 5;
    anf_conf  = 0;
    build_dir = ".";
    filename  = "";
    ext       = "";
    dev       = 0;
    prefix    = "";
    prims     = [];
  }

let check_build_dir d =
  if d = "" then "." else
  let isdir = 
    try Unix.((stat d).st_kind = S_DIR)
    with Unix.Unix_error (Unix.ENOENT, _, _) ->
      CErrors.user_err Pp.(str "Could not compile: build directory " ++ str d ++ str " not found.")
  in
  if not isdir then 
    CErrors.user_err Pp.(str "Could not compile: " ++ str d ++ str " is not a directory.")
  else d

let make_options (l : command_args list) (pr : ((Kernames.kername * Kernames.ident) * bool) list) (fname : string) : options =
  let rec aux (o : options) l =
    match l with
    | [] -> o
    | BYPASS_QED :: xs -> aux {o with bypass_qed = true} xs
    | CPS      :: xs -> aux {o with cps = true} xs
    | TIME     :: xs -> aux {o with time = true} xs
    | TIMEANF  :: xs -> aux {o with time_anf = true} xs
    | OPT n    :: xs -> aux {o with olevel = n} xs
    | DEBUG    :: xs -> aux {o with debug = true} xs
    | ARGS n   :: xs -> aux {o with args = n} xs
    | ANFCONFIG n :: xs -> aux {o with anf_conf = n} xs
    | BUILDDIR s  :: xs ->
      let s = check_build_dir s in
      aux {o with build_dir = s} xs
    | EXT s    :: xs -> aux {o with ext = s} xs
    | DEV n    :: xs -> aux {o with dev = n} xs
    | PREFIX s :: xs -> aux {o with prefix = s} xs
    | FILENAME s :: xs -> aux {o with filename = s} xs
  in
  let opts = { default_options with filename = fname } in
  let o = aux opts l in
  {o with prims = pr}

let make_pipeline_options (opts : options) =
  let cps    = opts.cps in
  let args = coq_nat_of_int opts.args in
  let olevel = coq_nat_of_int opts.olevel in
  let timing = opts.time in
  let timing_anf = opts.time_anf in
  let debug  = opts.debug in
  let anfc = coq_nat_of_int opts.anf_conf in
  let dev = coq_nat_of_int opts.dev in
  let prefix = bytestring_of_string opts.prefix in
  let prims = get_global_prims () @ opts.prims in
  (* Feedback.msg_debug Pp.(str"Prims: " ++ prlist_with_sep spc (fun ((x, y), wt) -> str (string_of_bytestring y)) prims); *)
  Pipeline.make_opts cps args anfc olevel timing timing_anf debug dev prefix prims

(** Main Compilation Functions *)

(* Get fully qualified name of a constant *)
let get_name (gr : Names.GlobRef.t) : string =
  match gr with
  | Names.GlobRef.ConstRef c -> Names.KerName.to_string (Names.Constant.canonical c)
  | _ -> CErrors.user_err Pp.(Printer.pr_global gr ++ str " is not a constant definition")


(* Quote Coq term *)
let quote opts gr =
  let debug = opts.debug in
  let bypass = opts.bypass_qed in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = Metacoq_template_plugin.Ast_quoter.quote_term_rec ~bypass env sigma (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.. compiling to L7." time);
  term

(* Compile Quoted term with CertiCoq *)

module type CompilerInterface = sig
  type name_env
  val compile : Pipeline_utils.coq_Options -> Ast0.Env.program -> ((name_env * Clight.program) * Clight.program) CompM.error * Bytestring.String.t
  val printProg : Clight.program -> name_env -> string -> import list -> unit

  val generate_glue : Pipeline_utils.coq_Options -> Ast0.Env.global_declarations -> 
    (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
  
  val generate_ffi :
    Pipeline_utils.coq_Options -> Ast0.Env.program -> (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
  
end

module MLCompiler : CompilerInterface with 
  type name_env = BasicAst.name Cps.M.t
  = struct
  type name_env = BasicAst.name Cps.M.t
  let compile = Pipeline.compile
  let printProg prog names (dest : string) (imports : import list) =
    let imports' = List.map (fun i -> match i with
      | FromRelativePath s -> "#include \"" ^ s ^ "\""
      | FromLibrary s -> "#include <" ^ s ^ ">"
      | FromAbsolutePath s ->
          failwith "Import with absolute path should have been filled") imports in
    PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'
  let generate_glue = Glue.generate_glue
  let generate_ffi = Ffi.generate_ffi
end


module CompileFunctor (CI : CompilerInterface) = struct

  let make_fname opts str =
    Filename.concat opts.build_dir str

  let compile opts term imports =
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let runtime_imports = [FromLibrary (if opts.cps then "gc.h" else "gc_stack.h")] in
    let curlib = Sys.getcwd () in
    let imports = List.map (fun i -> 
      match i with
      | FromAbsolutePath s -> FromRelativePath (Filename.concat curlib s)
      | _ -> i) imports in
    let imports = runtime_imports @ get_global_includes () @ imports in
    let p = CI.compile options term in
    match p with
    | (CompM.Ret ((nenv, header), prg), dbg) ->
      debug_msg debug "Finished compiling, printing to file.";
      let time = Unix.gettimeofday() in
      let fname = opts.filename in
      let suff = opts.ext in
      let cstr = fname ^ suff ^ ".c" in
      let hstr = fname ^ suff ^ ".h" in
      let cstr' = make_fname opts cstr in
      let hstr' = make_fname opts hstr in
      CI.printProg prg nenv cstr' (imports @ [FromRelativePath hstr]);
      CI.printProg header nenv hstr' (runtime_imports);

      (* let cstr = Metacoq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".c") in
      * let hstr = Metacoq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".h") in
      * Pipeline.printProg (nenv,prg) cstr;
      * Pipeline.printProg (nenv,header) hstr; *)
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed to file %s in %f s.." cstr' time);
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg)
    | (CompM.Err s, dbg) ->
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg);
      CErrors.user_err Pp.(str "Could not compile: " ++ (pr_string s) ++ str "\n")


  (* Generate glue code for the compiled program *)
  let generate_glue (standalone : bool) opts globs =
    if standalone && opts.filename = "" then
      CErrors.user_err Pp.(str "You need to provide a file name with the -file option.")
    else
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let runtime_imports = 
      [ FromLibrary (if opts.cps then "gc.h" else "gc_stack.h"); FromLibrary "stdio.h" ] in
    let time = Unix.gettimeofday() in
    (match CI.generate_glue options globs with
    | CompM.Ret (((nenv, header), prg), logs) ->
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Generated glue code in %f s.." time);
      (match logs with [] -> () | _ ->
        debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_bytestring logs))));
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let fname = opts.filename in
      let cstr = if standalone then fname ^ ".c" else "glue." ^ fname ^ suff ^ ".c" in
      let hstr = if standalone then fname ^ ".h" else "glue." ^ fname ^ suff ^ ".h" in
      let cstr' = make_fname opts cstr in
      let hstr' = make_fname opts hstr in
      CI.printProg prg nenv cstr' (runtime_imports @ [FromRelativePath hstr]);
      CI.printProg header nenv hstr' runtime_imports;

      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed glue code to file %s in %f s.." cstr time)
    | CompM.Err s ->
      CErrors.user_err Pp.(str "Could not generate glue code: " ++ pr_string s))

  let compile_only (opts : options) (gr : Names.GlobRef.t) (imports : import list) : unit =
    let term = quote opts gr in
    compile opts (Obj.magic term) imports

  let generate_glue_only opts gr =
    let term = quote opts gr in
    generate_glue true opts (Ast0.Env.declarations (fst (Obj.magic term)))
    
  let find_executable debug cmd = 
    let whichcmd = Unix.open_process_in cmd in
    let result = 
      try Stdlib.input_line whichcmd 
      with End_of_file -> ""
    in
    let status = Unix.close_process_in whichcmd in
    match status with
    | Unix.WEXITED 0 -> 
      if debug then Feedback.msg_debug Pp.(str "Compiler is " ++ str result);
      result
    | _ -> failwith "Compiler not found"

  let compiler_executable debug = find_executable debug "which gcc || which clang-11"
  
  type line = 
    | EOF
    | Info of string
    | Error of string

  let read_line stdout stderr =
    try Info (input_line stdout)
    with End_of_file -> 
      try Error (input_line stderr)
      with End_of_file -> EOF
  
  let run_program debug prog =
    let (stdout, stdin, stderr) = Unix.open_process_full ("./" ^ prog) (Unix.environment ()) in
    let continue = ref true in
    while !continue do 
      match read_line stdout stderr with
      | EOF -> debug_msg debug ("Program terminated"); continue := false
      | Info s -> Feedback.msg_notice Pp.(str prog ++ str": " ++ str s)
      | Error s -> Feedback.msg_warning Pp.(str prog ++ str": " ++ str s)
    done

  let runtime_dir () = 
    let open Boot in
    let env = Env.init () in
    Path.relative (Path.relative (Path.relative (Env.user_contrib env) "CertiCoq") "Plugin") "runtime"

  let make_rt_file na =
    Boot.Env.Path.(to_string (relative (runtime_dir ()) na))

  let compile_C opts gr imports =
    let () = compile_only opts gr imports in
    let imports = get_global_includes () @ imports in
    let debug = opts.debug in
    let fname = opts.filename in
    let suff = opts.ext in
    let name = make_fname opts (fname ^ suff) in
    let compiler = compiler_executable debug in
    let rt_dir = runtime_dir () in
    let cmd =
        Printf.sprintf "%s -Wno-everything -g -I %s -I %s -c -o %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) (name ^ ".o") (name ^ ".c") 
    in
    let importso =
      let oname s = 
        assert (CString.is_suffix ".h" s);
        String.sub s 0 (String.length s - 2) ^ ".o"
      in 
      let imports' = List.concat (List.map (fun i -> 
        match i with 
        | FromAbsolutePath s -> [oname s]
        | FromRelativePath s -> [oname s]
        | FromLibrary s -> [make_rt_file (oname s)]) imports) in
      let l = make_rt_file "certicoq_run_main.o" :: imports' in
      String.concat " " l
    in
    let gc_stack_o = make_rt_file "gc_stack.o" in
    debug_msg debug (Printf.sprintf "Executing command: %s" cmd);
    match Unix.system cmd with
    | Unix.WEXITED 0 -> 
      let linkcmd =
        Printf.sprintf "%s -Wno-everything -g -L %s -L %s -o %s %s %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) name gc_stack_o (name ^ ".o") importso
      in
      debug_msg debug (Printf.sprintf "Executing command: %s" linkcmd);
      (match Unix.system linkcmd with
      | Unix.WEXITED 0 ->
          debug_msg debug (Printf.sprintf "Compilation ran fine, running %s" name);
          run_program debug name
      | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str linkcmd)
      | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n))
    | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str cmd)
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n  ++ str" while running " ++ str cmd)
  

  let ocamlfind_executable _debug = 
    "_opam/bin/ocamlfind"
    (* find_executable debug "which ocamlfind"  *)

  type reifyable_type =
  | IsInductive of Names.inductive * Univ.Instance.t * Constr.t list
  | IsPrimitive of Names.Constant.t * Univ.Instance.t
  
  let find_nth_constant n ar =
    let open Inductiveops in
    let rec aux i const = 
      if Array.length ar <= i then raise Not_found
      else if CList.is_empty ar.(i).cs_args then  (* FIXME lets in constructors *)
        if const = n then i 
        else aux (i + 1) (const + 1)
      else aux (i + 1) const
    in aux 0 0
  
  let find_nth_non_constant n ar =
    let open Inductiveops in
    let rec aux i nconst = 
      if Array.length ar <= i then raise Not_found
      else if not (CList.is_empty ar.(i).cs_args) then 
        if nconst = n then i 
        else aux (i + 1) (nconst + 1)
      else aux (i + 1) nconst
    in aux 0 0

  let check_reifyable env sigma ty =
    (* We might have bound universes though. It's fine! *)
    try let (hd, u), args = Inductiveops.find_inductive env sigma ty in
      IsInductive (hd, EConstr.EInstance.kind sigma u, args)
    with Not_found -> 
      match EConstr.kind sigma (Reductionops.whd_all env sigma ty) with
      | Const (c, u) when Environ.is_primitive_type env c -> 
        IsPrimitive (c, EConstr.EInstance.kind sigma u)
      | _ -> CErrors.user_err 
        Pp.(str"Cannot reify values of non-inductive or non-primitive type: " ++ 
          Printer.pr_econstr_env env sigma ty)

  let reify debug env sigma ty v : Constr.t = 
    let open Declarations in
    let rec aux ty v =
    match ty with
    | IsInductive (hd, u, args) -> 
      let open Inductive in
      let open Inductiveops in
      let spec = lookup_mind_specif env hd in
      let indfam = make_ind_family ((hd, u), args) in
      let npars = inductive_params spec in
      let params, _indices = CList.chop npars args in
      let cstrs = get_constructors env indfam in
      let () = debug_msg true (Printf.sprintf "Reifying inductive value") in
      if Obj.is_block v then
        let () = debug_msg true (Printf.sprintf "Reifying constructor block") in
        let ord = get_boxed_ordinal v in
        (*if not (0 <= otag && otag < Obj.no_scan_tag) thenm
          CErrors.user_err Pp.(str "reify: Unexpected value tag: " ++ int otag); *)
        let () = debug_msg debug (Printf.sprintf "Reifying constructor block of tag %i" ord) in
        let coqidx = find_nth_non_constant ord cstrs in
        let cstr = cstrs.(coqidx) in
        let ctx = Vars.smash_rel_context cstr.cs_args in
        let vargs = List.init (List.length ctx) (Obj.field v) in
        let args' = List.map2 (fun decl v -> 
          let argty = check_reifyable env sigma 
          (EConstr.of_constr (Context.Rel.Declaration.get_type decl)) in
          aux argty v) (List.rev ctx) vargs in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) (params @ args')
      else (* Constant constructor *)
        let () = debug_msg debug (Printf.sprintf "Reifying constant constructor") in
        let ord = (Obj.magic v : int) in
        let () = debug_msg debug (Printf.sprintf "Reifying constant constructor: %i" ord) in
        let coqidx = find_nth_constant ord cstrs in
        let () = debug_msg debug (Printf.sprintf "Reifying constant constructor: %i is %i in Coq" ord coqidx) in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) params
    | IsPrimitive (c, u) -> 
      if Environ.is_array_type env c then 
        CErrors.user_err Pp.(str "Primitive arrays are not supported yet")
      else if Environ.is_float64_type env c then
        Constr.mkFloat (Obj.magic v)
      else if Environ.is_int63_type env c then
        Constr.mkInt (Obj.magic v)
      else CErrors.user_err Pp.(str "Unsupported primitive type")
    in aux ty v

  let compile_shared_C opts gr imports =
    let prog = quote opts gr in
    let env = Global.env () in
    let sigma, tyinfo = 
      let sigma = Evd.from_env env in 
      let sigma, frgr = Evd.fresh_global env sigma gr in
      let sigma, ty = Typing.type_of env sigma frgr in
      assert (Evd.is_empty sigma);
      sigma, check_reifyable env sigma ty
    in
    let () = compile opts (Obj.magic prog) imports in
    let () = compile_only opts gr imports in
    let imports = get_global_includes () @ imports in
    let debug = opts.debug in
    let fname = opts.filename in
    let suff = opts.ext in
    let name = make_fname opts (fname ^ suff) in
    let compiler = compiler_executable debug in
    let ocamlfind = ocamlfind_executable debug in
    let rt_dir = runtime_dir () in
    let cmd =
        Printf.sprintf "%s -Wno-everything -g -I %s -I %s -c -o %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) (name ^ ".o") (name ^ ".c") 
    in
    let importso =
      let oname s = 
        assert (CString.is_suffix ".h" s);
        String.sub s 0 (String.length s - 2) ^ ".o"
      in 
      let imports' = List.concat (List.map (fun i -> 
        match i with 
        | FromAbsolutePath s -> [oname s]
        | FromRelativePath s -> [oname s]
        | FromLibrary s -> [make_rt_file (oname s)]) imports) in
      let l = make_rt_file "certicoq_run.o" :: imports' in
      String.concat " " l
    in
    let gc_stack_o = make_rt_file "gc_stack.o" in
    debug_msg debug (Printf.sprintf "Executing command: %s" cmd);
    let packages = ["coq-core"; "coq-core.plugins.ltac"; "coq-metacoq-template-ocaml"; 
      "coq-core.interp"; "coq-core.kernel"; "coq-core.library"] in
    let pkgs = String.concat "," packages in
    let dontlink = "str,unix,dynlink,threads,zarith,coq-core,coq-core.plugins.ltac,coq-core.interp" in
    match Unix.system cmd with
    | Unix.WEXITED 0 -> 
      let shared_lib = name ^ ".cmxs" in 
      let linkcmd =
        Printf.sprintf "%s ocamlopt -shared -linkpkg -dontlink %s -thread -rectypes -package %s \
        -I . -I %s -o %s %s %s %s %s"
        ocamlfind dontlink pkgs opts.build_dir shared_lib (make_rt_file "certicoq_run_wrapper.cmx") gc_stack_o (name ^ ".o") importso
      in
      debug_msg debug (Printf.sprintf "Executing command: %s" linkcmd);
      (match Unix.system linkcmd with
      | Unix.WEXITED 0 ->
          debug_msg debug (Printf.sprintf "Compilation ran fine, linking compiled code for %s" name);
          Dynlink.loadfile_private shared_lib;
          debug_msg debug (Printf.sprintf "Dynamic linking succeeded, retrieving function %s" name);
          let result = run_certicoq_run "certicoq_run" (fst (Obj.magic prog)) ~typ:(snd (Obj.magic prog)) (* FIXME we should get the type*) in
          debug_msg debug (Printf.sprintf "Running they dynamic linked program succeeded, reifying result");
          reify debug env sigma tyinfo result
      | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str linkcmd)
      | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n))
    | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str cmd)
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n  ++ str" while running " ++ str cmd)
  

  let print_to_file (s : string) (file : string) =
    let f = open_out file in
    Printf.fprintf f "%s\n" s;
    close_out f

  let show_ir opts gr =
    let term = quote opts gr in
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let p = Pipeline.show_IR options (Obj.magic term) in
    match p with
    | (CompM.Ret prg, dbg) ->
      debug_msg debug "Finished compiling, printing to file.";
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let fname = opts.filename in
      let file = fname ^ suff ^ ".ir" in
      print_to_file (string_of_bytestring prg) file;
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed to file %s in %f s.." file time);
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg)
    | (CompM.Err s, dbg) ->
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg);
      CErrors.user_err Pp.(str "Could not compile: " ++ (pr_string s) ++ str "\n")


  (* Quote Coq inductive type *)
  let quote_ind opts gr : Metacoq_template_plugin.Ast_quoter.quoted_program * string =
    let debug = opts.debug in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, c = Evd.fresh_global env sigma gr in
    let name = match gr with
      | Names.GlobRef.IndRef i -> 
          let (mut, _) = i in
          Names.KerName.to_string (Names.MutInd.canonical mut)
      | _ -> CErrors.user_err
        Pp.(Printer.pr_global gr ++ str " is not an inductive type") in
    debug_msg debug "Quoting";
    let time = Unix.gettimeofday() in
    let term = quote_term_rec ~bypass:true env sigma (EConstr.to_constr sigma c) in
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Finished quoting in %f s.." time);
    (term, name)

  let ffi_command opts gr =
    let (term, name) = quote_ind opts gr in
    let debug = opts.debug in
    let options = make_pipeline_options opts in

    let time = Unix.gettimeofday() in
    (match CI.generate_ffi options (Obj.magic term) with
    | CompM.Ret (((nenv, header), prg), logs) ->
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Generated FFI glue code in %f s.." time);
      (match logs with [] -> () | _ ->
        debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_bytestring logs))));
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let cstr = ("ffi." ^ name ^ suff ^ ".c") in
      let hstr = ("ffi." ^ name ^ suff ^ ".h") in
      CI.printProg prg nenv cstr [];
      CI.printProg header nenv hstr [];

      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed FFI glue code to file in %f s.." time)
    | CompM.Err s ->
      CErrors.user_err Pp.(str "Could not generate FFI glue code: " ++ pr_string s))

  let glue_command opts grs =
    let terms = grs |> List.rev
                |> List.map (fun gr -> Metacoq_template_plugin.Ast0.Env.declarations (fst (quote opts gr))) 
                |> List.concat |> nub in
    generate_glue true opts (Obj.magic terms)

end

module MLCompile = CompileFunctor (MLCompiler)
include MLCompile

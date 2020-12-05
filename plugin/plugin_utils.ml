open Ast_quoter
open Names
open Pp


(* Various utils *)

let string_of_chars (chars : char list) : string =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let chars_of_string (s : string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


(* From GlobRef to kername *)

let extract_constant (g : Names.GlobRef.t) (s : string) : (BasicAst.kername * char list)  =
  match g with
  | Names.GlobRef.ConstRef c -> (quote_kn (Names.Constant.canonical c), chars_of_string s)
  | Names.GlobRef.VarRef(v) -> CErrors.user_err ~hdr:"extract-constant" (str "Expected a constant but found a variable. Only constants can be realized in C.")
  | Names.GlobRef.IndRef(i) -> CErrors.user_err ~hdr:"extract-constant" (str "Expected a constant but found an inductive type. Only constants can be realized in C.")
  | Names.GlobRef.ConstructRef(c) -> CErrors.user_err ~hdr:"extract-constant" (str "Expected a constant but found a constructor. Only constants can be realized in C. ")

let rec debug_mappings (ms : (BasicAst.kername * char list) list) : unit =
  match ms with
  | [] -> ()
  | (k, s) :: ms ->     
     Feedback.msg_debug (str ("Kername: " ^ (string_of_chars (BasicAst.string_of_kername k)) ^ " C: "  ^ (string_of_chars s)));
     debug_mappings ms
     
(* Help message *)
     
let help_msg : string =
  "Usage:\n\
To compile an program named <gid> type:\n\
   CertiCoq Compile [options] <gid>.\n\n\
To show this help message type:\n\
   CertiCoq -help.\n\n\
To produce an .ir file with the last IR (lambda-anf) of the compiler type:\n\
   CertiCoq Show IR [options] <global_identifier>.\n\n\
Valid options:\n\
-direct   :  Produce direct-style code (as opposed to he default which is continuation-passing style)\n\
-time     :  Time each compilation phase\n\
-time_anf :  Time λanf optimizations\n\
-O n      :  Perform more aggressive optimizations. 1: lambda lifting for closure environment unboxing, 2: lambda lifting and inling for lambda lifting shells\n\
-debug    :  Show debugging information\n\
-args X   :  Specify how many arguments are used in the C translation (on top of the thread_info argument)\n\
-ext S    :  Specify the string s to be appended to the file name\n\
-prefix S :  Specify the string s to be prepended to the FFI functions (to avoid clashes with C functions)\n\
\n\
To show this help message type:\n\
CertiCoq -help.\n"


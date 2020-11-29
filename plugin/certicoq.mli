type command_args =
 | ANF
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int 
 | ANFCONFIG of int (* The number of fvs passed as params and the original params shall not exceed this number *)
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int
 | PREFIX of string (* Prefix to add to the generated FFI fns, avoids clashes with C fns *)

type options =
  { cps       : bool;
    time      : bool;
    time_anf  : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    anf_conf  : int;
    ext       : string;
    dev       : int;
    prefix    : string;
    prims     : ((BasicAst.kername * char list) * Datatypes.nat) list;
  }

val default_options : options
val make_options : command_args list -> ((BasicAst.kername * char list) * Datatypes.nat) list -> options

val compile_with_glue : options -> Names.GlobRef.t -> unit
val compile_only : options -> Names.GlobRef.t -> unit
val generate_glue_only : options -> Names.GlobRef.t -> unit
val show_ir : options -> Names.GlobRef.t -> unit
val ffi_command : options -> Names.GlobRef.t -> unit

type command_args =
 | ANF
 | TIME
 | OPT of int
 | DEBUG
 | ARGS of int 
 | FVARGS of int (* The number of fvs passed as params and the original params shall not exceed this number *)
 | EXT of string (* Filename extension to be appended to the file name *)

type options =
  { cps       : bool;
    time      : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    fv_args   : int;
    ext       : string;
  }

val default_options : options
val make_options : command_args list -> options
val help_msg : string

val compile_with_glue : options -> Names.GlobRef.t -> unit
val compile_only : options -> Names.GlobRef.t -> unit
val generate_glue_only : options -> Names.GlobRef.t -> unit
val show_ir : options -> Names.GlobRef.t -> unit

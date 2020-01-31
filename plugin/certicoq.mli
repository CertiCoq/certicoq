type command_args =
 | ANF
 | TIME
 | OPT of int
 | DEBUG
 | ARGS of int 

type options =
  { cps       : bool;
    time      : bool;
    olevel : int;
    debug     : bool;
    args      : int;
  }

type 'a error = Res of 'a | Error of string

val default_options : options
val make_options : command_args list -> options error
val options_help : string

val compile_with_glue : options -> Names.GlobRef.t -> unit
val compile_only : options -> Names.GlobRef.t -> unit
val generate_glue_only : options -> Names.GlobRef.t -> unit
val show_ir : options -> Names.GlobRef.t -> unit

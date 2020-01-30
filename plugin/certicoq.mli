type command_args =
 | ANF
 | TIME
 | OPT of int
 | DEBUG
 | ARGS of int 

type options =
  { cps  : bool;
    time : bool;
    opt  : int;
    debug : bool;
    args  : int;
  }

type 'a error = Res of 'a | Error of string

val default_options : options
val make_options : command_args list -> options error
val options_help : string
val compile : options -> Globnames.global_reference -> unit

(* val show_l6 : Metacoq_template_plugin.Datatypes.nat -> Globnames.global_reference -> unit *)

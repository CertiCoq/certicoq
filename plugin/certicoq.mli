
type options =
  { cps  : bool;
    time : bool;
    opt  : int;
    debug : bool;
  }

type 'a error = Res of 'a | Error of string

val default_options : options
val parse_options : string list -> options error
val options_help : string
val compile : options -> Globnames.global_reference -> unit

(* val show_l6 : Metacoq_template_plugin.Datatypes.nat -> Globnames.global_reference -> unit *)

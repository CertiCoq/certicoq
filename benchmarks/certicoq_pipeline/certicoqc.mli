open Certicoq_plugin

val compile_with_glue : Certicoq.options -> Names.GlobRef.t -> string list -> unit
val compile_only : Certicoq.options -> Names.GlobRef.t -> string list -> unit
val generate_glue_only : Certicoq.options -> Names.GlobRef.t -> unit
val show_ir : Certicoq.options -> Names.GlobRef.t -> unit
val ffi_command : Certicoq.options -> Names.GlobRef.t -> unit
val glue_command : Certicoq.options -> Names.GlobRef.t list -> unit

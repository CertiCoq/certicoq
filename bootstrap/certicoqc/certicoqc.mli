open Certicoq_vanilla_plugin

val compile_only : Certicoq.options -> Names.GlobRef.t -> (string * bool) list -> unit
val compile_C : Certicoq.options -> Names.GlobRef.t -> (string * bool) list -> unit
val generate_glue_only : Certicoq.options -> Names.GlobRef.t -> unit
val show_ir : Certicoq.options -> Names.GlobRef.t -> unit
val ffi_command : Certicoq.options -> Names.GlobRef.t -> unit
val glue_command : Certicoq.options -> Names.GlobRef.t list -> unit

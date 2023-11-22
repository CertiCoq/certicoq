open Certicoq_vanilla_plugin
open Plugin_utils

val compile_only : Certicoq.options -> Names.GlobRef.t -> import list -> unit
val compile_C : Certicoq.options -> Names.GlobRef.t -> import list -> unit
val generate_glue_only : Certicoq.options -> Names.GlobRef.t -> unit
val show_ir : Certicoq.options -> Names.GlobRef.t -> unit
val ffi_command : Certicoq.options -> Names.GlobRef.t -> unit
val glue_command : Certicoq.options -> Names.GlobRef.t list -> unit

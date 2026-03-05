open Certirocq_vanilla_plugin
open Plugin_utils

val compile_only : Certirocq.options -> Names.GlobRef.t -> import list -> unit
val compile_C : Certirocq.options -> Names.GlobRef.t -> import list -> unit
val generate_glue_only : Certirocq.options -> Names.GlobRef.t -> unit
val show_ir : Certirocq.options -> Names.GlobRef.t -> unit
val ffi_command : Certirocq.options -> Names.GlobRef.t -> unit
val glue_command : Certirocq.options -> Names.GlobRef.t list -> unit

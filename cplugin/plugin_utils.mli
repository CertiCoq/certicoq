val string_of_bytestring : Bytestring.String.t -> string

val bytestring_of_string : string -> Bytestring.String.t

val extract_constant : Names.GlobRef.t -> string -> Kernames.kername * Kernames.ident

val debug_mappings : (Kernames.kername * Kernames.ident) list -> unit

val help_msg : string

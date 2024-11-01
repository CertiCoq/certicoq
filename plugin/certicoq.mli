open Plugin_utils

type command_args =
 | TYPED_ERASURE
 | UNSAFE_ERASURE
 | BYPASS_QED
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int 
 | ANFCONFIG of int (* The number of fvs passed as params and the original params shall not exceed this number *)
 | BUILDDIR of string
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int
 | PREFIX of string (* Prefix to add to the generated FFI fns, avoids clashes with C fns *)
 | TOPLEVEL_NAME of string (* Name of the toplevel function ("body" by default) *)
 | FILENAME of string (* Name of the generated file *)

type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list 
type prim = ((Kernames.kername * Kernames.ident) * bool)


type options =
  { typed_erasure : bool;
    unsafe_erasure : bool;
    bypass_qed : bool;
    cps       : bool;
    time      : bool;
    time_anf  : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    anf_conf  : int;
    build_dir : string;
    filename  : string;
    ext       : string;
    dev       : int;
    prefix    : string;
    toplevel_name : string;
    prims     : prim list;
    inductives_mapping : inductives_mapping;
  }

val default_options : unit -> options
val make_options : command_args list -> prim list -> string -> options

(* Register primitive operations and associated include file *)
val register : prim list -> import list -> unit

val register_inductives : inductives_mapping -> unit

val get_name : Names.GlobRef.t -> string

(* Support for running dynamically linked certicoq-compiled programs *)
type certicoq_run_function = unit -> Obj.t

(* [register_certicoq_run global_id fresh_name function]. A same global_id 
  can be compiled multiple times with different definitions, fresh_name indicates
  the version used this time *)
val register_certicoq_run : string -> string -> certicoq_run_function -> unit
val run_certicoq_run : string -> certicoq_run_function

module type CompilerInterface = sig
  type name_env
  val compile : Pipeline_utils.coq_Options -> Ast0.Env.program -> ((name_env * Clight.program) * Clight.program) CompM.error * Bytestring.String.t
  val printProg : Clight.program -> name_env -> string -> import list -> unit

  val generate_glue : Pipeline_utils.coq_Options -> Ast0.Env.global_declarations -> 
    (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
  
  val generate_ffi :
    Pipeline_utils.coq_Options -> Ast0.Env.program -> (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error  
end

module CompileFunctor (CI : CompilerInterface) : sig
  val compile_only : options -> Names.GlobRef.t -> import list -> unit
  val generate_glue_only : options -> Names.GlobRef.t -> unit
  val compile_C : options -> Names.GlobRef.t -> import list -> unit
  val show_ir : options -> Names.GlobRef.t -> unit
  val compile_wasm : options -> Names.GlobRef.t -> unit
  val ffi_command : options -> Names.GlobRef.t -> unit
  val glue_command : options -> Names.GlobRef.t list -> unit
  val eval_gr : options -> Names.GlobRef.t -> import list -> Constr.t
  val eval : options -> Environ.env -> Evd.evar_map -> EConstr.t -> import list -> Constr.t
end

val compile_only : options -> Names.GlobRef.t -> import list -> unit
val generate_glue_only : options -> Names.GlobRef.t -> unit
val compile_C : options -> Names.GlobRef.t -> import list -> unit
val show_ir : options -> Names.GlobRef.t -> unit
val compile_wasm : options -> Names.GlobRef.t -> unit
val ffi_command : options -> Names.GlobRef.t -> unit
val glue_command : options -> Names.GlobRef.t list -> unit
val eval_gr : options -> Names.GlobRef.t -> import list -> Constr.t
val eval : options -> Environ.env -> Evd.evar_map -> EConstr.t -> import list -> Constr.t
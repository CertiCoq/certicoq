open AST
open Archi
open Ascii
open BasicAst
open Basics
open BinInt
open BinNat
open BinPos
open Clight
open Clightdefs
open Cop
open Ctypes
open Datatypes
open Errors0
open Integers
open List0
open Maps
open Monad0
open MonadState
open Nat0
open OptionMonad
open PeanoNat
open StateMonad
open String1
open String0
open Cps
open Identifiers

val print_Clight_dest_names' :
  Clight.program -> (int * name) list -> char list -> unit

val maxArgs : int

val makeArgList' : int list -> int list

val makeArgList : int list -> int list

val compute_fEnv' : nat -> fEnv -> exp -> fEnv

val compute_fEnv_fundefs : nat -> fundefs -> fEnv -> fEnv

val max_depth : exp -> nat

val max_depth_fundefs : fundefs -> nat

val compute_fEnv : exp -> fEnv

val get_allocs : exp -> int list

val get_allocs_fundefs : fundefs -> int list

val max_allocs : exp -> nat

val max_allocs_fundefs : fundefs -> nat

type n_iTyInfo = name * (((name * cTag) * int) * int) list

type n_iEnv = n_iTyInfo M.t

val update_iEnv : n_iEnv -> int -> cTyInfo -> n_iEnv

val compute_iEnv : cEnv -> n_iEnv

type cRep =
| Coq_enum of int
| Coq_boxed of int * int

val make_cRep : cEnv -> cTag -> cRep option

val coq_val : coq_type

val uval : coq_type

val val_typ : typ

val coq_Init_int : int -> init_data

val add : expr -> expr -> expr

val sub : expr -> expr -> expr

val not : expr -> expr

val c_int' : int -> coq_type -> expr

val reserve :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> int -> int
  -> statement

val makeTagZ : cEnv -> cTag -> int option

val makeTag : cEnv -> cTag -> expr option

val makeVar : AST.ident -> int -> int M.t -> expr

val assignConstructorS' :
  AST.ident -> int M.t -> int -> nat -> int list -> statement

val assignConstructorS :
  AST.ident -> AST.ident -> cEnv -> n_iEnv -> int M.t -> int -> cTag -> int
  list -> statement option

val isPtr : AST.ident -> int -> int -> statement

val isBoxed : cEnv -> n_iEnv -> cTag -> bool

val asgnFunVars : AST.ident -> int list -> int list -> statement option

val asgnAppVars' :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> int list -> int list ->
  statement option

val asgnAppVars :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> int list -> int list ->
  statement option

val make_case_switch :
  AST.ident -> AST.ident -> int -> labeled_statements -> labeled_statements
  -> statement

val translate_body :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> exp -> fEnv -> cEnv -> n_iEnv -> int M.t -> statement option

val mkFun :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> int list -> statement -> coq_function

val translate_fundefs :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> AST.ident -> AST.ident -> fundefs -> fEnv -> cEnv -> n_iEnv -> int M.t
  -> (int * (Clight.fundef, coq_type) globdef) list option

val make_extern_decl :
  name M.t -> (int * (Clight.fundef, coq_type) globdef) -> bool ->
  (int * (Clight.fundef, coq_type) globdef) option

val make_extern_decls :
  name M.t -> (int * (Clight.fundef, coq_type) globdef) list -> bool ->
  (int * (Clight.fundef, coq_type) globdef) list

val body_external_decl :
  AST.ident -> AST.ident -> AST.ident -> int * (Clight.fundef, coq_type)
  globdef

val translate_funs :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> exp -> fEnv -> cEnv
  -> n_iEnv -> int M.t -> (int * (Clight.fundef, coq_type) globdef) list
  option

type 't nState = (int, 't) state

val getName : int nState

val make_ind_array : int list -> init_data list

val pos2string' : int -> char list -> char list

val pos2string : int -> char list

val show_pos : int -> char list

val update_nEnv_fun_info : int -> int -> name M.t -> name M.t

val make_fundef_info :
  fundefs -> fEnv -> name M.t -> (((int * (Clight.fundef, coq_type) globdef)
  list * int M.t) * name M.t) option nState

val add_bodyinfo :
  AST.ident -> exp -> fEnv -> name M.t -> int M.t -> (int * (Clight.fundef,
  coq_type) globdef) list -> (((int * (Clight.fundef, coq_type) globdef)
  list * int M.t) * name M.t) option nState

val make_funinfo :
  AST.ident -> exp -> fEnv -> name M.t -> (((int * (Clight.fundef, coq_type)
  globdef) list * int M.t) * name M.t) option nState

val global_defs :
  AST.ident -> AST.ident -> AST.ident -> exp -> (int * (Clight.fundef,
  coq_type) globdef) list

val make_defs :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> exp -> fEnv -> cEnv
  -> n_iEnv -> name M.t -> (name M.t * (int * (Clight.fundef, coq_type)
  globdef) list) option nState

val composites :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
  composite_definition list

val mk_prog_opt :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> (AST.ident * (Clight.fundef, coq_type) globdef) list -> AST.ident ->
  bool -> Clight.program option

val wrap_in_fun : exp -> exp

val add_inf_vars :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> name
  M.t -> name M.t

val ensure_unique : name M.t -> name M.t

val make_proj : expr -> nat -> nat -> expr list

val make_Asgn : expr list -> expr list -> statement

val make_argList' :
  nat -> name M.t -> (name M.t * (AST.ident * coq_type) list) nState

val make_argList :
  nat -> name M.t -> (name M.t * (AST.ident * coq_type) list) nState

val make_constrAsgn' :
  AST.ident -> (AST.ident * coq_type) list -> nat -> statement

val make_constrAsgn : AST.ident -> (AST.ident * coq_type) list -> statement

val make_constructors :
  cEnv -> ident -> (((name * cTag) * int) * int) list -> name M.t -> (name
  M.t * (int * (Clight.fundef, coq_type) globdef) list) nState

val make_elim_Asgn : AST.ident -> AST.ident -> nat -> statement

val asgn_string_init : char list -> init_data list

val make_arrGV : int list -> (Clight.fundef, coq_type) globdef

val pad_char_init : init_data list -> nat -> init_data list

val make_names_init : name list -> nat -> nat * init_data list

val make_namesGV : name list -> (Clight.fundef, coq_type) globdef

val make_eliminator :
  AST.ident -> AST.ident -> cEnv -> ident -> (((name * cTag) * int) * int)
  list -> name M.t -> (name M.t * (AST.ident * (Clight.fundef, coq_type)
  globdef) list) nState

val make_interface :
  AST.ident -> AST.ident -> cEnv -> (int * n_iTyInfo) list -> name M.t ->
  (name M.t * (AST.ident * (Clight.fundef, coq_type) globdef) list) nState

val make_tinfoIdent : int

val exportIdent : int

val make_tinfo_rec : AST.ident -> int * (Clight.fundef, coq_type) globdef

val export_rec : AST.ident -> int * (Clight.fundef, coq_type) globdef

val make_halt :
  AST.ident -> AST.ident -> name M.t -> ((name
  M.t * (AST.ident * (Clight.fundef, coq_type)
  globdef)) * (AST.ident * (Clight.fundef, coq_type) globdef)) nState

val make_call :
  AST.ident -> AST.ident -> expr -> AST.ident -> AST.ident -> expr ->
  AST.ident -> AST.ident -> statement

val make_n_calls :
  AST.ident -> AST.ident -> nat -> AST.ident -> AST.ident -> AST.ident ->
  expr -> (AST.ident * coq_type) list -> AST.ident -> AST.ident -> statement

val make_call_n_export_b :
  AST.ident -> AST.ident -> AST.ident -> name M.t -> nat -> bool -> AST.ident
  -> (name M.t * (AST.ident * (Clight.fundef, coq_type) globdef)) nState

val tinf_def : AST.ident -> (Clight.fundef, coq_type) globdef

val make_header :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> cEnv ->
  n_iEnv -> exp -> name M.t -> (name M.t * (AST.ident * (Clight.fundef,
  coq_type) globdef) list) option nState

val compile :
  AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident
  -> AST.ident -> AST.ident -> AST.ident -> AST.ident -> AST.ident ->
  AST.ident -> exp -> cEnv -> name M.t -> (name M.t * Clight.program
  option) * Clight.program option

val empty_program : AST.ident -> Clight.program

val stripOption : AST.ident -> Clight.program option -> Clight.program

val print_Clight_dest_names :
  Clight.program -> (int * name) list -> char list -> unit

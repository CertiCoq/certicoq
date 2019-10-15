open AST
open Archi
open BinInt
open BinNat
open Bool
open Coqlib0
open Datatypes
open Errors0
open Maps
open Nat0
open Zpower

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : int option }

val attr_volatile : attr -> bool

val attr_alignas : attr -> int option

val noattr : attr

type coq_type =
| Tvoid
| Tint of intsize * signedness * attr
| Tlong of signedness * attr
| Tfloat of floatsize * attr
| Tpointer of coq_type * attr
| Tarray of coq_type * int * attr
| Tfunction of typelist * coq_type * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr
and typelist =
| Tnil
| Tcons of coq_type * typelist

val intsize_eq : intsize -> intsize -> bool

val type_eq : coq_type -> coq_type -> bool

val typelist_eq : typelist -> typelist -> bool

val attr_of_type : coq_type -> attr

val change_attributes : (attr -> attr) -> coq_type -> coq_type

val remove_attributes : coq_type -> coq_type

val attr_union : attr -> attr -> attr

val merge_attributes : coq_type -> attr -> coq_type

type struct_or_union =
| Struct
| Union

type members = (ident * coq_type) list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

type composite = { co_su : struct_or_union; co_members : members;
                   co_attr : attr; co_sizeof : int; co_alignof : int;
                   co_rank : nat }

val co_members : composite -> members

val co_sizeof : composite -> int

val co_alignof : composite -> int

val co_rank : composite -> nat

type composite_env = composite PTree.t

val type_int32s : coq_type

val type_bool : coq_type

val typeconv : coq_type -> coq_type

val complete_type : composite_env -> coq_type -> bool

val align_attr : attr -> int -> int

val alignof : composite_env -> coq_type -> int

val sizeof : composite_env -> coq_type -> int

val alignof_composite : composite_env -> members -> int

val sizeof_struct : composite_env -> int -> members -> int

val sizeof_union : composite_env -> members -> int

val field_offset_rec : composite_env -> ident -> members -> int -> int res

val field_offset : composite_env -> ident -> members -> int res

type mode =
| By_value of memory_chunk
| By_reference
| By_copy
| By_nothing

val access_mode : coq_type -> mode

val type_is_volatile : coq_type -> bool

val alignof_blockcopy : composite_env -> coq_type -> int

val rank_type : composite_env -> coq_type -> nat

val rank_members : composite_env -> members -> nat

val type_of_params : (ident * coq_type) list -> typelist

val typ_of_type : coq_type -> typ

val opttyp_of_type : coq_type -> typ option

val typlist_of_typelist : typelist -> typ list

val signature_of_type :
  typelist -> coq_type -> calling_convention -> signature

val sizeof_composite : composite_env -> struct_or_union -> members -> int

val complete_members : composite_env -> members -> bool

val composite_of_def :
  composite_env -> ident -> struct_or_union -> members -> attr -> composite
  res

val add_composite_definitions :
  composite_env -> composite_definition list -> composite_env res

val build_composite_env : composite_definition list -> composite_env res

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * coq_type * calling_convention

type 'f program = { prog_defs : (ident * ('f fundef, coq_type) globdef) list;
                    prog_public : ident list; prog_main : ident;
                    prog_types : composite_definition list;
                    prog_comp_env : composite_env }

val prog_defs : 'a1 program -> (ident * ('a1 fundef, coq_type) globdef) list

val prog_public : 'a1 program -> ident list

val prog_main : 'a1 program -> ident

val prog_comp_env : 'a1 program -> composite_env

val program_of_program : 'a1 program -> ('a1 fundef, coq_type) AST.program

val make_program :
  composite_definition list -> (ident * ('a1 fundef, coq_type) globdef) list
  -> ident list -> ident -> 'a1 program res

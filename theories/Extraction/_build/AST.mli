open Archi
open BinInt
open Coqlib0
open Floats
open Integers

type ident = int

val ident_eq : int -> int -> bool

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

val coq_Tptr : typ

type calling_convention = { cc_vararg : bool; cc_unproto : bool;
                            cc_structret : bool }

val cc_default : calling_convention

type signature = { sig_args : typ list; sig_res : typ option;
                   sig_cc : calling_convention }

val signature_main : signature

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

val coq_Mptr : memory_chunk

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of int
| Init_addrof of ident * Ptrofs.int

val init_data_size : init_data -> int

val init_data_list_size : init_data list -> int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : bool }

val gvar_init : 'a1 globvar -> init_data list

val gvar_readonly : 'a1 globvar -> bool

val gvar_volatile : 'a1 globvar -> bool

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type ('f, 'v) program = { prog_defs : (ident * ('f, 'v) globdef) list;
                          prog_public : ident list; prog_main : ident }

val prog_defs : ('a1, 'a2) program -> (ident * ('a1, 'a2) globdef) list

val prog_public : ('a1, 'a2) program -> ident list

type external_function =
| EF_external of char list * signature
| EF_builtin of char list * signature
| EF_runtime of char list * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of int * int
| EF_annot of int * char list * typ list
| EF_annot_val of int * char list * typ
| EF_inline_asm of char list * signature * char list list
| EF_debug of int * ident * typ list

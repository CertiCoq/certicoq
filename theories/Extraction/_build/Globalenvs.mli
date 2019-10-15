open AST
open BinInt
open BinPos
open Coqlib0
open Datatypes
open Integers
open List0
open Maps
open Memory
open Memtype
open Values

val store_zeros : Mem.mem -> block -> int -> int -> Mem.mem option

module Genv :
 sig
  type ('f, 'v) t = { genv_public : ident list; genv_symb : block PTree.t;
                      genv_defs : ('f, 'v) globdef PTree.t; genv_next : 
                      block }

  val genv_public : ('a1, 'a2) t -> ident list

  val genv_symb : ('a1, 'a2) t -> block PTree.t

  val genv_defs : ('a1, 'a2) t -> ('a1, 'a2) globdef PTree.t

  val genv_next : ('a1, 'a2) t -> block

  val find_symbol : ('a1, 'a2) t -> ident -> block option

  val find_def : ('a1, 'a2) t -> block -> ('a1, 'a2) globdef option

  val find_funct_ptr : ('a1, 'a2) t -> block -> 'a1 option

  val find_funct : ('a1, 'a2) t -> coq_val -> 'a1 option

  val add_global :
    ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) -> ('a1, 'a2) t

  val add_globals :
    ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) list -> ('a1, 'a2) t

  val empty_genv : ident list -> ('a1, 'a2) t

  val globalenv : ('a1, 'a2) program -> ('a1, 'a2) t

  val store_init_data :
    ('a1, 'a2) t -> Mem.mem -> block -> int -> init_data -> Mem.mem option

  val store_init_data_list :
    ('a1, 'a2) t -> Mem.mem -> block -> int -> init_data list -> Mem.mem
    option

  val perm_globvar : 'a1 globvar -> permission

  val alloc_global :
    ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) -> Mem.mem option

  val alloc_globals :
    ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) list -> Mem.mem
    option

  val init_mem : ('a1, 'a2) program -> Mem.mem option
 end

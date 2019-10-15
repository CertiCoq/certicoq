open AST
open BinInt
open BinPos
open Coqlib0
open Datatypes
open Integers
open Maps
open Memdata
open Memtype
open Values

module Mem :
 sig
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (int -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  val mem_contents : mem' -> memval ZMap.t PMap.t

  val mem_access : mem' -> (int -> perm_kind -> permission option) PMap.t

  val nextblock : mem' -> block

  type mem = mem'

  val perm_order_dec : permission -> permission -> bool

  val perm_order'_dec : permission option -> permission -> bool

  val perm_dec : mem -> block -> int -> perm_kind -> permission -> bool

  val range_perm_dec :
    mem -> block -> int -> int -> perm_kind -> permission -> bool

  val valid_access_dec :
    mem -> memory_chunk -> block -> int -> permission -> bool

  val valid_pointer : mem -> block -> int -> bool

  val weak_valid_pointer : mem -> block -> int -> bool

  val empty : mem

  val alloc : mem -> int -> int -> mem' * block

  val unchecked_free : mem -> block -> int -> int -> mem

  val free : mem -> block -> int -> int -> mem option

  val free_list : mem -> ((block * int) * int) list -> mem option

  val getN : nat -> int -> memval ZMap.t -> memval list

  val load : memory_chunk -> mem -> block -> int -> coq_val option

  val loadv : memory_chunk -> mem -> coq_val -> coq_val option

  val loadbytes : mem -> block -> int -> int -> memval list option

  val setN : memval list -> int -> memval ZMap.t -> memval ZMap.t

  val store : memory_chunk -> mem -> block -> int -> coq_val -> mem option

  val storev : memory_chunk -> mem -> coq_val -> coq_val -> mem option

  val storebytes : mem -> block -> int -> memval list -> mem option

  val drop_perm : mem -> block -> int -> int -> permission -> mem option
 end

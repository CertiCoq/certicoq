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

(** val store_zeros : Mem.mem -> block -> int -> int -> Mem.mem option **)

let rec store_zeros m b p n =
  if zle n 0
  then Some m
  else (match Mem.store Mint8unsigned m b p coq_Vzero with
        | Some m' -> store_zeros m' b (Z.add p 1) (Z.sub n 1)
        | None -> None)

module Genv =
 struct
  type ('f, 'v) t = { genv_public : ident list; genv_symb : block PTree.t;
                      genv_defs : ('f, 'v) globdef PTree.t; genv_next : 
                      block }

  (** val genv_public : ('a1, 'a2) t -> ident list **)

  let genv_public x = x.genv_public

  (** val genv_symb : ('a1, 'a2) t -> block PTree.t **)

  let genv_symb x = x.genv_symb

  (** val genv_defs : ('a1, 'a2) t -> ('a1, 'a2) globdef PTree.t **)

  let genv_defs x = x.genv_defs

  (** val genv_next : ('a1, 'a2) t -> block **)

  let genv_next x = x.genv_next

  (** val find_symbol : ('a1, 'a2) t -> ident -> block option **)

  let find_symbol ge id =
    PTree.get id ge.genv_symb

  (** val find_def : ('a1, 'a2) t -> block -> ('a1, 'a2) globdef option **)

  let find_def ge b =
    PTree.get b ge.genv_defs

  (** val find_funct_ptr : ('a1, 'a2) t -> block -> 'a1 option **)

  let find_funct_ptr ge b =
    match find_def ge b with
    | Some g -> (match g with
                 | Gfun f -> Some f
                 | Gvar _ -> None)
    | None -> None

  (** val find_funct : ('a1, 'a2) t -> coq_val -> 'a1 option **)

  let find_funct ge = function
  | Vptr (b, ofs) ->
    if Ptrofs.eq_dec ofs Ptrofs.zero then find_funct_ptr ge b else None
  | _ -> None

  (** val add_global :
      ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) -> ('a1, 'a2) t **)

  let add_global ge idg =
    { genv_public = ge.genv_public; genv_symb =
      (PTree.set (fst idg) ge.genv_next ge.genv_symb); genv_defs =
      (PTree.set ge.genv_next (snd idg) ge.genv_defs); genv_next =
      (Pos.succ ge.genv_next) }

  (** val add_globals :
      ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) list -> ('a1, 'a2) t **)

  let add_globals ge gl =
    fold_left add_global gl ge

  (** val empty_genv : ident list -> ('a1, 'a2) t **)

  let empty_genv pub =
    { genv_public = pub; genv_symb = PTree.empty; genv_defs = PTree.empty;
      genv_next = 1 }

  (** val globalenv : ('a1, 'a2) program -> ('a1, 'a2) t **)

  let globalenv p =
    add_globals (empty_genv p.prog_public) p.prog_defs

  (** val store_init_data :
      ('a1, 'a2) t -> Mem.mem -> block -> int -> init_data -> Mem.mem option **)

  let store_init_data ge m b p = function
  | Init_int8 n -> Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n -> Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n -> Mem.store Mint32 m b p (Vint n)
  | Init_int64 n -> Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n -> Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n -> Mem.store Mfloat64 m b p (Vfloat n)
  | Init_space _ -> Some m
  | Init_addrof (symb, ofs) ->
    (match find_symbol ge symb with
     | Some b' -> Mem.store coq_Mptr m b p (Vptr (b', ofs))
     | None -> None)

  (** val store_init_data_list :
      ('a1, 'a2) t -> Mem.mem -> block -> int -> init_data list -> Mem.mem
      option **)

  let rec store_init_data_list ge m b p = function
  | [] -> Some m
  | id :: idl' ->
    (match store_init_data ge m b p id with
     | Some m' ->
       store_init_data_list ge m' b (Z.add p (init_data_size id)) idl'
     | None -> None)

  (** val perm_globvar : 'a1 globvar -> permission **)

  let perm_globvar gv =
    if gv.gvar_volatile
    then Nonempty
    else if gv.gvar_readonly then Readable else Writable

  (** val alloc_global :
      ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) -> Mem.mem
      option **)

  let alloc_global ge m = function
  | (_, g) ->
    (match g with
     | Gfun _ ->
       let (m1, b) = Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty
     | Gvar v ->
       let init = v.gvar_init in
       let sz = init_data_list_size init in
       let (m1, b) = Mem.alloc m 0 sz in
       (match store_zeros m1 b 0 sz with
        | Some m2 ->
          (match store_init_data_list ge m2 b 0 init with
           | Some m3 -> Mem.drop_perm m3 b 0 sz (perm_globvar v)
           | None -> None)
        | None -> None))

  (** val alloc_globals :
      ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) list -> Mem.mem
      option **)

  let rec alloc_globals ge m = function
  | [] -> Some m
  | g :: gl' ->
    (match alloc_global ge m g with
     | Some m' -> alloc_globals ge m' gl'
     | None -> None)

  (** val init_mem : ('a1, 'a2) program -> Mem.mem option **)

  let init_mem p =
    alloc_globals (globalenv p) Mem.empty p.prog_defs
 end

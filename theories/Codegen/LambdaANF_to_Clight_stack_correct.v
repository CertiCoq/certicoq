(*
  Proof of correctness of the Clight stack-based (ANF) code generation phase of CertiCoq

  Modeled after LambdaANF_to_Clight_correct.v (CPS backend proof),
  adapted for the direct-style / shadow-stack translator in LambdaANF_to_Clight_stack.v.

  Key differences from the CPS proof:
  - Functions return val (not Tvoid)
  - Shadow stack for live root tracking across non-tail calls
  - GC triggered after non-tail calls (not at function entry)
  - Return values captured via resultIdent
*)

Require Import CertiCoq.LambdaANF.cps
               CertiCoq.LambdaANF.eval
               CertiCoq.LambdaANF.cps_util
               CertiCoq.LambdaANF.List_util
               CertiCoq.LambdaANF.Ensembles_util
               CertiCoq.LambdaANF.identifiers
               CertiCoq.LambdaANF.tactics
               CertiCoq.LambdaANF.shrink_cps_corresp.

Require Import Coq.ZArith.BinInt
               Coq.ZArith.Znat
               Coq.Arith.Arith
               Coq.NArith.BinNat
               ExtLib.Data.String
               ExtLib.Data.List
               Coq.micromega.Lia
               Coq.Program.Program
               Coq.micromega.Psatz
               Coq.Sets.Ensembles
               Coq.Logic.Decidable
               Coq.Lists.ListDec
               Coq.Relations.Relations.

Require Import compcert.common.AST
               compcert.common.Errors
               compcert.lib.Integers
               compcert.cfrontend.Cop
               compcert.cfrontend.Ctypes
               compcert.cfrontend.Clight
               compcert.common.Values
               compcert.common.Globalenvs
               compcert.common.Memory.

Require Import CertiCoq.Codegen.tactics
               CertiCoq.Codegen.LambdaANF_to_Clight
               CertiCoq.Codegen.LambdaANF_to_Clight_stack.

(* Reuse global infrastructure from the CPS correctness proof:
   gc_size, loc, int_size, int_chunk, uint_range, pointer arithmetic lemmas,
   subvalue relations, closed_val, etc. *)
Require Import CertiCoq.Codegen.LambdaANF_to_Clight_correct.

Require Import CertiCoq.Libraries.maps_util.
From Coq.Lists Require List.
Import List.ListNotations.

(* Bind stack translator names to avoid ambiguity with CPS translator *)
Notation stack_val := LambdaANF_to_Clight_stack.val.
Notation stack_uval := LambdaANF_to_Clight_stack.uval.
Notation stack_make_ctor_rep := LambdaANF_to_Clight_stack.make_ctor_rep.
Notation stack_ctor_rep := LambdaANF_to_Clight_stack.ctor_rep.
Notation stack_enum := LambdaANF_to_Clight_stack.enum.
Notation stack_boxed := LambdaANF_to_Clight_stack.boxed.
Notation stack_makeVar := LambdaANF_to_Clight_stack.makeVar.
Notation stack_mkFun := LambdaANF_to_Clight_stack.mkFun.

Section STACK_CORRECT.

  (* Identifiers shared with the CPS backend *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent : ident).
  Variable (caseIdent : ident).
  Variable (nParam : nat).

  (* Identifiers specific to the stack/ANF backend *)
  Variable (nallocIdent : ident).
  Variable (resultIdent : ident).
  Variable (stackframeTIdent : ident).
  Variable (frameIdent : ident).
  Variable (rootIdent : ident).
  Variable (fpIdent : ident).
  Variable (nextFld : ident).
  Variable (rootFld : ident).
  Variable (prevFld : ident).

  Variable cenv : cps.ctor_env.
  Variable fenv : cps.fun_env.
  Variable finfo_env : LambdaANF_to_Clight_stack.fun_info_env.
  Variable p : program.

  (* Constructor representation, computed from cenv *)
  Variable rep_env : M.t (LambdaANF_to_Clight.ctor_rep).

  (* Type abbreviations matching the stack translator *)
  Notation threadStructInf := (Tstruct threadInfIdent noattr).
  Notation threadInf := (Tpointer threadStructInf noattr).
  Notation stackframeT := (Tstruct stackframeTIdent noattr).
  Notation stackframeTPtr := (Tpointer stackframeT noattr).

  (* In the ANF backend, functions return val (not Tvoid) *)
  Notation s_funTy := (Tfunction (Tcons threadInf Tnil) stack_val cc_default).

  (* The val type is the same as in the CPS backend *)
  Notation val := LambdaANF_to_Clight.val.
  Notation uval := LambdaANF_to_Clight.uval.
  Notation valPtr := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).

  (** ** Protected identifiers *)

  Definition stack_protectedIdent : list ident :=
    argsIdent :: allocIdent :: limitIdent :: gcIdent :: mainIdent :: bodyIdent ::
    threadInfIdent :: tinfIdent :: heapInfIdent :: numArgsIdent :: isptrIdent ::
    caseIdent :: nallocIdent :: resultIdent :: frameIdent :: rootIdent :: fpIdent :: [].

  Definition is_stack_protected_id (x : ident) : Prop :=
    List.In x stack_protectedIdent.

  (** ** Protected memory invariant *)

  (* L is the set of memory locations owned by user data.
     Protected locations (alloc-limit gap, args array, tinfo block, globals)
     are excluded from L. Identical to CPS version. *)
  Definition stack_protected_not_in_L (lenv : temp_env) (L : block -> Z -> Prop) : Prop :=
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      (forall j : Z,
          (Ptrofs.unsigned alloc_ofs <= j < Ptrofs.unsigned limit_ofs)%Z ->
          ~ L alloc_b j) /\
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      (forall z j : Z,
          (0 <= z < max_args)%Z ->
          (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z))) <= j <
           Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z))) + int_size)%Z ->
          ~ L args_b j) /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      (forall i, ~ L tinf_b i) /\
      (forall x b,
          Genv.find_symbol (globalenv p) x = Some b ->
          b <> args_b /\ b <> alloc_b /\
          forall i, ~ L b i).

  (** ** Thread info invariant *)

  (* Correct thread_info for the stack backend.
     Same heap invariants as CPS, with additional frame pointer field. *)
  Definition stack_correct_tinfo (max_alloc : Z) (lenv : temp_env) (m : mem) : Prop :=
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
      (* alloc pointer *)
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      (Z.divide int_size (Ptrofs.unsigned alloc_ofs)) /\
      (* writable range from alloc to alloc + max_alloc *)
      (forall ofs : Z,
          (Ptrofs.unsigned alloc_ofs <= ofs <
           Ptrofs.unsigned alloc_ofs + int_size * max_alloc)%Z ->
          Mem.perm m alloc_b ofs Cur Writable) /\
      (* limit pointer: same block as alloc *)
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      (* enough space between alloc and limit *)
      (int_size * max_alloc <=
       Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs)%Z /\
      (* args pointer *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      args_b <> alloc_b /\
      (forall z : Z,
          (0 <= z < max_args)%Z ->
          Mem.valid_access m int_chunk args_b
            (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z)))) Writable) /\
      (* tinfo pointer *)
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      tinf_b <> alloc_b /\
      tinf_b <> args_b.

  (** ** Unchanged globals *)

  Definition stack_unchanged_globals (m m' : mem) : Prop :=
    forall x b,
      Genv.find_symbol (globalenv p) x = Some b ->
      forall i chunk, Mem.loadv chunk m (Vptr b i) = Mem.loadv chunk m' (Vptr b i).

  Theorem stack_unchanged_globals_trans :
    forall m1 m2 m3,
      stack_unchanged_globals m1 m2 ->
      stack_unchanged_globals m2 m3 ->
      stack_unchanged_globals m1 m3.
  Proof.
    unfold stack_unchanged_globals; intros.
    rewrite (H _ _ H1 i chunk).
    apply (H0 _ _ H1 i chunk).
  Qed.

End STACK_CORRECT.

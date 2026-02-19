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

  (* Rebind CPS-side names to avoid ambiguity with stack imports *)
  Notation ctor_rep := LambdaANF_to_Clight.ctor_rep.
  Notation enum := LambdaANF_to_Clight.enum.
  Notation boxed := LambdaANF_to_Clight.boxed.
  Notation make_vint := LambdaANF_to_Clight.make_vint.
  Notation add := LambdaANF_to_Clight.add.

  (** ** Clight stepping *)

  Inductive s_traceless_step2 (ge : genv) : state -> state -> Prop :=
  | s_ts2_step : forall s1 s2,
      Clight.step2 ge s1 Events.E0 s2 ->
      s_traceless_step2 ge s1 s2.

  Definition s_m_tstep2 (ge : genv) := clos_trans _ (s_traceless_step2 ge).

  (** ** Variable resolution *)

  Definition s_Vint_or_Vptr (v : Values.val) : bool :=
    match v with
    | Vint _ => negb Archi.ptr64
    | Vlong _ => Archi.ptr64
    | Vptr _ _ => true
    | _ => false
    end.

  Inductive s_get_var_or_funvar (lenv : temp_env) : positive -> Values.val -> Prop :=
  | S_gVoF_fun : forall b x,
      Genv.find_symbol (globalenv p) x = Some b ->
      s_get_var_or_funvar lenv x (Vptr b (Ptrofs.repr 0%Z))
  | S_gVoF_var : forall x v,
      Genv.find_symbol (globalenv p) x = None ->
      M.get x lenv = Some v ->
      s_Vint_or_Vptr v = true ->
      s_get_var_or_funvar lenv x v.

  (** ** Value representation *)

  (* The heap representation of values is identical between CPS and ANF backends.
     Boxed constructors: block with [header | field_0 | ... | field_{n-1}]
     Unboxed constructors: tagged integer
     Functions: pointer to global function symbol *)

  Inductive s_repr_val (L : block -> Z -> Prop)
    : cps.val -> Values.val -> mem -> Prop :=
  | SRconstr_boxed :
      forall t vs h a ord b i m cinfo,
        M.get t cenv = Some cinfo ->
        ctor_arity cinfo = a ->
        ctor_ordinal cinfo = ord ->
        (a > 0)%N ->
        header_of_rep (boxed ord a) h ->
        Mem.load int_chunk m b
          (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size))) =
          Some (make_vint h) ->
        s_repr_val_list L vs (Vptr b i) m ->
        (forall j : Z,
            (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size)) <= j <
             Ptrofs.unsigned (Ptrofs.add i
               (Ptrofs.repr (int_size * Z.of_N a))))%Z ->
            L b j) ->
        s_repr_val L (Vconstr t vs) (Vptr b i) m
  | SRconstr_unboxed :
      forall t h ord cinfo m,
        M.get t cenv = Some cinfo ->
        ctor_arity cinfo = 0%N ->
        ctor_ordinal cinfo = ord ->
        header_of_rep (enum ord) h ->
        s_repr_val L (Vconstr t []) (make_vint h) m
  | SRfun :
      forall rho fds f t vs e b m,
        find_def f fds = Some (t, vs, e) ->
        Genv.find_symbol (globalenv p) f = Some b ->
        s_repr_val L (Vfun rho fds f) (Vptr b Ptrofs.zero) m
  with s_repr_val_list (L : block -> Z -> Prop)
    : list cps.val -> Values.val -> mem -> Prop :=
  | SRptr_nil : forall v m,
      s_repr_val_list L [] v m
  | SRptr_cons : forall v vs b i m cv,
      Mem.load int_chunk m b (Ptrofs.unsigned i) = Some cv ->
      s_repr_val L v cv m ->
      s_repr_val_list L vs
        (Vptr b (Ptrofs.add i (Ptrofs.repr int_size))) m ->
      s_repr_val_list L (v :: vs) (Vptr b i) m.

  (* Value of a named variable: resolve through lenv or global symbol table *)
  Inductive s_repr_val_id (L : block -> Z -> Prop)
    : positive -> cps.val -> temp_env -> mem -> Prop :=
  | SRid_local : forall x v cv lenv m,
      Genv.find_symbol (globalenv p) x = None ->
      M.get x lenv = Some cv ->
      s_repr_val L v cv m ->
      s_repr_val_id L x v lenv m
  | SRid_global : forall x v lenv m b,
      Genv.find_symbol (globalenv p) x = Some b ->
      s_repr_val L v (Vptr b Ptrofs.zero) m ->
      s_repr_val_id L x v lenv m.

  (** ** Correct function definitions *)

  (* A compiled function definition in the global env has the right body *)
  Definition s_correct_fundefs
    (fds : fundefs) (m : mem) : Prop :=
    forall f t vs e,
      find_def f fds = Some (t, vs, e) ->
      exists b,
        Genv.find_symbol (globalenv p) f = Some b.

  Theorem s_correct_fundefs_unchanged :
    forall fds m m',
      s_correct_fundefs fds m ->
      stack_unchanged_globals m m' ->
      s_correct_fundefs fds m'.
  Proof.
    unfold s_correct_fundefs; intros; eauto.
  Qed.

  (** ** Memory relation *)

  (* Relates a LambdaANF environment to a Clight local environment + memory.
     For each variable z:
     - If z is free in e and bound in rho, it is represented in lenv/memory
     - Function subvalues are correctly compiled in the global env *)
  Definition s_rel_mem
    (L : block -> Z -> Prop) (e : exp)
    (rho : cps.M.t cps.val)
    (lenv : temp_env) (m : mem) : Prop :=
    forall z,
      (occurs_free e z ->
       exists v, M.get z rho = Some v /\
                 s_repr_val_id L z v lenv m) /\
      (forall rho' fds f v,
         M.get z rho = Some v ->
         subval_or_eq (Vfun rho' fds f) v ->
         (exists b, Genv.find_symbol (globalenv p) f = Some b /\
                    s_repr_val L (Vfun rho' fds f) (Vptr b Ptrofs.zero) m) /\
         closed_val (Vfun rho' fds f) /\
         s_correct_fundefs fds m).

  (** ** Shadow stack invariant *)

  (* Number of slots currently used in a frame's roots array *)
  Definition roots_well_formed
    (m : mem) (roots_b : block) (roots_ofs : ptrofs) (n : N) : Prop :=
    forall i : Z,
      (0 <= i < Z.of_N n)%Z ->
      Mem.valid_access m int_chunk roots_b
        (Ptrofs.unsigned roots_ofs + int_size * i)%Z Readable.

  (* The roots array stores valid represented values *)
  Definition roots_represent
    (L : block -> Z -> Prop)
    (m : mem) (roots_b : block) (roots_ofs : ptrofs)
    (vals : list Values.val) : Prop :=
    forall i v,
      nth_error vals i = Some v ->
      Mem.load int_chunk m roots_b
        (Ptrofs.unsigned roots_ofs + int_size * Z.of_nat i)%Z = Some v.

  (** ** Full state invariant *)

  Definition s_inv (e : exp) (rho : cps.M.t cps.val)
    (lenv : temp_env) (m : mem) (max_alloc : Z) : Prop :=
    exists L : block -> Z -> Prop,
      stack_protected_not_in_L lenv L /\
      s_rel_mem L e rho lenv m /\
      stack_correct_tinfo max_alloc lenv m.

  (** ** Main correctness theorem *)

  (* The ANF backend preserves evaluation semantics:
     if expression e evaluates to value v under environment rho,
     and the Clight state satisfies the invariant with sufficient
     allocation space, then the compiled Clight code steps from
     (State fu stm k local_env lenv m) to
     (Returnstate rv (call_cont k) m') where rv represents v.

     Key differences from the CPS correctness theorem:
     - The Clight function returns val (not Tvoid), so we reach
       Returnstate rather than placing the result in args[1]
     - Non-tail calls (Eletapp) push live vars onto the shadow
       stack before calling, pop them after, and trigger GC
       post-call if needed
     - local_env contains the stack frame and roots array
       (from stack_decl in the translation)

     The hypothesis connecting stm to the compilation of e
     will be refined as individual cases are proved. *)

  Theorem stack_codegen_correct :
    forall e rho v c,
      bstep_e (M.empty _) cenv rho e v c ->
      forall stm lenv m max_alloc fu local_env k,
        s_inv e rho lenv m max_alloc ->
        (Z.of_nat (LambdaANF_to_Clight_stack.max_allocs e) <= max_alloc)%Z ->
        exists rv m',
          s_m_tstep2 (globalenv p)
            (State fu stm k local_env lenv m)
            (Returnstate rv (call_cont k) m') /\
          exists L, s_repr_val L v rv m'.
  Proof.
    intros e rho v c Heval.
    induction Heval.
    - (* BStep_constr: Econstr x t ys e *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_proj: Eproj x t n y e *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_case: Ecase y cl *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_app: Eapp f t ys — tail call *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_letapp: Eletapp x f t ys e — non-tail call with shadow stack *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_fun: Efun fl e *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_prim_val: Eprim_val x p e *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_prim: Eprim x f ys e *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
    - (* BStep_halt: Ehalt x *)
      intros stm lenv m max_alloc fu local_env k Hinv Halloc.
      admit.
  Admitted.

End STACK_CORRECT.

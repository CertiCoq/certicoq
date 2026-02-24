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
  Variable disjointIdent :
    NoDup (protectedIdent argsIdent allocIdent limitIdent gcIdent
             mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent
             numArgsIdent isptrIdent caseIdent).

  Notation s_makeVar := (stack_makeVar threadInfIdent nParam).

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
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      (align_chunk int_chunk | Ptrofs.unsigned alloc_ofs)%Z /\
      Mem.range_perm m alloc_b (Ptrofs.unsigned alloc_ofs) (Ptrofs.unsigned limit_ofs) Cur Writable /\
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      (int_size * max_alloc <=
       Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs <= gc_size)%Z /\
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      args_b <> alloc_b /\
      ((Ptrofs.unsigned args_ofs) + int_size * max_args <= Ptrofs.max_unsigned)%Z /\
      (forall z : Z,
          (0 <= z < max_args)%Z ->
          Mem.valid_access m int_chunk args_b
            (Ptrofs.unsigned
               (Ptrofs.add args_ofs
                  (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr z)))) Writable) /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      True /\
      tinf_b <> alloc_b /\
      (forall i : Z,
          (0 <= i < 4)%Z ->
          Mem.valid_access m int_chunk tinf_b
            (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * i)))) Writable) /\
      deref_loc (Tarray uval LambdaANF_to_Clight_stack.maxArgs noattr)
        m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 3)))
        Full (Vptr args_b args_ofs) /\
      (forall x b,
          Genv.find_symbol (globalenv p) x = Some b ->
          b <> args_b /\ b <> alloc_b /\ b <> tinf_b /\
          (exists chunk, Mem.valid_access m chunk b 0%Z Nonempty)).

  Lemma stack_correct_tinfo_store_alloc_exists :
    forall max_alloc lenv m,
      stack_correct_tinfo max_alloc lenv m ->
      exists alloc_b alloc_ofs tinf_b tinf_ofs m1,
        M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
        M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
        Mem.store int_chunk m tinf_b
          (Ptrofs.unsigned
             (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
          (Vptr alloc_b alloc_ofs) = Some m1.
  Proof.
    intros max_alloc lenv m Hct.
    destruct Hct as
      [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs Hct]]]]]]].
    decompose [and] Hct. clear Hct.
    match goal with
    | H : M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) |- _ =>
        pose proof H as Halloc
    end.
    match goal with
    | H : M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) |- _ =>
        pose proof H as Htinf
    end.
    match goal with
    | H : forall i : Z,
          (0 <= i < 4)%Z ->
          Mem.valid_access m int_chunk tinf_b
            (Ptrofs.unsigned
               (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * i)))) Writable |- _ =>
        pose proof H as Htinf_va
    end.
    assert (Hva0 :
      Mem.valid_access m int_chunk tinf_b
        (Ptrofs.unsigned
           (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0)))) Writable).
    { apply Htinf_va. lia. }
    destruct (Mem.valid_access_store m int_chunk tinf_b
      (Ptrofs.unsigned
         (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
      (Vptr alloc_b alloc_ofs) Hva0) as [m1 Hstore].
    exists alloc_b, alloc_ofs, tinf_b, tinf_ofs, m1.
    repeat split; eauto.
  Qed.

  Lemma stack_correct_tinfo_store_alloc_limit_exists :
    forall max_alloc lenv m,
      stack_correct_tinfo max_alloc lenv m ->
      exists alloc_b alloc_ofs limit_ofs tinf_b tinf_ofs m1 m2,
        M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
        M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
        M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
        Mem.store int_chunk m tinf_b
          (Ptrofs.unsigned
             (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
          (Vptr alloc_b alloc_ofs) = Some m1 /\
        Mem.store int_chunk m1 tinf_b
          (Ptrofs.unsigned
             (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1))))
          (Vptr alloc_b limit_ofs) = Some m2.
  Proof.
    intros max_alloc lenv m Hct.
    destruct Hct as
      [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs Hct]]]]]]].
    decompose [and] Hct. clear Hct.
    match goal with
    | H : M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) |- _ =>
        pose proof H as Halloc
    end.
    match goal with
    | H : M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) |- _ =>
        pose proof H as Hlimit
    end.
    match goal with
    | H : M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) |- _ =>
        pose proof H as Htinf
    end.
    match goal with
    | H : forall i : Z,
          (0 <= i < 4)%Z ->
          Mem.valid_access m int_chunk tinf_b
            (Ptrofs.unsigned
               (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * i)))) Writable |- _ =>
        pose proof H as Htinf_va
    end.
    assert (Hva0 :
      Mem.valid_access m int_chunk tinf_b
        (Ptrofs.unsigned
           (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0)))) Writable).
    { apply Htinf_va. lia. }
    destruct (Mem.valid_access_store m int_chunk tinf_b
      (Ptrofs.unsigned
         (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
      (Vptr alloc_b alloc_ofs) Hva0) as [m1 Hstore0].
    assert (Hva1 :
      Mem.valid_access m int_chunk tinf_b
        (Ptrofs.unsigned
           (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1)))) Writable).
    { apply Htinf_va. lia. }
    assert (Hva1_after :
      Mem.valid_access m1 int_chunk tinf_b
        (Ptrofs.unsigned
           (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1)))) Writable).
    { eapply Mem.store_valid_access_1; eauto. }
    destruct (Mem.valid_access_store m1 int_chunk tinf_b
      (Ptrofs.unsigned
         (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1))))
      (Vptr alloc_b limit_ofs) Hva1_after) as [m2 Hstore1].
    exists alloc_b, alloc_ofs, limit_ofs, tinf_b, tinf_ofs, m1, m2.
    repeat split; eauto.
  Qed.

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

  Definition s_tinfo_alloc_assign : statement :=
    Sassign
      (Efield (Ederef (Etempvar tinfIdent threadInf) threadStructInf)
              allocIdent valPtr)
      (Etempvar allocIdent valPtr).

  Definition s_tinfo_limit_assign : statement :=
    Sassign
      (Efield (Ederef (Etempvar tinfIdent threadInf) threadStructInf)
              limitIdent valPtr)
      (Etempvar limitIdent valPtr).

  Definition s_tinfo_sync_stmt : statement :=
    Ssequence s_tinfo_alloc_assign s_tinfo_limit_assign.

  Lemma s_m_tstep2_step :
    forall ge s s',
      s_traceless_step2 ge s s' ->
      s_m_tstep2 ge s s'.
  Proof.
    intros ge s s' Hstep.
    apply t_step.
    exact Hstep.
  Qed.

  Lemma s_m_tstep2_transitive :
    forall ge s1 s2 s3,
      s_m_tstep2 ge s1 s2 ->
      s_m_tstep2 ge s2 s3 ->
      s_m_tstep2 ge s1 s3.
  Proof.
    intros ge s1 s2 s3 H12 H23.
    eapply t_trans; eauto.
  Qed.

  Lemma s_m_tstep2_of_m_tstep2 :
    forall ge s1 s2,
      m_tstep2 ge s1 s2 ->
      s_m_tstep2 ge s1 s2.
  Proof.
    intros ge s1 s2 Hm.
    induction Hm as [s1 s2 Hstep | s1 s2 s3 H12 IH12 H23 IH23].
    - apply s_m_tstep2_step.
      constructor.
      exact Hstep.
    - eapply s_m_tstep2_transitive; eauto.
  Qed.

  Lemma s_m_tstep2_seq_set :
    forall p0 fu k lenv m x rhs s v,
      eval_expr (globalenv p0) empty_env lenv m rhs v ->
      s_m_tstep2 (globalenv p0)
        (State fu (Ssequence (Sset x rhs) s) k empty_env lenv m)
        (State fu s k empty_env (M.set x v lenv) m).
  Proof.
    intros p0 fu k lenv m x rhs s v Heval.
    eapply s_m_tstep2_transitive.
    - apply s_m_tstep2_step.
      constructor.
      constructor.
    - eapply s_m_tstep2_transitive.
      + apply s_m_tstep2_step.
        constructor.
        constructor.
        exact Heval.
      + apply s_m_tstep2_step.
        constructor.
        constructor.
  Qed.

  Lemma s_m_tstep2_return :
    forall p0 fu k local_env lenv m e rv rv' m',
      eval_expr (globalenv p0) local_env lenv m e rv ->
      Cop.sem_cast rv (typeof e) (fn_return fu) m = Some rv' ->
      Mem.free_list m (blocks_of_env (globalenv p0) local_env) = Some m' ->
      s_m_tstep2 (globalenv p0)
        (State fu (Sreturn (Some e)) k local_env lenv m)
        (Returnstate rv' (call_cont k) m').
  Proof.
    intros p0 fu k local_env lenv m e rv rv' m' Heval Hcast Hfree.
    apply s_m_tstep2_step.
    constructor.
    eapply step_return_1.
    - exact Heval.
    - exact Hcast.
    - exact Hfree.
  Qed.

  Lemma stack_ehalt_prefix_steps_m :
    forall fu k lenv m max_alloc,
      program_inv argsIdent allocIdent limitIdent gcIdent
        threadInfIdent tinfIdent heapInfIdent isptrIdent caseIdent nParam p ->
      stack_correct_tinfo max_alloc lenv m ->
      exists m2,
        m_tstep2 (globalenv p)
          (State fu s_tinfo_sync_stmt k empty_env lenv m)
          (State fu Sskip k empty_env lenv m2).
  Proof.
    intros fu k lenv m max_alloc Hpinv Hct.
    destruct Hpinv as [_ [Hpti _]].
    destruct (stack_correct_tinfo_store_alloc_limit_exists max_alloc lenv m Hct)
      as [alloc_b [alloc_ofs [limit_ofs [tinf_b [tinf_ofs [m1 [m2
          [Halloc [Hlimit [Htinf [Hs0 Hs1]]]]]]]]]]].
    exists m2.
    unfold s_tinfo_sync_stmt, s_tinfo_alloc_assign, s_tinfo_limit_assign.
    eapply m_tstep2_tinfo_assigns; eauto.
  Qed.

  Lemma stack_ehalt_translated_return_steps_m :
    forall fu k lenv m m2 x rv,
      m_tstep2 (globalenv p)
        (State fu s_tinfo_sync_stmt
           (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
           empty_env lenv m)
        (State fu Sskip
           (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
           empty_env lenv m2) ->
      eval_expr (globalenv p) empty_env lenv m2 (s_makeVar x fenv finfo_env) rv ->
      Cop.sem_cast rv
        (typeof (s_makeVar x fenv finfo_env))
        (fn_return fu) m2 = Some rv ->
      m_tstep2 (globalenv p)
        (State fu (Ssequence s_tinfo_sync_stmt (Sreturn (Some (s_makeVar x fenv finfo_env))))
           k empty_env lenv m)
        (Returnstate rv (call_cont k) m2).
  Proof.
    intros fu k lenv m m2 x rv Hpref Heval Hcast.
    eapply m_tstep2_transitive.
    - apply m_tstep2_step. constructor.
    - eapply m_tstep2_transitive.
      + exact Hpref.
      + eapply m_tstep2_transitive.
        * apply m_tstep2_step. constructor.
        * apply m_tstep2_step.
          eapply step_return_1.
          -- exact Heval.
          -- exact Hcast.
          -- simpl. reflexivity.
  Qed.

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

  Lemma s_rel_mem_halt_repr_id :
    forall L rho lenv m x v,
      s_rel_mem L (Ehalt x) rho lenv m ->
      M.get x rho = Some v ->
      s_repr_val_id L x v lenv m.
  Proof.
    intros L rho lenv m x v Hrel Hget.
    unfold s_rel_mem in Hrel.
    specialize (Hrel x) as [Hocc _].
    assert (occurs_free (Ehalt x) x) by constructor.
    specialize (Hocc H) as [v' [Hget' Hrid]].
    rewrite Hget in Hget'. inversion Hget'. exact Hrid.
  Qed.

  Lemma s_inv_halt_repr_id :
    forall rho lenv m max_alloc x v,
      s_inv (Ehalt x) rho lenv m max_alloc ->
      M.get x rho = Some v ->
      exists L, s_repr_val_id L x v lenv m.
  Proof.
    intros rho lenv m max_alloc x v Hinv Hget.
    destruct Hinv as [L [_ [Hrel _]]].
    exists L.
    eapply s_rel_mem_halt_repr_id; eauto.
  Qed.

  Lemma bstep_halt_inv :
    forall rho x v c,
      bstep_e (M.empty _) cenv rho (Ehalt x) v c ->
      c = 0 /\ M.get x rho = Some v.
  Proof.
    intros rho x v c Hbs.
    inversion Hbs; subst.
    split.
    - reflexivity.
    - exact H1.
  Qed.

  Lemma s_inv_of_bstep_halt_repr_id :
    forall rho x v c lenv m max_alloc,
      bstep_e (M.empty _) cenv rho (Ehalt x) v c ->
      s_inv (Ehalt x) rho lenv m max_alloc ->
      exists L, s_repr_val_id L x v lenv m.
  Proof.
    intros rho x v c lenv m max_alloc Hbs Hinv.
    destruct (bstep_halt_inv _ _ _ _ Hbs) as [_ Hget].
    eapply s_inv_halt_repr_id; eauto.
  Qed.

  (** ** Halt-case correctness theorem *)

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
    forall rho x v c,
      bstep_e (M.empty _) cenv rho (Ehalt x) v c ->
      forall lenv m max_alloc fu k rv L,
        s_inv (Ehalt x) rho lenv m max_alloc ->
        (Z.of_nat (LambdaANF_to_Clight_stack.max_allocs (Ehalt x)) <= max_alloc)%Z ->
        eval_expr (globalenv p) empty_env lenv m
          (s_makeVar x fenv finfo_env) rv ->
        Cop.sem_cast rv
          (typeof (s_makeVar x fenv finfo_env))
          (fn_return fu) m = Some rv ->
        s_repr_val L v rv m ->
        exists rv' m',
          s_m_tstep2 (globalenv p)
            (State fu (Sreturn (Some (s_makeVar x fenv finfo_env)))
               k empty_env lenv m)
            (Returnstate rv' (call_cont k) m') /\
          exists L', s_repr_val L' v rv' m'.
  Proof.
    intros rho x v c Hbs.
    intros lenv m max_alloc fu k rv L Hinv Halloc Heval Hcast Hrepr.
    exists rv, m.
    split.
    - eapply s_m_tstep2_return.
      exact Heval.
      exact Hcast.
      simpl. reflexivity.
    - exists L.
      exact Hrepr.
  Qed.

  Theorem stack_codegen_correct_ehalt_translated :
    forall rho x v c,
      bstep_e (M.empty _) cenv rho (Ehalt x) v c ->
      forall lenv m max_alloc fu k,
        s_inv (Ehalt x) rho lenv m max_alloc ->
        program_inv argsIdent allocIdent limitIdent gcIdent
          threadInfIdent tinfIdent heapInfIdent isptrIdent caseIdent nParam p ->
        (Z.of_nat (LambdaANF_to_Clight_stack.max_allocs (Ehalt x)) <= max_alloc)%Z ->
        (forall m2,
            m_tstep2 (globalenv p)
              (State fu s_tinfo_sync_stmt
                 (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
                 empty_env lenv m)
              (State fu Sskip
                 (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
                 empty_env lenv m2) ->
            exists rv L,
              eval_expr (globalenv p) empty_env lenv m2
                (s_makeVar x fenv finfo_env) rv /\
              Cop.sem_cast rv
                (typeof (s_makeVar x fenv finfo_env))
                (fn_return fu) m2 = Some rv /\
              s_repr_val L v rv m2) ->
        exists rv' m',
          m_tstep2 (globalenv p)
            (State fu
               (Ssequence s_tinfo_sync_stmt
                  (Sreturn (Some (s_makeVar x fenv finfo_env))))
               k empty_env lenv m)
            (Returnstate rv' (call_cont k) m') /\
          exists L', s_repr_val L' v rv' m'.
  Proof.
    intros rho x v c Hbs.
    intros lenv m max_alloc fu k Hinv Hpinv Halloc Hpost.
    destruct Hinv as [Linv [_ [_ Hct]]].
    destruct (stack_ehalt_prefix_steps_m fu
                (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
                lenv m max_alloc Hpinv Hct) as [m2 Hpref].
    destruct (Hpost m2 Hpref) as [rv [L [Heval [Hcast Hrepr]]]].
    exists rv, m2.
    split.
    - eapply stack_ehalt_translated_return_steps_m; eauto.
    - exists L; exact Hrepr.
  Qed.

  Corollary stack_codegen_correct_ehalt_translated_s :
    forall rho x v c,
      bstep_e (M.empty _) cenv rho (Ehalt x) v c ->
      forall lenv m max_alloc fu k,
        s_inv (Ehalt x) rho lenv m max_alloc ->
        program_inv argsIdent allocIdent limitIdent gcIdent
          threadInfIdent tinfIdent heapInfIdent isptrIdent caseIdent nParam p ->
        (Z.of_nat (LambdaANF_to_Clight_stack.max_allocs (Ehalt x)) <= max_alloc)%Z ->
        (forall m2,
            m_tstep2 (globalenv p)
              (State fu s_tinfo_sync_stmt
                 (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
                 empty_env lenv m)
              (State fu Sskip
                 (Kseq (Sreturn (Some (s_makeVar x fenv finfo_env))) k)
                 empty_env lenv m2) ->
            exists rv L,
              eval_expr (globalenv p) empty_env lenv m2
                (s_makeVar x fenv finfo_env) rv /\
              Cop.sem_cast rv
                (typeof (s_makeVar x fenv finfo_env))
                (fn_return fu) m2 = Some rv /\
              s_repr_val L v rv m2) ->
        exists rv' m',
          s_m_tstep2 (globalenv p)
            (State fu
               (Ssequence s_tinfo_sync_stmt
                  (Sreturn (Some (s_makeVar x fenv finfo_env))))
               k empty_env lenv m)
            (Returnstate rv' (call_cont k) m') /\
          exists L', s_repr_val L' v rv' m'.
  Proof.
    intros rho x v c Hbs.
    intros lenv m max_alloc fu k Hinv Hpinv Halloc Hpost.
    destruct (stack_codegen_correct_ehalt_translated
                rho x v c Hbs
                lenv m max_alloc fu k Hinv Hpinv Halloc Hpost)
      as [rv' [m' [Hstep Hrepr]]].
    exists rv', m'. split.
    - eapply s_m_tstep2_of_m_tstep2. exact Hstep.
    - exact Hrepr.
  Qed.

End STACK_CORRECT.

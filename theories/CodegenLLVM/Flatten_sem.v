(** * CodegenLLVM.Flatten_sem — semantic preservation of [Flatten].

    [Flatten.flatten_prog] lifts nested operand expressions into fresh
    [INSTR_Op] bindings named [flat_id c].  This file proves that this
    preserves the semantics (Vellvm's [interp_mcfg] after the call knot
    [interp_mrec]), up to the extra writes to the fresh locals.

    Overview.
    - Part 1 (syntax): a [T]-polymorphic copy of the flattener ([atomizeP],
      [flat_codeP], [flat_blockP], ...), its agreement with [Flatten] on [typ],
      and its commutation with [tfmap] (hence with [convert_typ], i.e. with the
      [typ] -> [dtyp] conversion).
    - Part 2 (semantics, on [dtyp]):  the state relation [Rst D G] (memory and
      globals equal, local frames equal except at fresh names [flat_id _],
      plus: the locals [D] and globals [G] are bound in the source state);
      simulation lemmas for expressions, instructions, code, terminators,
      blocks and open control-flow graphs.

    The source code must satisfy a light well-formedness condition
    ([exp_ok], [instr_ok], [term_ok], [block_ok]): every atomic operand is a
    bound non-fresh local of [D], a bound global of [G], or a literal whose
    evaluation is pure.  This is needed because flattening moves the
    evaluation of an atomic operand after that of the compound operands that
    follow it (e.g. [store %x, (gep %p, 1)]); if the atomic operand could fail
    (say, an unbound local) while the compound one raises a different abortive
    event (UB, out-of-memory), the two programs would be observably different.
*)

From Stdlib Require Import ZArith List Lia Program Morphisms.
From ITree Require Import ITree ITreeFacts Eq.Eqit Interp.InterpFacts
     Interp.RecursionFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Handlers.
From CertiRocq.CodegenLLVM Require Import Flatten LambdaANF_to_LLVM_statement
     LLVM_interp_lemmas.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

(* ================================================================== *)
(** * Part 1: a [T]-polymorphic flattener *)

Section FlatP.
  Context {T : Set}.

  Fixpoint atomizeP (e : exp T) (c : positive) {struct e}
    : code T * exp T * positive :=
    match e with
    | OP_IBinop op t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        let fid := flat_id n2 in
        ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_IBinop op t a1 a2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n2)
    | OP_ICmp ss cmp t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        let fid := flat_id n2 in
        ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_ICmp ss cmp t a1 a2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n2)
    | OP_Conversion cv t1 e1 t2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let fid := flat_id n1 in
        ((c1 ++ [(IId fid, INSTR_Op (OP_Conversion cv t1 a1 t2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n1)
    | OP_GetElementPtr t ptr idxs =>
        let '(pt, pe) := ptr in
        let '(cp, ape, np) := atomizeP pe c in
        let fix aidx (l : list (T * exp T)) (k : positive) {struct l}
              : code T * list (T * exp T) * positive :=
            match l with
            | [] => ([], [], k)
            | (it, ie) :: rest =>
                let '(ci, ai, k1) := atomizeP ie k in
                let '(cr, ar, k2) := aidx rest k1 in
                ((ci ++ cr)%list, (it, ai) :: ar, k2)
            end in
        let '(cidx, aidxs, ni) := aidx idxs np in
        let fid := flat_id ni in
        ((cp ++ cidx ++ [(IId fid, INSTR_Op (OP_GetElementPtr t (pt, ape) aidxs), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ ni)
    | _ => ([], e, c)
    end.

  Fixpoint atomize_idxsP (l : list (T * exp T)) (k : positive) {struct l}
    : code T * list (T * exp T) * positive :=
    match l with
    | [] => ([], [], k)
    | (it, ie) :: rest =>
        let '(ci, ai, k1) := atomizeP ie k in
        let '(cr, ar, k2) := atomize_idxsP rest k1 in
        ((ci ++ cr)%list, (it, ai) :: ar, k2)
    end.

  Definition atomize_texpP (te : T * exp T) (c : positive)
    : code T * (T * exp T) * positive :=
    let '(t, e) := te in
    let '(cc, ae, n) := atomizeP e c in
    (cc, (t, ae), n).

  Definition atomize_opP (e : exp T) (c : positive) : code T * exp T * positive :=
    match e with
    | OP_IBinop op t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        ((c1 ++ c2)%list, OP_IBinop op t a1 a2, n2)
    | OP_ICmp ss cmp t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        ((c1 ++ c2)%list, OP_ICmp ss cmp t a1 a2, n2)
    | OP_Conversion cv t1 e1 t2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        (c1, OP_Conversion cv t1 a1 t2, n1)
    | OP_GetElementPtr t ptr idxs =>
        let '(pt, pe) := ptr in
        let '(cp, ape, np) := atomizeP pe c in
        let '(cidx, aidxs, ni) := atomize_idxsP idxs np in
        ((cp ++ cidx)%list, OP_GetElementPtr t (pt, ape) aidxs, ni)
    | _ => ([], e, c)
    end.

  Fixpoint atomize_argsP (l : list (texp T * list param_attr)) (k : positive)
           {struct l} : code T * list (texp T * list param_attr) * positive :=
    match l with
    | [] => ([], [], k)
    | (te, pa) :: rest =>
        let '(cc, te', k1) := atomize_texpP te k in
        let '(cr, ar, k2) := atomize_argsP rest k1 in
        ((cc ++ cr)%list, (te', pa) :: ar, k2)
    end.

  (** NB: for calls, the arguments are atomized BEFORE the callee, matching
      Vellvm's evaluation order ([denote_instr] evaluates the arguments first). *)
  Definition flat_instrP (x : instr_id * instr T * list (metadata T)) (c : positive)
    : code T * positive :=
    let '(id, i, md) := x in
    match i with
    | INSTR_Op e =>
        let '(cc, e', n) := atomize_opP e c in
        ((cc ++ [(id, INSTR_Op e', md)])%list, n)
    | INSTR_Load t ptr anns =>
        let '(cc, ptr', n) := atomize_texpP ptr c in
        ((cc ++ [(id, INSTR_Load t ptr' anns, md)])%list, n)
    | INSTR_Store val ptr anns =>
        let '(c1, val', n1) := atomize_texpP val c in
        let '(c2, ptr', n2) := atomize_texpP ptr n1 in
        ((c1 ++ c2 ++ [(id, INSTR_Store val' ptr' anns, md)])%list, n2)
    | INSTR_Call fn args anns obs =>
        let '(c1, args', n1) := atomize_argsP args c in
        let '(c2, fn', n2) := atomize_texpP fn n1 in
        ((c1 ++ c2 ++ [(id, INSTR_Call fn' args' anns obs, md)])%list, n2)
    | _ => ([(id, i, md)], c)
    end.

  Fixpoint flat_codeP (l : code T) (c : positive) {struct l} : code T * positive :=
    match l with
    | [] => ([], c)
    | x :: rest =>
        let '(ci, n1) := flat_instrP x c in
        let '(cr, n2) := flat_codeP rest n1 in
        ((ci ++ cr)%list, n2)
    end.

  Definition flat_termP (tm : terminator T) (c : positive)
    : code T * terminator T * positive :=
    match tm with
    | TERM_Ret v      => let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Ret v', n)
    | TERM_Br v b1 b2 => let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Br v' b1 b2, n)
    | TERM_Switch v d brs =>
        let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Switch v' d brs, n)
    | _ => ([], tm, c)
    end.

  Definition flat_blockP (b : LLVMAst.block T) (c : positive) : LLVMAst.block T * positive :=
    let '(cc, n1) := flat_codeP (blk_code b) c in
    let '(tid, tm, tmd) := blk_term b in
    let '(tc, tm', n2) := flat_termP tm n1 in
    (mk_block (blk_id b) (blk_phis b) (cc ++ tc)%list (tid, tm', tmd) (blk_comments b), n2).

  Fixpoint flat_blocksP (bs : list (LLVMAst.block T)) (c : positive) {struct bs}
    : list (LLVMAst.block T) * positive :=
    match bs with
    | [] => ([], c)
    | b :: rest =>
        let '(b', n1) := flat_blockP b c in
        let '(rs, n2) := flat_blocksP rest n1 in
        (b' :: rs, n2)
    end.

  (** Custom induction principle following [atomizeP]'s recursion. *)
  Definition compound (e : exp T) : bool :=
    match e with
    | OP_IBinop _ _ _ _ | OP_ICmp _ _ _ _ _ | OP_Conversion _ _ _ _
    | OP_GetElementPtr _ _ _ => true
    | _ => false
    end.

  Lemma exp_indP (P : exp T -> Prop)
        (HA : forall e, compound e = false -> P e)
        (HB : forall op t e1 e2, P e1 -> P e2 -> P (OP_IBinop op t e1 e2))
        (HC : forall ss cmp t e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp t e1 e2))
        (HD : forall cv t1 e1 t2, P e1 -> P (OP_Conversion cv t1 e1 t2))
        (HG : forall t pt pe idxs, P pe -> Forall (fun te => P (snd te)) idxs ->
                              P (OP_GetElementPtr t (pt, pe) idxs)) :
    forall e, P e.
  Proof.
    fix F 1. intros e. destruct e; try (apply HA; reflexivity).
    - apply HB; apply F.
    - apply HC; apply F.
    - apply HD; apply F.
    - match goal with |- P (OP_GetElementPtr _ ?p ?l) => destruct p as [pt pe]; revert l end.
      intros idxs. apply HG; [apply F|].
      revert idxs. fix G 1. intros [|[it ie] r]; constructor; [apply F | apply G].
  Qed.

  Lemma atomizeP_atomic e c : compound e = false -> atomizeP e c = ([], e, c).
  Proof. destruct e; cbn; congruence. Qed.

  Lemma aidx_eq (idxs : list (T * exp T)) k :
    (fix aidx (l : list (T * exp T)) (k : positive) {struct l}
       : code T * list (T * exp T) * positive :=
       match l with
       | [] => ([], [], k)
       | (it, ie) :: rest =>
           let '(ci, ai, k1) := atomizeP ie k in
           let '(cr, ar, k2) := aidx rest k1 in
           ((ci ++ cr)%list, (it, ai) :: ar, k2)
       end) idxs k = atomize_idxsP idxs k.
  Proof.
    revert k; induction idxs as [|[it ie] r IH]; intros k; cbn; [reflexivity|].
    destruct (atomizeP ie k) as [[ci ai] k1].
    rewrite IH. reflexivity.
  Qed.

  Lemma atomizeP_GEP t pt pe idxs c :
    atomizeP (OP_GetElementPtr t (pt, pe) idxs) c =
      let '(cp, ape, np) := atomizeP pe c in
      let '(cidx, aidxs, ni) := atomize_idxsP idxs np in
      let fid := flat_id ni in
      ((cp ++ cidx ++ [(IId fid, INSTR_Op (OP_GetElementPtr t (pt, ape) aidxs), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ ni).
  Proof.
    cbn [atomizeP]. destruct (atomizeP pe c) as [[cp ape] np].
    rewrite aidx_eq. reflexivity.
  Qed.

End FlatP.

(** ** Agreement with [Flatten] (on [typ]) *)

Lemma atomize_eq (e : exp typ) c : Flatten.atomize e c = atomizeP e c.
Proof.
  revert c. induction e using exp_indP; intros c.
  - destruct e; cbn in *; congruence.
  - cbn. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
    rewrite IHe2. reflexivity.
  - cbn. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
    rewrite IHe2. reflexivity.
  - cbn. rewrite IHe. reflexivity.
  - cbn [Flatten.atomize]. rewrite atomizeP_GEP. rewrite IHe.
    destruct (atomizeP e c) as [[cp ape] np].
    match goal with
    | |- context [?F idxs np] =>
        match F with
        | context [Flatten.atomize] =>
            assert (Hf : forall k, F idxs k = atomize_idxsP idxs k)
        end
    end.
    { clear -H. induction H as [|[it ie] r Hie Hr IH]; intros k; cbn; [reflexivity|].
      cbn in Hie. rewrite Hie. destruct (atomizeP ie k) as [[ci ai] k1].
      rewrite IH. reflexivity. }
    rewrite Hf. reflexivity.
Qed.

Lemma atomize_idxs_eq (l : list (typ * exp typ)) k :
  Flatten.atomize_idxs l k = atomize_idxsP l k.
Proof.
  revert k; induction l as [|[it ie] r IH]; intros k; cbn; [reflexivity|].
  rewrite atomize_eq. destruct (atomizeP ie k) as [[ci ai] k1].
  rewrite IH. reflexivity.
Qed.

Lemma atomize_texp_eq (te : typ * exp typ) c :
  Flatten.atomize_texp te c = atomize_texpP te c.
Proof. destruct te; cbn. rewrite atomize_eq. reflexivity. Qed.

Lemma atomize_op_eq (e : exp typ) c : Flatten.atomize_op e c = atomize_opP e c.
Proof.
  destruct e; cbn; try reflexivity;
    try match goal with p : (typ * exp typ)%type |- _ => destruct p end;
    rewrite ?atomize_eq;
    repeat (match goal with |- context [atomizeP ?e ?c] =>
                              destruct (atomizeP e c) as [[? ?] ?] end;
            rewrite ?atomize_eq, ?atomize_idxs_eq);
    reflexivity.
Qed.

Lemma atomize_args_eq l k : Flatten.atomize_args l k = atomize_argsP l k.
Proof.
  revert k; induction l as [|[te pa] r IH]; intros k; cbn; [reflexivity|].
  rewrite atomize_texp_eq. destruct (atomize_texpP te k) as [[cc te'] k1].
  rewrite IH. reflexivity.
Qed.

(** [Flatten.flat_code] atomizes a call's callee before its arguments,
    [flat_codeP] after them.  The two agree whenever every callee is atomic
    (no code is generated for it); see the report / the suggested change to
    [Flatten.v] for the general case. *)
Definition callee_atomic {T} (x : instr_id * instr T * list (metadata T)) : Prop :=
  match x with
  | (_, INSTR_Call (_, f) _ _ _, _) => compound f = false
  | _ => True
  end.

Lemma flat_code_eq (l : code typ) c :
  Forall callee_atomic l -> Flatten.flat_code l c = flat_codeP l c.
Proof.
  revert c; induction l as [|[[id i] md] r IH]; intros c Hl;
    cbn [Flatten.flat_code flat_codeP]; [reflexivity|].
  inversion Hl as [|? ? Hx Hr]; subst.
  assert (Hi : (match i with
           | INSTR_Op e =>
               let '(cc, e', n) := Flatten.atomize_op e c in
               ((cc ++ [(id, INSTR_Op e', md)])%list, n)
           | INSTR_Load t ptr anns =>
               let '(cc, ptr', n) := Flatten.atomize_texp ptr c in
               ((cc ++ [(id, INSTR_Load t ptr' anns, md)])%list, n)
           | INSTR_Store val ptr anns =>
               let '(c1, val', n1) := Flatten.atomize_texp val c in
               let '(c2, ptr', n2) := Flatten.atomize_texp ptr n1 in
               ((c1 ++ c2 ++ [(id, INSTR_Store val' ptr' anns, md)])%list, n2)
           | INSTR_Call fn args anns obs =>
               let '(c1, fn', n1) := Flatten.atomize_texp fn c in
               let '(c2, args', n2) := Flatten.atomize_args args n1 in
               ((c1 ++ c2 ++ [(id, INSTR_Call fn' args' anns obs, md)])%list, n2)
           | _ => ([(id, i, md)], c)
           end) = flat_instrP (id, i, md) c).
  { destruct i; cbn -[Flatten.atomize_op atomize_opP Flatten.atomize_texp atomize_texpP
                      Flatten.atomize_args atomize_argsP]; try reflexivity.
    all: try (rewrite atomize_op_eq; reflexivity).
    all: try (rewrite atomize_texp_eq; reflexivity).
    all: try (rewrite atomize_texp_eq;
              match goal with |- context [atomize_texpP ?v ?c0] =>
                                destruct (atomize_texpP v c0) as [[c1 v'] n1] end;
              rewrite atomize_texp_eq; reflexivity).
    destruct fn as [ft f]. cbn in Hx.
    rewrite atomize_texp_eq. cbn. rewrite (atomizeP_atomic f c Hx).
    rewrite atomize_args_eq. destruct (atomize_argsP args c) as [[c2 args'] n2].
    cbn. rewrite (atomizeP_atomic f n2 Hx). reflexivity. }
  rewrite Hi. destruct (flat_instrP (id, i, md) c) as [ci n1].
  rewrite IH by assumption. reflexivity.
Qed.

(** ** Commutation with type conversion ([tfmap], hence [convert_typ]) *)

Section TFmap.
  Context {U V : Set} (f : U -> V).

  Notation fe := (@tfmap exp _ U V f).
  Notation fc := (@tfmap code _ U V f).

  Lemma fc_app (a b : code U) : fc (a ++ b)%list = (fc a ++ fc b)%list.
  Proof. unfold tfmap, TFunctor_code, tfmap, TFunctor_list. apply map_app. Qed.

  Lemma compound_tfmap e : compound (fe e) = compound e.
  Proof. destruct e; reflexivity. Qed.

  Lemma atomizeP_tfmap e c :
    atomizeP (fe e) c = let '(cc, a, n) := atomizeP e c in (fc cc, fe a, n).
  Proof.
    revert c. induction e using exp_indP; intros c.
    - rewrite !atomizeP_atomic by (rewrite ?compound_tfmap; assumption). reflexivity.
    - change (fe (OP_IBinop op t e1 e2)) with (OP_IBinop op (f t) (fe e1) (fe e2)).
      cbn [atomizeP]. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite IHe2. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_ICmp ss cmp t e1 e2)) with (OP_ICmp ss cmp (f t) (fe e1) (fe e2)).
      cbn [atomizeP]. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite IHe2. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_Conversion cv t1 e t2)) with (OP_Conversion cv (f t1) (fe e) (f t2)).
      cbn [atomizeP]. rewrite IHe. destruct (atomizeP e c) as [[c1 a1] n1].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_GetElementPtr t (pt, e) idxs))
        with (OP_GetElementPtr (f t) (f pt, fe e) (map (fun te => (f (fst te), fe (snd te))) idxs)).
      rewrite !atomizeP_GEP. rewrite IHe. destruct (atomizeP e c) as [[cp ape] np].
      assert (Hi : forall k, atomize_idxsP (map (fun te => (f (fst te), fe (snd te))) idxs) k =
                        let '(ci, ai, n) := atomize_idxsP idxs k in
                        (fc ci, map (fun te => (f (fst te), fe (snd te))) ai, n)).
      { clear -H. induction H as [|[it ie] r Hie Hr IH]; intros k; cbn [map atomize_idxsP fst snd];
          [reflexivity|].
        cbn in Hie. rewrite Hie. destruct (atomizeP ie k) as [[ci ai] k1].
        rewrite IH. destruct (atomize_idxsP r k1) as [[cr ar] k2].
        rewrite fc_app. reflexivity. }
      rewrite Hi. destruct (atomize_idxsP idxs np) as [[ci ai] ni].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation ft := (fun te : U * exp U => (f (fst te), fe (snd te))).

  Lemma atomize_idxsP_tfmap idxs k :
    atomize_idxsP (map ft idxs) k =
      let '(ci, ai, n) := atomize_idxsP idxs k in (fc ci, map ft ai, n).
  Proof.
    revert k; induction idxs as [|[it ie] r IH]; intros k; cbn [map atomize_idxsP fst snd];
      [reflexivity|].
    rewrite atomizeP_tfmap. destruct (atomizeP ie k) as [[ci ai] k1].
    rewrite IH. destruct (atomize_idxsP r k1) as [[cr ar] k2].
    cbv beta iota zeta; rewrite fc_app. reflexivity.
  Qed.

  Notation ft' := (fun te : U * exp U => let '(t, e) := te in (f t, fe e)).

  Lemma atomize_texpP_tfmap te c :
    atomize_texpP (ft' te) c = let '(cc, a, n) := atomize_texpP te c in (fc cc, ft' a, n).
  Proof.
    destruct te as [t e]. cbn [atomize_texpP fst snd]. rewrite atomizeP_tfmap.
    destruct (atomizeP e c) as [[cc a] n]. reflexivity.
  Qed.

  Lemma atomize_opP_tfmap e c :
    atomize_opP (fe e) c = let '(cc, a, n) := atomize_opP e c in (fc cc, fe a, n).
  Proof.
    destruct e; try reflexivity.
    - change (fe (OP_IBinop iop t e1 e2)) with (OP_IBinop iop (f t) (fe e1) (fe e2)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite atomizeP_tfmap. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_ICmp samesign cmp t e1 e2)) with (OP_ICmp samesign cmp (f t) (fe e1) (fe e2)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite atomizeP_tfmap. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_Conversion conv t_from e t_to)) with (OP_Conversion conv (f t_from) (fe e) (f t_to)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e c) as [[c1 a1] n1].
      reflexivity.
    - destruct ptrval as [pt pe].
      change (fe (OP_GetElementPtr t (pt, pe) idxs))
        with (OP_GetElementPtr (f t) (f pt, fe pe) (map ft idxs)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP pe c) as [[cp ape] np].
      rewrite atomize_idxsP_tfmap. destruct (atomize_idxsP idxs np) as [[ci ai] ni].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation fa := (fun x : texp U * list param_attr => let '(te, a) := x in (ft' te, a)).

  Lemma atomize_argsP_tfmap l k :
    atomize_argsP (map fa l) k =
      let '(ci, ai, n) := atomize_argsP l k in (fc ci, map fa ai, n).
  Proof.
    revert k; induction l as [|[te pa] r IH]; intros k; cbn [map atomize_argsP];
      [reflexivity|].
    rewrite atomize_texpP_tfmap. destruct (atomize_texpP te k) as [[ci ai] k1].
    rewrite IH. destruct (atomize_argsP r k1) as [[cr ar] k2].
    cbv beta iota zeta; rewrite fc_app. reflexivity.
  Qed.

  Notation fx := (fun x : instr_id * instr U * list (metadata U) =>
                    let '(id, i, l) := x in (@endo instr_id _ id, @tfmap instr _ U V f i, @tfmap (fun T => list (metadata T)) _ U V f l)).

  Lemma fc_map (l : code U) : fc l = map fx l.
  Proof. reflexivity. Qed.

  Lemma flat_instrP_tfmap x c :
    flat_instrP (fx x) c = let '(cc, n) := flat_instrP x c in (fc cc, n).
  Proof.
    destruct x as [[id i] md].
    destruct i; try reflexivity;
      match goal with
      | |- context [INSTR_Call ?fn ?args ?anns ?obs] =>
      destruct fn as [ft0 fn0];
      change (@tfmap instr _ U V f (INSTR_Call (ft0, fn0) args anns obs))
        with (INSTR_Call (ft' (ft0, fn0)) (map fa args) (@tfmap annotation _ U V f anns)
                (@tfmap (fun T => list (operand_bundle T)) _ U V f obs));
      cbn [flat_instrP]; rewrite atomize_argsP_tfmap; destruct (atomize_argsP args c) as [[c1 a1] n1];
      rewrite atomize_texpP_tfmap; destruct (atomize_texpP (ft0, fn0) n1) as [[c2 a2] n2];
      cbv beta iota zeta; rewrite !fc_app; reflexivity
      | |- context [INSTR_Op ?op] =>
      change (@tfmap instr _ U V f (INSTR_Op op)) with (INSTR_Op (fe op));
      cbn [flat_instrP]; rewrite atomize_opP_tfmap; destruct (atomize_opP op c) as [[c1 a1] n1];
      cbv beta iota zeta; rewrite !fc_app; reflexivity
      | |- context [INSTR_Load ?t ?ptr ?anns] =>
      change (@tfmap instr _ U V f (INSTR_Load t ptr anns))
        with (INSTR_Load (f t) (ft' ptr) (@tfmap annotation _ U V f anns));
      cbn [flat_instrP]; rewrite atomize_texpP_tfmap; destruct (atomize_texpP ptr c) as [[c1 a1] n1];
      cbv beta iota zeta; rewrite !fc_app; reflexivity
      | |- context [INSTR_Store ?val ?ptr ?anns] =>
      change (@tfmap instr _ U V f (INSTR_Store val ptr anns))
        with (INSTR_Store (ft' val) (ft' ptr) (@tfmap annotation _ U V f anns));
      cbn [flat_instrP]; rewrite atomize_texpP_tfmap; destruct (atomize_texpP val c) as [[c1 a1] n1];
      rewrite atomize_texpP_tfmap; destruct (atomize_texpP ptr n1) as [[c2 a2] n2];
      cbv beta iota zeta; rewrite !fc_app; reflexivity
      end.
  Qed.

  Lemma flat_codeP_tfmap l c :
    flat_codeP (fc l) c = let '(cc, n) := flat_codeP l c in (fc cc, n).
  Proof.
    revert c; induction l as [|x r IH]; intros c; [reflexivity|].
    change (fc (x :: r)) with (fx x :: fc r).
    cbn [flat_codeP]. rewrite flat_instrP_tfmap. destruct (flat_instrP x c) as [ci n1].
    rewrite IH. destruct (flat_codeP r n1) as [cr n2].
    cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation ftm := (@tfmap terminator _ U V f).

  Lemma flat_termP_tfmap tm c :
    flat_termP (ftm tm) c = let '(cc, tm', n) := flat_termP tm c in (fc cc, ftm tm', n).
  Proof.
    destruct tm; try reflexivity.
    - change (ftm (TERM_Ret v)) with (TERM_Ret (ft' v)). cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
    - change (ftm (TERM_Br v br1 br2)) with (TERM_Br (ft' v) br1 br2). cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
    - change (ftm (TERM_Switch v default_dest brs)) with (TERM_Switch (ft' v) default_dest brs).
      cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
  Qed.

  Notation fb := (@tfmap LLVMAst.block _ U V f).

  Lemma flat_blockP_tfmap b c :
    flat_blockP (fb b) c = let '(b', n) := flat_blockP b c in (fb b', n).
  Proof.
    destruct b as [bid phis code [[tid tm] tmd] cmt].
    unfold flat_blockP. cbn [blk_code blk_term blk_id blk_phis blk_comments].
    change (blk_code (fb (mk_block bid phis code (tid, tm, tmd) cmt))) with (fc code).
    change (blk_term (fb (mk_block bid phis code (tid, tm, tmd) cmt)))
      with (tid, ftm tm, @tfmap (fun T => list (metadata T)) _ U V f tmd).
    rewrite flat_codeP_tfmap. destruct (flat_codeP code c) as [cc n1].
    rewrite flat_termP_tfmap. destruct (flat_termP tm n1) as [[tc tm'] n2].
    unfold tfmap at 4, TFunctor_block. cbn [blk_code blk_term blk_id blk_phis blk_comments].
    rewrite fc_app. reflexivity.
  Qed.

  Lemma flat_blocksP_tfmap bs c :
    flat_blocksP (map fb bs) c = let '(bs', n) := flat_blocksP bs c in (map fb bs', n).
  Proof.
    revert c; induction bs as [|b r IH]; intros c; [reflexivity|].
    cbn [map flat_blocksP]. rewrite flat_blockP_tfmap. destruct (flat_blockP b c) as [b' n1].
    rewrite IH. destruct (flat_blocksP r n1) as [rs n2]. reflexivity.
  Qed.

End TFmap.

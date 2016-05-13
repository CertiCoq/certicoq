(** Naive conversion to a deBruijn-only expression language for a core calculus including
    mutually recursive functions, data constructors, and pattern matching.
 *)

(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStrippedL1" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4.
(******)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

Require Import L3.program.

Require L3.L3.
Module L3eval := L3.wcbvEval.
Module L3t := L3.term.
Module L3U := L3.unaryApplications.
Module L3N := L3.wNorm.

Require Import L4.expression.

Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in cut T;[intros H'; specialize (H H') | ]
  end.

Definition dcon_of_con (i : inductive) (n : nat) := N.of_nat n.

(** Erased terms are turned into axioms *)
Definition erased_exp := Ax_e "erased".

(** Definition environment *)
Definition env := list (string * exp).

Fixpoint cst_offset (e : env) (s : string) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if string_eq_bool s c then 0 else 1 + cst_offset tl s
  end.

(** Inductive environment: disappears at this stage *)
Definition ienv := list (string * itypPack).

Definition map_terms (f : L3t.Term -> exp) :=
  fix map_terms (l : L3t.Terms) : exps :=
  match l with
  | L3t.tnil => enil
  | L3t.tcons t ts => econs (f t) (map_terms ts)
  end.

Definition map_exps (f : exp -> exp) :=
  fix map_exps (l : exps) : exps :=
  match l with
  | enil => enil
  | econs t ts => econs (f t) (map_exps ts)
  end.


Section TermTranslation.
  Variable ie : ienv.
  Variable e : env.
    
  Fixpoint strip_lam (k : nat) (e : exp) : exp :=
    match k, e with
    | 0%nat, _ => e
    | S n, Lam_e e => strip_lam n e
    | S n, _ => e
    end.

  Section fixes.
    Variable trans : N -> L3t.Term -> exp.
    Definition trans_args (k : N) (t : L3t.Terms) : exps :=
      map_terms (trans k) t.
    Fixpoint trans_brs ann k n l :=
      match l with
      | L3t.tnil => brnil_e
      | L3t.tcons t ts =>
        let nargs := List.nth (N.to_nat n) ann 0%nat in
        brcons_e n (N.of_nat nargs) (strip_lam nargs (trans k t))
                 (trans_brs ann k (n + 1)%N ts)
      end.
    Fixpoint trans_fixes k l :=
      match l with
      | L3t.dnil => eflnil
      | L3t.dcons na t _ l' =>
        let t' := strip_lam 1 (trans k t) in
        eflcons t' (trans_fixes k l')
      end.

  End fixes.
  
  Fixpoint trans (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TAx s => Ax_e s
    | L3t.TProof => (* TODO: Ax_e for now *) Ax_e "proof"
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TSort s => (* Erase *) erased_exp
    | L3t.TProd n t => (* Erase *) erased_exp
    | L3t.TLambda n t => Lam_e (trans (k+1) t)
    | L3t.TLetIn n t u => Let_e (trans k t) (trans (k+1) u)
    | L3t.TApp t u => App_e (trans k t) (trans k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) erased_exp
    | L3t.TConstruct ind c args =>
      let args' := trans_args trans k args in
        Con_e (dcon_of_con ind c) args'
    | L3t.TCase ann t brs =>
      let brs' := trans_brs trans (snd ann) k 0%N brs in
      Match_e (trans k t) brs'
    | L3t.TFix d n =>
      let len := L3t.dlength d in
      let defs' := trans_fixes trans (N.of_nat len + k) d in
      Fix_e defs' (N.of_nat n)
    end.

End TermTranslation.

Definition translate (e : env) t :=
  trans e 0 t.

Definition translate_entry x acc :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    (s, t') :: acc
  | (s, ecTyp _ _) => acc
  end.

Definition translate_entry_aux x acc : option (string * exp) :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Some (s, t')
  | (s, ecTyp _ _) => None
  end.

Definition translate_env_aux (e : environ) (k : env) : env :=
  fold_right translate_entry k e.

Definition translate_env (e : environ) : env :=
  translate_env_aux e [].

Inductive wf_environ : environ -> Prop :=
| wf_nil : wf_environ []
| wf_cons_trm s t e : L3t.WFTrm t 0 -> wf_environ e -> wf_environ (cons (s, ecTrm t) e)
| wf_cons_ty s n t e : wf_environ e -> wf_environ (cons (s, ecTyp n t) e).

Inductive wf_tr_environ : list (string * exp) -> Prop :=
| wf_tr_nil : wf_tr_environ []
| wf_tr_cons s t e :
    wf_tr_environ e ->
    exp_wf 0 t -> (* Is closed w.r.t. environment *)
    is_value t -> (* Is a value *)
    wf_tr_environ (cons (s, t) e).

Lemma wf_environ_lookup (e : environ) (t : L3.term.Term) nm :
  wf_environ e -> LookupDfn nm e t -> L3t.WFTrm t 0.
Proof.
  intros wfe Het. revert wfe. red in Het.
  dependent induction Het; intros wfe.
  now inversion_clear wfe.
  apply IHHet. now inversion_clear wfe.
Qed.

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : string * exp) => Let_e (snd x) acc) e t.

Definition let_entry acc (a : string * envClass) e :=
  match a with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Let_e t' e
  | (s, ecTyp _ _) => e
  end.

Lemma mkLets_translate a e t :
  mkLets (translate_env (a :: e)) t =
  mkLets (translate_env e) (let_entry (translate_env e) a t).
Proof.
  now destruct a as [s [trm|ty]].
Qed.

Definition translate_program (e : environ) (t : L3t.Term) : exp :=
  let e' := translate_env e in
    mkLets e' (translate e' t).

Definition subst_env_aux e n (t : exp) :=
  fold_left
    (fun t (x : string * exp) => t{n := snd x})
    e t.

Definition subst_env e (t : exp) := subst_env_aux e 0 t.

Definition subst_entry (a : string * envClass) acc (e : exp) :=
  match a with
  | (s, ecTrm t) =>
    let t' := translate acc t in
      e{0 := t'}
  | (s, ecTyp _ _) => e
  end.

Lemma subst_env_tr a e k t :
  subst_env (translate_entry a (translate_env_aux e k)) t =
  subst_env (translate_env_aux e k)
            (subst_entry a (translate_env_aux e k) t).
Proof.
  destruct a as [s [trm|ty]]; cbn; reflexivity.
Qed.

Lemma translate_env_aux_snoc e a acc :
  translate_env_aux (e ++ [a]) acc =
  translate_env_aux e (translate_entry a acc). 
Proof.
  unfold translate_env_aux.
  rewrite fold_right_app; simpl. reflexivity.
Qed.

Definition build_subst_fn :=
  (fun (x : string * envClass) acc =>
                let '(acc, k) := acc in
                match translate_entry_aux x k with
                | Some r => (r :: acc, r :: k)
                | None => (acc, k)
                end).

Lemma snd_build_subst_fn a k :
  snd (build_subst_fn a k) = translate_entry a (snd k).
Proof.
  destruct k as [acc k].
  destruct a as [s [trm|ty]]; reflexivity.
Qed.

Definition build_subst_aux e acc :=
  fold_right build_subst_fn acc e.

Definition build_subst e k :=
  build_subst_aux e ([], k).

Definition substl l (e : exp) :=
  fold_left (fun t e => t{0 := e}) l e.

Lemma substl_app l l' e : substl l (substl l' e) = substl (l' ++ l) e.
Proof.
  revert l e; induction l'; intros l e; simpl.
  - reflexivity.
  - rewrite IHl'.
    reflexivity.
Qed.

Definition subst_entries e k (t : exp) :=
  let s := build_subst e k in
  substl (map snd (fst s)) t.

Lemma subst_env_translate_env e a k t :
  subst_env (translate_env_aux (a :: e) k) t =
  subst_env (translate_env_aux e k) (subst_entry a (translate_env_aux e k) t).
Proof.
  destruct a as [s [trm | ty]] ; simpl.
  + reflexivity.
  + reflexivity.
Qed.

Lemma build_subst_lemma a e' e :
  build_subst (a :: e') e =
  build_subst_fn a (build_subst e' e).
Proof. reflexivity. Qed.

Ltac case_call f :=
  let call := fresh "call" in
  remember f as call; destruct call.

Lemma build_subst_aux_lemma e' e'' acc :
  build_subst_aux (e'' ++ e') acc =
  build_subst_aux e'' (build_subst_aux e' acc).
Proof.
  revert e'' acc; induction e' as [ |x e'] using rev_ind; intros e'' acc.
  simpl.
  - now rewrite !app_nil_r. 
  - specialize (IHe' e'').
    unfold build_subst_aux.
    now rewrite fold_right_app.
Qed.

Definition build_subst_app e e' e'' :=
  let '(s, k) := build_subst e' e in
  let '(s', k') := build_subst e'' k in
  (s' ++ s, k').

Lemma build_subst_lemma' e' e'' e :
  build_subst (e'' ++ e') e = build_subst_app e e' e''.
Proof.
  unfold build_subst, build_subst_app in *.
  case_call (build_subst e' e).
  case_call (build_subst e'' e0).
  unfold build_subst, build_subst_app in *.
  rewrite build_subst_aux_lemma.
  rewrite <- Heqcall.
  clear Heqcall.
  revert l0 e1 e0 Heqcall0. clear.
  induction e''; simpl; intros.
  + injection Heqcall0; intros; subst. 
    reflexivity.
  + case_call (build_subst_aux e'' ([], e0)).
    specialize (IHe'' _ _ _ Heqcall).
    rewrite IHe''.
    simpl in *.
    case_call (translate_entry_aux a e);
    injection Heqcall0; intros; subst;
    reflexivity.
Qed.

Lemma translate_env_aux_build_subst e k :
  translate_env_aux e k = snd (build_subst e k).
Proof.
  revert k; induction e using rev_ind; intros; try reflexivity.
  unfold translate_env_aux, build_subst, build_subst_aux in *.
  simpl.
  rewrite !fold_right_app.
  rewrite IHe.
  simpl.
  unfold translate_entry, translate_entry_aux.
  destruct x as [s [trm|ty]]; simpl; try reflexivity.
  generalize ((s, translate k trm) :: k).
  clear. induction e; simpl; intros.
  + reflexivity.
  + rewrite !snd_build_subst_fn.
    f_equal. apply IHe.
Qed.
  
  
Lemma subst_entries_comm e e' k t :
  subst_entries e k (subst_entries e' (snd (build_subst e k)) t) =
  subst_entries (e' ++ e) k t.
Proof.
  unfold subst_entries.
  case_call (build_subst e k).
  case_call (build_subst e' e0).
  pose proof (build_subst_lemma' e e' k).
  unfold build_subst_app in H.
  rewrite <- Heqcall in *.
  rewrite <- Heqcall0 in H.
  rewrite H, substl_app. f_equal.
  simpl.
  f_equal. now rewrite <- Heqcall0; simpl; rewrite map_app.
Qed.

Lemma subst_env_translate_env_k e k t :
  subst_env (translate_env_aux e k) t =
  subst_env k (subst_entries e k t).
Proof.
  revert k t.
  induction e.
  - reflexivity.
  - intros. simpl.
    rewrite subst_env_tr.
    rewrite IHe.
    f_equal.
    rewrite translate_env_aux_build_subst.
    replace (subst_entry a (snd (build_subst e k)) t) with
    (subst_entries [a] (snd (build_subst e k)) t).
    rewrite subst_entries_comm. reflexivity.
    destruct a as [s [trm|ty]]; reflexivity.
Qed.


Lemma mkLets_app e e' t : mkLets (e ++ e') t =
                          mkLets e' (mkLets e t).
Proof.
  revert t; induction e; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHe.
    reflexivity.
Qed.

Lemma build_subst_aux_app e e' :
  snd (build_subst_aux e e') = snd (build_subst_aux e ([], snd e')).
Proof.
  induction e; simpl.
  - reflexivity.
  - case_call (build_subst_aux e e').
    case_call (build_subst_aux e ([], snd e')).
    simpl in *. subst.
    destruct a as [s [trm|ty]].
    reflexivity.
    reflexivity.
Qed.

Lemma build_subst_aux_app' e e' :
  snd (build_subst_aux e e') = fst (build_subst_aux e ([], snd e')) ++ snd e'.
Proof.
  revert e'; induction e; simpl; intros.
  + reflexivity.
  + specialize (IHe e').
    case_call (build_subst_aux e e').
    simpl.
    case_call (build_subst_aux e ([], snd e')).
    simpl in *. subst e0.
    destruct a as [s [trm|ty]]; simpl.
    - f_equal. f_equal.
      pose (build_subst_aux_app e e').
      rewrite <- Heqcall, <- Heqcall0 in e0.
      simpl in e0. subst e1. reflexivity.
    - reflexivity.
Qed.

Lemma build_subst_fst_snd e : snd (build_subst e []) = fst (build_subst e []).
Proof.
  induction e. reflexivity.
  simpl.
  destruct a as [s [trm|ty]];
  case_call (build_subst e []); simpl in *; subst; reflexivity.
Qed.  
                                 
Lemma translate_env_app e e' :
  translate_env (e' ++ e) = 
  (fst (build_subst e' (translate_env e))) ++ translate_env e.
Proof.
  unfold translate_env.
  rewrite !translate_env_aux_build_subst.
  unfold build_subst at 1.
  rewrite build_subst_aux_lemma, build_subst_aux_app'.
  f_equal.
Qed.

Lemma mkLets_translate_app e e' t :
  mkLets (translate_env (e' ++ e)) t =
  mkLets (translate_env e)
         (mkLets (fst (build_subst e' (translate_env e))) t).
Proof.
  now rewrite <- mkLets_app, translate_env_app.
Qed.

Lemma mkLets_translate_entry x  t :
  mkLets (translate_entry x []) t = let_entry [] x t.
Proof.
  destruct x as [s [trm|ty]]. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Definition sbst_env_aux (u : exp) (e : env) acc : N * env :=
  fold_right (fun s acc =>
                let '(n, l) := acc in
                (n+1, (fst s, (snd s){n := u}) :: l))
             acc e.

Definition sbst_env (u : exp) (n : N) (e : env) : N * env :=
  sbst_env_aux u e (n, []).

Lemma sbst_env_app e k l acc : sbst_env_aux e (k ++ l) acc =
                               sbst_env_aux e k (sbst_env_aux e l acc).
Proof.
  now unfold sbst_env_aux; rewrite fold_right_app. 
Qed.

Lemma fst_sbst_env_aux e k acc :
  fst (sbst_env_aux e k acc) = fst (sbst_env_aux e k (fst acc, [])).
Proof.
  induction k; simpl.
  - reflexivity.
  - case_call (sbst_env_aux e k acc).
    simpl in *. 
    case_call (sbst_env_aux e k (fst acc, [])).
    subst n; simpl. reflexivity.
Qed.

Lemma fst_sbst_env_aux' e k acc :
  fst (sbst_env_aux e k acc) = fst acc + N.of_nat (List.length k).
Proof.
  induction k; simpl.
  - destruct acc. simpl. lia.
  - case_call (sbst_env_aux e k acc).
    simpl in *. 
    case_call (sbst_env_aux e k (fst acc, [])).
    subst n; simpl. lia.
Qed.

Lemma snd_sbst_env_aux e k acc :
  snd (sbst_env_aux e k acc) =
  snd (sbst_env_aux e k (fst acc, [])) ++ snd acc.
Proof.
  induction k; simpl.

  - reflexivity.
  - generalize (fst_sbst_env_aux e k acc).
    case_call (sbst_env_aux e k acc).
    simpl in *. 
    case_call (sbst_env_aux e k (fst acc, [])).
    subst e0; simpl.
    f_equal. f_equal.
    simpl in *.
    now intros ->.
Qed.


Lemma sbst_lets (e : exp) (n : N) k t :
  let k' := (sbst_env e n k) in
  subst e n (mkLets k t) = mkLets (snd k') (subst e (fst k') t).
Proof.
  revert n t; induction k using rev_ind; intros.
  - simpl. reflexivity.
  - simpl.
    rewrite mkLets_app.
    simpl.
    unfold sbst_env in k'.
    rewrite IHk.
    subst k'. rewrite sbst_env_app.
    rewrite snd_sbst_env_aux.
    rewrite mkLets_app.
    rewrite snd_sbst_env_aux.
    rewrite mkLets_app.
    unfold mkLets at 2. simpl.
    f_equal. f_equal.
    + unfold sbst_env. now rewrite N.add_1_r, N.add_1_l.
    + unfold sbst_env. rewrite N.add_1_r, N.add_1_l.
      now setoid_rewrite fst_sbst_env_aux at 2.
Qed.
    
Lemma length_sbst_env e n k : length (snd (sbst_env e n k)) = length k.
Proof.
  revert e n; induction k using rev_ind; intros.
  simpl. reflexivity.
  unfold sbst_env.
  rewrite sbst_env_app.
  simpl.
  rewrite snd_sbst_env_aux.
  rewrite !app_length. simpl.
  unfold sbst_env in IHk. rewrite IHk.
  reflexivity.
Qed.

Lemma subst_env_app k x t :
  let k' := sbst_env (snd x) 0 k in
  subst_env (k ++ [x]) t =
  (subst_env (snd k') (subst (snd x) (fst k') t)).
Proof.
  intros.
  revert t x k'. induction k; intros.
  - reflexivity.
  - simpl.
    subst k'.
    rewrite IHk.
    unfold sbst_env.
    destruct a. destruct x. simpl.
    case_eq (sbst_env_aux e0 k (0, [])).
    intros. simpl. f_equal.
    (* commutation of substitution *)
    admit.
Admitted.

Lemma wf_tr_environ_inv k s x :
  wf_tr_environ (k ++ [(s, x)]) ->
   is_value x /\ exp_wf 0 x /\ wf_tr_environ k. 
Proof.
  induction k; simpl in *; intros.
  - now inv H.
  - inv H. intuition. constructor; auto.
Qed.

Lemma subst_env_aux_lam e k t :
  subst_env_aux e k (Lam_e t) = Lam_e (subst_env_aux e (1 + k) t).
Proof.
  revert t; induction e; intros; simpl.
  - reflexivity.
  - now rewrite IHe.
Qed.

Definition subst_env_lam e t : subst_env e (Lam_e t) = Lam_e (subst_env_aux e 1 t) :=
  subst_env_aux_lam e 0 t.

Inductive in_env : env -> N -> string -> exp -> env -> Prop :=
| in_env_here e nm t : in_env ((nm, t) :: e) 0 nm t e
| in_env_later e n decl nm t e' :
    in_env e n nm t e' ->
    in_env (decl :: e) (n + 1) nm t e'.

Lemma subst_env_application e t u :
  subst_env e (t $ u) = (subst_env e t $ subst_env e u).
Proof. revert t u; induction e; intros; simpl; try rewrite IHe; reflexivity. Qed.


Lemma subst_env_lambda e t :
  subst_env e (Lam_e t) =
  Lam_e (subst_env_aux e 1 t).
Proof.
  revert t; induction e; intros; simpl.

  reflexivity.
  destruct a as [s a]; simpl.
  rewrite <- IHe. reflexivity.
Qed.

Lemma shift0 :
  (forall e, forall i, shift 0 i e = e) /\
  (forall es, forall i, shifts 0 i es = es) /\
  (forall es, forall i, shift_fns 0 i es = es) /\
  (forall bs, forall i, shift_branches 0 i bs = bs).
Proof.
  apply my_exp_ind; intros; try rewrite_hyps; simpl; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity. now rewrite N.add_0_r.
Qed.

(* TODO: probably wrong statement *)
Lemma subst_env_instantiate e a k b :
  subst_env e (translate e (L3.term.instantiate a k b)) =
  ((subst_env_aux e 1 (trans e 1 b)) {0 ::= subst_env e (translate e a)}).
Proof.
  revert a k b; induction e; intros; simpl.

  induction b; simpl. unfold L3.term.instantiate.
  rewrite nat_compare_equiv.
  destruct lt_dec. now apply N.nlt_0_r in l. 
  unfold nat_compare_alt. destruct (lt_eq_lt_dec k n) as [[Hlt|Heq]|Hgt].
  destruct N.eq_dec.
  assert(n = 0%nat) by  lia.
  subst n. inversion Hlt.
  unfold translate. simpl. rewrite Nnat.Nat2N.inj_pred.
  now rewrite N.pred_sub.

  subst k. 
  destruct N.eq_dec. (* now rewrite (proj1 shift0). *) reflexivity.
Admitted.

Lemma eval_erased_exp e : eval (subst_env e erased_exp) (subst_env e erased_exp).
Proof.
  unfold erased_exp, subst_env. simpl.
  induction e; simpl; try apply IHe. constructor. 
Qed.

Lemma eval_axiom e nm : eval (subst_env e (Ax_e nm)) (subst_env e (Ax_e nm)).
Proof.
  unfold erased_exp, subst_env. simpl.
  induction e; simpl; try apply IHe. constructor. 
Qed.

Lemma subst_env_con_e e i r args :
  subst_env e (Con_e (dcon_of_con i r) args) =
  Con_e (dcon_of_con i r) (map_exps (subst_env e) args).
Proof.
  revert i r args; induction e; simpl; intros.
  f_equal. induction args; simpl; try rewrite IHargs at 1; reflexivity.
  
  rewrite IHe. f_equal.
  induction args; simpl; try rewrite IHargs at 1; reflexivity.
Qed.

Lemma subst_env_constructor e i r args :
  subst_env e (translate e (L3.term.TConstruct i r args)) =
  Con_e (dcon_of_con i r) (map_terms (fun x => subst_env e (translate e x)) args).
Proof.
  revert i r args; induction e; intros; unfold translate.
  - reflexivity.
  - simpl trans. rewrite subst_env_con_e. f_equal.
    induction args; simpl; try rewrite IHargs; try reflexivity.
Qed.

Lemma subst_env_lete e d b :
  subst_env e (Let_e d b) = Let_e (subst_env e d) (subst_env_aux e 1 b).
Proof.
  revert d b; induction e; intros; simpl; try rewrite IHe; reflexivity.
Qed.

Lemma subst_env_letin e n d b :
  subst_env e (translate e (L3.term.TLetIn n d b)) =
  Let_e (subst_env e (translate e d)) (subst_env_aux e 1 (trans e 1 b)).
Proof.
  unfold translate. simpl.
  now rewrite subst_env_lete.
Qed.

Inductive LookupEnv : string -> env -> exp -> Prop :=
  LHit : forall (s : string) (p : list (string * exp)) (t : exp),
    LookupEnv s ((s, t) :: p) t
| LMiss : forall (s1 s2 : string) (p : env) (t t' : exp),
    s2 <> s1 -> LookupEnv s2 p t' -> LookupEnv s2 ((s1, t) :: p) t'.

Lemma cst_offset_length e nm :
  (exists t, LookupEnv nm e t) ->
  cst_offset e nm < N.of_nat (List.length e).
Proof.
  revert nm.
  induction e; simpl; intros; try lia.
  destruct H. inversion H.
  destruct a as [s trm]. case_eq (string_eq_bool nm s). lia.
  intros. 
  destruct H. inversion H. subst.
  rewrite string_eq_bool_rfl in H0. discriminate.
  subst. specialize (IHe nm). forward IHe. lia.
  eexists; eauto.
Qed.

Inductive eval_env : env -> env -> Prop :=
| eval_env_nil : eval_env nil nil
| eval_env_cons nm t e e' t' :
    eval_env e e' ->
    eval (subst_env e' t) t' -> eval_env ((nm, t) :: e) ((nm, t') :: e').

Lemma exp_wf_strip_lam (k : nat) (e : exp) n :
  exp_wf n e -> exp_wf (N.of_nat k + n) (strip_lam k e).
Proof.
  revert e n; induction k; trivial.
  intros e n H.
  destruct H; simpl in *;
  try (eapply weaken_wf; eauto; lia).

  - (* Lambda *)
    specialize (IHk e (1 + i)).
    assert (N.of_nat k + (1 + i) = N.pos (Pos.of_succ_nat k) + i) by lia.
    rewrite H0 in IHk. eauto.

  - (* Ax *) constructor.
Qed.

Lemma efnlst_length_trans tr n d :
  efnlst_length (trans_fixes tr n d) = N.of_nat (L3t.dlength d).
Proof. induction d; simpl; try rewrite_hyps; auto; lia. Qed.

Lemma nth_empty (A : Type) n def : @nth A n [] def = def.
Proof.
  destruct n; reflexivity.
Qed.
  
Lemma WFTerm_exp_wf_ind e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e' ->
  (forall t n, L3t.WFTrm t n ->
          exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t)) /\
  (forall t n, L3t.WFTrms t n ->
          exps_wf (N.of_nat (n + List.length e')) (trans_args (trans e') (N.of_nat n) t) /\
          forall l k,
            branches_wf (N.of_nat (n + List.length e')) (trans_brs (trans e') l (N.of_nat n) k t)) /\
  (forall t n, L3t.WFTrmDs t n ->
          efnlst_wf (N.of_nat (n + 1 + List.length e'))
                    (trans_fixes (trans e') (N.of_nat n) t))
.
Proof.
  assert(Har:forall n, N.pos (Pos.of_succ_nat n) = 1 + N.of_nat n) by (intros; lia).
  intros wfe evee' wfe'.
  apply L3t.WFTrmTrmsDefs_ind; intros; unfold translate;
  simpl in *; repeat constructor; eauto; try lia.

  - (* Lambda *) 
    rewrite !Har in H0. now setoid_rewrite N.add_comm at 2. 
  - (* LetIn *)
    rewrite !Har in H2. now setoid_rewrite N.add_comm at 2.
  - (* Constant -> Rel *)
    generalize (cst_offset_length e' nm).
    intros. forward H. lia.
    (* Needs well-formedness condition of terms: well scoped definitions *)
    admit.
  - now destruct H0. 
  - now destruct H2.
  - rewrite efnlst_length_trans.
    assert (N.of_nat (n + L3t.dlength defs + 1 + Datatypes.length e') =
            N.of_nat (L3t.dlength defs) + 1 + N.of_nat (n + Datatypes.length e')) by lia.
    rewrite H1 in H0.
    rewrite <- !Nnat.Nat2N.inj_add.
    setoid_rewrite Nat.add_comm at 2.
    apply H0.
  - now destruct H2.
  - destruct l. rewrite nth_empty. simpl. apply H0.
    apply exp_wf_strip_lam. apply H0.
  - now destruct H2.
  - pose (exp_wf_strip_lam 1 _ _ H0).
    assert ((N.of_nat 1 + N.of_nat (n + Datatypes.length e')) =
            (N.of_nat (n + 1 + Datatypes.length e'))) by lia.
    rewrite H3 in e0. apply e0.
Admitted.

Lemma WFTerm_exp_wf e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e' ->
  forall t n, L3t.WFTrm t n ->
         exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t).
Proof. apply WFTerm_exp_wf_ind. Qed.

Lemma eval_wf n t t' : exp_wf n t -> eval t t' -> exp_wf n t'.
Proof. (* should be easy *) Admitted.

Lemma exp_wf_subst e n t  : exp_wf (n + N.of_nat (List.length e)) t ->
                            exp_wf n (subst_env e t).
Proof. (* just as well *) Admitted.

Lemma eval_env_offset n e e' : eval_env e e' -> cst_offset e n = cst_offset e' n.
Proof. induction 1; simpl; rewrite_hyps; trivial. Qed.

Lemma trans_env_eval e e' : eval_env e e' ->
                                (forall t n, trans e n t = trans e' n t) /\
  (forall es n, trans_args (trans e) n es = trans_args (trans e') n es) /\
  (forall d k, trans_fixes (trans e) k d = trans_fixes (trans e') k d).
Proof.
  intros eve.
  apply L3t.TrmTrmsDefs_ind; simpl; intros; try rewrite_hyps; trivial.

  erewrite eval_env_offset; eauto.
  f_equal.
  generalize 0.
  induction t0.
  reflexivity.
  simpl. intros. f_equal.
  injection (H0 n). intros. now rewrite H2.
  apply IHt0. intros.
  now injection (H0 n1).
Qed.

Lemma translate_env_eval e e' t : eval_env e e' -> translate e t = translate e' t.
Proof. intros H; apply (trans_env_eval e e' H). Qed.

Lemma wf_environ_tr e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e'.
Proof.
  intros Hwf; revert e'; induction Hwf.
  - intros e' H; inv H. constructor.
  - simpl; intros e' H'; inv H'. constructor; auto.
    specialize (IHHwf _ H4).
    pose (WFTerm_exp_wf _ _ Hwf H4 IHHwf _ _ H).
    simpl in e0.
    rewrite (translate_env_eval _ _ _ H4) in H5.
    apply (exp_wf_subst e'0 0) in e0.
    apply (eval_wf _ _ _ e0 H5).
    eapply eval_yields_value; now eauto.
  - intros. simpl in H. eauto.
Qed.


Lemma wf_tr_environ_sbst t n e :
  wf_tr_environ e -> e = snd (sbst_env t n e).
Proof.
  induction 1; simpl.
  - reflexivity.
  - destruct (sbst_env t n e); simpl in *.
    subst e0. repeat f_equal.  
    now (rewrite (proj1 (subst_closed_id t) 0); try lia).
Qed.
Lemma eval_env_length e e' : eval_env e e' -> Datatypes.length e = Datatypes.length e'.
Proof. induction 1; simpl; try rewrite_hyps; reflexivity. Qed.

Lemma sbst_env_length t k e :
  Datatypes.length (snd (sbst_env t k e)) = Datatypes.length e.
Proof.
  induction e; simpl in *; try rewrite_hyps; try reflexivity.
  destruct sbst_env. simpl in *. lia.
Qed.
  
Lemma eval_env_inv e e' nm t : wf_tr_environ e' ->
  eval_env (e ++ [(nm, t)]) e' ->
  exists e'' t', eval t t' /\ eval_env (snd (sbst_env t' 0 e)) e'' /\ e' = e'' ++ [(nm, t')].
Proof.
  fold env in *.
  intros wfe' H. revert e' wfe' H.
  induction e; intros.
  simpl in H.
  inv H. inv H4. simpl in *. exists [], t'. intuition. constructor.

  inv H.
  inv wfe'.
  specialize (IHe _ H3 H2).
  destruct IHe as [e'' [t'' [evtt' [evee'' eqe'0]]]].
  subst e'0.
  exists ((nm0, t') :: e''), t''; intuition eauto.
  simpl. case_eq (sbst_env t'' 0 e). intros.
  rewrite H in evee''.
  simpl. constructor. apply evee''.
  rewrite subst_env_app in H4. simpl in H4.
  rewrite <- wf_tr_environ_sbst in H4; eauto.
  pose (eval_env_length _ _ evee''). simpl in *.
  assert(fst (sbst_env t'' 0 e) = fst (sbst_env t'' 0 e'')).
  unfold sbst_env. rewrite !fst_sbst_env_aux'.
  rewrite <- (eval_env_length _ _ evee'').
  pose (length_sbst_env t'' 0 e). rewrite H in e2.
  simpl in e2. now rewrite <- e2.
  rewrite <- H0, H in H4. apply H4.
  apply wf_tr_environ_inv in H3. intuition.
Qed.

Lemma eval_lets e e' t t' : 
  eval_env e e' ->
  wf_tr_environ e' ->
  eval (subst_env e' t) t' ->
  eval (mkLets e t) t'.
Proof.
  revert t t' e'. pattern e. refine (wf_ind (@length _) _ _ e). clear.
  simpl. intros k IHk ? ?. destruct k using rev_ind; intros; simpl in *.
  + inv H; simpl. trivial.
  + simpl. clear IHk0.
    destruct x as [s e].
    apply eval_env_inv in H.
    destruct H as [e'' [t'']]. intuition.
    simpl.
    rewrite mkLets_app; simpl.
    subst e'.
    apply wf_tr_environ_inv in H0.
    apply eval_Let_e with (v1 := t''); intuition.
    simpl.
    rewrite (proj1 (closed_subst_sbst _ H0)).
    rewrite sbst_lets.
    eapply IHk; eauto.
    rewrite length_sbst_env, app_length; simpl; lia.
    rewrite subst_env_app in H1. simpl in H1.
    rewrite <- wf_tr_environ_sbst in H1; auto.
    unfold sbst_env in H1 |- *.
    rewrite fst_sbst_env_aux' in H1 |- *; simpl in *.
    assert (Datatypes.length e'' = Datatypes.length k).
    rewrite <- (eval_env_length _ _ H).
    now rewrite sbst_env_length. rewrite H4 in H1.
    apply H1. apply H0.
Qed.

Ltac crush :=
  simpl; intros; (try solve [rewrite_hyps; eauto; try lia; trivial])
                   || eauto; try lia; trivial.

Lemma subst_env_aux_closed:
  forall (e : list (string * exp)) (t : exp) (k : N),
    wf_tr_environ e -> exp_wf 0 t -> is_value t -> subst_env_aux e k t = t.
Proof.
  induction e; crush.

  erewrite (proj1 (subst_closed_id (snd a))); eauto.
  eapply IHe; eauto. inv H; eauto. lia.
Qed.
  
Lemma subst_env_aux_var_cst e nm k t : wf_tr_environ e ->
  LookupEnv nm e t ->
  subst_env_aux e k (Var_e (cst_offset e nm + k)) = t.
Proof with crush.
  revert t k; induction e; intros; simpl...
  - inversion H0.
  - destruct a as [s a]; simpl in *.
    inv H0.
    + (* Hit *)
      rewrite string_eq_bool_rfl. 
      destruct lt_dec... 
      destruct N.eq_dec...
      clear e0. inv H.
      rewrite (proj1 exp_wf_shift); eauto.
      now apply subst_env_aux_closed.
    + (* Miss *)
      case_eq (string_eq_bool nm s); intros Hnms. 
      apply string_eq_bool_eq in Hnms; contradiction.
      inv H.
      specialize (IHe _ k H3 H7); simpl in IHe.
      destruct lt_dec... 
      destruct N.eq_dec...
      rewrite <- IHe... f_equal. f_equal. lia.
Qed.

Lemma lookup_eval_env:
  forall e : environ,
    wf_environ e ->
    forall (nm : string) t, LookupDfn nm e t ->
    forall (e'' : env),
      eval_env (translate_env e) e'' ->
      wf_tr_environ e'' ->
      exists bef bef' t',
        eval_env bef bef' /\
        eval (subst_env bef' (translate bef t)) t' /\
        LookupEnv nm e'' t'.
Proof.
  intros e wfe nm t Hlookup.
  red in Hlookup.
  generalize_eqs_vars Hlookup. induction Hlookup; simplify_dep_elim;
  rename x0 into eve''; rename x into wfe''. 
  inv wfe. simpl in eve''.
  inv eve''.
  do 3 eexists; intuition eauto. inv wfe''. constructor.

  inv wfe. inv eve''. inv wfe''.
  destruct (IHHlookup H4 t eq_refl e' H6 H5) as
      [bef [bef' [pt'0 [evbef [evt lookupt]]]]].
  do 3 eexists; intuition eauto.
  constructor; eauto. 
  
  apply IHHlookup; eauto.
Qed.  


(** Questions:

  - In the neutral app case, one can have a match in function position,
   how to disallow it -> same idea that the scrutinee should then be a 
   neutral, and there are none in the empty environment might not work.
   It could be a lambda, i.e. ill-formed term.
 *)

Theorem translate_correct (e : environ) (t t' : L3t.Term) :
  wf_environ e -> L3t.WFTrm t 0 ->
  L3eval.WcbvEval e t t' -> (* big step non-deterministic *)
  let e' := translate_env e in
  forall e'', eval_env e' e'' ->
  eval (mkLets e' (translate e' t)) (subst_env e'' (translate e' t')).
  (* big-step deterministic *)
Proof with eauto.
  cbn. intros wfe wft H e'' evenv.
  assert(wfe'':=wf_environ_tr _ _ wfe evenv).
  eapply eval_lets... 
  rewrite !(translate_env_eval _ _ _ evenv).
  induction H.

  + (* Proof *)
    admit.

  + (* Lambda *)
    cbn.
    rewrite subst_env_lam. constructor.

  + (* Prod *)
    cbn. apply eval_erased_exp.

  + (* Constructor *)
    rewrite !subst_env_constructor.
    constructor.
    induction H. constructor.
    constructor. (* Need mutual statement *)
    - admit.
    - apply IHWcbvEvals.
      inversion_clear wft. constructor.
      now inversion_clear H1. 
    
  + (* Ind *)
    unfold translate.
    simpl. apply eval_erased_exp.

  + (* Sort *)
    apply eval_erased_exp.

  + (* Fix *)
    admit.

  + (* Ax *)
    unfold translate. simpl.
    apply eval_axiom.
    
  + (* Const *)
    unfold translate.
    simpl.
    unfold subst_env at 1.
    forward IHWcbvEval; [ |apply wf_environ_lookup in H; auto].
    destruct (lookup_eval_env _ wfe nm t H _ evenv wfe'') as
        [bef [bef' [t' [evbef [evt lookupt]]]]].
    erewrite subst_env_aux_var_cst; [ | eauto ..]. 
    cut(t' = (subst_env e'' (translate e'' s))).
    - intros ->.
      apply wf_value_self_eval; eauto.
      eapply eval_wf.
      -- assert (exp_wf 0 (subst_env e'' (translate e'' t))).
         pose (WFTerm_exp_wf e _ wfe evenv wfe'' _ _ H1). simpl in e0.
         now apply exp_wf_subst.
         apply H2.
      -- apply IHWcbvEval.
    - cut (subst_env e'' (translate e'' t) =
           subst_env bef' (translate bef t)).
      -- intros. rewrite H2 in IHWcbvEval.
         pose proof (proj1 eval_single_valued _ _ IHWcbvEval _ evt).
         now rewrite <- H3.
      -- admit. (* Weakening of environmanent *) 

    
  + (* App Lam *)
    unfold translate.
    simpl.
    rewrite subst_env_application.
    inversion_clear wft.
    econstructor; eauto.
    unfold translate in IHWcbvEval1. simpl in IHWcbvEval1.
    rewrite subst_env_lambda in IHWcbvEval1.
    apply IHWcbvEval1; auto.
    clear IHWcbvEval1 IHWcbvEval2.
    unfold L3.term.whBetaStep in IHWcbvEval3.
    rewrite subst_env_instantiate in IHWcbvEval3.
    apply IHWcbvEval3.

    - (* WF instantiate + wcbeval preserves WF *)
      admit.
      
  + (* LetIn *)
    simpl.
    rewrite subst_env_letin.
    inversion_clear wft.
    econstructor; [eauto| ].
    rewrite subst_env_instantiate in IHWcbvEval2.
    apply IHWcbvEval2.
    
    - (* WF instantiate *)
      admit.
      
  + (* App Fix *)
    admit.

  + (* App no redex: this cannot produce a well-formed value *)
    unfold translate. simpl.
    rewrite !subst_env_application.
    inversion_clear wft.
    assert (L3t.WFTrm efn 0).
    (* Wcbeval preserves wf *)
    admit.
    specialize (IHWcbvEval1 H4).
    specialize (IHWcbvEval2 H5).
    admit.
    
  + (* Case *)
    unfold translate; simpl.
    (* Simple congruence case *)
    admit.
Admitted.

(** start-to-L4 translations **)

Definition myprogram_Program (pgm : program) :=
  do pgm0 <- malecha_L1.program_Program pgm (Ret nil);
    let e' := stripEvalCommute.stripEnv (program.env pgm0) in
    match L3U.stripEnv e' with
    | Ret senv => 
      match L3U.strip e' (stripEvalCommute.strip (program.main pgm0)) with
      | Ret smain => Ret {| main := smain; L3.program.env := senv |}
      | Exc s => Exc ("Error in stripping: " ++ s)
      end
    | Exc s => Exc ("Error while stripping environment: " ++ s)
    end.

Definition program_exp (pgm:program) : exception exp :=
  do prg <- myprogram_Program pgm;
      let (main, env) := prg in
      Ret (translate_program env main).

Definition term_exp (e:program.environ) (t:term) : exception exp :=
  let e' := stripEvalCommute.stripEnv e in
  match L3U.term_Term e' t with
  | Exc s => Exc ("Error while translating term to L3: " ++ s)
  | Ret trm =>
    match L3U.stripEnv e' with
    | Exc s => Exc ("Error while stripping environment: " ++ s)
    | Ret e => Ret (translate_program e trm)
    end
  end.

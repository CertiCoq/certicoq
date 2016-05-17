(** Conversion from a environment-based language
    to a deBruijn-only expression language  for a core calculus including
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
Require Import L4.L3_to_L4.

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
  
Lemma mkLets_app e e' t : mkLets (e ++ e') t =
                          mkLets e' (mkLets e t).
Proof.
  revert t; induction e; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHe.
    reflexivity.
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

Lemma subst_env_app k x t : exp_wf 0 (snd x) ->
  let k' := sbst_env (snd x) 0 k in
  subst_env (k ++ [x]) t =
  (subst_env (snd k') (subst (snd x) (fst k') t)).
Proof.
  intros Hwf k'.
  revert t x k' Hwf. induction k; intros.
  - reflexivity.
  - simpl.
    subst k'.
    rewrite IHk; eauto.
    unfold sbst_env.
    destruct a. destruct x. simpl.
    case_eq (sbst_env_aux e0 k (0, [])).
    intros. simpl. f_equal. simpl in Hwf.
    rewrite substitution. simpl. repeat (f_equal; try lia). lia.
Qed.

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

Lemma subst_env_application e k t u :
  subst_env_aux e k (t $ u) = (subst_env_aux e k t $ subst_env_aux e k u).
Proof. revert t u; induction e; intros; simpl; try rewrite IHe; reflexivity. Qed.

Lemma subst_env_lambda e t :
  subst_env e (Lam_e t) = Lam_e (subst_env_aux e 1 t).
Proof.
  revert t; induction e; intros; try rewrite_hyps; simpl; auto.
Qed.

Lemma subst_env_local_var e k n : n < k ->
  subst_env_aux e k (Var_e n) = Var_e n.
Proof.
  induction e; simpl; auto.
  intros.
  destruct lt_dec. now apply IHe. lia.
Qed.

Lemma subst_env_aux_ax e k s : subst_env_aux e k (Ax_e s) = Ax_e s.
Proof.
  induction e; simpl; try apply IHe; auto.
Qed.

Lemma subst_env_erased_exp e : subst_env e erased_exp = erased_exp.
Proof. apply subst_env_aux_ax. Qed.
  
Lemma eval_erased_exp e : eval (subst_env e erased_exp) (subst_env e erased_exp).
Proof. rewrite subst_env_erased_exp. constructor. Qed.


Lemma subst_env_con_e e k i r args :
  subst_env_aux e k (Con_e (dcon_of_con i r) args) =
  Con_e (dcon_of_con i r) (map_exps (subst_env_aux e k) args).
Proof.
  revert k i r args; induction e; simpl; intros.
  f_equal. induction args; simpl; try rewrite IHargs at 1; reflexivity.
  
  rewrite IHe. f_equal.
  induction args; simpl; try rewrite IHargs at 1; reflexivity.
Qed.

Lemma subst_env_aux_constructor e k i r args :
  subst_env_aux e k (trans e k (L3.term.TConstruct i r args)) =
  Con_e (dcon_of_con i r) (map_terms (fun x => subst_env_aux e k (trans e k x)) args).
Proof.
  revert k i r args; induction e; intros; unfold translate.
  - reflexivity.
  - simpl trans. rewrite subst_env_con_e. f_equal.
    induction args; simpl; try rewrite IHargs; try reflexivity.
Qed.

Definition map_efnlst (f : exp -> exp) :=
  fix map_efnlst (l : efnlst) : efnlst :=
  match l with
  | eflnil => eflnil
  | eflcons t ts => eflcons (f t) (map_efnlst ts)
  end.

Lemma subst_env_fix_e e k defs n :
  subst_env_aux e k (Fix_e defs n) =
  Fix_e (map_efnlst (subst_env_aux e (efnlst_length defs + 1 + k)) defs) n.
Proof.
  revert k defs n; induction e; simpl; intros.
  f_equal. induction defs; simpl; try rewrite IHdefs at 1; reflexivity.

  rewrite IHe. f_equal. 
  revert k; induction defs; simpl; intros; try reflexivity.
  specialize (IHdefs (k + 1)).
  rewrite efnlst_length_subst in *.
  f_equal.
  replace ((1 + efnlst_length defs + 1 + k))
  with (efnlst_length defs + 1 + (k + 1)) by lia.
  rewrite IHdefs. reflexivity.
Qed.

Lemma subst_env_aux_let e k d b :
  subst_env_aux e k (Let_e d b) =
  Let_e (subst_env_aux e k d) (subst_env_aux e (1 + k) b).
Proof.
  revert d b; induction e; intros; simpl; try rewrite IHe; reflexivity.
Qed.

Lemma subst_env_lete e d b :
  subst_env e (Let_e d b) = Let_e (subst_env e d) (subst_env_aux e 1 b).
Proof. apply subst_env_aux_let. Qed.

Lemma subst_env_letin e n d b :
  subst_env e (translate e (L3.term.TLetIn n d b)) =
  Let_e (subst_env e (translate e d)) (subst_env_aux e 1 (trans e 1 b)).
Proof.
  unfold translate. simpl.
  now rewrite subst_env_lete.
Qed.


Ltac crush :=
  simpl; intros; (try solve [rewrite_hyps; eauto; try lia; trivial])
                   || eauto; try lia; trivial.

Inductive LookupEnv : string -> env -> exp -> Prop :=
  LHit : forall (s : string) (p : list (string * exp)) (t : exp),
    LookupEnv s ((s, t) :: p) t
| LMiss : forall (s1 s2 : string) (p : env) (t t' : exp),
    s2 <> s1 -> LookupEnv s2 p t' -> LookupEnv s2 ((s1, t) :: p) t'.

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
  subst_env_aux e k (Var_e (cst_offset e nm + k)) = t /\ exp_wf 0 t.
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
      now split; try apply subst_env_aux_closed.
    + (* Miss *)
      case_eq (string_eq_bool nm s); intros Hnms. 
      apply string_eq_bool_eq in Hnms; contradiction.
      inv H.
      specialize (IHe _ k H3 H7); simpl in IHe.
      destruct lt_dec... 
      destruct N.eq_dec... destruct IHe as [IHe wft]. intuition.
      rewrite <- IHe... f_equal. f_equal. lia.
Qed.

Lemma eval_wf n t t' : exp_wf n t -> eval t t' -> exp_wf n t'.
Proof. (* should be easy *) Admitted.

Lemma exp_wf_subst e n t :
  wf_tr_environ e ->
  exp_wf (n + N.of_nat (List.length e)) t ->
  exp_wf n (subst_env e t).
Proof. (* just as well *) Admitted.

Lemma sbst_closed_id v :
  (forall k t, exp_wf k t -> forall j, k <= j -> sbst v j t = t) /\
  (forall k es, exps_wf k es -> forall j, k <= j -> es{j::=v} = es) /\
  (forall k es, efnlst_wf k es -> forall j, k <= j -> es{j::=v} = es) /\
  (forall k bs, branches_wf k bs -> forall j, k <= j -> bs{j::=v} = bs).
Proof.
  apply my_exp_wf_ind; simpl; intros; try solve [rewrite_hyps; auto; lia]; trivial.
  destruct (lt_dec j j0). reflexivity.
  destruct (N.eq_dec j j0). lia. lia.
Qed.

Declare Equivalent Keys subst_env subst_env_aux.
Set Keyed Unification.

Lemma efnlst_length_trans tr n d :
  efnlst_length (trans_fixes tr n d) = N.of_nat (L3t.dlength d).
Proof. induction d; simpl; try rewrite_hyps; auto; lia. Qed.

(** Needed in well-formedness of cases and fixes *)
Fixpoint is_n_lambda n t :=
  match n with
  | 0%nat => true
  | S n => match t with
          | L3t.TLambda _ b => is_n_lambda n b
          | _ => false
          end
  end.

Fixpoint is_n_lam n t :=
  match n with
  | 0%nat => true
  | S n => match t with
          | Lam_e b => is_n_lam n b
          | _ => false
          end
  end.

Lemma strip_lam_sbst n a k t :
  is_n_lam n t = true ->
  strip_lam n (sbst a (N.of_nat k) t) =
  sbst a (N.of_nat n + N.of_nat k) (strip_lam n t).
Proof with auto; try lia.
  revert t k; induction n. simpl; intros; repeat (f_equal; lia).
  intros t k H.
  destruct t; try discriminate.
  simpl in H.
  simpl.
  specialize (IHn t (S k) H).
  assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
  rewrite H0 in IHn. rewrite IHn.
  f_equal. lia.
Qed.

Lemma strip_lam_subst n a k t :
  is_n_lam n t = true ->
  strip_lam n (subst a (N.of_nat k) t) =
  subst a (N.of_nat n + N.of_nat k) (strip_lam n t).
Proof with auto; try lia.
  revert t k; induction n. simpl; intros; repeat (f_equal; lia).
  intros t k H.
  destruct t; try discriminate.
  simpl in H.
  simpl.
  specialize (IHn t (S k) H).
  assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
  rewrite H0 in IHn. rewrite IHn.
  f_equal. lia.
Qed.

Lemma trans_instantiate e a k :
  wf_tr_environ e -> L3t.WFTrm a 0 ->
  forall b, L3t.WFTrm b (S k) ->
  trans e (N.of_nat k) (L3.term.instantiate a k b) =
  (trans e (1 + N.of_nat k) b) {N.of_nat k := trans e 0 a}.
Proof.
  intros wfe wfa b. revert b k.
  assert(
(forall b k, L3t.WFTrm b (S k) ->
        (trans e (N.of_nat k) (L3.term.instantiate a k b)) =
   (trans e (1 + N.of_nat k) b) {N.of_nat k := (trans e 0 a)}) /\
(forall b k, L3t.WFTrms b (S k) ->
   (trans_args (trans e) (N.of_nat k) (L3.term.instantiates a k b) =
    (trans_args (trans e) (1 + N.of_nat k) b) {N.of_nat k := trans e 0 a}) /\
   (forall ann l, trans_brs (trans e) ann (N.of_nat k) l (L3.term.instantiates a k b) =
           (trans_brs (trans e) ann (1 + N.of_nat k) l b) {N.of_nat k := trans e 0 a})) /\
(forall b k, L3t.WFTrmDs b (S k) ->
   trans_fixes (trans e) (N.of_nat k) (L3.term.instantiateDefs a k b) =
   (trans_fixes (trans e) (1 + N.of_nat k) b) {N.of_nat k + 1 := trans e 0 a})).
  apply L3t.TrmTrmsDefs_ind; try reflexivity.

  (* Var *)
  - intros n k wfn. inv wfn. 
    rewrite L3.term.instantiate_equation.
    rewrite nat_compare_equiv.
    unfold nat_compare_alt. destruct (lt_eq_lt_dec k n) as [[Hlt|Heq]|Hgt]; try lia.
    subst k. simpl.
    destruct lt_dec. lia.
    destruct N.eq_dec. admit. lia.
    simpl.
    destruct lt_dec. reflexivity.
    destruct N.eq_dec. lia. lia.

  - (* Lambda *)
    intros n t Ht k wft. 
    assert ((N.of_nat k + 1) = N.of_nat (S k)) by lia.
    rewrite L3.term.instantiate_equation. simpl.
    rewrite H, Ht. simpl. f_equal. repeat (f_equal; try lia).
    inv wft. auto.
    
  - (* LetIn *)
    intros s dfn IHdfn bod IHbod k wfbod.
    inv wfbod.
    rewrite L3.term.instantiate_equation; simpl.
    f_equal. rewrite IHdfn; auto. 
    assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
    specialize (IHbod (S k)).
    rewrite H in IHbod. 
    rewrite (N.add_comm _ 1), IHbod; auto.
    simpl. repeat (f_equal; try lia).

  - (* Application *)
    intros t IHt fn IHfn k wft. inv wft. 
    rewrite L3.term.instantiate_equation; simpl.
    repeat (f_equal; rewrite_hyps; try lia; eauto).

  - (* Const *)
    intros nm k wft. inv wft.
    rewrite L3.term.instantiate_equation; simpl.
    destruct lt_dec. lia.
    simpl. assert(exists t, LookupEnv nm e t). admit. (*WFtrm environment *)
    destruct H as [t Ht].
    destruct N.eq_dec. lia.
    repeat (f_equal; try lia).

  - (* Constructor *)
    intros i m args IHargs k wft. inv wft.
    rewrite L3.term.instantiate_equation; simpl.
    f_equal. destruct (IHargs k); auto.
    
  - (* Match *)
    intros. inv H1. destruct (H0 k H7). 
    rewrite L3.term.instantiate_equation; simpl; intuition.
    rewrite_hyps; f_equal; simpl; eauto. 

  - (* Fix *)
    intros defs IHdefs n k wft. inv wft.
    specialize (IHdefs (k + L3t.dlength defs)%nat).
    rewrite L3.term.instantiate_equation; simpl; intuition.
    rewrite_hyps. f_equal; simpl; eauto.
    rewrite efnlst_length_trans.
    rewrite <- L3t.instantiateDefs_pres_dlength.
    assert ((N.of_nat (k + L3t.dlength defs)) = (N.of_nat (L3t.dlength defs) + N.of_nat k)) by lia. rewrite <- H0.
    rewrite H.
    simpl. repeat (f_equal; try lia).

  - simpl. intuition trivial.
  - intros t IHt ts IHts k wft. inv wft.
    destruct (IHts k H3). specialize (IHt _ H1).
    rewrite L3.term.instantiates_equation; simpl; intuition.
    f_equal; auto.
    f_equal; auto.
    rewrite IHt.
    simpl.
    rewrite strip_lam_subst. reflexivity.
    (* Well-formedness of fixes *)
    admit.

  - intros n t IHt ann ts IHts k wft. inv wft.
    specialize (IHt k H4). specialize (IHts k H5).
    cut (is_n_lambda 1 t = true). intros H.
    rewrite L3.term.instantiateDefs_equation.
    destruct t; try discriminate.
    rewrite L3.term.instantiate_equation in IHt |- *.
    simpl in IHt |- *.
    f_equal.
    injection IHt as IHt. rewrite IHt. repeat (f_equal; try lia).
    apply IHts.
    admit.  (* Well-formedness of fixes *)
  - tauto.
Admitted.

Lemma subst_env_aux_subst e a k b :
  subst_env_aux e k (subst a 0 b) =
  subst (subst_env_aux e k a) 0 (subst_env_aux e (1 + k) b).
Proof.
  revert a k b. induction e; simpl; intros. reflexivity.
  pose (substitution b a0 (snd a) 0 k). simpl in e0.
  rewrite e0; try lia. rewrite IHe.
  repeat (f_equal; try lia).
Qed.

Lemma eval_axiom e nm : eval (subst_env e (Ax_e nm)) (subst_env e (Ax_e nm)).
Proof.
  unfold erased_exp, subst_env. simpl.
  induction e; simpl; try apply IHe. constructor. 
Qed.

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
    apply (exp_wf_subst e'0 0) in e0; auto.
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
  destruct (wf_tr_environ_inv _ _ _ H3) as (valt''&wft''&wfe'').
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
    apply H1. apply H0. auto.
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
  revert t t' H wft.
  assert ((forall t t' : L3t.Term,
   L3eval.WcbvEval e t t' ->
   L3t.WFTrm t 0 ->
   eval (subst_env e'' (translate e'' t)) (subst_env e'' (translate e'' t'))) /\
   (forall t t' : L3t.Terms,
   L3eval.WcbvEvals e t t' ->
   L3t.WFTrms t 0 ->
   evals (map_terms (fun t => subst_env e'' (translate e'' t)) t)
         (map_terms (fun t' => subst_env e'' (translate e'' t')) t'))).
  apply L3eval.WcbvEvalEvals_ind.

  + (* Proof *)
    intros wft. unfold translate. simpl.
    unfold subst_env; rewrite subst_env_aux_ax. constructor.

  + (* Lambda *)
    cbn. intros nm bod wft.
    rewrite subst_env_lam. constructor.

  + (* Prod *)
    intros bn bod wft.
    cbn. apply eval_erased_exp.

  + (* Constructor *)
    intros i r args args' Hargs Hargs' wft. inv wft.
    specialize (Hargs' H3).
    unfold subst_env.
    rewrite !subst_env_aux_constructor.
    constructor.
    apply Hargs'.
    
  + (* Ind *)
    unfold translate.
    intros i wft.
    simpl. apply eval_erased_exp.

  + (* Sort *)
    intros s wft.
    apply eval_erased_exp.

  + (* Fix *)
    intros dts m wft.
    unfold translate; simpl.
    unfold subst_env. rewrite subst_env_fix_e. constructor.

  + (* Ax *)
    intros nm wft.
    unfold translate, subst_env. simpl.
    apply eval_axiom.
    
  + (* Const *)
    unfold translate.
    intros nm t s H evalts IHt wft.
    simpl.
    unfold subst_env at 1.
    forward IHt; [ |apply wf_environ_lookup in H; auto].
    destruct (lookup_eval_env _ wfe nm t H _ evenv wfe'') as
        [bef [bef' [t' [evbef [evt lookupt]]]]].
    destruct (subst_env_aux_var_cst e'' nm 0 _ wfe'' lookupt) as [Hs ewf].
    rewrite Hs. 
    cut(t' = (subst_env e'' (translate e'' s))).
    - intros ->.
      apply wf_value_self_eval; eauto.
    - cut (subst_env e'' (translate e'' t) =
           subst_env bef' (translate bef t)).
      -- intros. rewrite H1 in IHt.
         pose proof (proj1 eval_single_valued _ _ IHt _ evt).
         now rewrite <- H2.
      -- admit. (* Weakening of environmanent *) 
    
  + (* App Lam *)
    unfold translate. simpl.
    intros * evfn IHWcbvEval1 eva1 IHWcbvEval2 evbod IHWcbvEval3 wft.
    unfold subst_env. rewrite subst_env_application.
    inversion_clear wft.
    specialize (IHWcbvEval1 H).
    specialize (IHWcbvEval2 H0).
    econstructor; eauto.
    unfold translate in IHWcbvEval1. simpl in IHWcbvEval1.
    rewrite subst_env_lambda in IHWcbvEval1.
    apply IHWcbvEval1; auto.
    clear IHWcbvEval1 IHWcbvEval2.
    unfold L3.term.whBetaStep in IHWcbvEval3.
    unfold subst_env in IHWcbvEval3.
    unfold translate in IHWcbvEval3.
    assert(L3t.WFTrm a1' 0).
    (* wcbeval preserves WF *)  admit.
    assert(L3t.WFTrm bod 1).
    (* wcbeval preserves WF *)  admit.
    erewrite (trans_instantiate e'' a1' 0) in IHWcbvEval3; eauto.
    simpl. simpl in IHWcbvEval3.
    rewrite subst_env_aux_subst in IHWcbvEval3; auto.
    assert(exp_wf 0 (subst_env e'' (translate e'' a1'))).
    apply exp_wf_subst; eauto.
    apply (WFTerm_exp_wf e e'' wfe evenv wfe'' _ _ H1).
    rewrite (proj1 (closed_subst_sbst _ H3)). 
    apply IHWcbvEval3; eauto.
    (* WF instantiate *)
    admit.
      
  + (* LetIn *)
    intros * evfn IHWcbvEval1 evbod IHWcbvEval2 wft. inv wft.
    specialize (IHWcbvEval1 H3). 
    simpl.
    rewrite subst_env_letin.
    econstructor; [eauto| ].
    assert(L3t.WFTrm dfn' 0).
    (* wcbeval preserves WF *)  admit.
    assert(L3t.WFTrm bod 1).
    (* wcbeval preserves WF *)  admit.
    forward IHWcbvEval2.
    unfold translate in IHWcbvEval2 |- *.
    rewrite (trans_instantiate e'' dfn' 0) in IHWcbvEval2; auto.
    simpl in IHWcbvEval2. unfold subst_env in IHWcbvEval2 |- *.
    rewrite subst_env_aux_subst in IHWcbvEval2; auto.
    simpl.
    assert(exp_wf 0 (subst_env e'' (translate e'' dfn'))).
    apply exp_wf_subst; eauto.
    apply (WFTerm_exp_wf e e'' wfe evenv wfe'' _ _ H).
    rewrite (proj1 (closed_subst_sbst _ H2)).
    apply IHWcbvEval2.
    (* WF instantiate *)
    admit.
      
  + (* App Fix *)
    intros * evfn Hfn fixstep evfix IHevfix wft.
    inv wft.
    specialize (Hfn H1).
    forward IHevfix. Focus 2. admit. (* WF *)
    unfold translate. simpl.
    unfold subst_env; rewrite subst_env_application.
    unfold subst_env, translate in Hfn. simpl in Hfn.
    rewrite subst_env_fix_e in Hfn.
    (* Treat fixstep *)
    admit.
    (* eapply eval_FixApp_e. apply Hfn. *)

  + (* App no redex: this cannot produce a well-formed value *)
    intros * evfn Hfn napp nlam nfix evarg Harg wft. inv wft.
    unfold translate. simpl.
    unfold subst_env.
    rewrite !subst_env_application.
    assert (L3t.WFTrm efn 0).
    (* Wcbeval preserves wf *)
    admit.
    specialize (Hfn H1).
    specialize (Harg H3).
    admit.
    
  + (* Case *)
    unfold translate; simpl.
    (* Simple congruence case *)
    admit.

  (** Terms *)
  + intros; constructor.
  + intros. inv H1. specialize (H0 H6). simpl.
    constructor; auto.

  (** Generalized goal *)
  + tauto.
Admitted.

(** Conversion from a environment-based language
    to a deBruijn-only expression language  for a core calculus including
    mutually recursive functions, data constructors, and pattern matching.
 *)

(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_QuotedCoq" as L1.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4.
(******)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
  Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

Require Import Common.AstCommon.
Require Import L3.program.
Require Import L3.term.
Require Import L3.compile.

Require L3.L3.
Module L3eval := L3.wcbvEval.
Module L3C := L3.compile.
Module L3t := L3.term.
Module L3U := L3.unaryApplications.
Module L3N := L3.wNorm.

Require Import L4.expression.
Require Import L4.L3_to_L4.

(** Should be true in L3 *)
Lemma wftrm_fix dts m t n :
  L3t.WFTrm (TFix dts m) n ->
  L3.term.dnthBody m dts = Some t -> isLambda t.
Proof. intros. inv H. Admitted.

Fixpoint is_n_lambda (n : nat) (t : L3t.Term) :=
  match n with
  | 0%nat => true
  | S n => 
    match t with
    | L3t.TLambda _ t => is_n_lambda n t
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

(* Now move to Crct predicate which implies WF 
  + closure w.r.t environment and correcness of annotations
  of cases.
*)
Lemma wftrm_case ann mch brs n :
  L3t.WFTrm (L3C.TCase ann mch brs) n ->
  tlength brs = List.length (snd ann) /\
  (forall n t, tnth n brs = Some t ->
          is_n_lambda (List.nth n (snd ann) 0%nat) t = true).
Proof. intros. inv H. Admitted.

Lemma wcbeval_preserves_wf e t t' :
  WFTrm t 0 -> L3eval.WcbvEval e t t' -> WFTrm t' 0.
Admitted.

Lemma instantiate_preserves_wf t k k' a : (k' <= k)%nat ->
  WFTrm a 0 ->
  WFTrm t (S k) ->
  WFTrm (L3.term.instantiate a k' t) k.
Admitted.
(* End of L3 requirements *)

Ltac crush :=
  simpl; intros; (try solve [rewrite_hyps; eauto; try lia; trivial])
                   || eauto; try lia; trivial.
Ltac case_call f :=
  let call := fresh "call" in
  remember f as call; destruct call.

Ltac equaln := repeat (f_equal; try lia); auto.

Inductive wf_environ : environ Term -> Prop :=
| wf_nil : wf_environ []
| wf_cons_trm s t e :
    WFTrm t 0 -> wf_environ e -> wf_environ (cons (s, ecTrm t) e)
| wf_cons_ty s n t e :
    wf_environ e -> wf_environ (cons (s, ecTyp Term n t) e).

Lemma wf_environ_lookup (e : environ Term) (t : Term) nm :
  wf_environ e -> LookupDfn nm e t -> WFTrm t 0.
Proof.
  intros wfe Het. revert wfe. red in Het.
  dependent induction Het; intros wfe.
  now inversion_clear wfe.
  apply IHHet. now inversion_clear wfe.
Qed.

Inductive wf_tr_environ : list (string * exp) -> Prop :=
| wf_tr_nil : wf_tr_environ []
| wf_tr_cons s t e :
    wf_tr_environ e ->
    exp_wf 0 t -> (* Is closed w.r.t. environment *)
    is_value t -> (* Is a value *)
    wf_tr_environ (cons (s, t) e).


Definition subst_env_aux e n (t : exp) :=
  fold_left
    (fun t (x : string * exp) => t{n := snd x})
    e t.

Definition subst_env e (t : exp) := subst_env_aux e 0 t.

Inductive eval_env : env -> env -> Prop :=
| eval_env_nil : eval_env nil nil
| eval_env_cons nm t e e' t' :
    eval_env e e' ->
    eval (subst_env e' t) t' -> eval_env ((nm, t) :: e) ((nm, t') :: e').

Lemma wf_tr_environ_inv k s x :
  wf_tr_environ (k ++ [(s, x)]) ->
   is_value x /\ exp_wf 0 x /\ wf_tr_environ k. 
Proof.
  induction k; simpl in *; intros.
  - now inv H.
  - inv H. intuition. constructor; auto.
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

(** Looking up in the evaluated environment *)
Lemma lookup_eval_env:
  forall e : environ L3.compile.Term,
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

Definition map_branches (f : N -> exp -> exp) :=
  fix map_branches (l : branches_e) : branches_e :=
  match l with
  | brnil_e => brnil_e
  | brcons_e d n e brs => brcons_e d n (f n e) (map_branches brs)
  end.

Definition map_efnlst (f : exp -> exp) :=
  fix map_efnlst (l : efnlst) : efnlst :=
  match l with
  | eflnil => eflnil
  | eflcons t ts => eflcons (f t) (map_efnlst ts)
  end.

Lemma efnlength_map g l : efnlength (map_efnlst g l) = efnlength l.
Proof. induction l; crush. Qed.

Lemma efnlength_trans g k l : efnlength (trans_fixes g k l) = dlength l.
Proof. induction l; crush. Qed.

Lemma map_efnlst_id es : map_efnlst (fun x => x) es = es.
Proof. induction es; simpl; intros; now rewrite_hyps. Qed.

Lemma map_efnlst_comp f g es : map_efnlst g (map_efnlst f es) = map_efnlst (fun x => g (f x)) es.
Proof. induction es; simpl; intros; now rewrite_hyps. Qed.

Lemma efnlst_length_map f es : efnlst_length (map_efnlst f es) = efnlst_length es.
Proof. induction es; simpl; intros; now rewrite_hyps. Qed.
Lemma efnlst_length_trans tr n d :
  efnlst_length (trans_fixes tr n d) = N.of_nat (dlength d).
Proof. induction d; simpl; try rewrite_hyps; auto; lia. Qed.
  
Lemma subst_efnlst_map x k v :
  subst_efnlst x k v = map_efnlst (subst x k) v.
Proof. induction v; simpl; intros; now try rewrite_hyps. Qed.

Lemma efnlength_efnlst_length l : N.of_nat (efnlength l) = efnlst_length l.
Proof. induction l; simpl; intros; try rewrite_hyps; lia. Qed.

(** Transformation of the environment into lets and its 
    relation to substitution.
 *)

Lemma mkLets_app e e' t : mkLets (e ++ e') t =
                          mkLets e' (mkLets e t).
Proof.
  revert t; induction e; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHe.
    reflexivity.
Qed.

(** This version of substitution implements the one used 
   by lets: folding from right to left, incrementally 
   substituting into the environment. *)

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
  fst (sbst_env_aux e k acc) = fst acc + N.of_nat (List.length k).
Proof.
  induction k; simpl.
  - destruct acc. simpl. lia.
  - case_call (sbst_env_aux e k acc).
    simpl in *. 
    case_call (sbst_env_aux e k (fst acc, [])).
    subst n; simpl. lia.
Qed.

Lemma fst_sbst_env_aux_acc e k acc :
  fst (sbst_env_aux e k acc) = fst (sbst_env_aux e k (fst acc, [])).
Proof.
  now rewrite !fst_sbst_env_aux.
Qed.

Lemma snd_sbst_env_aux e k acc :
  snd (sbst_env_aux e k acc) =
  snd (sbst_env_aux e k (fst acc, [])) ++ snd acc.
Proof.
  induction k; simpl.

  - reflexivity.
  - generalize (fst_sbst_env_aux_acc e k acc).
    case_call (sbst_env_aux e k acc).
    simpl in *. 
    case_call (sbst_env_aux e k (fst acc, [])).
    subst e0; simpl.
    f_equal. f_equal.
    simpl in *.
    now intros ->.
Qed.

Lemma sbst_env_length t k e :
  Datatypes.length (snd (sbst_env t k e)) = Datatypes.length e.
Proof.
  induction e; simpl in *; try rewrite_hyps; try reflexivity.
  destruct sbst_env. simpl in *. lia.
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
      now setoid_rewrite fst_sbst_env_aux_acc at 2.
Qed.
    
(** Relation of subst_env (folding left to right) and sbst_env *)

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

(** Simplification lemmas for [subst_env] *)

Lemma subst_env_aux_closed:
  forall (e : list (string * exp)) (t : exp) (k : N),
    wf_tr_environ e -> exp_wf 0 t -> is_value t -> subst_env_aux e k t = t.
Proof.
  induction e; crush.
  erewrite (proj1 (subst_closed_id (snd a))); eauto.
  eapply IHe; eauto. inv H; eauto. lia.
Qed.

Lemma subst_env_aux_local_var e k n : n < k ->
  subst_env_aux e k (Var_e n) = Var_e n.
Proof.
  induction e; simpl; auto.
  intros.
  destruct lt_dec. now apply IHe. lia.
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

Lemma subst_env_aux_subst e a k b :
  subst_env_aux e k (subst a 0 b) =
  subst (subst_env_aux e k a) 0 (subst_env_aux e (1 + k) b).
Proof.
  revert a k b. induction e; simpl; intros. reflexivity.
  pose (substitution b a0 (snd a) 0 k). simpl in e0.
  rewrite e0; try lia. rewrite IHe.
  repeat (f_equal; try lia).
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

Lemma subst_env_application e k t u :
  subst_env_aux e k (t $ u) = (subst_env_aux e k t $ subst_env_aux e k u).
Proof. revert t u; induction e; intros; simpl; try rewrite IHe; reflexivity. Qed.

Lemma subst_env_lambda e t :
  subst_env e (Lam_e t) = Lam_e (subst_env_aux e 1 t).
Proof.
  revert t; induction e; intros; try rewrite_hyps; simpl; auto.
Qed.

Lemma subst_env_aux_ax e k s : subst_env_aux e k (Ax_e s) = Ax_e s.
Proof.
  induction e; simpl; try apply IHe; auto.
Qed.

Lemma subst_env_erased_exp e : subst_env e erased_exp = erased_exp.
Proof. apply subst_env_aux_ax. Qed.

Lemma subst_env_aux_con_e e k i r args :
  subst_env_aux e k (Con_e (dcon_of_con i r) args) =
  Con_e (dcon_of_con i r) (map_exps (subst_env_aux e k) args).
Proof.
  revert k i r args; induction e; simpl; intros.
  f_equal. induction args; simpl; try rewrite IHargs at 1; reflexivity.
  
  rewrite IHe. f_equal.
  induction args; simpl; try rewrite IHargs at 1; reflexivity.
Qed.

Lemma subst_env_aux_constructor e k i r args :
  subst_env_aux e k (trans e k (TConstruct i r args)) =
  Con_e (dcon_of_con i r) (map_terms (fun x => subst_env_aux e k (trans e k x)) args).
Proof.
  revert k i r args; induction e; intros; unfold translate.
  - reflexivity.
  - simpl trans. rewrite subst_env_aux_con_e. f_equal.
    induction args; simpl; try rewrite IHargs; try reflexivity.
Qed.

Lemma subst_env_aux_fix_e e k defs n :
  subst_env_aux e k (Fix_e defs n) =
  Fix_e (map_efnlst (subst_env_aux e (efnlst_length defs + k)) defs) n.
Proof.
  revert k defs n; induction e; simpl; intros.
  f_equal. induction defs; simpl; try rewrite IHdefs at 1; reflexivity.

  rewrite IHe. f_equal. 
  revert k; induction defs; simpl; intros; try reflexivity.
  specialize (IHdefs (k + 1)).
  rewrite efnlst_length_subst in *.
  f_equal.
  replace ((1 + efnlst_length defs + k))
  with (efnlst_length defs + (k + 1)) by lia.
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
  subst_env e (translate e (TLetIn n d b)) =
  Let_e (subst_env e (translate e d)) (subst_env_aux e 1 (trans e 1 b)).
Proof.
  unfold translate. simpl.
  now rewrite subst_env_lete.
Qed.

Lemma subst_env_aux_match e k mch pars brs :
  subst_env_aux e k (Match_e mch pars brs) =
  Match_e (subst_env_aux e k mch) pars
          (map_branches (fun n => subst_env_aux e (n + k)) brs). 
Proof.
  revert k mch brs; induction e; simpl; intros; auto.

  f_equal.
  induction brs; simpl; auto. now rewrite <- IHbrs.

  rewrite IHe. f_equal.
  induction brs; simpl; auto. now rewrite <- IHbrs.
Qed.  

(** Well-formedness is preserved by subst_env *)

Lemma exp_wf_subst e n t :
  wf_tr_environ e ->
  exp_wf (n + N.of_nat (List.length e)) t ->
  exp_wf n (subst_env e t).
Proof.
  revert n t; induction e; simpl; intros.
  - now rewrite N.add_0_r in H0.
  - inv H. simpl.
    apply (IHe n (subst t0 0 t) H3).
    eapply (proj1 subst_preserves_wf'); eauto; lia.
Qed. 

(** Needed in well-formedness of cases and fixes,
  for strip_lam *)

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

Lemma strip_lam_shift n a k t :
  is_n_lam n t = true ->
  strip_lam n (shift a k t) =
  shift a (N.of_nat n + k) (strip_lam n t).
Proof with auto; try lia.
  revert t k; induction n. simpl; intros; repeat (f_equal; lia).
  intros t k H.
  destruct t; try discriminate.
  simpl in H.
  simpl.
  specialize (IHn t (1 + k) H).
  rewrite IHn.
  f_equal. lia.
Qed.

Lemma exp_wf_strip_lam (k : nat) (e : exp) n :
  exp_wf n e -> exp_wf (N.of_nat k + n) (strip_lam k e).
Proof.
  revert e n; induction k; trivial.
  intros e n H. 
  destruct H; simpl in *;
  try (unfold strip_lam; eapply weaken_wf; eauto; lia).

  - (* Lambda *)
    specialize (IHk e (1 + i)).
    assert (N.of_nat k + (1 + i) = N.pos (Pos.of_succ_nat k) + i) by lia.
    rewrite H0 in IHk. eauto.

  - (* Ax *) constructor.
Qed.

Arguments strip_lam : simpl never.


(** Well-formedness is preserved by the translation *)

Lemma nth_empty (A : Type) n def : @nth A n [] def = def.
Proof.
  destruct n; reflexivity.
Qed.

Lemma WFTerm_exp_wf_ind e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e' ->
  (forall t n, WFTrm t n ->
          exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t)) /\
  (forall t n, WFTrms t n ->
    exps_wf (N.of_nat (n + List.length e')) (trans_args (trans e') (N.of_nat n) t) /\
   forall i p l k,
     branches_wf (N.of_nat (n + List.length e'))
                 (trans_brs (trans e') i p l (N.of_nat n) k t)) /\
  (forall t n, WFTrmDs t n ->
          efnlst_wf (N.of_nat (n + List.length e'))
                    (trans_fixes (trans e') (N.of_nat n) t))
.
Proof.
  assert(Har:forall n, N.pos (Pos.of_succ_nat n) = 1 + N.of_nat n) by (intros; lia).
  intros wfe evee' wfe'.
  apply WFTrmTrmsDefs_ind; intros; unfold translate;
  simpl in *; repeat constructor; eauto; try lia.

  - (* Lambda *) 
    now rewrite !Har in H0. 
  - (* LetIn *)
    now rewrite !Har in H2. 
  - (* Constant -> Rel *)
    generalize (cst_offset_length e' nm).
    intros. forward H. lia.
    (* Needs well-formedness condition of terms: well scoped definitions *)
    admit.
  - now destruct H0. 
  - destruct m as [[i pars] l]. simpl. destruct H2.
    constructor. apply H0. apply H3.
  - rewrite efnlst_length_trans.
    assert (N.of_nat (n + dlength defs + Datatypes.length e') =
            N.of_nat (dlength defs + n + Datatypes.length e')) by lia.
    rewrite H1 in H0.
    rewrite <- !Nnat.Nat2N.inj_add.
    setoid_rewrite Nat.add_comm at 3.
    rewrite Nat.add_assoc.
    apply H0.
  - now destruct H2.
  - destruct l. rewrite nth_empty. simpl. apply H0.
    apply exp_wf_strip_lam. apply H0.
  - now destruct H2.
Admitted.

Lemma WFTerm_exp_wf e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e' ->
  forall t n, WFTrm t n ->
         exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t).
Proof. apply WFTerm_exp_wf_ind. Qed.

(** Translation respects shifting (only applied to initially closed [a]'s) *)

Lemma trans_shift e a n k : WFTrm a (N.to_nat k) ->
  trans e (k + N.of_nat n) a = shift (N.of_nat n) k (trans e k a).
Proof.
  revert a k.
  assert
    ((forall a k, WFTrm a (N.to_nat k) ->
             trans e (k + N.of_nat n) a = shift (N.of_nat n) k (trans e k a)) /\
     (forall a k, WFTrms a (N.to_nat k) ->
             (trans_args (trans e) (k + N.of_nat n) a =
              shifts (N.of_nat n) k (trans_args (trans e) k a)) /\
             (forall n' i p ann,
                 (trans_brs (trans e) i p ann (k + N.of_nat n) n' a =
             shift_branches (N.of_nat n) k (trans_brs (trans e) i p ann k n' a)))) /\
     (forall a k, WFTrmDs a (N.to_nat k) ->
             trans_fixes (trans e) (k + N.of_nat n) a =
             shift_fns (N.of_nat n) k (trans_fixes (trans e) k a))); [ |tauto].
  clear. apply TrmTrmsDefs_ind; intros *; auto.

  - simpl; destruct lt_dec. reflexivity.
    intros Hwf; inv Hwf. lia.

  - intros IHa k Hwf; inv Hwf.
    specialize (IHa (1 + k)).
    simpl; rewrite <- IHa; equaln.
    assert (S (N.to_nat k) = N.to_nat (1 + k)) by lia. congruence.

  - intros IHa1 t' IHa2 k Hwf. inv Hwf.
    specialize (IHa1 k).
    specialize (IHa2 (1 + k)).
    simpl; rewrite <- IHa1, <- IHa2; equaln.
    assert (S (N.to_nat k) = N.to_nat (1 + k)) by lia. congruence.

  - intros IHa1 a2 IHa2 k Hwf.
    simpl; inv Hwf; rewrite <- IHa1, <- IHa2; equaln.

  - intros Hwf. inv Hwf. simpl; destruct lt_dec; equaln.

  - intros IH k Hwf. inv Hwf. simpl.
    destruct (IH k); auto.
    now rewrite H.

  - intros IH ts IH2 k Hwf. inv Hwf. simpl.
    rewrite (IH k); auto.
    destruct p as [[ind pars] args]. simpl.
    f_equal.
    destruct (IH2 k); auto.

  - intros IH n' k Hwf. inv Hwf. simpl.
    f_equal.
    rewrite N.add_assoc, IH.
    rewrite efnlst_length_trans.
    unfold shift_fns. equaln.
    assert ((N.to_nat (N.of_nat (dlength d) + k))%nat =
            (N.to_nat k + dlength d)%nat) by lia.
    now rewrite H.

  - intros IHt ts IH k Hwf. inv Hwf. simpl.
    rewrite IHt; auto.
    destruct (IH k); auto.
    rewrite H. intuition. rewrite H0.
    equaln. rewrite strip_lam_shift. equaln.
    (* WF condition on matches *)
    admit.
  
  - intros IHt n1 d IHd k Hwf. inv Hwf.
    simpl.
    rewrite IHt; auto.
    rewrite IHd; auto. 
Admitted.    

(** Translation respects instantiation *)

Lemma trans_instantiate_any e a k (k' : nat) :
  WFTrm a 0 -> forall b, WFTrm b (S k) -> (k' <= k)%nat ->
  trans e (N.of_nat k) (L3.term.instantiate a k' b) =
  (trans e (1 + N.of_nat k) b)
    {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)}.
Proof.
  intros wfa b. revert b k k'.
  assert (
    (forall b k k', WFTrm b (S k) -> (k' <= k)%nat ->
            (trans e (N.of_nat k) (L3.term.instantiate a k' b)) =
            (trans e (1 + N.of_nat k) b)
              {N.of_nat k' := shift (N.of_nat (k - k')) 0
                                    (trans e 0 a)}) /\
    (forall b k k', WFTrms b (S k) -> (k' <= k)%nat ->
         (trans_args (trans e) (N.of_nat k) (L3.term.instantiates a k' b) =
          (trans_args (trans e) (1 + N.of_nat k) b)
            {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)}) /\
    (forall i p ann l,
        trans_brs (trans e) i p ann (N.of_nat k) l (L3.term.instantiates a k' b) =
        (trans_brs (trans e) i p ann (1 + N.of_nat k) l b)
          {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)})) /\
    (forall b k k', WFTrmDs b (S k) -> (k' <= k)%nat ->
        trans_fixes (trans e) (N.of_nat k) (L3.term.instantiateDefs a k' b) =
        (trans_fixes (trans e) (1 + N.of_nat k) b)
          {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)})).
  apply TrmTrmsDefs_ind; try reflexivity.

  (* Var *)
  - intros n k k' wfn kk'. inv wfn.
    rewrite L3.term.instantiate_equation.
    rewrite nat_compare_equiv.
    unfold nat_compare_alt.
    destruct (lt_eq_lt_dec k' n) as [[Hlt|Heq]|Hgt]; try lia.
    simpl. destruct lt_dec. lia. destruct N.eq_dec. lia.
    f_equal; lia.
    subst n. simpl.
    destruct lt_dec. lia.
    destruct N.eq_dec.
    + rewrite shift_twice by lia.
      replace (N.of_nat (k - k') + N.of_nat k') with (N.of_nat k) by lia.
      rewrite <- trans_shift by equaln. equaln.
    + lia.
    + simpl.
      destruct lt_dec. reflexivity.
      destruct N.eq_dec. lia. lia.

  - (* Lambda *)
    intros n t Ht k k' wft kk'.
    assert ((1 + N.of_nat k) = N.of_nat (S k)) by lia.
    rewrite L3.term.instantiate_equation. simpl.
    rewrite H, Ht. simpl. f_equal. repeat (f_equal; try lia).
    inv wft. auto. lia.
    
  - (* LetIn *)
    intros s dfn IHdfn bod IHbod k k' wfbod kk'.
    inv wfbod.
    rewrite L3.term.instantiate_equation; simpl.
    f_equal. rewrite IHdfn; auto.
    assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
    specialize (IHbod (S k)).
    rewrite H in IHbod.
    rewrite IHbod; auto. simpl. equaln. lia.

  - (* Application *)
    intros t IHt fn IHfn k k' wft kk'. inv wft.
    rewrite L3.term.instantiate_equation; simpl.
    repeat (f_equal; rewrite_hyps; try lia; eauto).

  - (* Const *)
    intros nm k k' wft kk'. inv wft.
    rewrite L3.term.instantiate_equation; simpl.
    destruct lt_dec. lia.
    simpl. assert(exists t, LookupEnv nm e t). admit. (*WFtrm environment *)
    destruct H as [t Ht].
    destruct N.eq_dec. lia.
    repeat (f_equal; try lia).

  - (* Constructor *)
    intros i m args IHargs k k' wft kk'. inv wft.
    rewrite L3.term.instantiate_equation; simpl.
    f_equal. destruct (IHargs k k' H3 kk'); auto.
    
  - (* Match *)
    intros. inv H1. destruct (H0 k k' H8 H2).
    rewrite L3.term.instantiate_equation; simpl; intuition.
    rewrite_hyps; f_equal; simpl; eauto.

  - (* Fix *)
    intros defs IHdefs n k k' wft kk'. inv wft.
    specialize (IHdefs (k + dlength defs)%nat).
    rewrite L3.term.instantiate_equation; simpl; intuition.
    assert (k' + dlength defs <= k + dlength defs)%nat by lia.
    specialize (IHdefs (k' + dlength defs)%nat H2 H).
    f_equal; simpl; eauto.
    rewrite efnlst_length_trans.
    rewrite <- instantiateDefs_pres_dlength.
    assert ((N.of_nat (k + dlength defs)) =
            (N.of_nat (dlength defs) + N.of_nat k)) by lia.
    rewrite <- H0. rewrite IHdefs.
    simpl. repeat (f_equal; try lia).

  - simpl. intuition trivial.
  - intros t IHt ts IHts k k' wft kk'. inv wft.
    destruct (IHts k k' H3 kk').
    specialize (IHt k k' H1 kk').
    rewrite L3.term.instantiates_equation. simpl trans_args.
    rewrite IHt.
    rewrite H. split; intuition.
    simpl.
    f_equal. rewrite IHt.
    rewrite strip_lam_subst. reflexivity.
    (* Well-formedness of matches *)
    admit.
    intuition.

  - intros n t IHt ann ts IHts k k' wft kk'. inv wft.
    specialize (IHt k k' H4 kk'). specialize (IHts k k' H5 kk').
    rewrite L3.term.instantiateDefs_equation.
    simpl. now rewrite IHt, IHts.
  - tauto.
Admitted.

Lemma trans_instantiate e a k :
  wf_tr_environ e -> WFTrm a 0 ->
  forall b, WFTrm b (S k) ->
  trans e (N.of_nat k) (L3.term.instantiate a k b) =
  (trans e (1 + N.of_nat k) b) {N.of_nat k := trans e 0 a}.
Proof.
  intros.
  rewrite trans_instantiate_any; auto.
  equaln. rewrite <- minus_n_n.
  now rewrite (proj1 shift0). 
Qed.

(** Evaluation in the target language *)

Lemma eval_erased_exp e : eval (subst_env e erased_exp) (subst_env e erased_exp).
Proof. rewrite subst_env_erased_exp. constructor. Qed.

Lemma eval_axiom e nm : eval (subst_env e (Ax_e nm)) (subst_env e (Ax_e nm)).
Proof.
  unfold erased_exp, subst_env. simpl.
  induction e; simpl; try apply IHe. constructor. 
Qed.

Lemma eval_env_offset n e e' : eval_env e e' -> cst_offset e n = cst_offset e' n.
Proof. induction 1; simpl; rewrite_hyps; trivial. Qed.

(** The translation is not looking at the values in the environment *)

Lemma trans_env_eval e e' : eval_env e e' ->
                                (forall t n, trans e n t = trans e' n t) /\
  (forall es n, trans_args (trans e) n es = trans_args (trans e') n es) /\
  (forall d k, trans_fixes (trans e) k d = trans_fixes (trans e') k d).
Proof.
  intros eve.
  apply TrmTrmsDefs_ind; simpl; intros; try rewrite_hyps; trivial.

  erewrite eval_env_offset; eauto.
  destruct p as [[ind pars] args].
  f_equal.
  generalize 0.
  induction t0.
  reflexivity.
  simpl. intros. f_equal.
  injection (H0 n). intros.
  now rewrite H2.
  apply IHt0. intros.
  now injection (H0 n1).
Qed.

Lemma translate_env_eval e e' t : eval_env e e' -> translate e t = translate e' t.
Proof. intros H; apply (trans_env_eval e e' H). Qed.

(** Well-formed environments give rise to well-formed evaluated environments *)

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
    now apply (eval_preserves_wf _ _ H5).
    eapply eval_yields_value; now eauto.
  - intros. simpl in H. eauto.
Qed.

(** Evaluated environments are closed *)

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
  
(** Inversion principle for evaluated environments. *)

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
  unfold sbst_env. rewrite !fst_sbst_env_aux.
  rewrite <- (eval_env_length _ _ evee'').
  pose (sbst_env_length t'' 0 e). rewrite H in e2.
  simpl in e2. now rewrite <- e2.
  rewrite <- H0, H in H4. apply H4.
  apply wf_tr_environ_inv in H3. intuition.
Qed.

(** The central lemma: if environment e evaluates to e', 
  then the let-bindings of environmnet e can be simulated
  by substituting the environment e'. *)

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
    rewrite sbst_env_length, app_length; simpl; lia.
    rewrite subst_env_app in H1. simpl in H1.
    rewrite <- wf_tr_environ_sbst in H1; auto.
    unfold sbst_env in H1 |- *.
    rewrite fst_sbst_env_aux in H1 |- *; simpl in *.
    assert (Datatypes.length e'' = Datatypes.length k).
    rewrite <- (eval_env_length _ _ H).
    now rewrite sbst_env_length. rewrite H4 in H1.
    apply H1. apply H0. auto.
Qed.

(** Weak typed normal form of wndEval: no wndEval steps possible. **)
Inductive WNorm: Term -> Prop :=
| WNPrf: WNorm TProof
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNProd: forall nm bod, WNorm (TProd nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNConstruct: forall i n args, WNorms args -> WNorm (TConstruct i n args)
| WNInd: forall i, WNorm (TInd i)
| WNSort: forall s, WNorm (TSort s)
| WNNeutral: forall e, WNeutral e -> WNorm e
with WNorms: Terms -> Prop :=
| WNtnil: WNorms tnil
| WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts)

with WNeutral : Term -> Prop :=
| WNVar n : WNeutral (TRel n)
| WNApp f a : WNeutral f -> WNorm a -> WNeutral (TApp f a)
| WNCase mch n brs : WNeutral mch -> WNorms brs -> WNeutral (TCase n mch brs).

Hint Constructors WNorm WNeutral WNorms.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
  with WNeutral_ind' := Induction for WNeutral Sort Prop
  with WNorms_ind' := Induction for WNorms Sort Prop.
Combined Scheme WNormWNeutralWNorms_ind from WNorm_ind', WNeutral_ind', WNorms_ind'.

Lemma wnorm_closed t : WFTrm t 0 -> WNorm t -> ~ WNeutral t.
Proof.
  remember 0%nat as n. intros wf. revert Heqn.
  induction wf; intros; intro HN; try solve [inv HN]. subst. lia.
  inv HN. inv H.
  specialize (IHwf1 eq_refl (WNNeutral _ H2)). contradiction.
  inv HN.
  specialize (IHwf eq_refl (WNNeutral _ H3)). contradiction.
Qed.

Lemma dnthbody m dts f e k g :
  L3.term.dnthBody m dts = Some f ->
  enthopt m (map_efnlst g (trans_fixes (trans e) k dts)) =
  Some (g (trans e k f)).
Proof.
  revert dts f e k. induction m; simpl; intros.
  destruct dts; simpl in H; try injection H. discriminate.
  intros ->. simpl. reflexivity.

  destruct dts; simpl in H; try injection H. discriminate.
  simpl. erewrite IHm. reflexivity. apply H.
Qed.

(** Translation of fixpoints and fixpoint reduction *)
Lemma L3sbst_fix_preserves_lam dts nm bod :
  fold_left
    (fun (bod : Term) (ndx : nat) =>
       L3.term.instantiate (TFix dts ndx) 0 bod)
    (list_to_zero (dlength dts)) (TLambda nm bod) =
  TLambda nm (fold_left
                (fun (bod : Term) (ndx : nat) =>
                   L3.term.instantiate (TFix dts ndx) 1 bod)
                (list_to_zero (dlength dts)) bod).
Proof.
  revert nm bod; induction (list_to_zero (dlength dts)); simpl; intros.
  reflexivity.
  simpl. setoid_rewrite L3.term.instantiate_equation at 2.
  simpl. rewrite IHl. reflexivity.
Qed.

Definition sbst_fix_aux (es:efnlst) (e : exp) (k : N) : exp :=
  let les := efnlength es in
    fold_left
      (fun e ndx => e{k := shift (N.of_nat ndx) 0 (Fix_e es (N.of_nat ndx))})
      (list_to_zero les) e.

Lemma list_to_zero_spec n :
  forall x, In x (list_to_zero n) -> (x < n)%nat.
Proof.
  induction n; simpl; intros.
  elim H.
  destruct H. subst x. auto with arith.
  specialize (IHn _ H). lia.
Qed.
  
Lemma sbst_fix_preserves_lam es bod :
  (forall i, (i < efnlength es)%nat -> exp_wf 0 (Fix_e es (N.of_nat i))) ->
  sbst_fix es (Lam_e bod) =
  Lam_e (sbst_fix_aux es bod 1).
Proof.
  revert bod; unfold sbst_fix, sbst_fix_aux.
  generalize (eq_refl (efnlength es)).
  generalize (efnlength es) at 1 3.
  generalize (le_refl (efnlength es)).
  generalize es at 1 4 5 7.
  generalize (list_to_zero_spec (efnlength es)).
  induction (list_to_zero (efnlength es)); simpl; intros.
  - reflexivity.
  - simpl. erewrite IHl; auto.
    f_equal.
    f_equal.
    rewrite N.add_0_r.
    assert (a < n)%nat. rewrite H1. apply H. left; trivial.
    specialize (H2 _ H3).
    rewrite (proj1 (closed_subst_sbst (Fix_e es0 (N.of_nat a)) H2)).
    f_equal.
    pose (proj1 (proj2 (proj2 (exp_wf_shift)))).
    inv H2. specialize (e _ _ H6). now rewrite e.
    rewrite <- H1. auto.
Qed.

Definition L3sbst_fix_aux dts body k :=
  let ldts := dlength dts in
  (fold_left
     (fun bod ndx => instantiate (TFix dts ndx) k bod)
     (list_to_zero ldts) body).

Lemma subst_subst_fix_aux x dts e1 : 
  subst x 1 (sbst_fix_aux dts e1 1) =
  sbst_fix_aux (map_efnlst (subst x (efnlst_length dts)) dts)
               (subst x (efnlst_length dts + 1) e1) 1.
Proof.
  unfold sbst_fix_aux.
  set (fn := (fun (e : exp) (ndx : nat) =>
              e {1 := shift (N.of_nat ndx) 0 (Fix_e dts (N.of_nat ndx))})).
  set (fn' := (fun (e : exp) (ndx : nat) =>
      e {1
         := shift (N.of_nat ndx) 0
       (Fix_e (map_efnlst (subst x (efnlst_length dts)) dts) (N.of_nat ndx))})).
  rewrite efnlength_map.
  generalize dts at 1 2 3. intros dts0.
  remember (efnlength dts0) as len.
  revert len Heqlen e1.
  induction dts0; simpl; intros.
  - simpl in *. subst len. simpl. equaln. 
  - Opaque shift.
    simpl in *; try discriminate. subst len.
    simpl. specialize (IHdts0 _ eq_refl).
    rewrite IHdts0. f_equal.
    subst fn fn'. Opaque subst.
    simpl.
    rewrite substitution by lia.
    simpl. equaln.
    replace (Fix_e (map_efnlst (subst x (efnlst_length dts)) dts)
                  (N.of_nat (efnlength dts0))) with
      (subst x 0 (Fix_e dts (N.of_nat (efnlength dts0)))).
    rewrite shift_subst; try lia. simpl. f_equal.
    rewrite efnlength_efnlst_length; lia.
    Transparent subst. simpl.
    rewrite subst_efnlst_map. equaln. 
    Transparent shift.
Qed.

Lemma subst_env_aux_sbst_fix_aux e dts e1 :
  subst_env_aux e 1 (sbst_fix_aux dts e1 1) =
  sbst_fix_aux
     (map_efnlst (subst_env_aux e (efnlst_length dts)) dts)
     (subst_env_aux e (1 + efnlst_length dts) e1) 1.
Proof.
  revert dts e1.
  pattern e. refine (wf_ind (@length _) _ _ e). clear. intros.
  destruct t.
  - simpl. intros.
    unfold subst_env_aux. simpl.
    now rewrite map_efnlst_id.
  - simpl; intros.
    rewrite subst_subst_fix_aux.
    rewrite H by (simpl; lia).
    rewrite efnlst_length_map.
    rewrite map_efnlst_comp. equaln.
Qed.

Lemma L3sbst_fix_aux_sbst_fix_aux env e dts body :
  wf_environ env -> eval_env (translate_env env) e -> wf_tr_environ e ->
  WFTrm body (S (dlength dts)) ->                                       
  (forall i, (i < dlength dts)%nat -> WFTrm (TFix dts i) 0) ->
  trans e (1 + 0) (L3sbst_fix_aux dts body 1) =
  sbst_fix_aux (trans_fixes (trans e) (N.of_nat (dlength dts)) dts)
               (trans e (N.of_nat (dlength dts) + 1) body) 1.
Proof.
  revert body.
  unfold L3sbst_fix_aux, sbst_fix_aux.
  generalize (le_refl (dlength dts)).
  Opaque shift.
  simpl.
  generalize dts at 2 4 5 6 8 9 10.

  induction dts; simpl; try solve [intros; trivial].
  intros dts0 Hdts body wfenv evenv wfe wfbod wffix.
  assert (dtsle:(dlength dts <= dlength dts0)%nat) by lia.
  assert (dtslt:(dlength dts < dlength dts0)%nat) by lia.
  specialize (IHdts dts0 dtsle (instantiate (TFix dts0 (dlength dts)) 1 body)
                    wfenv evenv wfe).
  rewrite IHdts; eauto.
  f_equal.
  rewrite !efnlength_trans.
  pose (e0:=trans_instantiate_any e (TFix dts0 (dlength dts)) (S (dlength dts)) 1
                                  (wffix _ dtslt) body).
  forward e0. forward e0; try lia.
  rewrite Nnat.Nat2N.inj_succ in e0.
  rewrite N.add_1_r, e0.
  - simpl.
    equaln; eauto.
  - eauto.
  - eapply instantiate_preserves_wf; eauto. lia.
Qed.

(** Lookup is the same *)
Lemma L3_tnth_find_branch n e ann brs t i p f :
  let nargs := (nth n ann 0%nat - p)%nat in
  tnth n brs = Some t ->
  find_branch (dcon_of_con i n) (N.of_nat nargs)
              (map_branches f (trans_brs (trans e) i p ann 0 0 brs)) =
  Some (f (N.of_nat nargs) (strip_lam nargs (trans e 0 t))).
Proof.
  revert brs t i; induction n; simpl; intros brs t i. 
  - intros H. destruct brs; simpl in H.
    + discriminate.
    + injection H. intros ->.
      simpl. destruct inductive_dec; try contradiction.
      destruct N.eq_dec; try contradiction.
      reflexivity. elim n. reflexivity.
      now elim n.
      
  - destruct brs.
    + discriminate. 
    + intros H. specialize (IHn _ _ i H).
      simpl trans_brs. simpl map_branches.
      simpl find_branch.
      unfold dcon_of_con in IHn.
      destruct inductive_dec. simpl.
      simpl.
Admitted.

(* TODO move *)
Lemma exps_length_map f l :
  exps_length (map_exps f l) = exps_length l.
Proof.
  induction l; crush.
Qed.
  
Lemma exps_skip_tskipn pars args args' e f :
  tskipn pars args = Some args' ->
  exps_skipn (N.of_nat pars) (map_exps f (trans_args (trans e) 0 args)) =
  map_exps f (trans_args (trans e) 0 args').
Proof.
  revert pars args'; induction args; intros pars args'.
  - destruct pars; simpl; intros [=]. now subst args'.
  - destruct pars; simpl; intros [=]. now subst args'.
    rewrite <- (IHargs _ _ H0). equaln.
    destruct pars; simpl. auto. now rewrite Pos.pred_N_succ.
Qed.

Lemma wftrm_construct {e : environ Term} {i n args} : wf_environ e ->
  L3t.WFTrm (TConstruct i n args) 0 ->
  cnstrArity e i n = Ret (tlength args).
Proof. intros. inv H. Admitted.
    
(** Questions:

  - In the neutral app case, one can have a match in function position,
   how to disallow it -> same idea that the scrutinee should then be a 
   neutral, and there are none in the empty environment might not work.
   It could be a lambda, i.e. ill-formed term.
 *)

Theorem translate_correct (e : environ Term) (t t' : Term) :
  wf_environ e -> WFTrm t 0 ->
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
  assert ((forall t t' : Term,
   L3eval.WcbvEval e t t' ->
   WFTrm t 0 ->
   eval (subst_env e'' (translate e'' t)) (subst_env e'' (translate e'' t'))) /\
   (forall t t' : Terms,
   L3eval.WcbvEvals e t t' ->
   WFTrms t 0 ->
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
    unfold translate, subst_env.
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
    unfold subst_env. rewrite subst_env_aux_fix_e. constructor.

  + (* Ax *)
    intros wft.
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
      * intros. unfold translate in H1. rewrite H1 in IHt.
        pose proof (proj1 eval_single_valued _ _ IHt _ evt).
        now rewrite <- H2.
      * admit. (* Weakening of environmanent *) 
    
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
    assert(WFTrm a1' 0).
    (* wcbeval preserves WF *)  admit.
    assert(WFTrm bod 1).
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
    assert(WFTrm dfn' 0).
    (* wcbeval preserves WF *)  admit.
    assert(WFTrm bod 1).
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
    rewrite subst_env_aux_fix_e in Hfn.
    (* Treat fixstep *)
    unfold translate, subst_env in IHevfix.
    simpl in IHevfix.
    rewrite subst_env_application in IHevfix.
    unfold L3.term.whFixStep in fixstep.
    case_eq (L3.term.dnthBody m dts); intros t'.

    - intros eqt'.
      rewrite eqt' in fixstep. injection fixstep.
      inv IHevfix. intros eqfs.
      * (* Originally a wAppLam transition *)
         eapply eval_FixApp_e; eauto. 
         rewrite Nnat.Nat2N.id.
         rewrite (dnthbody _ _ _ _ _ _ eqt').
         rewrite efnlst_length_trans. reflexivity.
         (* rewrite efnlst_length_trans. *)
         rewrite <- eqfs in H4.
         apply wcbeval_preserves_wf in evfn; auto.
         destruct (wftrm_fix _ _ _ _ evfn eqt') as [nm [bod ->]].
         (* pose (WFTerm_exp_wf _ _ wfe evenv wfe'' _ _ evfn).  *)
         rewrite L3sbst_fix_preserves_lam in H4. simpl in H4.
         rewrite subst_env_aux_lam in H4. inv H4. clear fixstep.
         simpl. rewrite subst_env_aux_lam.
         rewrite sbst_fix_preserves_lam.
         simpl. 
         econstructor. constructor.
         pose (eval_yields_value _ _ H5).
         apply (proj1 wf_value_self_eval _ i).
         eapply eval_preserves_wf; eauto.
         apply exp_wf_subst; eauto 3.
         eapply (WFTerm_exp_wf _ _ _ evenv wfe'' _ 0); auto.

         change ((subst_env_aux e'' (1 + 0)
             (trans e'' (1 + 0)
                (fold_left
                   (fun (bod : Term) (ndx : nat) =>
                    L3.term.instantiate (TFix dts ndx) 1 bod)
                   (list_to_zero (dlength dts)) bod))))
         with
         (subst_env_aux e'' (1 + 0)
                        (trans e'' (1 + 0) (L3sbst_fix_aux dts bod 1))) in *.
         rewrite (L3sbst_fix_aux_sbst_fix_aux e e'') in H7; auto.
         simpl in H7. rewrite !N.add_0_r in *.
         rewrite subst_env_aux_sbst_fix_aux in H7.
         rewrite !efnlst_length_trans in *.
         simpl. rewrite N.add_comm at 2. apply H7.
         admit. (* wf of fix *)
         admit. (* wf of fix *)
         intros i.
         rewrite efnlength_map, efnlength_trans.
         intros Hi.
         constructor.
         rewrite efnlst_length_map, efnlst_length_trans.
         pose proof (proj2 (proj2 (WFTerm_exp_wf_ind e e'' wfe evenv wfe''))).
         admit. (* wf of fix *)

      * (* Impossible, as t' must be a lambda, so cannot evaluate to a fix *)
         intros Hfs.
         apply wcbeval_preserves_wf in evfn; auto.
         destruct (wftrm_fix _ _ _ _ evfn eqt') as [nm [bod ->]].
         elimtype False.
         rewrite L3sbst_fix_preserves_lam in Hfs.
         simpl in Hfs.
         rewrite <- Hfs in H4. simpl in H4.
         rewrite subst_env_aux_lam in H4. inv H4.
         
    - rewrite t' in fixstep. discriminate.
    
  + (* App no redex: this cannot produce a well-formed value *)
    intros * evfn Hfn napp nlam nfix evarg Harg wft.
    cut (WNorm (TApp efn arg1)). intros wnorm.
    cut (WFTrm (TApp efn arg1) 0). intros wft'.
    pose proof (wnorm_closed _ wft' wnorm).
    inv wft'. inv wnorm. contradiction.
    (* Eval preserves wf *) eapply wcbeval_preserves_wf. eauto. eauto.
    (* Application in normal form *) admit.
    
  + (* Case *)
    unfold translate; simpl.
    (* Reduction case *)
    intros * evmch IHmch Hi Hskip Hcasestep evalcss IHcs Hwf.
    destruct ml as [[ind pars] largs].
    assert (Hwf':=wftrm_case _ _ _ _ Hwf).
    inv Hwf.
    assert (Har:WFTrm (TConstruct ind n args) 0).
    eapply wcbeval_preserves_wf; eauto.
    apply (wftrm_construct wfe) in Har.
    specialize (IHmch H3).
    unfold subst_env in *; rewrite subst_env_aux_match.
    unfold L3.term.whCaseStep in Hcasestep.
    case_eq (L3.term.tnth n brs); [intros t H | intros H];
      rewrite H in Hcasestep; try easy.
    econstructor.
    rewrite subst_env_aux_con_e in IHmch. apply IHmch.
    simpl in Hskip.
    erewrite exps_skip_tskipn; eauto.
    rewrite exps_length_map.
    assert(exps_length (trans_args (trans e'') 0 args') =
           N.of_nat (tlength args - pars)).
    admit. (* wf of case + construct *)
    rewrite H0.
    assert (nth n largs 0%nat = tlength args).
    admit.
    rewrite <- H1.
    apply L3_tnth_find_branch. eauto.
    simpl in *.
    (** Substitution of arguments *)
    erewrite exps_skip_tskipn; eauto.

    Lemma eval_app_lam e fn b b' s : is_n_lambda 1 fn = true ->
      eval (subst_env e (trans e 0 b)) b' ->
      eval (sbst b' 0 (subst_env_aux e (1 + 0)
                                     (strip_lam 1 (trans e 0 fn)))) s ->
      eval (subst_env e (trans e 0 (TApp fn b))) s.
      simpl. unfold subst_env. rewrite subst_env_application.
      simpl. destruct fn; try discriminate.
      intros _. econstructor.
      simpl. rewrite subst_env_aux_lam.
      constructor.
      eauto.
      simpl. 
      auto.
    Qed.

    injection (Hcasestep). intros <-.
    forward IHcs.
    destruct Hwf'.
    specialize (H2 _ _ H).
    admit.
    admit.
    (* assert((subst_env_aux e'' 0 (trans e'' 0 (tfold_left args' t))) = *)
    (*        (sbst_list *)
    (*     (subst_env_aux e'' (N.of_nat (nth n largs 0%nat - pars) + 0) *)
    (*        (strip_lam (nth n largs 0%nat - pars) (trans e'' 0 t))) *)
    (*     (map_exps (subst_env_aux e'' 0) (trans_args (trans e'') 0 args')))). *)
    (* induction args'. simpl. *)
    (* assert (nth n largs 0%nat = pars). *)
    
    (* Lemma subst_args args t cs s : *)
    (*   tfold_left args t = Some cs -> *)
    (*   L3eval.WcbvEval e cs s -> *)
    (*   (sbst_list *)
    (*     (subst_env_aux e'' (N.of_nat (nth n largs 0%nat - pars) + 0) *)
    (*        (strip_lam (nth n largs 0%nat - pars) (trans e'' 0 t))) *)
    (*     (map_exps (subst_env_aux e'' 0) (trans_args (trans e'') 0 args'))) *)
    (* admit. *)

  (** Terms *)
  + intros; constructor.
  + intros. inv H1. specialize (H0 H6). simpl.
    constructor; auto.

  (** Generalized goal *)
  + tauto.
Admitted.

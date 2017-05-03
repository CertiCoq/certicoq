(** Conversion from a environment-based language
    to a deBruijn-only expression language  for a core calculus including
    mutually recursive functions, data constructors, and pattern matching.
 *)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
  Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.
(* shared namespace *)
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

(** Tactics *)
Ltac crush :=
  simpl; intros; (try solve [rewrite_hyps; eauto; try lia; trivial])
                   || eauto; try lia; trivial.
Ltac case_call f :=
  let call := fresh "call" in
  remember f as call; destruct call.

Ltac equaln := repeat (f_equal; try lia); auto.

(* Observations *)
Require Import Bool.

Definition eq_decb {A} `{Eq A} (x y : A) : bool :=
  match eq_dec x y with left _ => true | right _ => false end.

Lemma eq_decb_refl {A} `{Eq A} (x : A) : eq_decb x x = true.
Proof.
  unfold eq_decb. destruct eq_dec; trivial. elim n; reflexivity.
Qed.

Section same_args.
  Variable f : Term -> exp -> bool.

  Fixpoint same_args (a : Terms) (a' : exps) :=
    match a, a' with
    | tnil, enil => true
    | tcons t ts, econs e es => f t e && same_args ts es
    | _, _ => false 
    end.
End same_args.

Fixpoint same_obs (t : Term) (v : exp) :=
  match t, v with
  | TConstruct i n args, Con_e dc args' =>
    (eq_decb i (fst dc)) && (eq_decb n (N.to_nat (snd dc))) && same_args same_obs args args'
  | TConstruct _ _ _, _ => false
  | TLambda _ _, Lam_e _ _ => true
  | TLambda _ _, _ => false
  | _, _ => true 
  end.

(** Should be true in L3 *)
Lemma wftrm_fix dts m t n :
  L3t.WFTrm (TFix dts m) n ->
  L3.term.dnthBody m dts = Some t -> isLambda t.
Proof. intros. inv H. Admitted.

Fixpoint is_n_lam n t :=
  match n with
  | 0%nat => true
  | S n => match t with
          | Lam_e _ b => is_n_lam n b
          | _ => false
          end
  end.

Fixpoint is_n_lambda n t :=
  match n with
  | 0%nat => true
  | S n => match t with
          | TLambda _ t => is_n_lambda n t
          | _ => false
          end
  end.

Hint Resolve (proj1 Crct_WFTrm).

Notation Crct := crctTerm.
Notation CrctDs := crctDs.
Notation wf_environ := crctEnv.

(* Now move to Crct predicate which implies WF 
  + closure w.r.t environment and correcness of annotations
  of cases.
*)
Lemma Crct_invrt_Case e n ann mch brs :
  Crct e n (TCase ann mch brs) ->
  Crct e n mch /\ CrctDs e n brs /\
  (forall i t, dnth i brs = Some t -> Crct e n (dbody _ t)
                                /\ is_n_lambda (rarg _ t) (dbody _ t) = true).
Admitted.
  
Lemma wcbeval_preserves_wf e t t' :
  WFTrm t 0 -> L3eval.WcbvEval e t t' -> WFTrm t' 0.
Admitted.

Lemma wcbeval_preserves_Crct e t t' :
  Crct e 0 t -> L3eval.WcbvEval e t t' -> Crct e 0 t'.
Admitted.

Lemma instantiate_preserves_wf t k k' a : (k' <= k)%nat ->
  WFTrm a 0 ->
  WFTrm t (S k) ->
  WFTrm (L3.term.instantiate a k' t) k.
Admitted.

Lemma whFixStep_preserves_Crct e dts m fs :
  Crct e 0 (TFix dts m) ->
  whFixStep dts m = Some fs ->
  Crct e 0 fs /\ isLambda fs.
Proof.
  induction 1; unfold whFixStep; simpl.
  + intros [=].
Admitted.

Lemma wftrm_construct {e : environ Term} {i n args} : wf_environ e ->
  L3t.WFTrm (TConstruct i n args) 0 ->
  cnstrArity e i n = Ret (0%nat, tlength args).
Proof. intros. inv H. Admitted.

Lemma wcbeval_values e mch ind n args : wf_environ e -> Crct e 0 mch ->
                                        L3eval.WcbvEval e mch (TConstruct ind n args) ->
                                        L3eval.no_Wcbvs_step e args.
Proof.
  intros.
  dependent induction H1.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
(* End of L3 requirements *)

Inductive LookupEnv : string -> env -> exp -> Prop :=
  LHit : forall (s : string) (p : list (string * exp)) (t : exp),
    LookupEnv s ((s, t) :: p) t
| LMiss : forall (s1 s2 : string) (p : env) (t t' : exp),
    s2 <> s1 -> LookupEnv s2 p t' -> LookupEnv s2 ((s1, t) :: p) t'.

Lemma wf_environ_lookup (e : environ Term) (t : Term) nm :
  wf_environ e -> LookupDfn nm e t -> WFTrm t 0.
Proof.
  intros wfe Het. revert wfe. red in Het.
  dependent induction Het; intros wfe.
  inversion_clear wfe; eauto. 
  apply IHHet; now inversion_clear wfe.
Qed.

Inductive wf_tr_pre_environ : list (string * exp) -> Prop :=
| wf_tr_pre_nil : wf_tr_pre_environ []
| wf_tr_pre_cons s t e :
    wf_tr_pre_environ e ->
    exp_wf (N.of_nat (List.length e)) t -> (* Refers only to the environment *)
    not (exists t', LookupEnv s e t') -> (* No other binding to s in the environment *)
    wf_tr_pre_environ (cons (s, t) e).

Inductive wf_tr_environ : list (string * exp) -> Prop :=
| wf_tr_nil : wf_tr_environ []
| wf_tr_cons s t e :
    wf_tr_environ e ->
    exp_wf 0 t -> (* Is closed w.r.t. environment *)
    is_value t -> (* Is a value *)
    not (exists t', LookupEnv s e t') -> (* No other binding to s in the environment *)
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
    intros [t' Ht'].
    apply H5. exists t'.
    clear -Ht'.
    induction Ht'. constructor.
    constructor 2; eauto.
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

(** Looking up in the evaluated environment *)
Lemma lookup_eval_env:
  forall e : environ L3.compile.Term,
    wf_environ e ->
    forall (nm : string) t, LookupDfn nm e t ->
    forall (e'' : env),
      eval_env (translate_env e) e'' ->
      wf_tr_environ e'' ->
      exists bef bef' after' t', wf_environ bef /\
        eval_env (translate_env bef) bef' /\
        Crct bef 0 t /\
        eval (subst_env bef' (translate (translate_env bef) t)) t' /\
        after' ++ bef' = e'' /\ 
        LookupEnv nm e'' t'.
Proof.
  intros e wfe nm t Hlookup.
  red in Hlookup.
  generalize_eqs_vars Hlookup. induction Hlookup; simplify_dep_elim;
  rename x0 into eve''; rename x into wfe''. 
  inv wfe. simpl in eve''.
  inv eve''.
  do 2 eexists. exists ((s, t') :: []); eexists; intuition eauto.
  inv wfe''. constructor.

  inv wfe. inv eve''. inv wfe''.
  destruct (IHHlookup H3 t eq_refl e' H7 H6) as
      [bef [bef' [after' [pt'0 [wfbef [evbef [evt [afterbef lookupt]]]]]]]].
  exists bef. exists bef'. exists ((s1, t') :: after'). eexists; intuition eauto. 
  simpl. subst e'. f_equal; eauto.
  constructor; eauto. 
  
  apply IHHlookup; eauto.
Qed. 

Definition map_branches (f : N -> exp -> exp) :=
  fix map_branches (l : branches_e) : branches_e :=
  match l with
  | brnil_e => brnil_e
  | brcons_e d n e brs => brcons_e d n (f (nargs n) e) (map_branches brs)
  end.

Definition map_efnlst (f : exp -> exp) :=
  fix map_efnlst (l : efnlst) : efnlst :=
  match l with
  | eflnil => eflnil
  | eflcons fna t ts => eflcons fna (f t) (map_efnlst ts)
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

Lemma exps_length_map f l :
  exps_length (map_exps f l) = exps_length l.
Proof.
  induction l; crush.
Qed.

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

Lemma subst_env_aux_lam e na k t :
  subst_env_aux e k (Lam_e na t) = Lam_e na (subst_env_aux e (1 + k) t).
Proof.
  revert t; induction e; intros; simpl.
  - reflexivity.
  - now rewrite IHe.
Qed.

Definition subst_env_lam e na t : subst_env e (Lam_e na t) = Lam_e na (subst_env_aux e 1 t) :=
  subst_env_aux_lam e na 0 t.

Lemma subst_env_application e k t u :
  subst_env_aux e k (t $ u) = (subst_env_aux e k t $ subst_env_aux e k u).
Proof. revert t u; induction e; intros; simpl; try rewrite IHe; reflexivity. Qed.

Lemma subst_env_lambda e na t :
  subst_env e (Lam_e na t) = Lam_e na (subst_env_aux e 1 t).
Proof.
  revert t; induction e; intros; try rewrite_hyps; simpl; auto.
Qed.

Lemma subst_env_aux_ax e k s : subst_env_aux e k (Ax_e s) = Ax_e s.
Proof.
  induction e; simpl; try apply IHe; auto.
Qed.

Lemma subst_env_aux_prf e k : subst_env_aux e k Prf_e = Prf_e.
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

Lemma subst_env_aux_constructor e k i r (* arty *) args :
  subst_env_aux e k (trans e k (TConstruct i r (* arty *) args)) =
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

Lemma subst_env_aux_let e na k d b :
  subst_env_aux e k (Let_e na d b) =
  Let_e na (subst_env_aux e k d) (subst_env_aux e (1 + k) b).
Proof.
  revert d b; induction e; intros; simpl; try rewrite IHe; reflexivity.
Qed.

Lemma subst_env_lete e na d b :
  subst_env e (Let_e na d b) = Let_e na (subst_env e d) (subst_env_aux e 1 b).
Proof. apply subst_env_aux_let. Qed.

Lemma subst_env_letin e n d b :
  subst_env e (translate e (TLetIn n d b)) =
  Let_e n (subst_env e (translate e d)) (subst_env_aux e 1 (trans e 1 b)).
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
  let t1 := strip_lam n (sbst a (N.of_nat k) t) in
  let t2 := strip_lam n t in
  snd t1 = sbst a (N.of_nat n + N.of_nat k) (snd t2) /\
  fst t1 = fst t2.
Proof with auto; try lia.
  revert t k; induction n. simpl; intros; repeat (split; f_equal; lia).
  intros t k H.
  destruct t; try discriminate.
  simpl in H.
  simpl.
  specialize (IHn t (S k) H).
  assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
  rewrite H0 in IHn. split; auto.
  destruct IHn.
  destruct_call strip_lam. simpl in *; subst.
  f_equal. lia. destruct_call strip_lam. reflexivity.
  repeat destruct_call strip_lam.
  now destruct IHn; simpl in *; subst. 
Qed.

Lemma strip_lam_subst n a k t :
  is_n_lam n t = true ->
  let t1 := strip_lam n (subst a (N.of_nat k) t) in
  let t2 := strip_lam n t in
  fst t1 = fst t2 /\
  snd t1 = subst a (N.of_nat n + N.of_nat k) (snd t2).
Proof with auto; try lia.
  revert t k; induction n.
  - simpl; intros; split; repeat (f_equal; lia).
  - intros t k H.
    destruct t; try discriminate.
    simpl in H.
    simpl.
    specialize (IHn t (S k) H).
    assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
    rewrite H0 in IHn.
    do 2 (destruct_call strip_lam; simpl in *).
    destruct IHn as [Hl IHn]; subst. split; auto.
    f_equal. lia.
Qed.

Lemma strip_lam_shift n a k t :
  is_n_lam n t = true ->
  let t1 := strip_lam n (shift a k t) in
  let t2 := strip_lam n t in
  fst t1 = fst t2 /\ snd t1 = shift a (N.of_nat n + k) (snd t2).
Proof with auto; try lia.
  revert t k; induction n.
  - simpl; intros; split; repeat (f_equal; lia).
  - intros t k H.
    destruct t; try discriminate.
    simpl in H.
    simpl.
    specialize (IHn t (1 + k) H).
    repeat (destruct_call strip_lam; simpl in *).
    destruct IHn as [Hl IHn]; subst.
    split; f_equal. lia.
Qed.

Lemma strip_lam_shift' n a k t :
  is_n_lam n t = true ->
  let '(names, t1) := strip_lam n (shift a k t) in
  let '(names', t2) := strip_lam n t in
  names = names' /\ t1 = shift a (N.of_nat n + k) t2.
Proof with auto; try lia.
  revert t k; induction n.
  - simpl; intros; split; repeat (f_equal; lia).
  - intros t k H.
    destruct t; try discriminate.
    simpl in H.
    simpl.
    specialize (IHn t (1 + k) H).
    repeat (destruct_call strip_lam; simpl in *).
    destruct IHn as [Hl IHn]; subst.
    split; f_equal. lia.
Qed.

Lemma exp_wf_strip_lam (k : nat) (e : exp) n :
  exp_wf n e -> exp_wf (N.of_nat k + n) (snd (strip_lam k e)).
Proof.
  revert e n; induction k; trivial.
  intros e n H. 
  destruct H; simpl in *;
  try (unfold strip_lam; eapply weaken_wf; eauto; lia).

  - (* Lambda *)
    specialize (IHk e (1 + i)).
    assert (N.of_nat k + (1 + i) = N.pos (Pos.of_succ_nat k) + i) by lia.
    rewrite H0 in IHk.
    destruct_call strip_lam. simpl in *. eauto.

  - (* Prf *) constructor.

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
    exps_wf (N.of_nat (n + List.length e')) (trans_args (trans e') (N.of_nat n) t)) /\
  (forall t n, WFTrmDs t n ->
          efnlst_wf (N.of_nat (n + List.length e'))
                    (trans_fixes (trans e') (N.of_nat n) t)
          /\
          forall i k,
            branches_wf (N.of_nat (n + List.length e'))
                        (trans_brs (trans e') i (N.of_nat n) k t)).
Proof.
  assert(Har:forall n, N.pos (Pos.of_succ_nat n) = 1 + N.of_nat n) by (intros; lia).
  intros wfe evee' wfe'.
  apply WFTrmTrmsDefs_ind; intros; unfold translate;
  cbn -[trans_brs] in *; repeat constructor; eauto; try lia.

  - (* Lambda *) 
    now rewrite !Har in H0. 
  - (* LetIn *)
    now rewrite !Har in H2. 
  - (* Constant -> Rel *)
    generalize (cst_offset_length e' nm).
    intros. forward H. lia.
    (* Needs well-formedness condition of terms: well scoped definitions *)
    admit.
  - destruct m as [i l]. simpl. destruct H2.
    apply H3.
  - rewrite efnlst_length_trans.
    assert (N.of_nat (n + dlength defs + Datatypes.length e') =
            N.of_nat (dlength defs + n + Datatypes.length e')) by lia.
    rewrite H1 in H0.
    rewrite <- !Nnat.Nat2N.inj_add.
    setoid_rewrite Nat.add_comm at 3.
    rewrite Nat.add_assoc.
    apply H0.
  - now destruct H2.
  - destruct H2. intros. simpl.
    destruct strip_lam eqn:Hs. constructor.
    change e0 with (snd (l, e0)). rewrite <- Hs.
    apply exp_wf_strip_lam. apply H0.
    apply H3.
Admitted.

Lemma WFTerm_exp_wf_ind' e (e' := translate_env e) :
  wf_environ e -> wf_tr_pre_environ e' ->
  (forall t n, WFTrm t n ->
          exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t)) /\
  (forall t n, WFTrms t n ->
    exps_wf (N.of_nat (n + List.length e')) (trans_args (trans e') (N.of_nat n) t)) /\
  (forall t n, WFTrmDs t n ->
          efnlst_wf (N.of_nat (n + List.length e'))
                    (trans_fixes (trans e') (N.of_nat n) t)
          /\
          forall i k,
            branches_wf (N.of_nat (n + List.length e'))
                        (trans_brs (trans e') i (N.of_nat n) k t)).
Proof.
  assert(Har:forall n, N.pos (Pos.of_succ_nat n) = 1 + N.of_nat n) by (intros; lia).
  intros wfe wfe'.
  apply WFTrmTrmsDefs_ind; intros; unfold translate;
  cbn -[trans_brs] in *; repeat constructor; eauto; try lia.

  - (* Lambda *) 
    now rewrite !Har in H0. 
  - (* LetIn *)
    now rewrite !Har in H2. 
  - (* Constant -> Rel *)
    generalize (cst_offset_length e' nm).
    intros. forward H. lia.
    (* Needs well-formedness condition of terms: well scoped definitions *)
    admit.
  - destruct m as [i l]. simpl. destruct H2.
    apply H3.
  - rewrite efnlst_length_trans.
    assert (N.of_nat (n + dlength defs + Datatypes.length e') =
            N.of_nat (dlength defs + n + Datatypes.length e')) by lia.
    rewrite H1 in H0.
    rewrite <- !Nnat.Nat2N.inj_add.
    setoid_rewrite Nat.add_comm at 3.
    rewrite Nat.add_assoc.
    apply H0.
  - now destruct H2.
  - destruct H2. intros. simpl.
    destruct strip_lam eqn:Hs. constructor.
    change e0 with (snd (l, e0)). rewrite <- Hs.
    apply exp_wf_strip_lam. apply H0.
    apply H3.
Admitted.

Lemma WFTerm_exp_wf e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e' ->
  forall t n, WFTrm t n ->
         exp_wf (N.of_nat (n + List.length e')) (trans e' (N.of_nat n) t).
Proof. apply WFTerm_exp_wf_ind. Qed.

Lemma wf_pre_environ_pres_fresh e :
  wf_environ e -> forall s, fresh s e ->
  not (exists t, LookupEnv s (translate_env e) t).
Proof.
  intros Hwf.
  induction Hwf; simpl; intros; auto.
  - inv H. intro Ht. destruct Ht. inv H.
  - inv H1. intro Ht. 
    destruct Ht as [t'' Ht'].
    inv Ht'. apply H6; reflexivity.
    apply (IHHwf _ H4). exists t''; eauto.
  - eapply IHHwf.
    now inv H0.
Qed.

Lemma wf_environ_pre e : wf_environ e -> wf_tr_pre_environ (translate_env e).
Proof.
  induction 1.
  - constructor.
  - simpl. constructor; auto.
    unfold translate.
    destruct (WFTerm_exp_wf_ind' p H IHcrctEnv).
    apply (H2 s 0%nat). eauto.
    now apply wf_pre_environ_pres_fresh.
  - now simpl.
Qed.
    
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
              shifts (N.of_nat n) k (trans_args (trans e) k a))) /\
     (forall a k, WFTrmDs a (N.to_nat k) ->
             trans_fixes (trans e) (k + N.of_nat n) a =
             shift_fns (N.of_nat n) k (trans_fixes (trans e) k a)
     /\
     (forall n' i,
                 (trans_brs (trans e) i (k + N.of_nat n) n' a =
             shift_branches (N.of_nat n) k (trans_brs (trans e) i k n' a))))); [ |tauto].
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
    now rewrite (IH k H3).

  - intros IH ts IH2 k Hwf. inv Hwf. simpl.
    rewrite (IH k); auto.
    destruct i as [ind args]. simpl.
    f_equal.
    destruct (IH2 k); auto.

  - intros IH n' k Hwf. inv Hwf. simpl.
    f_equal.
    rewrite N.add_assoc. specialize (IH (N.of_nat (L3t.dlength d) + k)).
    destruct IH.
    assert ((N.to_nat (N.of_nat (dlength d) + k))%nat =
            (N.to_nat k + dlength d)%nat) by lia.
    now rewrite H.
    rewrite efnlst_length_trans.
    unfold shift_fns. equaln.

  - intros IHt ts IH k Hwf. inv Hwf. simpl.
    rewrite IHt; auto.
    destruct (IH k); auto.

  - intros IHt ts Defs Hwf k HwfDs. inv HwfDs.
    destruct (Hwf k H5) as [Hwf' Hwf'']; clear Hwf. split. 

    simpl. equaln.

    intros n' i.
    simpl.
    rewrite Hwf''. rewrite IHt; auto.
    generalize (strip_lam_shift' ts (N.of_nat n) k (trans e k t)).
    destruct strip_lam eqn:stripshift.
    destruct (strip_lam _ (trans _ _ _)) eqn:striptrans.
    simpl. intros Hl. forward Hl. destruct Hl as [Hl He0]; subst.
    equaln. 
    (* WF condition on matches *)
    admit.
  
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
            {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)})) /\
    (forall b k k', WFTrmDs b (S k) -> (k' <= k)%nat ->
        trans_fixes (trans e) (N.of_nat k) (L3.term.instantiateDefs a k' b) =
        (trans_fixes (trans e) (1 + N.of_nat k) b)
          {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)} /\
    (forall i l,
        trans_brs (trans e) i (N.of_nat k) l (L3.term.instantiateDefs a k' b) =
        (trans_brs (trans e) i (1 + N.of_nat k) l b)
          {N.of_nat k' := shift (N.of_nat (k - k')) 0 (trans e 0 a)}))).
  apply TrmTrmsDefs_ind; try reflexivity.

  (* Var *)
  - intros n k k' wfn kk'. inv wfn.
    unfold instantiate.
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
    rewrite instantiate_TLambda. simpl.
    rewrite H, Ht. simpl. f_equal. repeat (f_equal; try lia).
    inv wft. auto. lia.
    
  - (* LetIn *)
    intros s dfn IHdfn bod IHbod k k' wfbod kk'.
    inv wfbod.
    cbn.
    f_equal. rewrite IHdfn; auto.
    assert(N.of_nat (S k) = 1 + N.of_nat k) by lia.
    specialize (IHbod (S k)).
    rewrite H in IHbod.
    rewrite IHbod; auto. simpl. equaln. lia.

  - (* Application *)
    intros t IHt fn IHfn k k' wft kk'. inv wft.
    cbn. repeat (f_equal; rewrite_hyps; try lia; eauto).

  - (* Const *)
    intros nm k k' wft kk'. inv wft.
    cbn. 
    destruct lt_dec. lia.
    simpl. assert(exists t, LookupEnv nm e t). admit. (*WFtrm environment *)
    destruct H as [t Ht].
    destruct N.eq_dec. lia.
    repeat (f_equal; try lia).

  - (* Constructor *)
    intros i m (* arty *) args IHargs k k' wft kk'. inv wft.
    cbn.
    f_equal. destruct (IHargs k k'  H3  kk'); auto.
    
  - (* Match *)
    intros. inv H1. destruct (H0 k k' H8 H2).
    cbn; intuition.
    rewrite_hyps; f_equal; simpl; eauto.

  - (* Fix *)
    intros defs IHdefs n k k' wft kk'. inv wft.
    specialize (IHdefs (k + dlength defs)%nat).
    rewrite instantiate_TFix.
    assert (k' + dlength defs <= k + dlength defs)%nat by lia.
    specialize (IHdefs (k' + dlength defs)%nat H2 H).
    f_equal; simpl; eauto.
    rewrite efnlst_length_trans.
    rewrite <- instantiateDefs_pres_dlength.
    assert ((N.of_nat (k + dlength defs)) =
            (N.of_nat (dlength defs) + N.of_nat k)) by lia.
    rewrite <- H0. rewrite (proj1 IHdefs).
    simpl. repeat (f_equal; try lia).


  - intros t IHt ts IHts k k' wft kk'. inv wft.
    specialize (IHt k k' H1 kk'). specialize (IHts k k' H3 kk').
    rewrite instantiates_tcons.
    simpl. now rewrite IHt, IHts.
    
  - tauto.

  - intros n t IHt ann ts IHts k k' wft kk'. inv wft. 
    specialize (IHt k k' H4 kk'). specialize (IHts k k' H5 kk').
    destruct IHts as [IHts IHbrs].
    cbn. repeat fold (instantiate a k' t).
    simpl. rewrite IHt. split; equaln.
    intros i l.

    specialize (IHbrs i (l + 1)). simpl.
    rewrite IHbrs.
    generalize (strip_lam_subst ann
                                (shift (N.of_nat (k - k')) 0 (trans e 0 a))
                                k' (trans e (1 + N.of_nat k) t)).
    (* rewrite IHbrs.  *)
    destruct strip_lam eqn:stripshift.
    destruct (strip_lam _ (trans _ _ t)) eqn:striptrans.
    simpl. intros Hl. forward Hl.
    destruct Hl as [Hl He0]; subst.
    f_equal. 
    (* Well-formedness of matches *)
    admit.

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
  (forall d k, trans_fixes (trans e) k d = trans_fixes (trans e') k d /\
          (forall ind n, trans_brs (trans e) ind k n d = trans_brs (trans e') ind k n d)).
Proof.
  intros eve.
  apply TrmTrmsDefs_ind; simpl; intros; try rewrite_hyps; trivial.
  
  - erewrite eval_env_offset; eauto.
  - destruct (H0 n). 
    destruct i as [ind args].
    f_equal. apply H2.
  - f_equal. apply H.
  - split; auto.
  - destruct (H0 k). split; auto. f_equal; auto.
    intros. destruct (strip_lam n0 (trans e' k t)).
    f_equal; auto.
Qed.

Lemma translate_env_eval e e' t : eval_env e e' -> translate e t = translate e' t.
Proof. intros H; apply (trans_env_eval e e' H). Qed.

(** Well-formed environments give rise to well-formed evaluated environments *)

Lemma wf_environ_pres_dfn e e' :
  wf_environ e -> eval_env (translate_env e) e' ->
  forall s t, LookupDfn s e t -> exists t', LookupEnv s e' t'.
Proof.
  intros Hwf.
  revert e'; induction Hwf; simpl; intros; auto.
  - inv H0.
  - inv H1.
    specialize (IHHwf _ H7).
    inv H2.
    exists t'. constructor.
    destruct (IHHwf s0 t).
    apply H10.
    exists x. constructor 2; eauto.
  - inv H1.
    eapply IHHwf; eauto.
Qed.

Lemma wf_environ_pres_fresh e e' :
  wf_environ e -> eval_env (translate_env e) e' ->
  forall s, fresh s e -> not (exists t, LookupEnv s e' t).
Proof.
  intros Hwf.
  revert e'; induction Hwf; simpl; intros; auto.
  - inv H. intro Ht. destruct Ht. inv H.
  - inv H1. intro Ht. 
    destruct Ht as [t'' Ht'].
    inv Ht'. inv H2. apply H6; reflexivity.
    inv H2.
    specialize (IHHwf _ H7 s0 H4).
    apply IHHwf. exists t''; eauto.
  - eapply IHHwf. eauto.
    now inv H1.
Qed.

Lemma wf_environ_tr e e' :
  wf_environ e -> eval_env (translate_env e) e' -> wf_tr_environ e'.
Proof.
  intros Hwf; revert e'; induction Hwf.
  - intros e' H; inv H. constructor.
  - simpl; intros e' H'; inv H'. specialize (IHHwf _ H5).
    constructor; auto.
    pose (WFTerm_exp_wf _ _ Hwf H5 IHHwf _ _ (proj1 Crct_WFTrm _ _ _ H0)).
    simpl in e.
    rewrite (translate_env_eval _ _ _ H5) in H6.
    apply (exp_wf_subst e'0 0) in e; auto.
    now apply (eval_preserves_wf _ _ H6).
    eapply eval_yields_value; now eauto.
    eapply wf_environ_pres_fresh; eauto.
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

Lemma exp_wf_mkLets n e t :
  wf_tr_pre_environ e ->
  exp_wf (N.of_nat (n + length e))%nat t -> exp_wf (N.of_nat n) (mkLets e t).
Proof.
  revert n t; induction e; simpl; intros.
  
  now rewrite Nat.add_0_r in H0.

  inv H.
  apply IHe; auto.
  simpl.
  constructor; eapply (proj1 weaken_wf_le); eauto; try lia.
Qed.

Lemma exp_wf_lets e t : crctEnv e ->
  Crct e 0 t ->
  exp_wf 0 (mkLets (translate_env e) (trans (translate_env e) 0 t)).
Proof.
  intros.
  pose proof (wf_environ_pre _ H).
  
  eapply (exp_wf_mkLets 0); auto.
  apply WFTerm_exp_wf_ind'; eauto.
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

Fixpoint terms_of_defs (d : Defs) : Terms :=
  match d with
  | dcons _ t _ ds => tcons t (terms_of_defs ds)
  | dnil => tnil
  end.

(** Weak typed normal form of wndEval: no wndEval steps possible. **)
Inductive WNorm: Term -> Prop :=
| WNPrf: WNorm TProof
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNConstruct: forall i n (* arty *) args, WNorms args -> WNorm (TConstruct i n (* arty *) args)
| WNNeutral: forall e, WNeutral e -> WNorm e
with WNorms: Terms -> Prop :=
| WNtnil: WNorms tnil
| WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts)

with WNeutral : Term -> Prop :=
| WNVar n : WNeutral (TRel n)
| WNApp f a : WNeutral f -> WNorm a -> WNeutral (TApp f a)
| WNCase mch n brs : WNeutral mch -> WNorms (terms_of_defs brs) -> WNeutral (TCase n mch brs).

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
  simpl. rewrite L3.term.instantiate_TLambda. 
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
  
Lemma sbst_fix_preserves_lam es na bod :
  (forall i, (i < efnlength es)%nat -> exp_wf 0 (Fix_e es (N.of_nat i))) ->
  sbst_fix es (Lam_e na bod) =
  Lam_e na (sbst_fix_aux es bod 1).
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

Lemma find_branch_map_branches_some n m f brs t :
  find_branch n m (map_branches f brs) = Some t ->
  exists t', find_branch n m brs = Some t' /\ t = f m t'.
Proof.
  induction brs; simpl; intros; try discriminate.

  destruct n as [ind n].
  destruct d as [ind' d].
  destruct inductive_dec.
  destruct N.eq_dec.
  subst ind' d.
  destruct N.eq_dec.
  injection H; intros <-.
  do 2 eexists; eauto. subst m. eauto.
  discriminate.
  subst ind'.
  apply (IHbrs H).
  apply (IHbrs H).
Qed.

Lemma find_branch_map_branches_none n m f brs :
  find_branch n m (map_branches f brs) = None -> find_branch n m brs = None.
Proof.
  induction brs; simpl; intros; eauto. 
  destruct n, d, inductive_dec; eauto.
  destruct N.eq_dec; eauto. destruct N.eq_dec; eauto. discriminate.
Qed.

Fixpoint nth_branch n b :=
  match b with
  | brnil_e => None
  | brcons_e dc an exp exps =>
    match n with
    | 0%nat => Some exp
    | S n => nth_branch n exps
    end
  end.

Lemma find_branch_trans e (t : def Term) (i : inductive) (n : nat) brs :
  dnth n brs = Some t ->
  find_branch (dcon_of_con i n) (N.of_nat (rarg Term t)) (trans_brs (trans e) i 0 0 brs) =
  nth_branch n (trans_brs (trans e) i 0 0 brs).
Proof.
  assert(0 = N.of_nat (dlength brs - dlength brs)) by lia.
  revert H.
  generalize (le_refl (dlength brs)).
  assert(0 <= N.of_nat n) by lia.
  revert H.
  replace n with (n - N.to_nat 0)%nat at 2 4 by lia.
  generalize 0 at 1 2 3 5 6 8 as k.
  revert t i n; induction brs at -2 -3.

  simpl; intros; discriminate.

  intros.
  simpl.
  destruct strip_lam.
  destruct n1. 
  - simpl.
    destruct inductive_dec.
    destruct k.
    + destruct N.eq_dec.
      reflexivity. simpl in H0.
      elim n1. injection H2; intros <-.
      simpl. reflexivity.
    + elimtype False. lia.
    + now elim n1.
      
  - Opaque N.eq_dec. simpl.
    destruct inductive_dec.
    destruct k.
    destruct N.eq_dec. discriminate.
    simpl.
    specialize (IHd t0 i (S n1) 1).
    forward IHd; [ |lia].
    simpl in H0, H1, H2.
    forward IHd; [ |lia].
    forward IHd; [ |lia].
    simpl in IHd. simpl in H1. rewrite Nat.sub_0_r in IHd.
    specialize (IHd H2).
    apply IHd.

    destruct N.eq_dec. injection e2; intros <-.
    simpl in *.
    replace (Pos.to_nat (Pos.of_succ_nat n1)) with (S n1) in * by lia.
    rewrite Nat.sub_diag in *. simpl.
    destruct N.eq_dec. reflexivity.
    injection H2; intros <-. simpl in n2.
    elim n2; reflexivity.

    simpl.
    case_eq (Pos.to_nat p). simpl.
    intros Hp. specialize (IHd t0 i (S n1) (N.pos p + 1)).
    do 4 (forward IHd; [ |lia]).
    rewrite IHd. equaln.


    intros.
    simpl.

    assert(n3 = Pos.to_nat p - 1)%nat by lia.
    subst n3.
    assert (n1 - (Pos.to_nat p - 1) = S (n1 - Pos.to_nat p))%nat by lia.
    rewrite H4. simpl.
    erewrite IHd. equaln. lia. simpl in H0. lia. simpl in H1. lia.
    rewrite <- H2.
    assert (S n1 - N.to_nat (N.pos p) = S (n1 - N.to_nat (N.pos p)))%nat by lia.
    rewrite H5. simpl dnth at 2. equaln.

    now elim n2.
Qed.

(** Lookup is the same *)
Lemma L3_tnth_find_branch n e brs t i f :
  dnth n brs = Some t ->
  find_branch (dcon_of_con i n) (N.of_nat (rarg _ t))
              (map_branches f (trans_brs (trans e) i 0 0 brs)) =
  Some (f (N.of_nat (rarg _ t)) (snd (strip_lam (rarg _ t) (trans e 0 (dbody _ t))))).
Proof.
  intros Hnth.
  case_eq (find_branch (dcon_of_con i n) (N.of_nat (rarg Term t))
                       (map_branches f (trans_brs (trans e) i 0 0 brs))).
  intros. f_equal.
  apply find_branch_map_branches_some in H. destruct H as [exp [findbr ->]].
  f_equal.
  rewrite find_branch_trans in findbr; eauto.
  revert n Hnth findbr. generalize 0 at 2.
  induction brs; simpl in * ; intros.
  - discriminate. 
  - destruct n2.
    + simpl in findbr. 
      injection Hnth; intros <-; simpl in *.
      destruct strip_lam. now injection findbr.
    + apply (IHbrs (n1 + 1) n2 Hnth). clear IHbrs.
      destruct strip_lam. now simpl in findbr.
  - intros.
    elimtype False.
    apply find_branch_map_branches_none in H.
    rewrite find_branch_trans in H; eauto.
    revert n H Hnth. generalize 0 at 2.
    induction brs; simpl in *; intros. discriminate.
    destruct n2.
    injection Hnth ; intros <-. simpl in *.
    destruct strip_lam. discriminate.
    destruct strip_lam. simpl in H.
    eauto.
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
    
(** Questions:

  - In the neutral app case, one can have a match in function position,
   how to disallow it -> same idea that the scrutinee should then be a 
   neutral, and there are none in the empty environment might not work.
   It could be a lambda, i.e. ill-formed term.
 *)

Hint Resolve wcbeval_preserves_wf.
Hint Resolve wcbeval_preserves_Crct.


Lemma wf_dnthBody dts m nm bod :
  WFTrm (TFix dts m) 0 ->
  dnthBody m dts = Some (TLambda nm bod) ->
  WFTrm bod (S (dlength dts)).
Proof.
  intros Hwf; inv Hwf.
  simpl in H2.
  remember (dlength dts) as dtsl. clear Heqdtsl. revert m.
  induction dts; simpl.
  + intros _ [=].
  + destruct m. intros [=]. inv H2.
    now inv H6.
    apply IHdts. now inv H2.
Qed.

Lemma wf_fix_any dts m :
  WFTrm (TFix dts m) 0 ->
  forall i : nat, (i < dlength dts)%nat -> WFTrm (TFix dts i) 0.
Proof.
  intros H. inv H.
  intros.
  constructor. auto.
Qed.

Lemma exp_wf_subst_aux e n t :
  wf_tr_environ e ->
  exp_wf (n + N.of_nat (List.length e)) t ->
  exp_wf n (subst_env_aux e n t).
Proof.
  revert n t; induction e; simpl; intros.
  - now rewrite N.add_0_r in H0.
  - inv H. simpl.
    apply (IHe n). auto.
    eapply (proj1 subst_preserves_wf'); eauto; lia.
Qed.

Lemma efnlst_wf_subst_env e'' k fixes : wf_tr_environ e'' ->
  efnlst_wf (N.of_nat (k + Datatypes.length e'')) fixes ->
  efnlst_wf (N.of_nat k)
            (map_efnlst (subst_env_aux e'' (N.of_nat k)) fixes).
Proof.
  intros wfe.
  remember (N.of_nat (k + Datatypes.length e'')).
  intros H. revert Heqn. induction H.
  intros ->. constructor.
  intros.
  specialize (IHefnlst_wf Heqn).
  simpl.
  constructor.
  rewrite Heqn in H.
  replace (N.of_nat (k + Datatypes.length e'')) with
  (N.of_nat k + N.of_nat (Datatypes.length e'')) in H by lia.
  eapply exp_wf_subst_aux in H. apply H. eauto.
  apply IHefnlst_wf.
Qed.

Lemma eval_app_lam e fn b b' s :
  is_n_lambda 1 fn = true ->
  eval (subst_env e (trans e 0 b)) b' ->
  eval (sbst b' 0 (subst_env_aux e (1 + 0)
                                 (snd (strip_lam 1 (trans e 0 fn))))) s ->
  eval (subst_env e (trans e 0 (TApp fn b))) s.
Proof.
  simpl. unfold subst_env. rewrite subst_env_application.
  simpl. destruct fn; try discriminate.
  intros _. econstructor.
  simpl. rewrite subst_env_aux_lam.
  constructor.
  eauto.
  simpl. 
  auto.
Qed.

Lemma Crct_invrt_wrong_aux p n x : Crct p n x -> x = TWrong -> False.
Proof.
  induction 1; intros; congruence.
Qed.

Lemma Crct_invrt_wrong p n : Crct p n TWrong -> False.
Proof. intros; eapply Crct_invrt_wrong_aux; eauto. Qed.

Lemma dnthBody_dnth n brs t : dnthBody n brs = Some t -> exists d, dnth n brs = Some d /\ dbody _ d = t.
Proof.
  revert brs; induction n; destruct brs; simpl; intros; auto. discriminate.
  injection H. intros ->. eexists; intuition eauto.
  unfold dnthBody in H. simpl in H. discriminate.
Qed.

Lemma subst_env_aux_shift aft bef t :
  subst_env_aux (aft ++ bef) 0 (shift (N.of_nat (List.length aft)) 0 t) =
  subst_env_aux bef 0 t.
Proof.
  induction aft; simpl.
  + rewrite (proj1 shift_0). reflexivity.
  + rewrite <- IHaft. f_equal.
    pose proof (shift_twice t 0 0 (N.of_nat (List.length aft)) 1).
    Transparent N.add. simpl in H.
    rewrite N.add_comm in H.
    assert(1 + N.of_nat (Datatypes.length aft) = (N.pos (Pos.of_succ_nat (Datatypes.length aft)))) by lia.
    rewrite H0 in H. rewrite <- H; try lia.
    pose (shift_away_subst (shift (N.of_nat (Datatypes.length aft)) 0 t) 0 0 0 (snd a)).
    simpl in e. rewrite e; try lia.
    Opaque N.add.
    rewrite (proj1 shift_0). reflexivity.
Qed.

Lemma S_to_nat k : (S (N.to_nat k) = N.to_nat (1 + k)).
Proof. lia. Qed.
Lemma lookup_env_extend s e e' t : LookupEnv s e t -> exists t', LookupEnv s (e' ++ e) t'.
Proof.
  induction e'. inversion 1; subst. exists t. apply H.
  simpl. exists t. auto.

  intros. simpl. destruct a.
  case_eq (string_eq_bool s s0).
  intros. apply string_eq_bool_eq in H0. subst. exists e0. constructor.
  intros. apply string_neq_bool_neq in H0.
  destruct (IHe' H). eexists; eauto. constructor; eauto.
Qed.

Fixpoint mkApp_e (f : exp) (a : exps) :=
  match a with
  | enil => f
  | econs e es => mkApp_e (App_e f e) es
  end.

Lemma trans_mkapp e k f a : trans e k (mkApp f a) =
                            mkApp_e (trans e k f) (trans_args (trans e) k a).
Proof.
  revert f; induction a; intros; simpl; try reflexivity.
  now rewrite IHa. 
Qed.

Lemma subst_app_e e k f a :
  subst e k (mkApp_e f a) =
  mkApp_e (subst e k f) (map_exps (subst e k) a).
Proof.
  revert e k f; induction a; simpl; intros; trivial.
  now rewrite IHa.
Qed.

Lemma map_exps_compose f g a : map_exps f (map_exps g a) = map_exps (fun x => f (g x)) a.
Proof.
  induction a; simpl.
  - reflexivity.
  - now rewrite IHa. 
Qed.

Lemma subst_env_app_e e k f a :
  subst_env_aux e k (mkApp_e f a) =
  mkApp_e (subst_env_aux e k f) (map_exps (subst_env_aux e k) a).
Proof.
  revert k f a; induction e; simpl; intros; trivial.
  + f_equal. induction a; trivial. simpl. f_equal. auto.
  + rewrite subst_app_e. rewrite IHe.
    f_equal. rewrite map_exps_compose. f_equal.
Qed.

Lemma subst_env_weaken after bef bef' k t :
  Crct bef (N.to_nat k) t ->
  wf_environ bef ->
  wf_tr_environ (after ++ bef') ->
  eval_env (translate_env bef) bef' ->
  trans (after ++ bef') k t = shift (N.of_nat (List.length after)) k (trans bef' k t).
Proof.
  intros Ht Hwfbef Hwf Hbef'.
  revert t k Ht.
  assert 
    ((forall t k, Crct bef (N.to_nat k) t ->
             trans (after ++ bef') k t =
             trans bef' (k + N.of_nat (Datatypes.length after)) t) /\

     (forall a k, crctTerms bef (N.to_nat k) a ->
             trans_args (trans (after ++ bef')) k a =
             trans_args (trans bef') (k + N.of_nat (Datatypes.length after)) a) /\
     (forall a k, CrctDs bef (N.to_nat k) a ->
             trans_fixes (trans (after ++ bef')) k a =
             trans_fixes (trans bef') (k + N.of_nat (Datatypes.length after)) a /\
             (forall i n, trans_brs (trans (after ++ bef')) i k n a =
             trans_brs (trans bef') i (k + N.of_nat (Datatypes.length after)) n a))); cycle 1.
  { destruct H. intros. rewrite <- trans_shift; eauto; apply H; eauto. }

  apply TrmTrmsDefs_ind; intros *; simpl; auto.

  + intros IH k Ht. simpl.
    f_equal. rewrite IH. now rewrite N.add_assoc.
    eapply Crct_invrt_Lam in Ht; eauto.
    rewrite S_to_nat in Ht. auto.
  + intros. eapply Crct_invrt_LetIn in H1; eauto.
    destruct H1. rewrite H; auto.
    rewrite H0. now rewrite N.add_assoc.
    now rewrite S_to_nat in H2.
  + intros IH1 ? IH2 k Ht.
    eapply Crct_invrt_App in Ht; eauto. intuition.
    rewrite IH1, IH2; eauto.
  + intros. f_equal.
    eapply Crct_invrt_Const in H as [H [pd H']]; eauto.
    rewrite (N.add_comm k), N.add_assoc. f_equal.
    pose proof (wf_environ_pres_dfn _ _ Hwfbef Hbef' _ _ pd).
    clear -H' H0 Hwf. induction after. simpl. lia.
    simpl.
    destruct a. case_eq (string_eq_bool s s0).
    intros Hss0. apply string_eq_bool_eq in Hss0. subst s0.
    inv Hwf. elim H7.
    destruct H0 as [ts Hts]. 
    eapply lookup_env_extend; eauto.
    intros. apply string_neq_bool_neq in H1.
    simpl in Hwf. inv Hwf. specialize (IHafter H5).
    rewrite IHafter. lia.
  + intros. rewrite H; auto. destruct i.
    eapply Crct_invrt_Construct in H0. destruct H0.
    intuition eauto. 
  + intros. destruct i.
    eapply Crct_invrt_Case in H1; eauto; intuition.
    specialize (H0 k H1). f_equal; intuition eauto.
  + intros.
    f_equal.
    eapply Crct_invrt_Fix in H0.
    specialize (H (k + N.of_nat (dlength d))); intuition eauto.
    destruct H.
    assert ((N.to_nat k + dlength d)%nat = (N.to_nat (k + N.of_nat (dlength d)))) by lia.
    now rewrite <- H.
    assert(k + N.of_nat (dlength d) = N.of_nat (L3t.dlength d) + k) by lia.
    rewrite <- H2. rewrite H. equaln.
  + intros.
    inv H1.
    f_equal; eauto.
  + intros.
    inv H1. destruct (H0 k H11).
    split; f_equal; eauto.
    intros.
    rewrite H; eauto.
    destruct strip_lam.
    f_equal.
    now rewrite H2.
Qed.

Fixpoint is_n_lambda_app n t :=
  match n with
  | 0%nat => true
  | S n => match t with
          | TLambda _ t => is_n_lambda_app n t
          | TApp f _ => is_n_lambda_app (S (S n)) f
          | _ => false
          end
  end.

Lemma is_n_lambda_app_lam n t : is_n_lambda_app (S n) t = true ->
                                forall e, is_n_lambda_app n (TApp t e) = true.
Proof.
  induction n; intros; trivial.
Qed.

Lemma Crct_mkApp e k f a : is_n_lambda_app (tlength a) f = true ->
                           crctEnv e -> Crct e k f -> crctTerms e k a -> Crct e k (mkApp f a).
Proof.
  revert e k f; induction a; intros; trivial.
  inv H2.
  destruct f; simpl in H; try discriminate.
  eapply Crct_invrt_Lam in H1.
  apply IHa; auto. apply is_n_lambda_app_lam. apply H. 
  simpl. apply IHa; auto.
  eapply Crct_invrt_App in H1.
  destruct H1 as (Hf1&Hf2).
  apply is_n_lambda_app_lam. apply is_n_lambda_app_lam. apply H.
Qed.

Lemma is_n_lambda_is_n_lamba_app n t : is_n_lambda n t = true -> is_n_lambda_app n t = true.
Proof.
  revert t; induction n; destruct t; simpl; intros; try (discriminate || reflexivity).
  now apply IHn.
Qed.

Lemma snd_strip_lam na n t : snd (strip_lam (S n) (Lam_e na t)) = snd (strip_lam n t).
Proof. unfold strip_lam at 1. fold (strip_lam n t). now destruct strip_lam. Qed.

Lemma fst_strip_lam na n t : fst (strip_lam (S n) (Lam_e na t)) = na :: fst (strip_lam n t).
Proof. unfold strip_lam at 1. fold (strip_lam n t). now destruct strip_lam. Qed.

Lemma is_n_lam_sbst e n t : is_n_lam n t = true -> forall k, is_n_lam n (sbst e k t) = true.
Proof.
  revert t; induction n; intros; trivial.
  destruct t; simpl in *; try discriminate.
  now apply IHn.
Qed.

Lemma closed_sbst_map v k l : exps_wf 0 l -> map_exps (sbst v k) l = l.
Proof.
  induction l; simpl; intros; trivial.
  inv H. rewrite (IHl H4).
  f_equal. rewrite (proj1 (sbst_closed_id v) k); eauto; try lia.
Qed.

Lemma sbst_sbst_list v k f l :
  exp_wf 0 v -> exps_wf 0 l ->
  sbst v k (sbst_list f l) =
  sbst_list (sbst v (exps_length l + k) f)
            (map_exps (sbst v k) l).
Proof.
  revert v k f; induction l; simpl; intros.
  - equaln.
  - inv H0.
    rewrite (proj1 (closed_subst_sbst _ H)). 
    rewrite (proj1 (closed_subst_sbst _ H4)).
    rewrite substitution; try lia.
    simpl.
    rewrite <- !(proj1 (closed_subst_sbst _ H)). 
    rewrite (proj1 (sbst_closed_id v) 0); try lia; auto.
    rewrite <- (proj1 (closed_subst_sbst _ H4)). 
    rewrite (IHl v (1 + k) f); auto.
    rewrite (proj1 (sbst_closed_id v) 0 e H4 k); try lia; auto.
    f_equal. f_equal. equaln.
    rewrite !closed_sbst_map; auto.
Qed.

Lemma eval_sbst_list_eval f f' a s k :
  is_n_lam (S k) f = true ->
  eval f f' ->
  eval (sbst_list (snd (strip_lam (N.to_nat (exps_length a)) f')) a) s ->
  eval (sbst_list (snd (strip_lam (N.to_nat (exps_length a)) f)) a) s.
Proof.
  revert f f' s k; induction a. simpl.
  - intros.
    pose proof (proj1 eval_idempotent _ _ H0).
    pose proof (proj1 eval_single_valued _ _ H2 _ H1). now subst.
  - intros.
    destruct f; try discriminate. inv H0.
    auto.
Qed.

Lemma evals_preserves_length {a a'} : evals a a' -> exps_length a = exps_length a'.
Proof. induction 1; simpl; trivial. now rewrite IHevals. Qed.

Lemma is_n_lam_eval n f : is_n_lam (N.to_nat (1 + n)) f = true -> eval f f.
Proof.
  intros.
  rewrite <- S_to_nat in H.
  destruct f; try discriminate. constructor.
Qed.

Lemma eval_lam_app n f e s : exp_wf 0 e -> is_value e -> eval (sbst e 0 f) s -> eval (Lam_e n f $ e) s.
Proof.
  intros.
  econstructor. constructor.
  now apply wf_value_self_eval.
  apply H1.
Qed.

Lemma eval_is_n_lam n t t' : is_n_lam n t = true -> eval t t' -> is_n_lam n t' = true.
Proof.
  induction n; simpl; intros Hlam; auto.
  
  destruct t; try discriminate.
  intros. inv H.
  auto.
Qed.

Lemma mk_App_einv {f a s} : eval (mkApp_e f a) s -> exists s', eval f s'.
Proof.
  revert f; induction a; simpl; intros.
  - now exists s.
  - specialize (IHa (f $ e) H).
    destruct IHa.
    inv H0. now exists (Lam_e na e1').
    exists (Fix_e es n). auto.
    eexists; eauto.
Qed.

Lemma eval_mkApp_e_inner f f' s' a s :
  let n := (N.to_nat (exps_length a)) in
  is_n_lam n s' = true -> 
  eval f s' ->
  eval f' s' -> 
  eval (mkApp_e f a) s -> eval (mkApp_e f' a) s.
Proof.
  revert f f' s' s; induction a; intros *; intros Hlam evf evf' evapp; simpl in *.
  - now rewrite <- (proj1 eval_single_valued _ _ evf _ evapp).
  - subst n; simpl in *.
    rewrite <- S_to_nat in Hlam.
    destruct s'; try discriminate. simpl in Hlam.
    destruct (mk_App_einv evapp) as [s'' evs''].
    
    assert(eval (f' $ e) s'').
    { inv evs''. injection (proj1 eval_single_valued _ _ evf _ H1). intros -> ->.
      econstructor; eauto. 
      pose proof (proj1 eval_single_valued _ _ evf _ H1). discriminate.
      pose proof (proj1 eval_single_valued _ _ evf _ H2). discriminate. }
    eapply (IHa (f $ e) (f' $ e) s'' s ); auto.
    
    inv evs''.
    injection (proj1 eval_single_valued _ _ evf _ H2). intros -> ->.
    eapply (is_n_lam_sbst v2 _) in Hlam.
    eapply eval_is_n_lam; eauto.
    pose proof (proj1 eval_single_valued _ _ evf _ H2). discriminate.
    pose proof (proj1 eval_single_valued _ _ evf _ H3). discriminate.
Qed.

Lemma eval_mkApp_e_inv f a s :
  is_n_lam (N.to_nat (exps_length a)) f = true ->
  exp_wf 0 f -> exps_wf 0 a -> are_values a ->
  eval (mkApp_e f a) s ->
  exists f', eval f f' /\ eval (sbst_list (snd (strip_lam (N.to_nat (exps_length a)) f')) a) s.
Proof.
  revert f; induction a; intros f.
  - 
    simpl.
    intros. do 2 eexists; intuition eauto. 
    eapply eval_idempotent; eauto.
    
  - simpl.
    intros Hfe.
    rewrite <- S_to_nat in Hfe. destruct f; try discriminate.
    intros wff wfa vas Hev.
    simpl in Hfe.
    rewrite <- S_to_nat.
    destruct a.
    + simpl in Hev.
      inv Hev; try inv H1.
      specialize (IHa (e1' {0 ::= v2}) eq_refl).
      inv wff. inv wfa. inv vas. 
      apply wf_value_self_eval in H3; eauto.
      pose proof (proj1 eval_single_valued _ _ H3 _ H2). subst v2.
      forward IHa.
      specialize (IHa (enil_wf _) enil_are_values H4).
      destruct IHa as (f'&evf'&evf's).
      exists (Lam_e na e1'). 
      intuition auto. constructor. 
      apply eval_preserves_wf in H2; auto.
      inv H2.
    + simpl in IHa. simpl in Hev. simpl in Hfe.
      exists (Lam_e n f).
      inv wff; inv wfa.
      specialize (IHa (sbst e 0 f)). simpl in IHa.
      inv H4. inv vas. intuition auto. constructor.
      forward IHa; [ | now apply is_n_lam_sbst ].
      forward IHa; eauto. forward IHa; eauto.
      specialize (IHa H4).
      pose proof (is_n_lam_eval _ _ H).
      forward IHa.
      destruct IHa as (f'&evf&evsbst).
      simpl.
      pose proof (proj1 eval_single_valued _ _ evf _ H8). subst f'.
      rewrite <- S_to_nat. rewrite <- S_to_nat in H.
      rewrite snd_strip_lam.
      pose (substitution (sbst_list (snd (strip_lam (S (N.to_nat (exps_length a))) f)) a) e0 e 0 0).
      forward e1; try lia. simpl in e1.
      rewrite <- (proj1 (closed_subst_sbst _ H3)) in e1; auto.
      rewrite <- (proj1 (closed_subst_sbst _ H5)) in e1.
      rewrite e1. rewrite (proj1 (subst_closed_id e) 0); eauto.
      rewrite <- (proj1 (closed_subst_sbst _ H3)). 
      rewrite <- (proj1 (closed_subst_sbst _ H5)).
      clear e1.
      rewrite sbst_sbst_list; eauto.
      assert (Hstrip:=strip_lam_sbst (N.to_nat (1 + exps_length a)) e 0 f).
      specialize (Hstrip Hfe).
      destruct Hstrip as [Hstrip _].
      rewrite N.add_0_r. rewrite N.add_0_r in Hstrip.
      rewrite N.add_comm. rewrite S_to_nat. rewrite Nnat.N2Nat.id in Hstrip.
      rewrite <- Hstrip.
      inv H4.
      rewrite closed_sbst_map; auto.
      
      apply (eval_mkApp_e_inner (Lam_e n f $ e) (sbst e 0 f) (sbst e 0 f) (econs e0 a)); auto.
      apply eval_lam_app; auto.
Qed.
    
Lemma eval_App_e f a s :
  forall k, k = N.to_nat (exps_length a) ->
       exp_wf 0 f ->
       exps_wf 0 a ->
       are_values a ->
  is_n_lam k f = true ->
  eval (mkApp_e f a) s ->
  eval (sbst_list (snd (strip_lam k f)) a) s.
Proof.
  intros k -> ?????.
  apply eval_mkApp_e_inv in H3; auto. destruct H3 as (f'&evf&evs).
  destruct a; simpl in *.
  pose (proj1 eval_idempotent _ _ evf).
  pose proof (proj1 eval_single_valued _ _ evs _ e); subst f'. auto.

  rewrite <- S_to_nat in H2.
  destruct f; try discriminate.
  now inv evf.
Qed.

Lemma crctTerms_skipn e n i a a' : crctTerms e n a -> tskipn i a = Some a' -> crctTerms e n a'.
Proof.
  revert a a'; induction i; simpl; intros.
  + now injection H0 as ->.
  + destruct a. discriminate.
    inv H.
    eapply IHi; eauto.
Qed.

Lemma subst_env_aux_strip_lam e n k t :
  is_n_lam n t = true ->
  subst_env_aux e (N.of_nat n + k) (snd (strip_lam n t)) =
  (snd (strip_lam n (subst_env_aux e k t))).
Proof.
  revert n t; induction e; simpl; intros; trivial.
  rewrite <- IHe. f_equal.
  generalize (snd a). intros; clear IHe a.
  revert k t e0 H; induction n; simpl; intros; trivial.
  destruct t; simpl in H; try discriminate.
  rewrite snd_strip_lam.
  simpl. rewrite snd_strip_lam.
  specialize (IHn (1 + k) _ e0 H).
  rewrite <- IHn. equaln.
  clear -H.
  revert t k H; induction n; intros; destruct t; simpl in *; eauto.
  discriminate.
Qed.

Lemma is_n_lambda_is_n_lam n e k a : is_n_lambda n%nat a = true -> is_n_lam n (trans e k a) = true.
Proof.
  revert e k a ; induction n; intros; trivial.
  destruct a; try discriminate. simpl in *.
  now apply IHn.
Qed.

Lemma exps_length_trans f k a : exps_length (trans_args f k a) = N.of_nat (tlength a).
Proof. induction a; simpl; trivial. rewrite IHa. lia. Qed.

Lemma exps_skipn_cons n a e : exps_skipn (1 + n) (econs a e) = exps_skipn n e.
Proof.
  simpl. rewrite N.add_1_l. case_eq (N.succ n). intros. lia.
  intros.
  rewrite <- H. now rewrite N.pred_succ.
Qed.      

Lemma exps_length_skipn n e : exps_length (exps_skipn (N.of_nat n) e) = exps_length e - N.of_nat n.
Proof.
  revert e; induction n; destruct e. simpl in *. trivial. simpl. lia. trivial.
  assert (N.of_nat (S n) = 1 + N.of_nat n) by lia. rewrite H.
  simpl exps_length at 2.
  replace (1 + exps_length e0 - (1 + N.of_nat n)) with (exps_length e0 - N.of_nat n) by lia.
  rewrite <- IHn.
  now rewrite exps_skipn_cons.
Qed.

Lemma tskipn_length n a a' : tskipn n a = Some a' ->
                             (tlength a' = tlength a - n)%nat.
Proof.
  revert a a'; induction n; simpl; intros *.
  intros [=->]. lia.
  destruct a. intros; discriminate.
  intros; now apply IHn.
Qed.
  
Lemma is_n_lam_subst_env n t e : is_n_lam n t = true -> is_n_lam n (subst_env_aux e 0 t) = true.
Proof.
  revert t; induction e; simpl; trivial.
  intros t Ht.
  apply IHe.

  clear -Ht. generalize 0.
  revert t Ht; induction n; intros; trivial.
  destruct t; simpl in Ht; try discriminate.
  apply (IHn _ Ht).
Qed.

Lemma are_values_exps_skipn n a : are_values a -> are_values (exps_skipn (N.of_nat n) a).
Proof.
  revert a; induction n; simpl; trivial.
  intros. destruct a; trivial.

  intros.
  destruct a; simpl; trivial.
  assert (Pos.pred_N (Pos.of_succ_nat n) = N.of_nat n).
  destruct n; auto. simpl. now rewrite Pos.pred_N_succ.
  rewrite H0. inv H. eauto.
Qed.

Theorem translate_correct_subst (e : environ Term) (t t' : Term) :
  wf_environ e -> Crct e 0 t ->
  L3eval.WcbvEval e t t' -> 
  let e' := translate_env e in
  forall e'', eval_env e' e'' ->
    eval (subst_env e'' (translate e'' t)) (subst_env e'' (translate e'' t')).
Admitted.
(*****
Proof with eauto.
  cbn. intros wfe crctt H e'' evenv.
  assert(wfe'':=wf_environ_tr _ _ wfe evenv).
  revert t t' H crctt.
  assert ((forall t t' : Term,
   L3eval.WcbvEval e t t' ->
   Crct e 0 t ->
   eval (subst_env e'' (translate e'' t)) (subst_env e'' (translate e'' t'))) /\
   (forall t t' : Terms,
   L3eval.WcbvEvals e t t' ->
   crctTerms e 0 t ->
   evals (map_terms (fun t => subst_env e'' (translate e'' t)) t)
         (map_terms (fun t' => subst_env e'' (translate e'' t')) t'))).
  apply L3eval.WcbvEvalEvals_ind.

  + (* Proof *)
    intros wft. unfold translate. simpl.
    unfold subst_env; rewrite subst_env_aux_prf. constructor.

  + (* Proof application *)
    intros.
    unfold translate in *; simpl in *.
    unfold subst_env in *; rewrite subst_env_aux_prf in *.
    rewrite subst_env_application. constructor.
    apply H. now apply Crct_invrt_App in H0.

  + (* Lambda *)
    cbn. intros nm bod wft.
    rewrite subst_env_lam. constructor.

  + (* Constructor *)
    intros i r (*arty *) args args' Hargs Hargs' wft.
    destruct i.
    eapply Crct_invrt_Construct in wft; eauto. intuition. 
    unfold translate, subst_env.
    rewrite !subst_env_aux_constructor.
    constructor; auto.
    
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
    assert (crctt := LookupDfn_pres_Crct wft H).
    forward IHt; [ |apply wf_environ_lookup in H; auto].
    destruct (lookup_eval_env _ wfe nm t H _ evenv wfe'') as
        [bef [bef' [after' [t' [wfbef [evbef [Crctt [evt [eqe' lookupt]]]]]]]]].
    destruct (subst_env_aux_var_cst e'' nm 0 _ wfe'' lookupt) as [Hs ewf].
    rewrite Hs. 
    cut(t' = (subst_env e'' (translate e'' s))).
    - intros ->.
      apply wf_value_self_eval; eauto.
    - cut (subst_env e'' (translate e'' t) =
           subst_env bef' (translate (translate_env bef) t)).
      * intros. unfold translate in H1. rewrite H1 in IHt.
        pose proof (proj1 eval_single_valued _ _ IHt _ evt).
        now rewrite <- H2.
      * subst e''.
        rewrite (translate_env_eval (translate_env bef) bef'); auto.
        unfold translate at 1.
        rewrite (subst_env_weaken after' bef bef' 0 t Crctt); eauto.
        unfold subst_env.
        apply subst_env_aux_shift; auto.
      
  + (* App Lam *)
    unfold translate. simpl.
    intros * evfn IHWcbvEval1 eva1 IHWcbvEval2 evbod IHWcbvEval3 wft.
    unfold subst_env. rewrite subst_env_application.
    eapply Crct_invrt_App in wft.
    destruct wft as [H H0].
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
    assert(H1:=wcbeval_preserves_Crct _ _ _ H0 eva1).
    assert(H2:=wcbeval_preserves_Crct _ _ _ H evfn).
    eapply Crct_invrt_Lam in H2.
    erewrite (trans_instantiate e'' a1' 0) in IHWcbvEval3; eauto.
    simpl. simpl in IHWcbvEval3.
    rewrite subst_env_aux_subst in IHWcbvEval3; auto.
    assert(exp_wf 0 (subst_env e'' (translate e'' a1'))).
    apply exp_wf_subst; eauto.
    apply Crct_WFTrm in H1.
    apply (WFTerm_exp_wf e e'' wfe evenv wfe'' _ _ H1).
    rewrite (proj1 (closed_subst_sbst _ H3)). 
    apply IHWcbvEval3. 
    (* WF instantiate *)
    (* Now commented in L3/program, why? *)
    (* eapply Instantiate_pres_Crct; eauto. *)
    (* eapply (instantiate_Instantiate a1'); eauto. *)
    admit.
    
  + (* LetIn *)
    intros * evfn IHWcbvEval1 evbod IHWcbvEval2 wft.
    eapply Crct_invrt_LetIn in wft. inv wft.
    specialize (IHWcbvEval1 H). 
    simpl.
    rewrite subst_env_letin.
    econstructor; [eauto| ].
    assert (Hwf':=wcbeval_preserves_Crct _ _ _ H evfn).
    forward IHWcbvEval2. 
    unfold translate in IHWcbvEval2 |- *.
    rewrite (trans_instantiate e'' dfn' 0) in IHWcbvEval2; eauto.
    simpl in IHWcbvEval2. unfold subst_env in IHWcbvEval2 |- *.
    rewrite subst_env_aux_subst in IHWcbvEval2; auto.
    simpl.
    assert(exp_wf 0 (subst_env e'' (translate e'' dfn'))).
    apply exp_wf_subst; eauto.
    apply (WFTerm_exp_wf e e'' wfe evenv wfe'' _ 0); eauto.
    rewrite (proj1 (closed_subst_sbst _ H2)).
    apply IHWcbvEval2.
    (* WF instantiate *)
    (* eapply Instantiate_pres_Crct; eauto. *)
    (* eapply (instantiate_Instantiate dfn'); eauto. *)
    admit.
    
  + (* App Fix *)
    intros * evfn Hfn fixstep evfix IHevfix wft.
    eapply Crct_invrt_App in wft; eauto.
    destruct wft as [H1 H2].
    specialize (Hfn H1).
    forward IHevfix; cycle 1.
    { assert (Crct e 0 (TFix dts m)) by eauto.
      eapply whFixStep_preserves_Crct in H as [Hfs Hfs']; [ | eauto].
      constructor; eauto.
      (*inv Hfs'. destruct H as [bod ->]. intro Hisc; inv Hisc.
      destruct H as [n [ts eq]]. discriminate. *) }
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
         apply wcbeval_preserves_wf in evfn; eauto.
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
         eapply (WFTerm_exp_wf _ _ wfe evenv wfe'' _ 0); eauto.

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
         eapply wf_dnthBody; eauto.
         eapply wf_fix_any; eauto.
         intros i.
         rewrite efnlength_map, efnlength_trans.
         intros Hi.
         constructor.
         rewrite efnlst_length_map, efnlst_length_trans.
         pose proof (proj2 (proj2 (WFTerm_exp_wf_ind e e'' wfe evenv wfe''))).
         specialize (H0 dts (L3t.dlength dts)).
         forward H0; eauto.
         rewrite !N.add_0_r.
         apply efnlst_wf_subst_env; eauto.
         destruct H0. apply H0.
         now inv evfn.
         
      * (* Impossible, as t' must be a lambda, so cannot evaluate to a fix *)
         intros Hfs.
         apply wcbeval_preserves_wf in evfn; eauto.
         destruct (wftrm_fix _ _ _ _ evfn eqt') as [nm [bod ->]].
         elimtype False.
         rewrite L3sbst_fix_preserves_lam in Hfs.
         simpl in Hfs.
         rewrite <- Hfs in H4. simpl in H4.
         rewrite subst_env_aux_lam in H4. inv H4.

      * intros Hfs.
        apply wcbeval_preserves_wf in evfn; eauto.
        destruct (wftrm_fix _ _ _ _ evfn eqt') as [nm [bod ->]].
        elimtype False.
        rewrite L3sbst_fix_preserves_lam in Hfs.
        simpl in Hfs.
        rewrite <- Hfs in H3. simpl in H3.
        rewrite subst_env_aux_lam in H3. inv H3.

    - rewrite t' in fixstep. discriminate.
    
  + (* App no redex: this cannot produce a well-formed value *)
    intros * evfn Hfn nlam nfix nproof evarg Harg wft.
    cut (WNorm (TApp efn arg1)). intros wnorm.
    cut (WFTrm (TApp efn arg1) 0). intros wft'.
    pose proof (wnorm_closed _ wft' wnorm).
    inv wft'. inv wnorm. contradiction.
    (* Eval preserves wf *)
    eapply wcbeval_preserves_wf.
    eapply Crct_WFTrm. apply wft.
    eauto.
    (* Application in normal form *)
    eapply Crct_invrt_App in wft; trivial.
    destruct wft as [Crctfn Crctarg].
    constructor.
    assert (Crct e 0 efn) by eauto.
    (* There's a contradiction here: efn is a Crct closed term, which
isn't a lambda or fix or constructor or application, also not a rel as
it is closed.  But it could still be a: - Proof, Prod, LetIn Const Ax
Ind Case or Wrong. How can we prove it isn't?? *)
    admit.
    
  + (* Case *)
    unfold translate; simpl.
    (* Reduction case *)
    intros * evmch IHmch Hcasestep Hcs IHcs Hcrct.
    assert (i = j) by admit. (* Missing check in wcbveval *)
    subst i.
    assert(Hwf:=proj1 Crct_WFTrm _ _ _ Hcrct).
    eapply Crct_invrt_Case in Hcrct as (Hmch&Hbrs&Hbr).
    assert (Har:WFTrm (TConstruct j n (* arty *) args) 0).
    inv Hwf.
    eapply wcbeval_preserves_wf; eauto.
    apply (wftrm_construct wfe) in Har.
    specialize (IHmch Hmch).
    unfold subst_env in *; rewrite subst_env_aux_match.
    unfold L3.term.whCaseStep in Hcasestep.
    case_eq (dnthBody n brs); [intros t H | intros H];
      rewrite H in Hcasestep; try easy.
    apply dnthBody_dnth in H. destruct H as [def [Hdnth Ht]].
    assert(Hargsdef:tlength args = rarg _ def).
    (* Well-formedness of case *)
    admit.

    econstructor.
    rewrite subst_env_aux_con_e in IHmch. apply IHmch.
    Lemma exps_skipn0 e : exps_skipn 0 e = e.
    Proof. destruct e; reflexivity. Qed.
    rewrite exps_skipn0.
    rewrite exps_length_map.
    assert(Hargs':= exps_length_trans (trans e'') 0 args).
    rewrite Hargs'.
    rewrite Hargsdef.
    apply L3_tnth_find_branch; eauto.
    destruct def as [dna dty dbody rarg]; simpl in *.
    subst t. 
    injection Hcasestep; intros <-.
    specialize (Hbr _ _ Hdnth). simpl in Hbr.
    destruct Hbr as [Hbr Hwf'].
    forward IHcs.
    rewrite trans_mkapp in IHcs.
    rewrite subst_env_app_e in IHcs.
    rewrite subst_env_aux_strip_lam.
    eapply eval_App_e. 
    - rewrite <- Hargsdef.
      rewrite exps_skipn0, exps_length_map, exps_length_trans.
      lia.
    - apply exp_wf_subst_aux; auto. eapply (WFTerm_exp_wf e e'' wfe evenv wfe'' dbody 0).
      now apply Crct_WFTrm in Hbr.
    - admit. (* WF proof *)
    - rewrite exps_skipn0.
      admit. (* Wcbveval produces values ! *)
    - apply (is_n_lambda_is_n_lam _ e'' 0) in Hwf'. 
      now apply is_n_lam_subst_env.
    - rewrite exps_skipn0.
      apply IHcs.
    - now apply is_n_lambda_is_n_lam.
    - apply wcbeval_preserves_Crct in evmch; auto.
      destruct j as [ind ml].
      eapply Crct_invrt_Construct in evmch.
      destruct evmch as [crcte [crctss [pars' [itypk [look crctc]]]]].
      eapply Crct_mkApp; auto.
      -- apply is_n_lambda_is_n_lamba_app. now rewrite Hargsdef.
          
  (** Case congruence *)
  + admit.

  + intros. now apply Crct_invrt_wrong in H.
    
  (** Terms *)
  + intros; constructor.
  + intros. inv H1. specialize (H0 H8). simpl.
    constructor; auto.

  (** Generalized goal *)
  + tauto.
Admitted.
 ************************)

Lemma WcbvEval_env_eval_env e e' :
  wf_environ e -> L3eval.WcbvEval_env e e' -> exists e'', eval_env (translate_env e) e''.
Proof.
  induction 2.
  - exists nil; constructor.
  - inv H. destruct (IHWcbvEval_env H5) as [e'' Hev].
    simpl. 
    exists ((nm, subst_env e'' (translate (translate_env e) t')) :: e'').
    constructor; auto.
    pose proof (translate_correct_subst e t t' H5 H7 H1 _ Hev).
    now rewrite !(translate_env_eval _ _ _ Hev).
  - inv H.
    destruct (IHWcbvEval_env H3) as [e'' Hev].
    simpl.
    now exists e''.
Qed.

Theorem translate_correct (e : environ Term) (t t' : Term) :
  wf_environ e -> Crct e 0 t ->
  L3eval.WcbvEval e t t' -> (* big step non-deterministic *)
  let e' := translate_env e in
  forall e'', eval_env e' e'' ->
  eval (mkLets e' (translate e' t)) (subst_env e'' (translate e' t')).
  (* big-step deterministic *)
Proof with eauto.
  cbn. intros wfe crctt H e'' evenv.
  assert(wfe'':=wf_environ_tr _ _ wfe evenv).
  eapply eval_lets...
  rewrite !(translate_env_eval _ _ _ evenv).
  eapply translate_correct_subst; eauto.
Qed.

Lemma obs_prevervation t e :
  same_obs t (subst_env e (translate e t)) = true.
Proof.
  revert t.
  eapply (@TrmTrms_ind
  (fun t : Term => same_obs t (subst_env e (translate e t)) = true)
  (fun ts => same_args same_obs ts
                    (map_terms (fun x : L3t.Term => subst_env_aux e 0 (trans e 0 x)) ts) = true)
  (fun ds => True)); simpl; auto.

  - intros.
    unfold translate, subst_env.
    simpl. rewrite subst_env_aux_lam. reflexivity.

  - intros.
    unfold translate, subst_env.
    rewrite subst_env_aux_constructor.
    intuition trivial. simpl.
    now rewrite Nnat.Nat2N.id; repeat rewrite eq_decb_refl; simpl.
  - intros. unfold translate, subst_env in H. rewrite H. now simpl.
Qed.

Theorem translate_correct' (e e' : environ Term) (t t' : Term) :
  wf_environ e -> Crct e 0 t ->
  L3eval.WcbvEval_env e e' ->
  L3eval.WcbvEval e t t' -> (* big step non-deterministic *)
  exists v,
    eval (mkLets (translate_env e) (translate (translate_env e) t)) v /\
    same_obs t' v = true.
Proof with eauto.
  cbn. intros wfe crctt He H.
  destruct (WcbvEval_env_eval_env _ _ wfe He) as [e'' evenv].
  assert(wfe'':=wf_environ_tr _ _ wfe evenv).
  econstructor. split. eapply eval_lets...
  rewrite !(translate_env_eval _ _ _ evenv).
  eapply translate_correct_subst; eauto.

  apply obs_prevervation.
Qed.

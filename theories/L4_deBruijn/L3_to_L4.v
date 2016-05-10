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

Require Import Arith BinNat String List Omega Coq.Program.Program Psatz.
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

Definition dcon_of_con (i : inductive) (n : nat) := N.of_nat n.

(** Unit type single constructor *)
Definition dummy := Con_e 0 enil.

(** Definition environment *)
Definition env := list (string * exp).

Fixpoint cst_offset (e : env) (s : string) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if string_eq_bool s c then 0 else cst_offset tl s + 1
  end.

(** Inductive environment: disappears at this stage *)
Definition ienv := list (string * itypPack).

Section TermTranslation.
  Variable ie : ienv.
  Variable e : env.
    
  Fixpoint strip_lam (k : nat) (e : exp) : exp :=
    match k, e with
    | 0%nat, _ => e
    | S n, Lam_e e => strip_lam n e
    | S n, _ => e
    end.
  
  Fixpoint trans (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TAx _ => (* TODO *) dummy
    | L3t.TProof => (* TODO *) dummy                                  
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TSort s => (* Erase *) dummy
    | L3t.TProd n t => (* Erase *) dummy
    | L3t.TLambda n t => Lam_e (trans (k+1) t)
    | L3t.TLetIn n t u => Let_e (trans k t) (trans (k+1) u)
    | L3t.TApp t u => App_e (trans k t) (trans k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) dummy
    | L3t.TConstruct ind c args =>
      let fix args' l :=
        match l with
        | L3t.tnil => enil
        | L3t.tcons t ts => econs (trans k t) (args' ts)
        end
      in Con_e (dcon_of_con ind c) (args' args)
    | L3t.TCase ann t brs =>
      let fix brs' n l :=
          match l with
          | L3t.tnil => brnil_e
          | L3t.tcons t ts =>
            let nargs := List.nth (N.to_nat n) (snd ann) 0%nat in
            brcons_e n (N.of_nat nargs) (strip_lam nargs (trans k t))
                 (brs' (n + 1)%N ts)
          end
      in Match_e (trans k t) (brs' (0%N) brs)
    | L3t.TFix d n =>
      let fix defs' l :=
          match l with
          | L3t.dnil => eflnil
          | L3t.dcons na t _ l' =>
            let t' := trans (k + 1) t in
              eflcons (strip_lam 1 t') (defs' l')
          end
      in      
      Fix_e (defs' d) (N.of_nat n)
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
| wf_cons_trm s t e : L3t.WFTrm t 0 -> L3N.WNorm t -> wf_environ e -> wf_environ (cons (s, ecTrm t) e)
| wf_cons_ty s n t e : wf_environ e -> wf_environ (cons (s, ecTyp n t) e).

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
    simpl.
Admitted.

Inductive wf_tr_environ : list (string * exp) -> Prop :=
| wf_tr_nil : wf_tr_environ []
| wf_tr_cons s t e : wf_tr_environ e ->
                       exp_wf (N.of_nat (List.length e)) t -> (* Is closed w.r.t. environment *)
                       is_value t -> (* Is a value *)
                       wf_tr_environ (cons (s, t) e).

Ltac inv H := inversion_clear H.
Ltac rewrite_hyps :=
  repeat match goal with
    | [ H : _ |- _ ] => rewrite !H
  end.

Lemma efnlst_length_sbst v k es :
  efnlst_length (sbst_efnlst v k es) = efnlst_length es.
Proof. induction es; simpl; try rewrite_hyps; trivial. Qed.

Lemma efnlst_length_subst v k es :
  efnlst_length (subst_efnlst v k es) = efnlst_length es.
Proof. induction es; simpl; try rewrite_hyps; trivial. Qed.

(* Move to expression *)
Lemma exp_wf_shift :
  (forall i e, exp_wf i e -> forall j, shift j i e = e) /\
  (forall i es, exps_wf i es -> forall j, shifts j i es = es) /\
  (forall i es, efnlst_wf i es -> forall j, shift_fns j i es = es) /\
  (forall i bs, branches_wf i bs -> forall j, shift_branches j i bs = bs).
Proof.
  apply my_exp_wf_ind; simpl; intros; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity. contradiction.
  f_equal. now rewrite N.add_comm.
Qed.

Lemma closed_subst_sbst v :
  exp_wf 0 v ->
  (forall t k, sbst v k t = subst v k t) /\
  (forall es k, sbsts v k es = es{k := v}) /\
  (forall es k, sbst_efnlst v k es = es{k:=v}) /\
  (forall bs k, sbst_branches v k bs = bs{k:=v}).
Proof.
  intros Hv.
  apply my_exp_ind; simpl; intros; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity.
  destruct N.eq_dec. subst n.
  symmetry; now apply exp_wf_shift.
  reflexivity.
Qed.

Lemma sbst_preserves_wf' :
  (forall i' e, exp_wf i' e ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exp_wf i (e{k::=v})) /\
  (forall i' es, exps_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exps_wf i (es{k::=v})) /\
  (forall i' es, efnlst_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> efnlst_wf i (es{k::=v})) /\
  (forall i' bs, branches_wf i' bs ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> branches_wf i (bs{k::=v})).
Proof.
  apply my_exp_wf_ind; simpl; intros; subst; eauto.
  - repeat if_split; try (constructor; auto; lia).
  - constructor. apply H; try lia; auto.
  - constructor; auto. apply H0; try lia; auto.
  - constructor; auto. rewrite efnlst_length_sbst; apply H; try lia; auto.
  - constructor; auto. 
  - constructor; auto. 
  - constructor; auto. apply H; try lia; auto.
Qed.

(** Weakening with respect to [exp_wf]. *)
Lemma weaken_wf' :
  (forall i e, exp_wf i e -> forall j, i <= j -> exp_wf j e) /\
  (forall i es, exps_wf i es -> forall j, i <= j -> exps_wf j es) /\
  (forall i es, efnlst_wf i es -> forall j, i <= j -> efnlst_wf j es) /\
  (forall i bs, branches_wf i bs -> forall j, i <= j -> branches_wf j bs).
Proof.  
  apply my_exp_wf_ind; intros; econstructor; auto; try lia; 
  match goal with
    | [ H: forall _, _ -> exp_wf _ ?e |- exp_wf _ ?e] => apply H; lia
    | _ => idtac
  end.
  apply H. lia.
Qed.

Lemma subst_preserves_wf' :
  (forall i' e, exp_wf i' e ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exp_wf i (e{k:=v})) /\
  (forall i' es, exps_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exps_wf i (es{k:=v})) /\
  (forall i' es, efnlst_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> efnlst_wf i (es{k:=v})) /\
  (forall i' bs, branches_wf i' bs ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> branches_wf i (bs{k:=v})).
Proof.
  apply my_exp_wf_ind; simpl; intros; subst; eauto.
  - repeat if_split; try (constructor; auto; lia).
    rewrite (proj1 exp_wf_shift _ _ H0).
    eapply (proj1 weaken_wf'); eauto; lia.
  - constructor. apply H; try lia; auto.
  - constructor; auto. apply H0; try lia; auto.
  - constructor; auto. rewrite efnlst_length_subst; apply H; try lia; auto.
  - constructor; auto. 
  - constructor; auto. 
  - constructor; auto. apply H; try lia; auto.
Qed.

Lemma value_value_subst n v :
  is_value v -> exp_wf 0 v ->
  (forall e, is_value e -> is_value (subst v n e)) /\
  (forall es, are_values es -> are_values (substs v n es)).
Proof.
  intros vv wfv.
  apply my_is_value_ind; simpl; intros; try constructor; trivial.
  intros.
  destruct lt_dec. constructor.
  destruct N.eq_dec. now rewrite (proj1 exp_wf_shift).
  constructor.
Qed.  

Lemma wf_value_self_eval :
  (forall v, is_value v -> exp_wf 0 v -> eval v v) /\
  (forall vs, are_values vs -> exps_wf 0 vs -> evals vs vs).
Proof.
  apply my_is_value_ind; simpl; intros; auto; try constructor; auto.
  inv H. lia.
  inv H0. auto.
  inv H1. intuition.
  inv H1. intuition.
Qed.

Lemma wf_tr_environ_inv k s x :
  wf_tr_environ (k ++ [(s, x)]) ->
  is_value x /\ exp_wf 0 x /\ wf_tr_environ (snd (sbst_env x 0 k)).
Proof.
  induction k; simpl in *; intros.
  - now inv H.
  - inv H. intuition.
    case_eq (sbst_env x 0 k).
    intros.
    simpl. rewrite H4 in H5. simpl in H5.
    constructor. auto. simpl in H1.
    pose (length_sbst_env x 0 k). rewrite H4 in e0. simpl in e0.
    rewrite e0. eapply (proj1 subst_preserves_wf'); eauto.
    rewrite app_length. simpl. lia.
    unfold sbst_env in H4.
    pose (fst_sbst_env_aux x k (0, [])).
    rewrite H4 in e1. simpl in e1.
    rewrite fst_sbst_env_aux' in e1. simpl in e1. lia.
    (* Substituting values in values... keeps being a value! *)
    now apply value_value_subst.
Qed.

Lemma eval_lets e t t' :
  wf_tr_environ e ->
  eval (subst_env e t) t' ->
  eval (mkLets e t) t'.
Proof.
  revert t t'. pattern e. refine (wf_ind (@length _) _ _ e). clear.
  simpl. intros k IHk ? ?. destruct k using rev_ind; intros.
  + simpl. trivial.
  + simpl. clear IHk0.
    rewrite mkLets_app; simpl.
    destruct x as [s e]; simpl.
    apply wf_tr_environ_inv in H. 
    apply eval_Let_e with (v1 := e); intuition.
    simpl.
    now apply wf_value_self_eval.
    simpl.
    rewrite (proj1 (closed_subst_sbst _ H)).
    rewrite sbst_lets.
    apply IHk; auto. 
    rewrite length_sbst_env, app_length. 
    simpl. lia.
    rewrite <- (subst_env_app k (s, e)). assumption.
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

Lemma subst_env_aux_var2 e k nm t e' :
  in_env e (cst_offset e nm) nm t e' ->
  subst_env_aux e k (Var_e (cst_offset e nm + k)) =
  shift k 0 (subst_env_aux e' 0 t).
Proof.
  revert t; induction e; intros; simpl.
  - inversion H.
  - destruct a as [s v].
    case_eq (string_eq_bool nm s); intros Heq; simpl.
    + rewrite N.add_0_l. case (lt_dec k k).
      * now intros H'%N.lt_irrefl.
      * intros _. destruct (N.eq_dec k k) as [_|H'].
        simpl in H. rewrite Heq in H.
        inversion H. subst.
Admitted.
  
Lemma subst_env_aux_var' e k nm t :
  LookupDfn nm e t ->
  subst_env_aux (translate_env e) k (Var_e (cst_offset (translate_env e) nm + k)) =
  (trans (translate_env e) k t).
Proof.
  revert t; induction e; intros; simpl.
  - inversion H.
  - destruct a as [s [trm|ty]].
    unfold subst_env_aux.
    unfold translate_entry.
Admitted.    

Lemma subst_env_aux_var e k nm t :
  LookupDfn nm e t ->
  subst_env_aux (translate_env e) k (Var_e (cst_offset (translate_env e) nm + k)) =
  subst_env_aux (translate_env e) k (trans (translate_env e) k t).
Proof.
  revert t; induction e; intros; simpl.
  - inversion H.
  - destruct a as [s [trm|ty]].
    simpl in *.
Admitted.

Lemma subst_env_application e t u :
  subst_env e (t $ u) = (subst_env e t $ subst_env e u).
Proof. revert t u; induction e; intros; simpl; try rewrite IHe; reflexivity. Qed.


Lemma subst_env_lambda e t :
  subst_env (translate_env e) (Lam_e t) =
  Lam_e (subst_env_aux (translate_env e) 1 t).
Proof.
  revert t; induction e; intros; simpl.

  reflexivity.
  destruct a as [s [trm | ty]]; simpl.
  rewrite <- IHe. reflexivity.

  apply IHe.
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

Lemma eval_dummy e : eval (subst_env e dummy) (subst_env e dummy).
Proof.
  unfold dummy, subst_env. simpl.
  induction e; simpl; try apply IHe. constructor. constructor.
Qed.

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

(** A well-formed, closed term in normal form cannot be a redex *)

Lemma wftrm_0_no_redex:
  forall (e : environ) (efn : L3.term.Term),
    ~ L3.term.isApp efn ->
    ~ L3.term.isLambda efn ->
    ~ L3.term.isFix efn ->
    ~ L3.term.isConstruct efn ->
    L3N.WNorm efn ->
    L3t.WFTrm efn 0 -> translate (translate_env e) efn = dummy.
Proof.
  intros e efn H0 H1 H2 H3 H6 H7.
  revert H0 H1 H2 H3 H6.
  inv H7; unfold translate; simpl; intros; try reflexivity.

  inv H.
  elim H1. apply L3.term.IsLambda.

  inv H6.
  elim H1; apply L3.term.IsApp.

  inv H6.
  elim H3. apply L3.term.IsConstruct.
  
  inv H6.
  admit.

  elim H2. apply L3.term.IsFix.

Admitted.

Lemma WFTerm_exp_wf t n e : L3t.WFTrm t n -> exp_wf (N.of_nat n) (translate e t).
Proof.
  induction 1; unfold translate; simpl in *;
  try repeat constructor; try lia.
  Admitted.
  
  
Lemma wf_environ_tr e : wf_environ e -> wf_tr_environ (translate_env e).
Proof.
  induction 1.
  - constructor.
  - simpl. constructor; auto.
    admit.
    induction H0; unfold translate; try solve [simpl; repeat constructor].
    inv H.
    (* In L3, matches can be values... assuming the scrutinee is not a constructor.
       This is not so in L4. The match scrutinee has to be a closed value,
       it could be a lambda or a fix *)
    specialize (IHWNorm H4).
    eapply WFTerm_exp_wf in H4. 
    simpl in H4.
Admitted.    
    
(** Questions:

  - Is this the right kind of preservation theorem?
  
   Small to big step seems wrong. But a small step in the source language
   needs big steps in the target because we add the lets which need to
   be reduced before we come to the original source reduction. 

   The target "t'" needs a substitution of the environment definitions
   that might appear under lambda abstractions. We have to ensure 
   that t' is a normal form, i.e. not of the form (App (Const c) u) 
   otherwise the big step could go further.

  - In the neutral app case, one can have a match in function position,
   how to disallow it -> same idea that the scrutinee should then be a 
   neutral, and there are none in the empty environment might not work.
   It could be a lambda, i.e. ill-formed term.
 *)
    

Theorem translate_correct (e : environ) (t t' : L3t.Term) :
  wf_environ e -> L3t.WFTrm t 0 ->
  L3eval.WcbvEval e t t' -> (* big step non-deterministic *)
  let e' := translate_env e in
  eval (mkLets e' (translate e' t)) (subst_env e' (translate e' t')).
  (* big-step deterministic *)
Proof.
  cbn. intros wfe wft H. apply eval_lets.
  now apply wf_environ_tr.
  induction H.

  + (* Proof *)
    admit.

  + (* Lambda *)
    cbn.
    rewrite subst_env_lam. constructor.

  + (* Prod *)
    cbn. apply eval_dummy.

  + (* Constructor *)
    rewrite !subst_env_constructor.
    constructor.
    induction H. constructor.
    constructor. (* Need mutual statement *) admit.
    apply IHWcbvEvals.

    - inversion_clear wft. constructor. now inversion_clear H1. 
    
  + (* Ind *)
    unfold translate.
    simpl. apply eval_dummy.

  + (* Sort *)
    apply eval_dummy.

  + (* Fix *)
    admit.

  + (* Ax *)
    unfold translate. simpl. apply eval_dummy.
    
  + (* Const *)
    unfold translate.
    simpl.
    unfold subst_env at 1.
    erewrite subst_env_aux_var; try eassumption.
    apply IHWcbvEval.

    - apply wf_environ_lookup in H; auto.
    
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

  + (* App not lambda *)
    unfold translate. simpl.
    rewrite !subst_env_application.
    inversion_clear wft.
    assert (L3t.WFTrm efn 0).
    admit.
    pose (wftrm_0_no_redex e efn H0 H1 H2).
    assert (~ L3.term.isConstruct efn). admit.
    assert (L3N.WNorm efn). admit.
    specialize (e0 H7 H8 H6). 
    unfold translate in e0. rewrite !e0.
    admit.

  + (* Case *)
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

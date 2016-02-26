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
  | (s, ecTyp _) => acc
  end.

Definition translate_entry_aux x acc : option (string * exp) :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Some (s, t')
  | (s, ecTyp _) => None
  end.

Definition translate_env_aux (e : environ) (k : env) : env :=
  fold_right translate_entry k e.

Definition translate_env (e : environ) : env :=
  translate_env_aux e [].

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : string * exp) => Let_e (snd x) acc) e t.

Definition let_entry acc (a : string * envClass) e :=
  match a with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Let_e t' e
  | (s, ecTyp _) => e
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
    (fun t (x : string * exp) => t{n ::= snd x})
    e t.

Definition subst_env e (t : exp) := subst_env_aux e 0 t.

Definition subst_entry (a : string * envClass) acc (e : exp) :=
  match a with
  | (s, ecTrm t) =>
    let t' := translate acc t in
      e{0 ::= t'}
  | (s, ecTyp _) => e
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
  fold_left (fun t e => t{0 ::= e}) l e.

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
                (n+1, (fst s, (snd s){n ::= u}) :: l))
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
  sbst e n (mkLets k t) = mkLets (snd k') (sbst e (fst k') t).
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
  (subst_env (snd k') (sbst (snd x) (fst k') t)).
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

Lemma eval_lets e t t' :
  eval (subst_env e t) t' ->
  eval (mkLets e t) t'.
Proof.
  revert t t'. pattern e. refine (wf_ind (@length _) _ _ e). clear.
  simpl. intros k IHk ? ?. destruct k using rev_ind; intros.
  + simpl. trivial.
  + simpl. clear IHk0.
    rewrite mkLets_app.
    simpl.
    econstructor. instantiate (v1 := snd x). admit.
    simpl in IHk.
    simpl.
    rewrite sbst_lets.
    apply IHk.
    rewrite length_sbst_env, app_length.
    simpl. omega.
    rewrite <- subst_env_app. assumption.
Admitted.

Lemma subst_env_aux_lam e k t :
  subst_env_aux e k (Lam_e t) = Lam_e (subst_env_aux e (1 + k) t).
Proof.
  revert t; induction e; intros; simpl.
  - reflexivity.
  - now rewrite IHe.
Qed.

Definition subst_env_lam e t : subst_env e (Lam_e t) = Lam_e (subst_env_aux e 1 t) :=
  subst_env_aux_lam e 0 t.

Lemma subst_env_aux_var e k nm t :
  LookupDfn nm e t ->
  subst_env_aux (translate_env e) k (Var_e (cst_offset (translate_env e) nm + k)) =
  subst_env (translate_env e) (translate (translate_env e) t).
Proof.
  revert t; induction e; intros; simpl.
  - inversion H.
Admitted.

Theorem translate_correct (e : environ) (t t' : L3t.Term) :
  L3eval.WcbvEval e t t' -> (* small step non-deterministic *)
  let e' := translate_env e in
  eval (mkLets e' (translate e' t)) (subst_env e' (translate e' t')). (* big-step deterministic *)
Proof.
  cbn. intros H. apply eval_lets.
  induction H.

  + (* Lambda *)
    cbn.
    rewrite subst_env_lam. constructor.

  + (* Prod *)
    cbn. 
    admit.

  + unfold translate. (* mutual *)
    admit.

  + (* Ind *)
    unfold translate.
    simpl.
    admit.

  + (* Sort *)
    admit.

  + (* Fix *)
    admit.

  + (* Ax *)
    admit.
    
  + (* Const *)
    unfold translate.
    simpl.
    (* IH is not strong enough here *)
    unfold subst_env at 1.
    erewrite subst_env_aux_var.
    apply IHWcbvEval. assumption.

  + (* App Lam *)
    admit.

  + (* LetIn *)
    admit.

  + (* App Fix *)
    admit.

  + (* Construct *)
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

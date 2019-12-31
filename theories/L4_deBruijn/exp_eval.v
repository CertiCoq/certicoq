Require Import Coq.Arith.Arith Coq.NArith.BinNat omega.Omega Coq.Strings.String
        Coq.Lists.List.
Require Import Common.Common.
Require Import L4.expression L6.List_util.


(* Definition Clo := (env, expression.exp). *)

(* extend is_value from L4.expression to include closures perhaps *)
Inductive value :=
| Con_v : dcon -> list value -> value 
| Prf_v : value
| Clos_v : list value -> name -> expression.exp -> value
| ClosFix_v : list value -> efnlst -> N -> value.


Lemma value_ind' (P : value -> Prop) :
  (forall dcon vs, Forall P vs -> P (Con_v dcon vs)) ->
  (P Prf_v) ->
  (forall vs na e, P (Clos_v vs na e)) ->
  (forall vs fnl n, P (ClosFix_v vs fnl n)) ->
  (forall v,  P v).
Proof.
  intros H1 H2 H3 H4.
  fix 1. destruct v.
  - eapply H1. induction l.
    constructor.
    constructor. eapply value_ind'. eassumption.
  - eauto.
  - eauto. 
  - eauto.  
Qed.
                             
(* Definition of env *)
Definition env := list value.

(* Fixpoint make_rec_env (fnlst : efnlst) (rho : env) : env := *)
(*   let fix make_env_aux funcs rec_env := *)
(*       match funcs with *)
(*       | eflnil => List.rev rec_env ++ rho *)
(*       | eflcons na e fnlst' => *)
(*         make_env_aux fnlst' ((Clos_v rho na e) :: rec_env) *)
(*       end *)
(*   in *)
(*   make_env_aux fnlst nil. *)

Definition make_rec_env (fnlst : efnlst) (rho : env) : env :=
  let fix make_env_aux funcs n :=
      match funcs with
      | eflnil => rho
      | eflcons na e fnlst' =>
        let rec_env := make_env_aux fnlst' (n + 1) in
        ((ClosFix_v rho fnlst n) :: rec_env)
      end
  in
  make_env_aux fnlst 0.

Fixpoint exps_to_list (es : expression.exps) : list exp :=
  match es with
  | enil => nil
  | econs e es' =>
    let l := exps_to_list es' in
    e::l
  end.

Fixpoint list_to_exps l : expression.exps :=
  match l with
  | nil => enil
  | cons e l' =>
    let exps' := list_to_exps l' in
    (econs e exps')
  end.
                                      
Inductive eval_env: env -> exp -> value -> Prop :=
| eval_Var:
    forall (x: N) (rho: env) (n: value),
      (nth (N.to_nat x) rho Prf_v) = n ->
      eval_env rho (Var_e x) n
| eval_Lam:
    forall (e: expression.exp) (rho:env) (na: name),
      eval_env rho (Lam_e na e) (Clos_v rho na e)
| eval_App:
    forall (e1 e2 e1': expression.exp) (v v2 : value) (na : name) (rho rho': env),
      eval_env rho e1 (Clos_v rho' na e1') ->
      eval_env rho e2 v2 ->
      eval_env (v2::rho') e1' v ->
      eval_env rho (App_e e1 e2) v
| eval_Let:
    forall (e1 e2 : expression.exp) (v1 v2 : value) (rho: env) (na: name),
      eval_env rho e1 v1 ->
      eval_env (v1::rho) e2 v2 ->
      eval_env rho (Let_e na e1 e2) v2
| eval_Con:
    forall (es: expression.exps) (vs : list value) (rho: env) (dc: dcon),
      Forall2 (fun e v => eval_env rho e v) (exps_to_list es) vs -> 
      eval_env rho (Con_e dc es) (Con_v dc vs)
| eval_Fix:
    forall (n: N) (rho: env) (fnlst: efnlst),
      eval_env rho (Fix_e fnlst n) (ClosFix_v rho fnlst n)
| eval_FixApp:
    forall (e1 e2 e' e'': expression.exp) (rho rho' rho'' rho_f: env) (n: N)
    (fnlst: efnlst) (v2 v : value) (na : name),
      eval_env rho e1 (ClosFix_v rho' fnlst n) ->
      enthopt (N.to_nat n) fnlst = Some e' ->
      make_rec_env fnlst rho' = rho'' ->  
      eval_env rho'' e' (Clos_v rho_f na e'') ->
      eval_env rho e2 v2 -> 
      eval_env (v2::rho_f) e'' v ->
      eval_env rho (App_e e1 e2) v
| eval_Match:
    forall (e1 e': expression.exp) (rho: env) (dc: dcon) (vs: list value)
    (n: N) (brnchs: branches_e) (v: value),
      eval_env rho e1 (Con_v dc vs) ->
      find_branch dc (N.of_nat (List.length vs)) brnchs = Some e' ->
      (*?*) eval_env ((List.rev vs) ++ rho) e' v ->
      eval_env rho (Match_e e1 n brnchs) v
| eval_Prf: forall rho, eval_env rho Prf_e Prf_v
| eval_ProofApp:
    forall (f: expression.exp) (rho: env) (e : expression.exp) (e' : value),
      eval_env rho f Prf_v ->
      eval_env rho e e' ->
      eval_env rho (App_e f e) Prf_v.

(* not being used for semantics *)
Inductive evals_env: env -> exps -> list value -> Prop :=
| evals_nil: forall (rho: env),
    evals_env rho enil nil
| evals_cons: forall (e: expression.exp) (es': expression.exps) (rho: env)
  (v: value) (vs': list value),
    eval_env rho e v ->
    evals_env rho es' vs' ->
    evals_env rho (econs e es') (cons v vs').


Lemma eval_env_ind_strong :
  forall P : env -> exp -> value -> Prop,
    (forall (x : N) (rho : env) (n : value),
        nth (N.to_nat x) rho Prf_v = n -> P rho (Var_e x) n) ->
    (forall (e : exp) (rho : env) (na : name), P rho (Lam_e na e) (Clos_v rho na e)) ->
    (forall (e1 e2 e1' : exp) (v v2 : value) (na : name) (rho rho' : env),
        eval_env rho e1 (Clos_v rho' na e1') ->
        P rho e1 (Clos_v rho' na e1') ->
        eval_env rho e2 v2 ->
        P rho e2 v2 ->
        eval_env (v2 :: rho') e1' v -> P (v2 :: rho') e1' v -> P rho (e1 $ e2) v) ->
    (forall (e1 e2 : exp) (v1 v2 : value) (rho : env) (na : name),
        eval_env rho e1 v1 ->
        P rho e1 v1 ->
        eval_env (v1 :: rho) e2 v2 -> P (v1 :: rho) e2 v2 -> P rho (Let_e na e1 e2) v2) ->
    (forall (es : exps) (vs : list value) (rho : env) (dc : dcon),
        Forall2 (fun (e : exp) (v : value) => eval_env rho e v) (exps_to_list es) vs ->
        Forall2 (fun (e : exp) (v : value) => P rho e v) (exps_to_list es) vs ->        
        P rho (Con_e dc es) (Con_v dc vs)) ->
    (forall (n : N) (rho : env) (fnlst : efnlst),
        P rho (Fix_e fnlst n) (ClosFix_v rho fnlst n)) ->
    (forall (e1 e2 e' e'' : exp) (rho rho' rho'' rho_f : env) 
            (n : N) (fnlst : efnlst) (v2 v : value) (na : name),
        eval_env rho e1 (ClosFix_v rho' fnlst n) ->
        P rho e1 (ClosFix_v rho' fnlst n) ->
        enthopt (N.to_nat n) fnlst = Some e' ->
        make_rec_env fnlst rho' = rho'' ->
        eval_env rho'' e' (Clos_v rho_f na e'') ->
        P rho'' e' (Clos_v rho_f na e'') ->
        eval_env rho e2 v2 ->
        P rho e2 v2 ->
        eval_env (v2 :: rho_f) e'' v -> P (v2 :: rho_f) e'' v -> P rho (e1 $ e2) v) ->
    (forall (e1 e' : exp) (rho : env) (dc : dcon) (vs : list value) 
            (n : N) (brnchs : branches_e) (v : value),
        eval_env rho e1 (Con_v dc vs) ->
        P rho e1 (Con_v dc vs) ->
        find_branch dc (N.of_nat (Datatypes.length vs)) brnchs = Some e' ->
        eval_env (rev vs ++ rho) e' v ->
        P (rev vs ++ rho) e' v -> P rho (Match_e e1 n brnchs) v) ->
    (forall rho : env, P rho Prf_e Prf_v) ->
    (forall (f8 : exp) (rho : env) (e : exp) (e' : value),
        eval_env rho f8 Prf_v ->
        P rho f8 Prf_v -> eval_env rho e e' -> P rho e e' -> P rho (f8 $ e) Prf_v) ->
    forall (rho : env) (e : exp) (v : value), eval_env rho e v -> P rho e v.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. fix 4.
  intros rho e v Heval; inv Heval;
    try (now clear eval_env_ind_strong; eauto).
  - eapply H4.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
  - eapply H5.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
  - eapply H6.
    eassumption.
    induction H.
    + constructor.
    + simpl in *.
      constructor.
      * eapply eval_env_ind_strong. eassumption.
      * eapply IHForall2.
  - eapply H8.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. reflexivity. eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
  - eapply H9.
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eassumption. 
    eapply eval_env_ind_strong. eassumption.
  - eapply H11. 
    eassumption. eapply eval_env_ind_strong. eassumption.
    eassumption. eapply eval_env_ind_strong. eassumption.
Qed.
        
    
(* write custom induction hypothesis? *)
Lemma eval_env_single_valued:
  (forall e rho d, eval_env rho e d -> forall f, eval_env rho e f -> d = f).
Proof.
  intros e rho d Hd f Hf.
  induction e.
  - inv Hd. inv Hf. reflexivity.
  - inv Hd. inv Hf. reflexivity.
  - admit.
  - inv Hd. inv Hf.
    assert (Heq: vs = vs0).
    { induction vs.
      + destruct vs0. reflexivity.
        inv H3. inv H4. rewrite <- H0 in H. now inv H.
      + destruct vs0.
        inv H3. inv H4. rewrite <- H in H1. now inv H1.
        inv H3. inv H4. 
Admitted. 

Fixpoint efnlst_to_list (fnlst: efnlst) :=
  match fnlst with
  | eflnil => nil
  | eflcons na e fnlst' =>
    let l := efnlst_to_list fnlst' in
    (e::l)
  end.

Definition well_formed_in_env (e : exp) (rho : list value) :=
  exp_wf (list.NLength rho) e.

Definition well_formed_exps_in_env (es : exps) (rho : list value) :=
  Forall (fun e => well_formed_in_env e rho) (exps_to_list es).

Inductive well_formed_val : value -> Prop :=
| Wf_Con :
    forall dc vs,
      Forall well_formed_val vs ->
      well_formed_val (Con_v dc vs)
| Wf_Prf :
    well_formed_val Prf_v
| Wf_Clos :
    forall vs n e,
      Forall well_formed_val vs -> 
      (forall x, well_formed_in_env e (x :: vs)) ->
      well_formed_val (Clos_v vs n e)
| Wf_ClosFix :
    forall vs n efns,
      Forall well_formed_val vs ->
      (forall fs,
          list.NLength fs = efnlst_length efns ->
          Forall (fun (p : name * exp) =>
                    let (n, e) := p in 
                    well_formed_in_env e (fs ++ vs)) (efnlst_as_list efns)) ->
          well_formed_val (ClosFix_v vs efns n).

Definition well_formed_env (rho : list value) : Prop :=
  Forall well_formed_val rho.

Opaque N.add.

Lemma well_formed_in_env_App:
  forall e1 e2 rho,
    well_formed_in_env (App_e e1 e2) rho ->
    well_formed_in_env e1 rho /\ well_formed_in_env e2 rho.
Proof.
  intros e1 e2 rho H.
  unfold well_formed_in_env in *.
  inv H. split; eassumption.
Qed.

Lemma well_formed_in_env_Let:
  forall na e1 e2 rho,
    well_formed_in_env (Let_e na e1 e2) rho ->
    well_formed_in_env e1 rho.
Proof.
  intros na e1 e2 rho H.
  unfold well_formed_in_env in *.
  inv H. 
  eassumption.
Qed.

Lemma well_formed_in_env_Con:
  forall dc es rho,
    well_formed_in_env (Con_e dc es) rho ->
    well_formed_exps_in_env es rho.
Proof.
  intros dc es rho H.
  induction es.
  - now constructor.
  - inv H. unfold well_formed_exps_in_env in *.
    econstructor. inv H2.
    unfold well_formed_in_env. eassumption.
    fold exps_to_list.
    eapply IHes.
    unfold well_formed_in_env. inv H2.
    try econstructor. eassumption.
Qed.

Lemma well_formed_in_env_Match:
  forall e bs rho i,
    well_formed_in_env (Match_e e i bs) rho ->
    well_formed_in_env e rho.
Proof.
  intros e bs rho i H.
  inv H. unfold well_formed_in_env.
  eassumption.
Qed.

Lemma app_length_N:
  forall (T : Type) (l1 l2 : list T),
    list.NLength (l1 ++ l2) = list.NLength l1 + list.NLength l2.
Proof.
  intros T l1 l2.
  induction l1.
  - simpl. unfold list.NLength. simpl. reflexivity.
  - unfold list.NLength in *. simpl.
    rewrite !Pos.of_nat_succ.
    rewrite <- !positive_nat_N.
    rewrite !Nat2Pos.id; try (intros; discriminate).
    rewrite !Nnat.Nat2N.inj_succ. 
    rewrite IHl1. rewrite <- N.add_succ_r.
    rewrite N.add_succ_comm. reflexivity.
Qed.

Lemma well_formed_in_env_Match_branches:
  forall e e' bs rho i dc vs,
    eval_env rho e (Con_v dc vs) ->
    well_formed_in_env (Match_e e i bs) rho ->
    find_branch dc (N.of_nat (Datatypes.length vs)) bs = Some e' ->
    well_formed_in_env e' (vs ++ rho).
Proof.
  intros e e' bs rho i d vs Heval Hwf H.
  inv Hwf.
  unfold well_formed_in_env.
  rewrite app_length_N. unfold list.NLength.
  eapply find_branch_preserves_wf; eassumption.
Qed. 

(* e2 should also evaluate to value *)
Lemma eval_env_app_subterm:
      forall e1 e2 rho v,
        eval_env rho (e1 $ e2) v ->
        exists v1, eval_env rho e1 v1.
Proof.
  intros e1 e2 rho v H.
  inv H; try (eexists; eassumption).
Qed.

Lemma nth_inlist_Forall A (P : A -> Prop) :
  forall l n default,
    lt (N.to_nat n) (List.length l) -> 
    Forall P l ->
    P (nth (N.to_nat n) l default).
Proof.
  intros l n default Hn Hl.
  generalize dependent n.
  induction l; intros n Hn.
  - simpl. inv Hn. 
  - simpl. destruct (N.to_nat n) eqn:Hnat.
    inv Hl. eassumption.
    assert (Heq : ((N.to_nat n) - (N.to_nat 1%N))%nat = n0).
    { simpl. rewrite Pos2Nat.inj_1. omega. }
    rewrite <- Nnat.N2Nat.inj_sub in Heq.
    rewrite <- N.pred_sub in Heq. symmetry in Heq.    
    rewrite Heq. eapply IHl.
    inv Hl. eassumption.
    inversion Hn. rewrite <- Hnat. try (zify; omega).
    rewrite <- Heq. subst. omega.
Qed. 

Lemma make_rec_env_exists fnlst rho n : 
  exists rhof,
    make_rec_env fnlst rho = rhof ++ rho /\
    list.NLength rhof = efnlst_length fnlst /\
    (well_formed_val (ClosFix_v rho fnlst n) ->
     well_formed_env rho ->
     well_formed_env (rhof ++ rho)).
Proof.
  unfold make_rec_env. generalize fnlst at 1 4.
  generalize 0. 
  induction fnlst; intros n' F.
  - eexists nil.
    repeat split; eauto.
  - edestruct (IHfnlst (n' + 1) F) as (rhof & Hmake & Hlen & Hwf).
    exists ((ClosFix_v rho F n') :: rhof). repeat split.
    + simpl. f_equal. rewrite <- Hmake. reflexivity.
    + simpl. rewrite <- Hlen. unfold list.NLength.
      simpl. zify. omega.
    + intros Hwf1 Hwf2. constructor.
      inv Hwf1. now constructor; eauto.
      eapply Hwf.
      inv Hwf1. now constructor; eauto.
      eassumption.
Qed.

Lemma enthopt_inlist_Forall (P : exp -> Prop) :
  forall efnl n e,
    Forall (fun (p : name * exp) => let (_, e) := p in P e) (efnlst_as_list efnl) ->
    enthopt (N.to_nat n) efnl = Some e ->
    P e.
Proof.
  intros efnl n.
  generalize (N.to_nat n). induction efnl; intros n' e' Hall Hnth.
  - destruct n'; simpl in Hnth; inv Hnth.
  - destruct  n'. inv Hnth.
    + inv Hall. eassumption.
    + inv Hall. simpl in Hnth. eapply IHefnl.
      eassumption. eassumption.
Qed.

Lemma Forall_app_bkwd:
  forall (A : Type) (P : A -> Prop) (l l' : list A),
    Forall P l /\ Forall P l' -> Forall P (l ++ l').
Proof.
  intros A P l l' H.
  destruct H.
  induction l.
  - destruct l'.
    simpl. constructor.
    simpl. eassumption.
  - destruct l'.
    rewrite (app_nil_r (a :: l)). eassumption.
    simpl. eapply Forall_cons.
    inv H. eassumption.
    eapply IHl. inv H. eassumption.
Qed.

Lemma Forall_rev:
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l -> Forall P (rev l).
Proof.
  intros A P l H.
  induction l.
  - simpl. constructor.
  - simpl. eapply Forall_app_bkwd.
    split. eapply IHl. inv H. eassumption.
    inv H. eapply Forall_cons. eassumption. now constructor.
Qed.

Lemma list_rev_length_N:
  forall (A : Type) (l : list A),
    list.NLength l = list.NLength (rev l).
Proof.
  intros A l.
  induction l.
  - reflexivity.
  - simpl. rewrite app_length_N.
    rewrite <- IHl.
    unfold list.NLength. simpl.
    rewrite Pos.of_nat_succ.
    rewrite <- positive_nat_N.
    rewrite Nat2Pos.id.
    rewrite N.add_1_r.
    rewrite <- Nnat.Nat2N.inj_succ.
    reflexivity. intros Hfalse. now inv Hfalse.
Qed. 

Lemma eval_env_preserves_well_formed:
  forall rho e v,
    eval_env rho e v ->
    well_formed_in_env e rho ->
    well_formed_env rho ->
    well_formed_val v.
Proof.
  pose (P := fun rho e v => well_formed_in_env e rho ->
                            well_formed_env rho ->
                            well_formed_val v).
  replace (forall (rho : env) (e : exp) (v : value),
              eval_env rho e v ->
              well_formed_in_env e rho ->
              well_formed_env rho -> well_formed_val v)
    with (forall rho e v, eval_env rho e v -> P rho e v); eauto.
  eapply eval_env_ind_strong with (P := P); unfold P; clear P; intros.
  - (* Var *)
    unfold well_formed_in_env in *. inv H0.
    eapply nth_inlist_Forall; [ | eassumption ].
    unfold list.NLength in *.    
    zify. omega.
  - (* Lam *)
    econstructor. eassumption. 
    intros x. unfold well_formed_in_env in *.
    inv H.
    unfold list.NLength in *. simpl. 
    rewrite Pos.of_nat_succ.
    rewrite <- positive_nat_N.
    rewrite Nat2Pos.id.
    rewrite N.add_1_l in H3.
    rewrite <- Nnat.Nat2N.inj_succ in H3. 
    eassumption. intros Hfalse. now inv Hfalse. 
  - (* LamApp *)
    eapply well_formed_in_env_App in H5.
    destruct H5 as [He1 He2].
    specialize (H0 He1 H6). specialize (H2 He2 H6).
    eapply H4.
    + inv H0. eapply H10.
    + constructor. eassumption. inv H0. eassumption.  
  - (* Let *)
    eapply H2.  inv H3.
    unfold well_formed_in_env.
    unfold list.NLength in *. simpl.
    rewrite Pos.of_nat_succ.
    rewrite <- positive_nat_N.
    rewrite Nat2Pos.id.
    rewrite N.add_1_l in H10.
    rewrite <- Nnat.Nat2N.inj_succ in H10. 
    eassumption. intros Hfalse. now inv Hfalse.
    econstructor. eapply H0.
    eapply well_formed_in_env_Let in H3. eassumption. 
    eassumption.
    eassumption.
  - (* Con *)
    econstructor.
    eapply well_formed_in_env_Con in H1. 
    generalize dependent es. 
    induction vs; intros. 
    + now constructor.
    + econstructor; destruct es; inv H0.
      -- inv H. inv H1. apply H6; eassumption.
      -- inv H. eapply IHvs.
         eassumption. eassumption. inv H1. eassumption.
  - (* Fix *)
    econstructor. eassumption. 
    inv H. generalize dependent (efnlst_length fnlst). 
    induction fnlst.
    + intros l Hl fs Hfs.
      simpl. now econstructor.
    + intros l Hl fs Hfs. simpl.
      econstructor.
      -- unfold well_formed_in_env in *.
         inv Hl. rewrite app_length_N. eassumption.
      -- inv Hl. eapply IHfnlst.
         eapply H6. reflexivity.
  - (* FixApp *)
    subst.
    eapply well_formed_in_env_App in H9.
    destruct H9 as [He1 He2].
    specialize (H0 He1 H10). inv H0.
    edestruct (make_rec_env_exists fnlst rho' 0) as (rhof & Heqf & Hlenf & Hwff).
    assert (Ha1 : well_formed_in_env e' (make_rec_env fnlst rho')).
    { rewrite Heqf.
      specialize (H13 rhof Hlenf).  
      eapply enthopt_inlist_Forall in H13; eauto. }
    assert (Ha2 : well_formed_env (make_rec_env fnlst rho')).
    { rewrite Heqf. eapply Hwff. constructor. eassumption.
      eassumption. eassumption. }
    specialize (H4 Ha1 Ha2). inv H4.
    eapply H8.
    + eapply H14.
    + constructor. eapply H6; eauto. eassumption.
  - (* Match *)
    eapply H3.
    + unfold well_formed_in_env. inv H4.
      rewrite app_length_N. rewrite <- list_rev_length_N.
      eapply find_branch_preserves_wf; eassumption. 
    + unfold well_formed_env.
      eapply Forall_app_bkwd. split.
      -- eapply well_formed_in_env_Match in H4.
         specialize (H0 H4 H5).
         inv H0.
         eapply Forall_rev. eassumption.
      -- eassumption.
  - (* Prf *)
    now constructor.
  - (* PrfApp *)
    eapply well_formed_in_env_App in H3.
    destruct H3 as [Hf8 He].
    eapply H0; eassumption.
Qed.

Lemma make_rec_env_wf:
  forall rho fnlst n, 
    well_formed_val (ClosFix_v rho fnlst n) ->
    well_formed_env (make_rec_env fnlst rho).
Proof.
  intros rho fnlst n Hwf.
  inv Hwf. induction fnlst.
  - simpl in *. unfold make_rec_env. eapply H1.
  - simpl in *. unfold well_formed_env.
    unfold make_rec_env. 
Admitted. 
   
      
(* TODOO move to expression *)
Fixpoint parallel_sbst (e : exp) (depth : N) (esubst : list exp) :=
  match e with
  | Var_e i =>
    if i <? depth then Var_e i
    else
      nth (N.to_nat (i - depth)) esubst (Var_e (i - (list.NLength esubst)))
  | Lam_e na e1 =>
    Lam_e na (parallel_sbst e1 (depth + 1) esubst)
  | App_e e1 e2 =>
    App_e (parallel_sbst e1 depth esubst) (parallel_sbst e2 depth esubst)
  | Let_e na e1 e2 =>
    Let_e na (parallel_sbst e1 depth esubst) (parallel_sbst e2 (depth + 1) esubst)
  | Con_e d es => Con_e d (parallel_sbsts es depth esubst)
  | Fix_e efns i =>
    let l := efnlst_length efns in
    Fix_e (parallel_sbst_efnlst efns (depth + l) esubst) i
  | Match_e e1 n bs =>
    Match_e (parallel_sbst e1 depth esubst) n (parallel_sbst_branches bs depth esubst)
  | Prf_e => Prf_e
  end
with parallel_sbsts (es : exps) (depth : N) (esubst : list exp) :=
       match es with
       | enil => enil
       | econs e es' =>
         econs (parallel_sbst e depth esubst) (parallel_sbsts es' depth esubst)
       end
with parallel_sbst_efnlst (efns : efnlst) (depth : N) (esubst : list exp) :=
       match efns with
       | eflnil => eflnil
       | eflcons na f efns' =>
         let f' := (parallel_sbst f depth esubst) in
         eflcons na f' (parallel_sbst_efnlst efns' depth esubst)
       end
with parallel_sbst_branches (bs : branches_e) (depth : N) (esubst : list exp) :=
       match bs with
       | brnil_e => brnil_e
       | brcons_e d (n, l) e bs' =>
         let e' := parallel_sbst e (depth + n) esubst in
         brcons_e d (n, l) e' (parallel_sbst_branches bs' depth esubst)
       end.

Fixpoint sbst_list_n (e : exp) (vs : exps) (n : N) : exp :=
  match vs with
  | enil => e
  | econs v vs' => (sbst_list_n e vs' n) {n ::= v}
  end.

Fixpoint val_to_exp (v : value) : expression.exp :=
  match v with
  | Con_v d vs => Con_e d (list_to_exps (List.map val_to_exp vs))
  | Prf_v => Prf_e
  | Clos_v rho na e =>
    let es := List.map val_to_exp rho in 
    Lam_e na (parallel_sbst e (Npos 1%positive) es)
  | ClosFix_v rho fnlst n =>
    let len := efnlst_length fnlst in
    let fix aux_efnlst fnlst len : efnlst :=
        match fnlst with
        | eflnil => eflnil
        | eflcons n e fnlst' =>
          let es := List.map val_to_exp rho in
          eflcons n (parallel_sbst e len es) (aux_efnlst fnlst' len)
        end in
    Fix_e (aux_efnlst fnlst len) n
  end.

Definition sbst_env (e: expression.exp) (rho: env) (n : N) : expression.exp :=
  let es := List.map val_to_exp rho in
  parallel_sbst e n es.

(* the exps in this inductive relation should satisfy is_valueb *)
Inductive rel_value: expression.exp -> value -> Prop :=
| rel_Lam:
    forall (e e': expression.exp) (rho: env) (na: name),
      sbst_env e' rho 1%N = e ->
      rel_value (Lam_e na e) (Clos_v rho na e')
| rel_Fix:
    forall (fnlst_s fnlst_t: efnlst) (rho: env) (k1 k2: N),
      k1 = k2 ->
      let lst_s := efnlst_as_list fnlst_s in
      let lst_t := efnlst_as_list fnlst_t in
      Forall2 (fun s t =>
                 let (n_s, e_s) := s : name * exp in
                 let (n_t, e_t) := t : name * exp in
                 (n_s = n_t) /\
                 sbst_env e_t rho (efnlst_length fnlst_s) = e_s) lst_s lst_t ->
      rel_value (Fix_e fnlst_s k1) (ClosFix_v rho fnlst_t k2)
| rel_Con:
    forall (es_s: expression.exps) (vs_t: list value) (dc1 dc2: dcon),
      dc1 = dc2 ->
      Forall2 (fun e_s v_t => rel_value e_s v_t) (exps_to_list es_s) vs_t -> 
      rel_value (Con_e dc1 es_s) (Con_v dc2 vs_t)
| rel_Prf:
    rel_value Prf_e Prf_v.

Lemma my_rel_value_ind (P : exp -> value -> Prop) :
  (forall (e e' : exp) (rho : env) (na : name),
      sbst_env e' rho 1 = e -> P (Lam_e na e) (Clos_v rho na e')) ->
  (forall (fnlst_s fnlst_t : efnlst) (rho : env) (k1 k2 : N),
      k1 = k2 ->
      let lst_s := efnlst_as_list fnlst_s in
      let lst_t := efnlst_as_list fnlst_t in
      Forall2
          (fun s t : name * exp =>
           let (n_s, e_s) := s in
           let (n_t, e_t) := t in
           n_s = n_t /\ sbst_env e_t rho (efnlst_length fnlst_s) = e_s) lst_s lst_t ->
        P (Fix_e fnlst_s k1) (ClosFix_v rho fnlst_t k2)) ->
  (forall (es_s : exps) (vs_t : list value) (dc1 dc2 : dcon),
      dc1 = dc2 ->
      Forall2 (fun (e_s : exp) (v_t : value) => rel_value e_s v_t) 
              (exps_to_list es_s) vs_t ->
      Forall2 (fun e_s v_t => P e_s v_t) (exps_to_list es_s) vs_t ->
      P (Con_e dc1 es_s) (Con_v dc2 vs_t)) ->
  P Prf_e Prf_v -> forall (e : exp) (v : value), rel_value e v -> P e v.
Proof.
  intros H1 H2 H3 H4. 
  fix 1. intros e. destruct v.
  - intros H.
    destruct e; try inv H.
    eapply H3.
    reflexivity.
    eassumption. 
    + generalize dependent l. induction e; intros l.
      -- intros. inv H9. constructor.
      -- intros. destruct l.
         inv H9. 
         constructor. inv H9. eapply my_rel_value_ind. eassumption.
         eapply IHe. inv H9. eapply H8.
  - intros. destruct e; try inv H. eapply H4.  
  - intros. destruct e; try inv H. eapply H1. reflexivity. 
  - intros. destruct e; try inv H. eapply H2. reflexivity. eassumption.
Qed.     

Inductive rel_subst_env: exps -> env -> Prop :=
| rel_true: forall (es: exps) (rho: env),
    Forall2 (fun e v => rel_value e v) (exps_to_list es) rho ->
    rel_subst_env es rho.

(* Unset Printing Notation. *)

Fixpoint map_exps (f : exp -> exp) (es : exps) : exps :=
  match es with
  | enil => enil
  | econs e es => econs (f e) (map_exps f es)
  end.

Fixpoint sbst_list_n_exps (es es_sbst : exps) (n : N)  :=
  map_exps (fun e => sbst_list_n e es_sbst n) es.


Inductive is_value_env : exp -> Prop :=
  | lam_is_value_env : forall (na : name) (e : exp), is_value_env (Lam_e na e)
  | con_is_value_env :
      forall (d : dcon) (es : exps),
        are_values_env es -> is_value_env (Con_e d es)
  | fix_is_value_env : forall (es : efnlst) (k : N), is_value_env (Fix_e es k)
  | prf_is_value_env : is_value_env Prf_e
with are_values_env : exps -> Prop :=
       enil_are_values_env : are_values_env enil
     | econs_are_values_env : forall (e : exp) (es : exps),
         is_value_env e -> are_values_env es -> are_values_env (econs e es).

Scheme is_value_env_ind2 := Induction for is_value_env Sort Prop
with are_values_env_ind2 := Induction for are_values_env Sort Prop.

Combined Scheme is_value_env_ind_mut
         from is_value_env_ind2, are_values_env_ind2.

Lemma value_self_eval :
  (forall v, is_value_env v -> eval v v) /\
  (forall vs, are_values_env vs -> evals vs vs).
Proof.
  apply is_value_env_ind_mut; simpl; intros; auto; try constructor; auto.
Qed.

Lemma is_value_env_val_to_exp :
  (forall v, is_value_env (val_to_exp v)).
Proof.
  apply value_ind'.
  + intros dcon vs Hall. simpl. 
    constructor.
    induction vs. now constructor. 
    inv Hall.
    simpl. constructor. eassumption.
    eauto.
  + constructor.
  + intros. constructor.
  + intros. constructor.
Qed.   

Lemma sbst_all_values :
  forall es esubst, List.map val_to_exp es = esubst ->
                    Forall (fun e => is_value_env e) esubst.
Proof.
  intros es.
  induction es.
  - intros esubst Hmap.
    simpl in *.
    rewrite <- Hmap.
    apply Forall_nil.
  - intros esubst Hmap.
    simpl in *.
    rewrite <- Hmap. 
    eapply Forall_cons.
    eapply is_value_env_val_to_exp.
    eapply IHes.
    reflexivity. 
Qed.

Lemma n_sub_0 n :
  n - 0 = n.
Proof.
  destruct n. reflexivity. reflexivity.
Qed.

Lemma exps_length_is_Datatypes_length:
  forall es, exps_length es = N.of_nat (Datatypes.length (exps_to_list es)).
Proof.
  induction es.
  - reflexivity. 
  - simpl. zify. omega.
Qed. 
    
Lemma nth_inlist_is_value' :
  forall l default n, 
    Forall is_value_env l -> is_value_env default ->
    is_value_env (nth (N.to_nat n) l default).
Proof.
  intros l default n Hl Hdef.
  generalize dependent (N.to_nat n). 
  induction l.
  - intros n0. simpl. destruct n0; eassumption.
  - intros n0. inv Hl. 
    simpl. destruct n0.
    + eassumption.
    + eapply IHl.
      eassumption.
Qed.

Lemma len_cons_lt:
      forall n (e : exp) l,
        lt (S n) (List.length ((e::nil) ++ l)) -> lt n (List.length l).
Proof.
  intros n e l H.
  destruct n.
  - simpl in H. omega.
  - simpl in H. eapply UsefulTypes.S_lt_inj in H. eassumption.
Qed. 

(* list.NLength uses N.of_nat *)
Lemma nth_inlist_is_value :
  forall l n default,
    lt (N.to_nat n) (List.length l) -> 
    Forall is_value_env l ->
    is_value_env (nth (N.to_nat n) l default).
Proof.
  intros l n default Hn Hl.
  generalize dependent n.
  induction l; intros n Hn.
  - simpl. inv Hn. 
  - simpl. destruct (N.to_nat n) eqn:Hnat.
    inv Hl. eassumption.
    assert (Heq : ((N.to_nat n) - (N.to_nat 1%N))%nat = n0).
    { simpl. rewrite Pos2Nat.inj_1. omega. }
    rewrite <- Nnat.N2Nat.inj_sub in Heq.
    rewrite <- N.pred_sub in Heq. symmetry in Heq.    
    rewrite Heq. eapply IHl.
    inv Hl. eassumption.
    inversion Hn. rewrite <- Hnat. try (zify; omega).
    rewrite <- Heq.
    rewrite (list.cons_as_app exp a l) in Hn.
    eapply len_cons_lt in Hn. eassumption.
Qed. 

Lemma f_efnlst_length':
      forall l fnl rho, efnlst_length
                      ((fix aux_efnlst (fnlst : efnlst) (len : N) {struct fnlst} :
                         efnlst :=
                         match fnlst with
                         | eflnil => eflnil
                         | eflcons n e fnlst' =>
                           eflcons n (parallel_sbst e len (map val_to_exp rho))
                                   (aux_efnlst fnlst' len)
                         end) fnl l) = efnlst_length fnl.
Proof.
  induction fnl; intros.
  - reflexivity.
  - simpl. rewrite (IHfnl rho). reflexivity.
Qed.

Lemma f_efnlst_length_inv:
  forall rho fnl,
  efnlst_length ((fix aux_efnlst (fnlst : efnlst) (len : N) {struct fnlst} :
                         efnlst :=
                         match fnlst with
                         | eflnil => eflnil
                         | eflcons n e fnlst' =>
                           eflcons n (parallel_sbst e len (map val_to_exp rho))
                                   (aux_efnlst fnlst' len)
                         end) fnl (efnlst_length fnl)) =
                      efnlst_length fnl.
Proof.
  intros. eapply (f_efnlst_length' (efnlst_length fnl) fnl rho).
Qed.

Opaque N.add.

Lemma efnlst_length_commut flst :
   N.to_nat (efnlst_length flst) = List.length (efnlst_as_list flst).
Proof.
  simpl. induction flst; eauto.
  - simpl. rewrite Nnat.N2Nat.inj_add.
    rewrite <- IHflst. simpl. reflexivity.
Qed.
    
Lemma rel_value_val_to_exp :
  forall v, rel_value (val_to_exp v) v.
Proof.
  eapply value_ind'. 
  - constructor.
    reflexivity.
    fold val_to_exp.
    induction vs.
    + simpl. eapply List.Forall2_nil.
    + eapply Forall2_cons.
      inv H. eassumption.  
      eapply IHvs. inv H. eassumption. 
  - constructor.
  - constructor.
    fold val_to_exp.
    unfold sbst_env.
    reflexivity.
  - intros vs fnl n. simpl. constructor.
    reflexivity.
    set (f := (fix aux_efnlst (fnlst : efnlst) (len0 : N) {struct fnlst} : efnlst :=
                 match fnlst with
                 | eflnil => eflnil
                 | eflcons n1 e0 fnlst' =>
                   eflcons n1 (parallel_sbst e0 len0 (map val_to_exp vs))
                           (aux_efnlst fnlst' len0)
                 end)).
    assert (Hf_eq : forall l, efnlst_length (f fnl l) = efnlst_length fnl).
    { induction fnl; intros l.
      - simpl. reflexivity.
      - simpl. rewrite IHfnl. reflexivity.
    }
    assert (Hlen_eq : efnlst_length (f fnl (efnlst_length fnl)) =
                      efnlst_length fnl).
    { eapply Hf_eq. } 
    rewrite Hlen_eq. clear Hlen_eq. clear Hf_eq. 
    generalize dependent (efnlst_length fnl).
    induction fnl; intros len.
    + simpl. now constructor.
    + simpl. 
      constructor.
      * split; reflexivity. 
      * simpl. eapply IHfnl.
Qed.

Lemma forall_val_to_exp_equiv_map :
  forall l l',
  Forall2 (fun e v => e = val_to_exp v) l l' ->
  l = map val_to_exp l'.
Proof.
  intros l. induction l; intros l' H.
  - destruct l'.
    simpl. reflexivity.
    inv H.
  - destruct l'.
    inv H.
    simpl. inversion H. f_equal.
    rewrite H3. reflexivity.
    eapply IHl. eassumption.
Qed.


Lemma exps_to_list_list_to_exps_inv :
  forall l, list_to_exps (exps_to_list l) = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed. 

Lemma exps_to_list_cons_commut :
        forall hd tl es,
        (hd :: tl) = exps_to_list es ->
        es = (econs hd (list_to_exps tl)).
Proof.
  intros hd tl es H.
  destruct es.
  - inv H.
  - inversion H. rewrite (exps_to_list_list_to_exps_inv es). reflexivity.
Qed. 

Lemma rel_value_then_val_to_exp:
  forall v v', rel_value v v' -> v = val_to_exp v'.
Proof.
  eapply my_rel_value_ind; intros.
  - simpl. unfold sbst_env in H. rewrite H. reflexivity.
  - simpl.
    set (f := (fix aux_efnlst (fnlst : efnlst) (len0 : N) {struct fnlst} : efnlst :=
                 match fnlst with
                 | eflnil => eflnil
                 | eflcons n1 e0 fnlst' =>
                   eflcons n1 (parallel_sbst e0 len0 (map val_to_exp rho))
                           (aux_efnlst fnlst' len0)
                 end)).
    subst. f_equal.
    assert (Hleq : length lst_s = length lst_t).
    { eapply Forall2_length. eassumption. }
    unfold lst_s , lst_t in Hleq. rewrite <- !efnlst_length_commut in Hleq.
    eapply Nnat.N2Nat.inj in Hleq. rewrite <- Hleq. clear Hleq.
    generalize dependent (efnlst_length fnlst_s). 
    generalize dependent fnlst_s.
    induction fnlst_t; intros.
    + simpl. unfold lst_t in H0. simpl in H0. inv H0.
      destruct fnlst_s; eauto. inv H1.
    + destruct fnlst_s.
      inv H0. simpl. subst. unfold f; simpl.
      fold f. inv H0.
      eapply IHfnlst_t in H5. subst. destruct H3.  
      f_equal. eassumption.
      unfold sbst_env in H0. rewrite H0. reflexivity. 
  - simpl. inv H0.
    + simpl. assert (es_s = enil).
      { destruct es_s. reflexivity. try discriminate. }
      rewrite H. reflexivity.
    + simpl. inv H1. inversion H2.
      eapply forall_val_to_exp_equiv_map in H7. rewrite H7 in H.
      eapply exps_to_list_cons_commut in H. rewrite H. reflexivity. 
  - simpl. reflexivity.
Qed.

Lemma nth_inlist_map:
  forall default1 default2 es esubst n,
    n < N.of_nat (List.length esubst) ->
    List.map val_to_exp es = esubst ->
    (nth (N.to_nat n) esubst default1) = val_to_exp (nth (N.to_nat n) es default2).
Proof.
  intros default1 default2 es esubst n H1 H2.
  generalize dependent esubst. 
  generalize dependent n. 
  induction es; intros n esubst H H1.
  - simpl in *. inv H1. simpl in H.
    inv H. destruct n eqn:Hn.
    edestruct (N.compare_0_r 0). eassumption.
    edestruct (N.compare_0_r (N.pos p)). eassumption. 
  - destruct esubst.
    + inv H1.
    + simpl. destruct (N.to_nat n) eqn:Hn.
      inversion H1. reflexivity.
      assert (Heq : ((N.to_nat n) - (N.to_nat 1%N))%nat = n0).
      { simpl. rewrite Pos2Nat.inj_1. omega. }
      rewrite <- Nnat.N2Nat.inj_sub in Heq.
      rewrite <- N.pred_sub in Heq.
      rewrite <- Heq. eapply IHes. simpl in H. 
      rewrite Pos.of_nat_succ in H.
      rewrite <- positive_nat_N in H.
      rewrite Nat2Pos.id in H.
      rewrite Nnat.Nat2N.inj_succ in H.
      eapply N.pred_lt_mono in H.
      rewrite N.pred_succ in H. now eapply H.
      intros Hfalse. zify. omega. 
      intros Hfalse. discriminate.
      inv H1. reflexivity. 
Qed. 
      
Lemma rel_value_nth_inlist:
  forall default1 default2 es esubst n,
  n < N.of_nat (List.length esubst) ->
  List.map val_to_exp es = esubst ->
  rel_value (nth (N.to_nat n) esubst default1) (nth (N.to_nat n) es default2).
Proof.
  intros default1 default2 es esubst n Hn Hes.
  rewrite (nth_inlist_map default1 default2 es esubst n).
  eapply rel_value_val_to_exp.
  eassumption.
  eassumption. 
Qed.

Lemma not_default_then_nth:
  forall (n: N) (l : list exp) default val,
  nth (N.to_nat n) l default = val ->
  val <> default ->
  lt (N.to_nat n) (List.length l).
Proof.
  intros n l default val H H1.
  generalize dependent n.
  induction l; intros n Hn.
  - simpl in *. destruct (N.to_nat n).
    unfold not in H1. symmetry in Hn. apply H1 in Hn. destruct Hn.
    unfold not in H1. symmetry in Hn. apply H1 in Hn. destruct Hn.
  - simpl in *. destruct (N.to_nat n). omega.
    eapply lt_n_S. 
    specialize IHl with (N.of_nat n0).
    rewrite (Nnat.Nat2N.id n0) in IHl.
    eapply IHl. eassumption.
Qed.

Lemma N2Nat_inj_lt :
   forall n1 n2,
     n1 < n2 <-> lt (N.to_nat n1) (N.to_nat n2).
Proof.
  intros n1 n2. split.
  - intros H. destruct n1; destruct n2.
    + inv H.
    + simpl. zify. omega.
    + inv H.
    + zify. omega.
  - intros H. destruct n1; destruct n2.
    + omega.
    + zify. omega.
    + inv H.
    + zify. omega. 
Qed.

Lemma nlt_len_then_not_default:
  forall (A : Type) (l : list A) (n : N) (default1 default2: A),
    (N.to_nat n < Datatypes.length l)%nat ->
    nth (N.to_nat n) l default1 = nth (N.to_nat n) l default2.
Proof.
  intros A l n default1 default2 Hle.
  generalize dependent n.
  induction l; intros n Hle.
  - simpl in Hle. inv Hle. 
  - simpl in *. destruct (N.to_nat n) eqn:Hn.
    reflexivity.
    assert (Heq : ((N.to_nat n) - (N.to_nat 1%N))%nat = n0).
    { simpl. rewrite Pos2Nat.inj_1. omega. }
    rewrite <- Nnat.N2Nat.inj_sub in Heq.
    rewrite <- N.pred_sub in Heq.
    rewrite <- Heq. eapply IHl.
    omega.
Qed.

(* Statements of Lemmas *)
Definition equiv_semantics_stmt_exp e := 
  forall rho e',
    eval (parallel_sbst e N0 (List.map val_to_exp rho)) e' ->
    exists v, eval_env rho e v /\ rel_value e' v.

Definition equiv_semantics_stmt_exps es :=
  forall rho es',
    evals (parallel_sbsts es N0 (List.map val_to_exp rho)) es' ->
    Forall2 (fun e' e => exists v, eval_env rho e v /\ rel_value e' v)
            (exps_to_list es') (exps_to_list es).

Definition equiv_semantics_stmt_efnlst efns := 
  forall rho n,
    rel_value (parallel_sbst (Fix_e efns n) N0 (List.map val_to_exp rho))
              (ClosFix_v rho efns n).

Definition equiv_semantics_stmt_branches bs :=
  Forall (fun e => equiv_semantics_stmt_exp (snd e)) (branches_as_list bs).

(*
Lemma sbst_list_inv_Lam_e na n e es :
  exists e', sbst_list_n (Lam_e na e) es n = Lam_e na e'
             /\ sbst_list_n e es (n+1) = e'.
Proof.
  induction es.
  - simpl. eexists. split; reflexivity.
  - simpl. destruct IHes as [e' Hlst].
    destruct Hlst.
    destruct n.
    + simpl in *. rewrite H0.
      rewrite H.
      eexists; split; reflexivity.
    + simpl in *.
      rewrite H. rewrite H0.
      eexists. split.
      reflexivity.
      fold sbst.
      assert (Hpos: N.pos (BinPos.Pos.add p 1) = 1 + N.pos p).
      -- destruct p; simpl; reflexivity.
      -- rewrite Hpos. reflexivity.
Qed.
*)

Lemma parallel_sbst_inv_Lam_e na n e es :
  exists e', parallel_sbst (Lam_e na e) n es = Lam_e na e'
             /\ parallel_sbst e (n+1) es = e'.
Proof.
  eexists.
  split.
  - simpl. reflexivity.
  - reflexivity.
Qed.

Lemma sbst_list_inv_Con_e n d es esubst:
  exists es', sbst_list_n (Con_e d es) esubst n = Con_e d es'
              /\ Forall2 (fun e e' => sbst_list_n e esubst n = e')
                         (exps_to_list es) (exps_to_list es'). 
Proof.
  generalize dependent n. induction esubst.
  - intros n. exists es. simpl. split. reflexivity.
    eapply Forall2_refl. eauto with typeclass_instances.
  - intros n. simpl.
    destruct (IHesubst n) as [es' [Hsbst Hall]].
    eexists.
    rewrite Hsbst. simpl. split.
    + reflexivity.
    + revert Hall. clear.
      revert es'. induction es; intros es' Hall; destruct es'; try (now inv Hall).
      * simpl. constructor.
      * simpl in *. inv Hall. constructor.
        -- reflexivity.
        -- eauto.
Qed.

Lemma parallel_sbst_inv_Con_e n d es esubst:
  exists es', parallel_sbst (Con_e d es) n esubst = Con_e d es'
              /\ map_exps (fun e => parallel_sbst e n esubst) es = es'.
Proof.
  exists (parallel_sbsts es n esubst).
  split.
  reflexivity.
  induction es.
  - simpl. reflexivity.
  - simpl. rewrite IHes. reflexivity.
Qed.


Lemma parallel_sbsts_map_exps_equiv es n esubst:
  parallel_sbsts es n esubst = map_exps (fun e => parallel_sbst e n esubst) es.
Proof.
  induction es.
  - simpl. reflexivity.
  - simpl. rewrite <- IHes. reflexivity.
Qed.

Lemma Con_e_exists_list es es' rho:
      Forall2 (fun e' e =>  exists v : value, eval_env rho e v /\ rel_value e' v)
              (exps_to_list es') (exps_to_list es) ->
      exists vs, Forall2 (fun e v => eval_env rho e v) (exps_to_list es) vs
                 /\ Forall2 (fun e' v => rel_value e' v) (exps_to_list es') vs.
Proof.
  intros H.
  induction H.
  - exists nil. split; eapply List.Forall2_nil.
  - destruct H. destruct IHForall2.
    exists (x0::x1). destruct H, H1.  
    split.
    + eapply Forall2_cons; eassumption.
    + eapply Forall2_cons; eassumption.
Qed.

Lemma parallel_sbst_inv_Fix_e efns i n esubst:
  exists efns', parallel_sbst (Fix_e efns i) n esubst = Fix_e efns' i
                /\ let l := efnlst_length efns in
                   Forall2 (fun e e' => parallel_sbst e (n + l) esubst = e')
                           (efnlst_to_list efns) (efnlst_to_list efns'). 
Proof.
  exists (parallel_sbst_efnlst efns (n + (efnlst_length efns)) esubst).
  split.
  - simpl. reflexivity.
  - simpl.
    generalize dependent (n + efnlst_length efns). 
    induction efns; intros n1.
    + simpl. eapply List.Forall2_nil.
    + simpl. eapply Forall2_cons. reflexivity.
      eapply IHefns.
Qed.
    
    
(*
Lemma equiv_semantics_fwd_exp: forall e, equiv_semantics_stmt_exp e
with equiv_semantics_fwd_exps: forall es, equiv_semantics_stmt_exps es
with equiv_semantics_fwd_efnlst: forall efns, equiv_semantics_stmt_efnlst efns
with equiv_semantics_fwd_branches: forall bs, equiv_semantics_stmt_branches bs.
Proof.
  - clear equiv_semantics_fwd_exp.
    induction e. 
 *)


Definition equiv_semantics_stmt_exp' (e1 e' : exp) (P :  eval e1 e') :=
  forall rho e2,
    well_formed_in_env e2 rho ->
    well_formed_env rho ->
    e1 = parallel_sbst e2 N0 (List.map val_to_exp rho) ->
  exists v, eval_env rho e2 v /\ rel_value e' v.

Definition equiv_semantics_stmt_exps' (es1 es' : exps) (P : evals es1 es') :=
  (forall rho es2,
      well_formed_exps_in_env es2 rho ->
      well_formed_env rho ->
      es1 = (parallel_sbsts es2 N0 (List.map val_to_exp rho)) ->
      Forall2 (fun e' e => exists v, eval_env rho e v /\ rel_value e' v)
              (exps_to_list es') (exps_to_list es2)).

Lemma is_value_env_not_Var :
  forall e n, is_value_env e -> e <> Var_e n.
Proof.
  intros e n H.
  inv H; unfold not; intros; try inv H.
Qed.

Lemma sbst_all_values_not_Var es :
  Forall (fun e => is_value_env e) es ->
  Forall (fun e => forall n, e <> Var_e n) es.
Proof.
  intros. induction es.
  - econstructor.
  - econstructor.
    intros n. eapply is_value_env_not_Var. inv H. eassumption.
    eapply IHes. inv H. eassumption.
Qed.

Lemma app_not_value :
  forall e1 e2,
    ~(is_value_env (App_e e1 e2)).
Proof.
  intros e1 e2. unfold not. intros H.
  inv H.
Qed. 

Lemma parallel_sbst_inv_App_e' :
  forall (n : N) (e1 e2 e : exp) (es : list exp),
    Forall (fun e => is_value_env e) es ->
    parallel_sbst e n es = (e1 $ e2) ->
    exists e1' e2' : exp,
      e = (e1' $ e2') /\
      parallel_sbst e1' n es = e1 /\
      parallel_sbst e2' n es = e2.
Proof.
  intros n e1 e2 e es H Hsbst.
  destruct e; try inv Hsbst.
  - destruct (n0 <? n). inv H1.
    pose proof (app_not_value e1 e2) as Happ. 
    pose proof (nth_inlist_is_value es (n0 - n) (Var_e (n0 - list.NLength es)))
      as Hnth.
    assert (Hlen: (N.to_nat (n0 - n) < Datatypes.length es)%nat).
    { eapply not_default_then_nth. eapply H1.
      unfold not. intros H2. inv H2.
    }
    eapply Hnth in Hlen. rewrite H1 in Hlen.
    unfold not in Happ. apply Happ in Hlen. destruct Hlen.
    eassumption.
  - eexists. eexists. split.
    reflexivity. split; reflexivity.
Qed.

Lemma parallel_sbst_inv_Let_e' :
  forall (n : N) (na : name) (e1 e2 e : exp) (es : list exp),
    Forall (fun e => is_value_env e) es ->
    parallel_sbst e n es = (Let_e na e1 e2) ->
    exists e1' e2',
      e = (Let_e na e1' e2') /\
      parallel_sbst e1' n es = e1 /\
      parallel_sbst e2' (n + 1) es = e2.
Proof.
  intros n na e1 e2 e es H Hsubst.
  destruct e; try inv Hsubst.
  - destruct (n0 <? n). inv H1.
    assert (Hnotval: ~(is_value_env (Let_e na e1 e2))).
    { intros Hfalse. inv Hfalse. }
    pose proof (nth_inlist_is_value es (n0 - n) (Var_e (n0 - list.NLength es)))
      as Hnth.
    assert (Hlen: (N.to_nat (n0 - n) < Datatypes.length es)%nat).
    { eapply not_default_then_nth. eapply H1.
      unfold not. intros H2. inv H2.
    }
    eapply Hnth in Hlen. rewrite H1 in Hlen.
    unfold not in Hnotval. apply Hnotval in Hlen. destruct Hlen.
    eassumption.
  - repeat eexists.
Qed. 

Lemma parallel_sbst_inv_Con_e' :
  forall (es es': exps) (n : N) (esubst : list exp),
    parallel_sbsts es n esubst = es'->
    map_exps (fun e => parallel_sbst e n esubst) es = es'.
Proof.
  intros es es' n esubst H.
  generalize dependent es'.
  induction es; intros es' H.
  - simpl in *. rewrite H. reflexivity.
  - simpl in *.
    specialize IHes with (parallel_sbsts es n esubst).
    rewrite IHes. eassumption. reflexivity.
Qed.

Lemma parallel_sbst_inv_efnlst_length :
  forall efns esubst depth,
    efnlst_length (parallel_sbst_efnlst efns depth esubst) =
    efnlst_length efns.
Proof.
  intros efns esubst.
  induction efns; intros depth. 
  - simpl. reflexivity.
  - simpl. rewrite (IHefns depth). reflexivity.
Qed.

Lemma nth_cons {A : Type} n (x : A) l :
  (n > 0)%nat ->
  nth n (x :: l) = nth (n - 1)%nat l.
Proof.
  intros H.
  destruct n eqn:Hn.
  - simpl. inv H.
  - simpl. rewrite Nat.sub_0_r.
    destruct l eqn:Hl.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Definition parallel_sbst_inv_wf_exp e :=
  forall n rho,
    exp_wf n e ->
    parallel_sbst e n rho = e.

Definition parallel_sbst_inv_wf_exps es :=
  forall n rho,
    exps_wf n es ->
    parallel_sbsts es n rho = es.

Definition parallel_sbst_inv_wf_efnlst efns :=
  forall n rho,
    efnlst_wf n efns ->
    parallel_sbst_efnlst efns n rho = efns.

Definition parallel_sbst_inv_wf_branches bs :=
  forall n rho,
    branches_wf n bs ->
    parallel_sbst_branches bs n rho = bs. 

Lemma parallel_sbst_inv_wf:
  (forall e, parallel_sbst_inv_wf_exp e) /\
  (forall es, parallel_sbst_inv_wf_exps es) /\
  (forall efns, parallel_sbst_inv_wf_efnlst efns) /\
  (forall bs, parallel_sbst_inv_wf_branches bs).
Proof.
  apply my_exp_ind; unfold parallel_sbst_inv_wf_exp.
  - intros n i rho Hwf.
    simpl. destruct (lt_dec n i).
    + eapply OrdersEx.N_as_OT.ltb_lt in l. rewrite l.
      reflexivity.
    + eapply OrdersEx.N_as_OT.ge_le in g.
      inv Hwf. zify. omega. 
  - intros na e IH n rho Hwf.
    simpl. inv Hwf.
    eapply IH in H1. rewrite N.add_comm.
    rewrite H1. reflexivity.
  - intros e1 IHe1 e2 IHe2 n rho Hwf.
    simpl. inv Hwf.
    eapply IHe1 in H2. eapply IHe2 in H3.
    rewrite H2. rewrite H3. reflexivity.
  - intros dc es IHes n rho Hwf.
    simpl. unfold parallel_sbst_inv_wf_exps in IHes.
    rewrite IHes. reflexivity.
    inv Hwf. eassumption.
  - intros e IHe pars bs IHbs n rho Hwf.
    unfold parallel_sbst_inv_wf_branches in IHbs.
    simpl. inv Hwf. 
    rewrite IHe; try eassumption.
    rewrite IHbs; try eassumption. reflexivity.
  - intros na e1 IHe1 e2 IHe2 n rho Hwf.
    simpl. inv Hwf.
    eapply IHe1 in H2. eapply IHe2 in H4.
    rewrite H2. rewrite N.add_comm. rewrite H4.
    reflexivity.
  - intros e IHe n i rho Hwf.
    unfold parallel_sbst_inv_wf_efnlst in IHe.
    simpl. inv Hwf. eapply IHe in H1.
    rewrite N.add_comm. rewrite H1.
    reflexivity.
  - intros n rho Hwf. simpl. reflexivity.
  - unfold parallel_sbst_inv_wf_exps. reflexivity.
  - intros e IHe es IHes.
    unfold parallel_sbst_inv_wf_exps in *.
    intros n rho Hwf. simpl.
    inv Hwf. rewrite IHe; try eassumption.
    rewrite IHes; try eassumption. reflexivity.
  - unfold parallel_sbst_inv_wf_efnlst. reflexivity.
  - intros na e IHe efns IHefns.
    unfold parallel_sbst_inv_wf_efnlst in *.
    intros n rho Hwf. simpl.
    inv Hwf. rewrite IHe; try eassumption.
    rewrite IHefns; try eassumption. reflexivity.
  - unfold parallel_sbst_inv_wf_branches. reflexivity.
  - intros dc p e IHe bs IHbs.
    unfold parallel_sbst_inv_wf_branches in *.
    intros n rho Hwf. simpl.
    destruct p. inv Hwf.
    simpl in H2. rewrite N.add_comm. 
    rewrite IHe; try eassumption.
    rewrite IHbs; try eassumption. reflexivity.
Qed.


Definition val_to_exp_is_wf_exp e :=
  forall v, well_formed_val v -> val_to_exp v = e -> exp_wf 0 e.

Definition val_to_exp_is_wf_exps es :=
  forall vs, Forall well_formed_val vs ->
             map val_to_exp vs = (exps_to_list es) -> exps_wf 0 es.

Definition val_to_exp_is_wf_efnlst efns :=
  forall vs n efnlst, well_formed_val (ClosFix_v vs efns n) ->
               val_to_exp (ClosFix_v vs efns n) = Fix_e efnlst n ->
               efnlst_wf 0 efnlst.

(* val_to_exp never applies to branches *)
Definition val_to_exp_is_wf_branches bs :=
  branches_wf 0 bs.

Lemma val_to_exp_is_wf' :
  forall v, 
    (* well_formed_val v -> exp_wf 0 (val_to_exp v).  *)
    exp_wf 0 (val_to_exp v). 
Proof.
  apply value_ind'.
  - intros dc vs Hvs.
    induction vs.
    + simpl in *.
      constructor. constructor. 
    + simpl in *.
      constructor. constructor.
      inv Hvs. eassumption.
      inv Hvs. eapply IHvs in H2.
      inv H2. eassumption.
  - constructor.
  - intros vs na e.     
    
Abort. 

Lemma val_to_exp_is_wf :
  (forall e, val_to_exp_is_wf_exp e) /\
  (forall es, val_to_exp_is_wf_exps es) /\
  (forall efns, val_to_exp_is_wf_efnlst efns) /\
  (forall bs, val_to_exp_is_wf_branches bs).
Proof.
  apply my_exp_ind; unfold val_to_exp_is_wf_exp.
  - intros n v Hwf H. destruct v; inv H.
  - intros na e IH v Hwf H.
    destruct v; try inversion H.
    subst. constructor. inv Hwf.
    (* need to do induction on value cases *)
    (* specialize (IH (Clos_v l na e0) Hwf H). *)
Abort.

Definition parallel_sbst_makes_wf_exp e :=
  forall n rho,
    well_formed_in_env e rho ->
    exp_wf n (parallel_sbst e n (map val_to_exp rho)).

Definition parallel_sbst_makes_wf_exps es :=
  forall n rho,
    Forall (fun e => well_formed_in_env e rho) (exps_to_list es) ->
    exps_wf n (parallel_sbsts es n (map val_to_exp rho)).

Definition parallel_sbst_makes_wf_efnlst efns :=
  forall n rho,
    Forall (fun (p: name * exp) => let (_, e) := p in well_formed_in_env e rho)
           (efnlst_as_list efns) ->
    efnlst_wf n (*??*) (parallel_sbst_efnlst efns n (map val_to_exp rho)).

Definition parallel_sbst_makes_wf_branches bs :=
  forall n rho,
    Forall (fun (b: dcon * (N * list name) * exp) => let '(_, _, e) := b in
                                                     well_formed_in_env e rho)
           (branches_as_list bs) ->
    branches_wf n (parallel_sbst_branches bs n (map val_to_exp rho)). 

Lemma parallel_sbst_makes_wf:
  (forall e, parallel_sbst_makes_wf_exp e) /\
  (forall es, parallel_sbst_makes_wf_exps es) /\
  (forall efns, parallel_sbst_makes_wf_efnlst efns) /\
  (forall bs, parallel_sbst_makes_wf_branches bs).
Proof.
  apply my_exp_ind; unfold parallel_sbst_makes_wf_exp.
  - intros n i rho Hwf.
    simpl. inv Hwf.
    destruct (lt_dec n i).
    + eapply OrdersEx.N_as_OT.ltb_lt in l. rewrite l.
      constructor.
      eapply OrdersEx.N_as_OT.ltb_lt in l. eassumption. 
    + eapply OrdersEx.N_as_OT.ge_le in g. 
      eapply N.ltb_ge in g. rewrite g.
      (* val_to_exp_is_wf -> Forall (exp_wf 0) rho -> nth is wf *)
      admit.
  - intros na e IHe n rho Hwf.
    simpl. inv Hwf. constructor.
    rewrite N.add_comm. eapply IHe.
    unfold well_formed_in_env. 
Abort. 

Definition parallel_sbst_with_sbst_exp e :=
  forall rho x n,
    exp_wf (n + 1 + list.NLength rho) e ->
    Forall (exp_wf 0) (x :: rho) ->
    parallel_sbst e n (x :: rho) = sbst x n (parallel_sbst e (n + 1) rho).

Definition parallel_sbst_with_sbst_exps es :=
  forall rho x n,
    exps_wf (n + 1 + list.NLength rho) es ->
    Forall (exp_wf 0) (x :: rho) ->
    parallel_sbsts es n (x :: rho) = sbsts x n (parallel_sbsts es (n + 1) rho).

Definition parallel_sbst_with_sbst_efnlst efns :=
  forall rho x n,
    efnlst_wf (n + 1 + list.NLength rho) efns ->
    Forall (exp_wf 0) (x :: rho) ->
    parallel_sbst_efnlst efns n (x :: rho) =
    sbst_efnlst x n (parallel_sbst_efnlst efns (n + 1) rho).

Definition parallel_sbst_with_sbst_branches bs :=
  forall rho x n,
    branches_wf (n + 1 + list.NLength rho) bs ->
    Forall (exp_wf 0) (x :: rho) ->
    parallel_sbst_branches bs n (x :: rho) =
    sbst_branches x n (parallel_sbst_branches bs (n + 1) rho).

Lemma parallel_sbst_with_sbst :
  (forall e, parallel_sbst_with_sbst_exp e) /\
  (forall es, parallel_sbst_with_sbst_exps es) /\
  (forall efns, parallel_sbst_with_sbst_efnlst efns) /\
  (forall bs, parallel_sbst_with_sbst_branches bs).
Proof.
  eapply my_exp_ind; unfold parallel_sbst_with_sbst_exp.
  - intros n rho x i Hwf1 Hwf2; eauto.
    unfold parallel_sbst.
    destruct (lt_dec n i).
    * assert (Hleq : n < i + 1) by (zify; omega).
      eapply OrdersEx.N_as_OT.ltb_lt in l. rewrite l.
      eapply OrdersEx.N_as_OT.ltb_lt in Hleq. rewrite Hleq. simpl.
      eapply OrdersEx.N_as_OT.ltb_lt in l.
      eapply OrdersEx.N_as_OT.ltb_lt in Hleq.
      destruct (lt_dec n i); try (zify; omega).
      reflexivity.
    * assert (Heq := g). eapply OrdersEx.N_as_OT.ge_le in g. 
      eapply N.ltb_ge in g. rewrite g.
      destruct (N.eq_dec n i); subst.
      ** rewrite OrdersEx.N_as_OT.sub_diag.
         assert (Hlt : i <? i + 1 = true).
         { eapply N.ltb_lt. zify. omega. }
         rewrite Hlt. simpl.
         destruct (lt_dec i i); try (zify; omega).
         destruct (N.eq_dec i i); try (zify; omega).
         reflexivity.
      ** assert (Hleq : n <? i + 1 = false).
         { eapply N.ltb_ge. zify. omega. }
         rewrite Hleq. 
         assert (Hlt : ~ n < i + 1). zify. omega.
         eapply OrdersEx.N_as_DT.ltb_nlt in Hlt.
         rewrite nth_cons; [ | zify; omega ].
         assert (Heq' : (N.to_nat (n - i)%N - 1)%nat = N.to_nat (n - (i + 1))).
         { zify. omega. } rewrite Heq'.
         edestruct sbst_closed_id as [Hsbst _].
         erewrite Hsbst.
         inv Hwf1.
         assert (Hltlen: n - (i + 1) < list.NLength rho).
         { zify. omega. } eapply nlt_len_then_not_default.
         unfold list.NLength in Hltlen.
         eapply N2Nat_inj_lt in Hltlen.
         rewrite Nnat.Nat2N.id in Hltlen. eassumption. 
         inv Hwf2.
         eapply nth_inlist_Forall; [ | eassumption ].
         inv Hwf1. unfold list.NLength in H3. zify; omega.         
         zify; omega.
  - intros na e IHe rho x i Hwf1 Hwf2. 
    simpl. rewrite IHe. rewrite (N.add_comm i 1). reflexivity.
    inv Hwf1. rewrite !N.add_assoc in H1.
    rewrite (N.add_comm i 1). eassumption.
    eassumption.
  - intros e1 IHe1 e2 IHe2 rho x n Hwf1 Hwf2.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    inv Hwf1. eassumption. 
    eassumption.
    inv Hwf1. eassumption. 
    eassumption.
  - intros d es Hes rho x n Hwf1 Hwf2.
    unfold parallel_sbst_with_sbst_exps in Hes.
    inv Hwf1. specialize (Hes rho x n H1 Hwf2).
    simpl. rewrite Hes. reflexivity.
  - intros e IHe pars bs Hbs rho x n Hwf1 Hwf2.
    unfold parallel_sbst_with_sbst_branches in Hbs.
    inv Hwf1. specialize (Hbs rho x n H4 Hwf2).
    specialize (IHe rho x n H2 Hwf2). 
    simpl. rewrite IHe. rewrite Hbs. reflexivity.
  - intros na e IHe1 e2 IHe2 rho x n Hwf1 Hwf2.
    simpl. rewrite IHe1; try eassumption. rewrite IHe2; try eassumption.
    rewrite (N.add_comm n 1). reflexivity.
    inv Hwf1. rewrite !N.add_assoc in H4.
    rewrite (N.add_comm n 1). eassumption.
    inv Hwf1. eassumption. 
  - intros efns Hefns i rho x n Hwf1 Hwf2.
    unfold parallel_sbst_with_sbst_efnlst in Hefns.
    simpl.
    assert (Hleneq: efnlst_length
                      (parallel_sbst_efnlst efns (n + 1 + efnlst_length efns) rho) =
                    efnlst_length efns).
    { eapply parallel_sbst_inv_efnlst_length. } 
    rewrite Hleneq. erewrite Hefns.
    rewrite N.add_shuffle0.
    rewrite (N.add_comm n (efnlst_length efns)).
    reflexivity.
    inv Hwf1. 
    rewrite !N.add_assoc in *.
    rewrite (N.add_comm n (efnlst_length efns)).
    eassumption. eassumption.
  - intros rho x n Hwf1 Hwf2.
    simpl. reflexivity.
  - unfold parallel_sbst_with_sbst_exps.
    simpl. reflexivity.
  - intros e IHe es Hes.
    unfold parallel_sbst_with_sbst_exps in *.
    intros rho x n Hwf1 Hwf2.
    simpl. inv Hwf1.
    rewrite IHe; try eassumption. 
    rewrite Hes; try eassumption. reflexivity.
  - unfold parallel_sbst_with_sbst_efnlst.
    simpl. reflexivity.
  - intros na e IHe efns Hefns.
    unfold parallel_sbst_with_sbst_efnlst in *.
    intros rho x n Hwf1 Hwf2.
    simpl. inv Hwf1.
    rewrite IHe; try eassumption.
    rewrite Hefns; try eassumption. reflexivity.
  - unfold parallel_sbst_with_sbst_branches.
    simpl. reflexivity.
  - intros dc [n names] e IHe bs Hbs. 
    unfold parallel_sbst_with_sbst_branches in *. 
    intros rho x n' Hwf1 Hwf2.
    simpl. inv Hwf1. rewrite Hbs; try eassumption.
    replace (n' + 1 + n) with (n' + n + 1) by (zify; omega).
    rewrite IHe; try eassumption.
    rewrite (N.add_comm n' n).
    reflexivity. simpl in H2.
    replace (n' + n + 1 + list.NLength rho) with (n + (n' + 1 + list.NLength rho))
      by (zify; omega).
    eassumption.
Qed. 

Lemma eval_is_value_env :
  forall e e', is_value_env e -> eval e e' -> e = e'.
Proof.
  intros e e' Hv Hev.
  destruct value_self_eval as [Hv' _].
  eapply Hv' in Hv.
  eapply eval_single_valued; eauto.
Qed.

Lemma evals_are_value_env :
  forall es es', are_values_env es -> evals es es' -> es = es'.
Proof.
  intros es es' Hv Hev.
  destruct value_self_eval as [_ Hv'].
  eapply Hv' in Hv.
  eapply eval_single_valued; eauto.
Qed.

Lemma find_branch_parallel_sbst:
  forall l dc b es e,
    find_branch dc l (parallel_sbst_branches b 0 es) = Some e -> 
    exists n e', e = parallel_sbst e' n es. 
Proof.
  intros l dc b es e H.
  induction b.
  - inv H.
  - simpl in H. destruct p eqn: Hp.
Abort.
  
Lemma equiv_semantics_fwd_version2 :
  (forall e e' P, equiv_semantics_stmt_exp' e e' P) /\
  (forall es es' P,  equiv_semantics_stmt_exps' es es' P).
Proof. 
  eapply my_eval_ind with (P := equiv_semantics_stmt_exp');
    unfold equiv_semantics_stmt_exp', equiv_semantics_stmt_exps';
    intros; subst.
  - (* Lam_e *)
    symmetry in H1.
    destruct e2; try inv H1.
    + destruct (n <? 0) eqn:Heq.
      inv H3. rewrite n_sub_0 in *.
      eexists. split. econstructor. reflexivity.
      eapply rel_value_nth_inlist.
      eapply N2Nat_inj_lt.
      rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
      eapply not_default_then_nth.
      eapply H3.
      unfold not. intros Hfalse. inv Hfalse.
      reflexivity. 
    + eexists. split.
      constructor.
      constructor. reflexivity. 
  - (* App_e (of Lam_e) *)
    simpl in *.
    symmetry in H4.
    eapply parallel_sbst_inv_App_e' in H4.
    + destruct H4 as [e1'' [e2'' [Heqapp [Hs1 Hs2]]]]. subst.
      assert (Hwf1 : well_formed_in_env e1'' rho).
      { eapply well_formed_in_env_App in H2.
        destruct H2 as [He1'' He2'']. eassumption. }     
      assert (Hwf2 : well_formed_in_env e2'' rho).
      { eapply well_formed_in_env_App in H2.
        destruct H2 as [He1'' He2'']. eassumption. } 
      destruct (H rho _ Hwf1 H3 (eq_refl _)) as [v1 [He1 Hr1]].
      destruct (H0 rho _ Hwf2 H3 (eq_refl _)) as [v2' [He2 Hr2]].      
      inv Hr1.
      assert (HClos_wf: well_formed_val (Clos_v rho0 na e')).
        { eapply eval_env_preserves_well_formed.
          eapply He1. eassumption. eassumption. }
      edestruct (H1 (v2' :: rho0) e') as [v3 [He3 Hr3]].
      * inv HClos_wf. now eapply H8. 
      * unfold well_formed_env.
        eapply Forall_cons.
        eapply eval_env_preserves_well_formed.
        eapply He2. eassumption. eassumption. 
        inv HClos_wf. eassumption. 
      * unfold sbst_env. symmetry.
        simpl. eapply rel_value_then_val_to_exp in Hr2.
        rewrite Hr2.
        edestruct parallel_sbst_with_sbst. eapply H4. clear H4 H5. 
        inv HClos_wf. rewrite N.add_0_l.
        unfold well_formed_in_env in H8. unfold list.NLength in *.
        simpl in H8. rewrite Pos.of_nat_succ in H8.
        rewrite <- positive_nat_N in H8.
        rewrite Nat2Pos.id in H8.
        rewrite Nnat.Nat2N.inj_succ in H8. rewrite <- N.add_1_l in H8.
        rewrite map_length. eapply H8. eassumption.
        intros Hfalse; inv Hfalse.        
        admit.
      * eexists. split.       
        ++ econstructor. eassumption. eassumption.
           eassumption.
        ++ eassumption.
    + eapply sbst_all_values. reflexivity. 
  - (* Con_e *)
    destruct e2; try inv H2.
    + destruct (n <? 0).
      now inv H4. rewrite n_sub_0 in *.
      eexists. split.
      econstructor. reflexivity.
      eapply evals_are_value_env in e. subst.
      * rewrite H4. eapply rel_value_nth_inlist.
        eapply N2Nat_inj_lt.
        rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
        eapply not_default_then_nth.
        symmetry in H4. eapply H4.
        intros Hfalse; discriminate.
        reflexivity. 
      * assert (Hval : is_value_env (Con_e d es)).
        { rewrite H4.
          eapply nth_inlist_is_value.
          eapply not_default_then_nth.
          symmetry in H4. eapply H4.
          intros Hfalse; discriminate.
          eapply sbst_all_values. reflexivity. }
        inv Hval. eassumption. 
    + assert (Hwf' : well_formed_exps_in_env e0 rho).
      { eapply well_formed_in_env_Con in H0. eassumption. } 
      specialize (H rho e0 Hwf' H1 ltac:(reflexivity)).
      eapply Con_e_exists_list in H.
      destruct H as [vs2 [Hall1 Hall2]].
      exists (Con_v d0 vs2). split.
      * constructor. eapply Hall1.
      * constructor. reflexivity. eapply Hall2.
  - (* Let_e *)
    simpl in *.
    symmetry in H3.
    eapply parallel_sbst_inv_Let_e' in H3.
    + destruct H3 as [e1'' [e2'' [Heqlet [Hs1 Hs2]]]]. subst.
      assert (Hwf1: well_formed_in_env e1'' rho).
      { eapply well_formed_in_env_Let in H1.
        eassumption. }
      destruct (H rho _ Hwf1 H2 (eq_refl _)) as [v1' [He1 Hr1]].
      assert (Hwf2: well_formed_in_env e2'' (v1' :: rho)). 
      { inv H1. unfold well_formed_in_env.
        unfold list.NLength in *. simpl.
        rewrite Pos.of_nat_succ.
        rewrite <- positive_nat_N.
        rewrite Nat2Pos.id.
        rewrite Nnat.Nat2N.inj_succ.
        rewrite N.add_1_l in H8.
        eassumption.
        intros Hfalse; discriminate. } 
      edestruct (H0 (v1' :: rho) e2'') as [v2' [He2 Hr2]]. 
      * eassumption.
      * econstructor.
        eapply eval_env_preserves_well_formed.
        eapply He1. eassumption. eassumption.
        eassumption.
      * simpl. eapply rel_value_then_val_to_exp in Hr1.
        rewrite Hr1. symmetry. 
        edestruct parallel_sbst_with_sbst. eapply H3.
        unfold well_formed_in_env in Hwf2. unfold list.NLength in *.
        simpl in Hwf2. rewrite Pos.of_nat_succ in Hwf2.
        rewrite <- positive_nat_N in Hwf2.
        rewrite Nat2Pos.id in Hwf2.
        rewrite Nnat.Nat2N.inj_succ in Hwf2. rewrite <- N.add_1_l in Hwf2.
        rewrite map_length. eapply Hwf2. 
        intros Hfalse; inv Hfalse.
        constructor. admit. admit.
      * eexists. split.
        ++ econstructor. eapply He1. eapply He2.
        ++ eassumption.
    + eapply sbst_all_values. reflexivity. 
  - (* Match_e *)
    destruct e3; try inv H3.
    + destruct (n <? 0).
      now inv H5.
      rewrite n_sub_0 in *.
      eexists. split.
      econstructor. reflexivity.
      assert (Hnotval: ~(is_value_env (Match_e e p bs))).
      { intros Hfalse. inv Hfalse. }
      assert (Hval: is_value_env (Match_e e p bs)).
      { rewrite H5. eapply nth_inlist_Forall.
        eapply not_default_then_nth.
        symmetry in H5. now eapply H5.
        intros Hfalse. inv Hfalse.
        eapply sbst_all_values. reflexivity. }
      eapply Hnotval in Hval. destruct Hval.
    + inv H1. specialize (H rho e3 H6 H2 ltac:(reflexivity)).
      edestruct H as [v3 He3].
      destruct He3. inv H3.
      eexists. split.
      * econstructor. eapply H1.
        assert (Hlen: exps_length vs = N.of_nat (Datatypes.length vs_t)). 
        { eapply Forall2_length in H10. rewrite <- H10. 
          eapply exps_length_is_Datatypes_length. }
        rewrite <- Hlen. admit. admit.
      * admit. 
  - (* Fix_e *)
    destruct e2; try inv H1.
    + destruct (n <? 0).
      inv H3. rewrite n_sub_0 in *.
      eexists. split. econstructor. reflexivity.
      rewrite H3.
      eapply rel_value_nth_inlist.
      eapply N2Nat_inj_lt.
      rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
      eapply not_default_then_nth.
      symmetry in H3. eapply H3.
      unfold not. intros Hfalse. inv Hfalse.
      reflexivity.
    + eexists. split.
      now econstructor.
      econstructor. reflexivity.
      rewrite (N.add_0_l (efnlst_length e)).
      unfold sbst_env. 
      pose proof (parallel_sbst_inv_efnlst_length
                    e (map val_to_exp rho) (efnlst_length e)) as Hlen.
      rewrite !Hlen. 
      clear Hlen.
      inv H. revert H3.
      generalize dependent (efnlst_length e).
      induction e.
      -- intros n0. simpl. econstructor.
      -- intros n1.
         econstructor; fold parallel_sbst.
         split; reflexivity. 
         fold efnlst_as_list. fold parallel_sbst_efnlst.
         eapply IHe. inv H3. eassumption.
  - (* Fix_app *)
    symmetry in H4. 
    eapply parallel_sbst_inv_App_e' in H4.
    + destruct H4 as [e1'' [e2'' [Heqapp [Hs1 Hs2]]]]. subst.
      inv e4.      
      * assert (Hwf1 : well_formed_in_env e1'' rho).
        { eapply well_formed_in_env_App in H2.
          destruct H2 as [He1'' He2'']. eassumption. }     
        assert (Hwf2 : well_formed_in_env e2'' rho).
        { eapply well_formed_in_env_App in H2.
          destruct H2 as [He1'' He2'']. eassumption. }                
        destruct (H rho _ Hwf1 H3 (eq_refl _)) as [v1 [He1 Hr1]].
        inv Hr1.        
        specialize (H1 (make_rec_env fnlst_t rho0) (e' $ v2)).
        destruct (H0 rho _ Hwf2 H3 (eq_refl _)) as [v2' [He2 Hr2]].
        assert (HClosFix_wf: well_formed_val (ClosFix_v rho0 fnlst_t k2)).
        { eapply eval_env_preserves_well_formed.
        eapply He1. eassumption. eassumption. }
        edestruct H1 as [vf [Heval Hrel]].
        ** constructor.
           +++ (* well_formed_in env -> parallel_sbst 0 rho -> exp_wf 0 *)
             
             admit.
           +++ (* use val_to_exp is wf- we have that rel_value v2 v2' *)
             admit. 
        ** eapply make_rec_env_wf (*admitted*). now eapply HClosFix_wf. 
        ** (* first derive that (sbst_fix es e' $ v2) if exp_wf 0 and then 
              that parallel subst has no effect *)
          admit.          
        ** inv Heval.
           +++ (* the fun app *)
               eexists. split.
               { eapply eval_FixApp.
                 - eassumption.                   
                 - admit.
                   (* lemma : if enthop k fnl = Some e -> Forall2 P (as_list fnl) (as_list fnl') -> exists e, enthopt k fnl' = Some e' *)
                 - reflexivity.
                 - eassumption.
                 - eassumption.
                 - 

                  
using e3 (enthopt) 
               eassumption.
               econstructor. 
             admit.
           +++ (* because e' is lambda, subst_fix es e' is lambda, --> 
                  inv H8 --> contraiction *)
               admit. 
           +++ admit. 

          simpl. 
      assert (Heq : 
        admit.
      * admit. (* contradiction *)
      * admit. (* contradiction *)
      inv Hr1.
      assert (HClosFix_wf: well_formed_val (ClosFix_v rho0 fnlst_t k2)).
      { eapply eval_env_preserves_well_formed.
        eapply He1. eassumption. eassumption. }
      edestruct (H1 (v2'::rho0) e') as [v3 [He3 Hr3]].
      * inv HClosFix_wf. unfold well_formed_in_env.
        eapply nthopt_preserves_wf.
        
    admit.
  - (* Prf_app *)
    symmetry in H3. 
    eapply parallel_sbst_inv_App_e' in H3.
    + destruct H3 as [e1'' [e2'' [Heqlet [Hs1 Hs2]]]]. subst.
      assert (Hwf1 : well_formed_in_env e1'' rho).
      { inv H1. eapply H6. }      
      assert (Hwf2 : well_formed_in_env e2'' rho).
      { inv H1. eapply H7. } 
      destruct (H rho _ Hwf1 H2 (eq_refl _)) as [v1 [He1 Hr1]].
      destruct (H0 rho _ Hwf2 H2 (eq_refl _)) as [v2' [He2 Hr2]].
      inv Hr1.
      eexists. split.
      * eapply eval_ProofApp. eassumption. eapply He2.
      * constructor.
    + eapply sbst_all_values. reflexivity. 
  - (* Prf *)
    destruct e2; try inv H1.
    + destruct (n <? 0).
      inv H3.
      eexists. split. econstructor. reflexivity.
      rewrite H3. rewrite n_sub_0 in *. 
      eapply rel_value_nth_inlist.
      eapply N2Nat_inj_lt.
      rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
      eapply not_default_then_nth.
      symmetry in H3. eapply H3.
      unfold not. intros Hfalse. inv Hfalse.
      reflexivity.
    + repeat eexists; try econstructor. 
  - (* exps nil *)
    simpl. destruct es2.
    + simpl. econstructor.
    + inv H1. 
  - (* exps cons *)
    simpl. destruct es2.
    + inv H3.
    + simpl. econstructor.
      * eapply H.
        inv H1. eassumption.
        eassumption.
        inv H3. reflexivity.
      * eapply H0.
        inv H1. eapply H7.
        eassumption.
        inv H3. reflexivity.
Admitted. 
  
Lemma equiv_semantics_fwd_version1:
  (forall e, equiv_semantics_stmt_exp e) /\
  (forall es,  equiv_semantics_stmt_exps es) /\
  (forall efns, equiv_semantics_stmt_efnlst efns) /\
  (forall bs, equiv_semantics_stmt_branches bs).
Proof. 
  eapply my_exp_ind; unfold equiv_semantics_stmt_exp.
  - intros n rho e' IH.
    simpl in IH.
    edestruct (OrdersEx.N_as_OT.ltb_spec n 0).
    exfalso. eapply N.nlt_0_r. eassumption.
    rewrite N.sub_0_r in IH.
    eexists. split. constructor. reflexivity.
    assert (Hval : is_value_env (nth (N.to_nat n) (map val_to_exp rho) Prf_e)).
    eapply nth_inlist_is_value.
    eapply sbst_all_values.
    reflexivity.
    now constructor.
    destruct (value_self_eval).
    eapply H0 in Hval.
    assert (He : e' = (nth (N.to_nat n) (map val_to_exp rho) Prf_e)).
    eapply eval_single_valued.
    eassumption.
    eassumption.
    rewrite He.
    generalize dependent (N.to_nat n). 
    induction rho.
    + intros n0 H2 H3 H4. simpl. destruct n0.
      now constructor.
      now constructor.
    + intros n0 H2 H3 H4. simpl. destruct n0.
      eapply rel_value_val_to_exp.
      eapply IHrho; simpl in *; eassumption. 
  - intros n e IH rho e' Heval.
    edestruct (parallel_sbst_inv_Lam_e n 0 e (map val_to_exp rho)) as [e1 Heq].
    destruct Heq as [Heq1 Heq2]. simpl in *. 
    rewrite Heq1 in Heval. inversion Heval.
    eexists. split. constructor.
    constructor. unfold sbst_env.
    eassumption. 
  - intros e1 IH1 e2 IH2 rho e' H.
    admit. 
  - intros d e IH rho e' Heval.
    edestruct (parallel_sbst_inv_Con_e 0 d e (map val_to_exp rho)) as [e1 Heq].
    destruct Heq as [Heq1 Heq2]. subst. 
    rewrite Heq1 in Heval. inv Heval. 
    unfold equiv_semantics_stmt_exps in IH.
    pose proof (parallel_sbsts_map_exps_equiv e 0 (map val_to_exp rho)) as Hmap.
    rewrite <- Hmap in H2.
    apply IH in H2.
    eapply Con_e_exists_list in H2.
    destruct H2. destruct H. 
    exists (Con_v d x).
    split.
    + constructor. eapply H.
    + constructor. reflexivity. eapply H0.
  - admit.
  - admit.
  - intros e IHefns n rho e' Heval.
    edestruct (parallel_sbst_inv_Fix_e e n 0 (map val_to_exp rho)) as [e1 Heq].
    destruct Heq as [Heq1 Heq2]. rewrite Heq1 in Heval.
    unfold equiv_semantics_stmt_efnlst in IHefns. 
    specialize IHefns with rho n. rewrite Heq1 in IHefns.
    exists (ClosFix_v rho e n). split.
    + constructor.
    + inv Heval. eassumption.
  - exists Prf_v.
    split.
    constructor.
    inv H. constructor.
  - unfold equiv_semantics_stmt_exps.
    intros rho es' IHevals.
    simpl in *. inv IHevals. simpl.
    eapply List.Forall2_nil.
  - intros e IH es IHes.
    unfold equiv_semantics_stmt_exps in *.
    intros rho es' H. simpl.
    inv H. simpl. constructor.
    + eapply IH in H2. eassumption.
    + eapply IHes in H4. eassumption.
  - unfold equiv_semantics_stmt_efnlst.
    intros rho n. simpl. constructor.
    reflexivity.
    simpl. now constructor.
  - intros n e IHe efns IHefns.
    unfold equiv_semantics_stmt_efnlst in *.
    intros rho N.
    edestruct (parallel_sbst_inv_Fix_e (eflcons n e efns) N
                                       0 (map val_to_exp rho)) as [e1 Heq].
    destruct Heq as [Heq1 Heq2]. rewrite Heq1.
    constructor. reflexivity.
    unfold sbst_env. Opaque parallel_sbst. simpl in *.
    simpl in Heq2.
      in Heval.
    unfold equiv_semantics_stmt_efnlst in IHefns. 
    specialize IHefns with rho n. rewrite Heq1 in IHefns.
    exists (ClosFix_v rho e n). split.
    + constructor.
    + inv Heval. eassumption.

    intros rho i. (* generalize efnlst_length in equiv_semantics_stmt_efnlst? *)
    simpl.

    admit.
  - unfold equiv_semantics_stmt_branches.
    simpl. now constructor.
  - intros d p e IHe bs IHbs.
    unfold equiv_semantics_stmt_branches in *.
    constructor.
    + simpl. unfold equiv_semantics_stmt_exp. eassumption.
    + 
    Abort.

Lemma equiv_semantics_fwd:
  forall rho es e e',
    rel_subst_env es rho /\ eval (sbst_list e es) e' ->
    exists v, eval_env rho e v /\ rel_value e' v. 
Proof.
  intros rho es e e' [Hsubst Heval]. 
  assert (Heq: sbst_list e es = sbst_list e es) by reflexivity.
  revert Heq. generalize (sbst_list e es) at 1. intros e1 Heq.
  rewrite <- Heq in Heval. revert es e Hsubst Heq.
  
  induction Heval; intros subst e0 Hsubst Heq; subst.
  - 
    exists (Clos_v rho e0). split. 
    destruct e0; try (simpl in *; discriminate). 
    simpl in Heq.
  ; revert rho es.
  induction e.
  eexists.
  split.
  inversion H.
  inversion H1; try simpl; try discriminate.
Abort.


assert (Hb: forall l,
                 find_branch dc2 l
                             (parallel_sbst_branches b 0 (map val_to_exp rho))
                 = Some e' ->
                 exists e'', find_branch dc2 l b = Some e'').
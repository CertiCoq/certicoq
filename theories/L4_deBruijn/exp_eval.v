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

Fixpoint make_rec_env (fnlst : efnlst) (rho : env) : env :=
  let fix make_env_aux funcs rec_env :=
      match fnlst with
      | eflnil => rho
      | eflcons na e fnlst' =>
        let rec_env' := make_rec_env fnlst' rec_env in
        ((Clos_v rho na e)::rec_env)
      end
  in
  make_env_aux fnlst rho.

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

Fixpoint efnlst_to_list (fnlst: efnlst) :=
  match fnlst with
  | eflnil => nil
  | eflcons na e fnlst' =>
    let l := efnlst_to_list fnlst' in
    (e::l)
  end.

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
      pose proof (Nnat.N2Nat.inj_succ (N.of_nat n0)) as Hsucc.
      rewrite (Nnat.Nat2N.id n0) in Hsucc.
      rewrite <- Hn in Hsucc.
      
      eapply Nnat.N2Nat.inj in Hsucc.
      rewrite <- (Nnat.Nat2N.inj_succ n0) in Hsucc.
      (* assert (H2: n0 = (N.to_nat (N.pred n))). *)
      admit. 
Admitted. 
      
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
  forall rho e2, e1 = parallel_sbst e2 N0 (List.map val_to_exp rho) ->
  exists v, eval_env rho e2 v /\ rel_value e' v.

Definition equiv_semantics_stmt_exps' (es1 es' : exps) (P : evals es1 es') :=
  (forall rho es2,
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

Lemma parallel_sbst_with_sbst :
  forall e rho x n,
    parallel_sbst e n (x :: rho) = sbst x n (parallel_sbst e (n + 1) rho).
Proof.
  intros e rho x.
  induction e; intros i; eauto.
  - unfold parallel_sbst.
    destruct (lt_dec n i).
    * assert (Hleq : n < i + 1) by (zify; omega).
      eapply OrdersEx.N_as_OT.ltb_lt in l. rewrite l.
      eapply OrdersEx.N_as_OT.ltb_lt in Hleq. rewrite Hleq. simpl.
      eapply OrdersEx.N_as_OT.ltb_lt in l.
      eapply OrdersEx.N_as_OT.ltb_lt in Hleq.
      destruct (lt_dec n i); try (zify; omega).
      reflexivity.
    * eapply OrdersEx.N_as_OT.ge_le in g. 
      eapply N.ltb_ge in g. rewrite g. 
      destruct (N.eq_dec n i); subst.
      ** rewrite OrdersEx.N_as_OT.sub_diag.
         assert (Hlt : i <? i + 1 = true).
         { eapply N.ltb_lt. zify. omega. }
         rewrite Hlt. simpl.
         destruct (lt_dec i i); try (zify; omega).
         destruct (N.eq_dec i i); try (zify; omega).
         reflexivity.
      ** eapply N.ltb_ge in g. 
         assert (Hlt : ~ n < i + 1). zify. omega.
         eapply OrdersEx.N_as_DT.ltb_nlt in Hlt.
         rewrite Hlt. simpl nth.
         admit.
         (*
         ({
           
        ** assert (Hneq : n - n1 = 0). subst. zify. omega.
           rewrite Hneq. reflexivity.
        ** eapply N.ltb_ge in g.
           assert (Hlt : 0 < n - n1) by (zify; omega).
           destruct (N.to_nat (n - n1)) eqn:Hsub; try (zify; omega). 
           unfold list.NLength. simpl. destruct n3; reflexivity.
    + unfold parallel_sbst in *.  
      destruct (lt_dec n n1).
      * assert (Hleq : n < n1 + 1). zify; omega.
        eapply OrdersEx.N_as_OT.ltb_lt in l.
        eapply OrdersEx.N_as_OT.ltb_lt in Hleq. rewrite l, Hleq.
        simpl.
        eapply OrdersEx.N_as_OT.ltb_lt in l.
        eapply OrdersEx.N_as_OT.ltb_lt in Hleq.
        destruct (lt_dec n n1); try contradiction. reflexivity.
      * eapply OrdersEx.N_as_OT.ge_le in g. 
        eapply N.ltb_ge in g. rewrite g. *)
        
  - assert (Hfalse : i = 0) by admit. subst.
    
    simpl. simpl. rewrite N.add_0_r.
    rewrite N.add_0_l.
    f_equal.
    (* specialize IHe with (n0 + 1). *)
    (* rewrite IHe. (* simplifies to this because sbst uses (1 + n) *) *)
Abort.


Lemma equiv_semantics_fwd_version2 :
  (forall e e' P, equiv_semantics_stmt_exp' e e' P) /\
  (forall es es' P,  equiv_semantics_stmt_exps' es es' P).
Proof. 
  eapply my_eval_ind with (P := equiv_semantics_stmt_exp');
  unfold equiv_semantics_stmt_exp', equiv_semantics_stmt_exps'; intros; subst.
  - symmetry in H.
    destruct e2; try inv H.
    + destruct (n <? 0) eqn:Heq.
      inv H1. rewrite n_sub_0 in *.
      eexists. split. econstructor. reflexivity.
      eapply rel_value_nth_inlist.
      eapply N2Nat_inj_lt.
      rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
      eapply not_default_then_nth.
      eapply H1.
      unfold not. intros Hfalse. inv Hfalse.
      reflexivity. 
    + eexists. split.
      constructor.
      constructor. reflexivity. 
  - simpl in *.
    symmetry in H2.    
    eapply parallel_sbst_inv_App_e' in H2.
    destruct H2 as [e1'' [e2'' [Heqapp [Hs1 Hs2]]]]. subst.
    destruct (H rho _ (eq_refl _)) as [v1 [He1 Hr1]].
    destruct (H0 rho _ (eq_refl _)) as [v2' [He2 Hr2]].
    inv Hr1.
    edestruct (H1 (v2' :: rho0) e') as [v3 [He3 Hr3]].
    { simpl. unfold sbst_env.
      admit. 
    } 
    eexists. split.
    + econstructor. eassumption. eassumption.
      eassumption.
    + eassumption.
    + eapply sbst_all_values. reflexivity. 
  - destruct e2; try inv H0.
    + destruct (n <? 0).
      inv H2. rewrite n_sub_0 in *.
      eexists. split.
      econstructor. reflexivity.
      inv e.
      -- rewrite H2.
         eapply rel_value_nth_inlist.
         eapply N2Nat_inj_lt.
         rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
         eapply not_default_then_nth.
         symmetry in H2. eapply H2.
         unfold not. intros Hfalse. inv Hfalse.
         reflexivity.
      -- 
        admit.
    + induction e0.
      -- simpl in *.
         inv e.
         exists (Con_v d0 nil). split; constructor.
         simpl.
         now constructor.
         reflexivity.
         now constructor.
      -- simpl in *. inv e. 
         admit.
  - admit.
  - admit.
  - destruct e2; try inv H.
    + destruct (n <? 0).
      inv H1. rewrite n_sub_0 in *.
      eexists. split. econstructor. reflexivity.
      rewrite H1.
      eapply rel_value_nth_inlist.
      eapply N2Nat_inj_lt.
      rewrite (Nnat.Nat2N.id (Datatypes.length (map val_to_exp rho))).
      eapply not_default_then_nth.
      symmetry in H1. eapply H1.
      unfold not. intros Hfalse. inv Hfalse.
      reflexivity.
    + eexists. split.
      econstructor.
      econstructor. reflexivity.
      rewrite (N.add_0_l (efnlst_length e)).
      unfold sbst_env.
      pose proof (parallel_sbst_inv_efnlst_length
                    e (map val_to_exp rho) (efnlst_length e)) as Hlen.
      rewrite !Hlen.
      generalize dependent (efnlst_length e).
      induction e. 
      -- intros n0 H. simpl. econstructor.
      -- intros n1 H.
         econstructor; fold parallel_sbst.
         split; reflexivity. 
         fold efnlst_as_list. fold parallel_sbst_efnlst.
         assert (Hcons : efnlst_length e0 = (n1 - 1)) by admit. 
         eapply IHe.
         admit. 
  - admit.
  - destruct e2; try inv H1.
    + destruct (n <? 0).
      inv H3. rewrite n_sub_0 in *.
      eexists. split. econstructor. reflexivity.
      (* (f $ a) is not a value *)
      
Abort.      
  
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
Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
        Coq.omega.Omega Coq.Sets.Ensembles Coq.Relations.Relation_Operators.

Require Import Libraries.CpdtTactics.
Require Import L6.cps L6.ctx L6.eval L6.Ensembles_util L6.List_util.

Import ListNotations.

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.

Definition var_dec := M.elt_eq.

(** Lemmas about [findtag] *)
Lemma findtag_not_empty:
  forall A cl (k : A) (v : cTag), findtag cl v = Some k -> 0 < (length cl).
Proof.
  induction cl; intros.
  - inversion H.
  - simpl in H. destruct a. destruct (M.elt_eq c v).
    + inversion H. simpl. omega.
    + simpl. apply IHcl in H. omega.
Qed.

Lemma findtag_In_patterns {A} P c (v : A) :
  findtag P c = Some v ->
  List.In (c, v) P.
Proof.
  induction P as [ | [c' e'] P IHP]; intros H; try discriminate.
  simpl in H. edestruct (M.elt_eq c' c).
  - inv H. now left.
  - right. eauto.
Qed.
   
Lemma findtag_append_spec {A} c P P' (v : A) :
  findtag (P ++ P') c = Some v ->
  (findtag P c = Some v) \/
  (findtag P' c = Some v /\ forall v, ~ List.In (c, v) P).
Proof.
  induction P as [| [c' v'] P IHP]; intros H.
  - simpl in H. right; split; eauto.
  - simpl in *.
    destruct (M.elt_eq c' c); eauto.
    destruct (IHP H) as [H1 | [H1 H2]]; eauto.
    right; split; eauto. intros v''.
    intros Hc. inv Hc. inv H0; congruence.
    eapply H2; eauto.
Qed.

Lemma findtag_append_is_Some {A} c P P' (v : A) :
  findtag P c = Some v ->
  findtag (P ++ P') c = Some v.
Proof.
  induction P as [| [c' v'] P IHP]; simpl; intros H; eauto.
  - inv H.
  - destruct (M.elt_eq c' c); eauto.
Qed.

Lemma findtag_append_not_In {A} c (P P' : list (cTag * A)) :
  (forall v, ~ List.In (c, v) P) ->
  findtag (P ++ P') c = findtag P' c.
Proof.
  induction P as [| [c' v'] P IHP]; simpl; intros H; eauto.
  destruct (M.elt_eq c' c); eauto.
  - exfalso. subst. eapply H. left; eauto.
  - eapply IHP. intros x Hc. eapply H. eauto.
Qed.

Lemma findtag_In {A} (P : list (cTag * A)) c e :
  findtag P c = Some e -> List.In (c, e) P.
Proof.
  revert e. induction P as [| [c' e'] P IHp]; intros x H; try now inv H.
  simpl in H. inv H.
  destruct (M.elt_eq c' c); inv H1; try now constructor.
  constructor 2. apply IHp; eauto.
Qed.

(** [split_fds B1 B2 B] iff B is an interleaving of the definitions in B1 and B2 *)
Inductive split_fds: fundefs -> fundefs -> fundefs -> Prop :=
| Left_f:
    forall lfds rfds lrfds v t ys e,
      split_fds lfds rfds lrfds ->
      split_fds (Fcons v t ys e lfds) rfds (Fcons v t ys e lrfds)
| Right_f:
    forall lfds rfds lrfds v t ys e,
      split_fds lfds rfds lrfds ->
      split_fds lfds (Fcons v t ys e rfds) (Fcons v t ys e lrfds)
| End_f: split_fds Fnil Fnil Fnil.

(** Lemmas about [split_fds]. *)
Lemma split_fds_nil_l fdefs : split_fds fdefs Fnil fdefs.
  induction fdefs; constructor; eauto.
Qed.

Lemma split_fds_nil_r fdefs : split_fds Fnil fdefs fdefs.
  induction fdefs; constructor; eauto.
Qed.

Lemma split_fds_trans B1 B2 B3 B1' B2' :
  split_fds B1 B1' B2 ->
  split_fds B2 B2' B3 ->
  exists B2,
    split_fds B1' B2' B2 /\ split_fds B1 B2 B3.
Proof.
  intros Hs1 Hs2. revert B1 B1' Hs1. induction Hs2; intros B1 B1' Hs1.
  - inv Hs1. 
    edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; eauto. constructor; eauto.
    edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; constructor; eauto.
  - edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; constructor; eauto.
  - eexists; split; eauto using split_fds_nil_l.
Qed.  

Lemma split_fds_sym B1 B2 B3 :
  split_fds B1 B2 B3 ->
  split_fds B2 B1 B3.
Proof.
  intros Hs1. induction Hs1; now constructor; eauto.
Qed.

Lemma split_fds_Fnil B1 B2 :
  split_fds B1 B2 Fnil ->
  B1 = Fnil /\ B2 = Fnil.
Proof.
  intros H. inv H; eauto.
Qed.

Lemma split_fds_Fcons_l B1 B2 B3 :
  split_fds B1 B2 B3 ->
  B1 <> Fnil -> B3 <> Fnil.
Proof.
  intros H1 H2. inv H1; eauto; congruence.
Qed.

Lemma split_fds_Fcons_r B1 B2 B3 :
  split_fds B1 B2 B3 ->
  B2 <> Fnil -> B3 <> Fnil.
Proof.
  intros H1 H2. inv H1; eauto; congruence.
Qed.


Lemma split_fds_Fnil_eq_l B1 B2 :
  split_fds Fnil B1 B2 -> B1 = B2.
Proof.
  revert B1. induction B2; intros B1 H; auto; inv H; f_equal; eauto.
Qed.

Lemma split_fds_Fnil_eq_r B1 B2 :
  split_fds B1 Fnil B2 -> B1 = B2.
Proof.
  revert B1. induction B2; intros B1 H; auto; inv H; f_equal; eauto.
Qed.

(** Append function definitions *)
Fixpoint fundefs_append (B1 B2 : fundefs) : fundefs :=
  match B1 with
    | Fcons f t xs xe B => Fcons f t xs xe (fundefs_append B B2)
    | Fnil => B2
  end.

(** Lemmas about [fundefs_append] *)
Lemma def_funs_append B B1 B2 rho rho' :
  def_funs B (fundefs_append B1 B2) rho rho' =
  def_funs B B1 rho (def_funs B B2 rho rho').
Proof.
  induction B1; simpl; eauto. now rewrite IHB1.
Qed.

Lemma find_def_fundefs_append_r f B1 B2 v:
  find_def f B2 = Some v ->
  find_def f B1 = None ->
  find_def f (fundefs_append B1 B2) = find_def f B2.
Proof.
  induction B1; simpl; intros H1 H2; eauto.
  destruct (M.elt_eq f v0); try discriminate; eauto.
Qed.

Lemma find_def_fundefs_append_l f B1 B2 v:
  find_def f B1 = Some v ->
  find_def f (fundefs_append B1 B2) = find_def f B1.
Proof.
  induction B1; simpl; intros H2; eauto; try discriminate.
  destruct (M.elt_eq f v0); try discriminate; eauto.
Qed.

Lemma fundefs_append_split_fds B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  split_fds B1 B2 B3.
Proof.
  revert B1. induction B3; intros B1 Hdefs.
  - destruct B1; simpl in Hdefs; subst. inv Hdefs.
    constructor. eauto.
    eapply split_fds_nil_r.
  - destruct B1; simpl in Hdefs; try congruence. subst.
    constructor.
Qed.

Lemma find_def_fundefs_append_Fcons_neq f v t ys e B1 B2 :
  f <> v ->
  find_def f (fundefs_append B1 (Fcons v t ys e B2)) =
  find_def f (fundefs_append B1 B2).
Proof.
  intros Hneq. revert B2. induction B1; intros B2.
  - simpl. destruct (M.elt_eq f v0); eauto.
  - simpl. destruct (M.elt_eq f v); try contradiction; eauto.
Qed.

Lemma split_fds_cons_l_append_fundefs f tau xs e B1 B2 B3 : 
  split_fds (Fcons f tau xs e B1) B2 B3 ->
  exists B1' B2',
    B3 = fundefs_append B1' (Fcons f tau xs e B2') /\
    split_fds B1 B2 (fundefs_append B1' B2').
Proof.
  revert B1 B2. induction B3; intros B1 B2 Hspl.
  - inv Hspl.
    + exists Fnil, B3; eauto.
    + edestruct IHB3 as [B1' [B2' [Heq Hspl]]]; eauto.
      exists (Fcons v f0 l e0 B1'), B2'. rewrite Heq; split; eauto.
      simpl; constructor; eauto.
  - inv Hspl.
Qed.

Lemma split_fds_cons_r_append_fundefs f tau xs e B1 B2 B3 : 
  split_fds B1 (Fcons f tau xs e B2) B3 ->
  exists B1' B2',
    B3 = fundefs_append B1' (Fcons f tau xs e B2') /\
    split_fds B1 B2 (fundefs_append B1' B2').
Proof.
  revert B1 B2. induction B3; intros B1 B2 Hspl.
  - inv Hspl.
    + edestruct IHB3 as [B1' [B2' [Heq Hspl]]]; eauto.
      exists (Fcons v f0 l e0 B1'), B2'. rewrite Heq; eauto. split; eauto.
      simpl. constructor; eauto.
    + exists Fnil, B3; eauto.
  - inv Hspl.
Qed.


(** Lemmas about [getlist] *)
Lemma getlist_In (rho : env) ys x vs :
  getlist ys rho = Some vs ->
  List.In x ys ->
  exists v, M.get x rho = Some v.
Proof.
  revert x vs. induction ys; intros x vs Hget H. inv H.
  inv H; simpl in Hget.
  - destruct (M.get x rho) eqn:Heq; try discriminate; eauto.
  - destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
    destruct (getlist ys rho) eqn:Heq'; try discriminate; eauto.
Qed.

Lemma In_getlist (xs : list var) (rho : env) :
  (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
  exists vs, getlist xs rho = Some vs. 
Proof.                                            
  intros H. induction xs. 
  - eexists; simpl; eauto.
  - edestruct IHxs. 
    + intros x Hin. eapply H. now constructor 2. 
    + edestruct H. now constructor. 
      eexists. simpl. erewrite H1, H0. 
      reflexivity. 
Qed.

Lemma getlist_nth_get (xs : list var) (vs : list val) rho (x : var) N :
  getlist xs rho = Some vs ->
  nthN xs N = Some x ->
  exists v, nthN vs N = Some v /\ M.get x rho = Some v. 
Proof.
  revert vs N; induction xs; intros vs N Hget Hnth.
  - inv Hnth. 
  - simpl in Hget.
    destruct (M.get a rho) eqn:Hget'; try discriminate.
    destruct (getlist xs rho) eqn:Hgetlist'; try discriminate.
    inv Hget. destruct N. 
    + inv Hnth. eexists; simpl; eauto.
    + edestruct IHxs as [v' [Hnth1 Hget1]]; eauto. 
Qed.

Lemma getlist_set_neq {A} xs x (v : A) rho :
  ~ List.In x xs ->
  getlist xs (M.set x v rho) = getlist xs rho. 
Proof.
  intros Hin.
  revert rho. induction xs; intros rho.
  - reflexivity.
  - simpl. rewrite M.gso.
    + rewrite IHxs. reflexivity.
      intros Hin'. eapply Hin. now constructor 2.
    + intros Heq; subst. eapply Hin. now constructor.
Qed.

(** Lemmas about [setlist]  *)
Lemma setlist_Forall2_get (P : val -> val -> Prop)
      xs vs1 vs2 rho1 rho2 rho1' rho2' x : 
  Forall2 P vs1 vs2 ->
  setlist xs vs1 rho1 = Some rho1' ->
  setlist xs vs2 rho2 = Some rho2' ->
  List.In x xs ->
  exists v1 v2,
    M.get x rho1' = Some v1 /\
    M.get x rho2' = Some v2 /\ P v1 v2.
Proof.
  revert rho1' rho2' vs1 vs2.
  induction xs; simpl; intros rho1' rho2' vs1 vs2 Hall Hset1 Hset2 Hin.
  - inv Hin.
  - destruct (Coqlib.peq a x); subst.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (setlist xs vs1 rho1) eqn:Heq1;
        destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall.
      repeat eexists; try rewrite M.gss; eauto.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (setlist xs vs1 rho1) eqn:Heq1;
        destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall. inv Hin; try congruence.
      edestruct IHxs as [v1 [v2 [Hget1 [Hget2 HP]]]]; eauto.
      repeat eexists; eauto; rewrite M.gso; eauto.
Qed.

Lemma get_setlist_In_xs x xs vs rho rho' :
  In var (FromList xs) x ->
  setlist xs vs rho = Some rho' ->
  exists v : val, M.get x rho' = Some v.
Proof.
  revert rho rho' vs. induction xs; intros rho rho' vs Hin Hset.
  - rewrite FromList_nil in Hin. exfalso.
    eapply not_In_Empty_set. eassumption. 
  - rewrite FromList_cons in Hin.
    destruct vs; try discriminate.    
    simpl in Hset. destruct (setlist xs vs rho) eqn:Hsetlist; try discriminate.
    inv Hset. inv Hin.
    + inv H. eexists. rewrite M.gss. reflexivity.
    + destruct (Coqlib.peq x a); subst.
      * eexists. now rewrite M.gss.
      * edestruct IHxs; eauto.
        eexists. simpl. rewrite M.gso; eauto. 
Qed.

Lemma setlist_not_In (xs : list var) (vs : list val) (rho rho' : env) (x : var) : 
  setlist xs vs rho = Some rho' ->
  ~ List.In x xs ->
  M.get x rho = M.get x rho'.
Proof.
  revert vs rho'.
  induction xs; simpl; intros vs rho' Hset Hin.
  - destruct vs; congruence.
  - destruct vs; try discriminate.
    destruct (setlist xs vs rho) eqn:Heq1; try discriminate. inv Hset.
    rewrite M.gso; eauto.
Qed.

Lemma setlist_length (rho rho' rho1 : env)
      (xs : list var) (vs1 vs2 : list val) :
  length vs1 = length vs2 -> 
  setlist xs vs1 rho = Some rho1 ->
  exists rho2, setlist xs vs2 rho' = Some rho2.
Proof.
  revert vs1 vs2 rho1.
  induction xs as [| x xs IHxs ]; intros vs1 vs2 rho1 Hlen Hset.
  - inv Hset. destruct vs1; try discriminate. inv H0.
    destruct vs2; try discriminate. eexists; simpl; eauto. 
  - destruct vs1; try discriminate. destruct vs2; try discriminate.
    inv Hlen. simpl in Hset. 
    destruct (setlist xs vs1 rho) eqn:Heq2; try discriminate.
    edestruct (IHxs _ _ _ H0 Heq2) as  [vs2' Hset2].
    eexists. simpl; rewrite Hset2; eauto.
Qed.

(** Lemmas about case consistent *)

Lemma caseConsistent_same_cTags cenv P1 P2 t :
  Forall2 (fun pat pat' => fst pat = fst pat') P1 P2 ->
  caseConsistent cenv P1 t ->
  caseConsistent cenv P2 t.
Proof.
  intros H Hc; induction H.
  - now constructor. 
  - inv Hc. destruct y as [t'' e'']. simpl in *. subst.
    econstructor; now eauto.
Qed.

(** ** Existance (or not) of a binding in a map -- TODO : maybe move the a map_util.v? *)

(** The variables in S are defined in the map. *)
Definition binding_in_map {A} (S : Ensemble M.elt) (map : M.t A) : Prop :=
  forall x, In _ S x -> exists v, M.get x map = Some v. 

(** The variables in S are not defined in the map. *)
Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) := 
  forall x : M.elt, In M.elt S x -> M.get x map = None.


(** * Lemmas about [binding_in_map] *)

(** [binding_in_map] is anti-monotonic on its first argument *)
Lemma binding_in_map_antimon {A} S S' (rho : M.t A) :
  Included _ S' S ->
  binding_in_map S rho ->
  binding_in_map S' rho.
Proof.
  intros Hin Hv x Hs. eauto.
Qed.

(** Extend the environment with a variable and put it in the set *)
Lemma binding_in_map_set {A} x (v : A) S rho :
  binding_in_map S rho ->
  binding_in_map (Union _ S (Singleton _ x)) (M.set x v rho).
Proof. 
  intros H x' Hs. inv Hs.
  - edestruct H; eauto.
    destruct (Coqlib.peq x' x) eqn:Heq'.
    + eexists. simpl. now rewrite M.gsspec, Heq'.
    + eexists. simpl. rewrite M.gsspec, Heq'.
      eassumption.
  - inv H0. eexists. rewrite M.gss. eauto.
Qed.

(** Extend the environment with a list of variables and put them in the set *)
Lemma binding_in_map_setlist xs vs S (rho rho' : env) :
  binding_in_map S rho ->
  setlist xs vs rho = Some rho' ->
  binding_in_map (Union _ (FromList xs) S) rho'.
Proof.
  intros H Hset x' Hs.
  destruct (Decidable_FromList xs). destruct (Dec x').
  - eapply get_setlist_In_xs; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite <- setlist_not_In; eauto.
Qed.

Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
  Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
Proof. 
  intros Hin Hb x Hin'. eauto.
Qed.

Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
  binding_not_in_map S map ->
  ~ In _ S x ->
  binding_not_in_map S (M.set x v map). 
Proof. 
  intros HB Hnin x' Hin.
  rewrite M.gsspec. destruct (Coqlib.peq x' x); subst; try contradiction. 
  eauto. 
Qed.

Lemma binding_in_map_Included {A} S (rho : M.t A) :
  binding_in_map S rho ->
  Included _ S (FromList (List.map fst (M.elements rho))).
Proof.
  intros Hin x Hx. unfold FromList, In.
  eapply in_map_iff. edestruct Hin as [v Hget]; eauto.
  eexists (x, v). split; eauto.
  eapply M.elements_correct. eassumption.
Qed.    


(* XXX: These definitions need to be updated to work with the new syntax of L6.
        Whoever needs them has to update them. Otherwise, they will
        self-destruct in an arbitrary amount of time.

Inductive dsubterm_e:exp -> exp -> Prop :=
| dsubterm_constr: forall x t c ys e, dsubterm_e e (Econstr x t c ys e)
| dsubterm_proj: forall v t n y e, dsubterm_e e (Eproj v t n y e)
| dsubterm_prim: forall x t f ys e, dsubterm_e e (Eprim x t f ys e)
| dsubterm_fds:
    forall e' fds e,
      dsubterm_fds_e e' fds -> dsubterm_e e' (Efun fds e)
with dsubterm_fds_e: exp -> fundefs -> Prop :=
     | dsubterm_cons:
         forall e f t ys fds', dsubterm_fds_e e (Fcons f t ys e fds')
     | dsubterm_cons_fds:
         forall e' fds' f t ys e , dsubterm_fds_e e' fds' -> dsubterm_fds_e e' (Fcons f t ys e fds').

Definition subterm_e := clos_trans _ dsubterm_e.
Definition subterm_or_eq := clos_refl_trans _ dsubterm_e.

Inductive subterm_fds_e: exp -> fundefs -> Prop :=
| subterm_cons:
    forall e e' f t ys fds', subterm_e e' e -> subterm_fds_e e' (Fcons f t ys e fds')
| subterm_cons_fds:
         forall e' fds' f t ys e , subterm_fds_e e' fds' -> subterm_fds_e e' (Fcons f t ys e fds').


Inductive subfds_fds: fundefs -> fundefs -> Prop :=
| subfds_cons':
    forall fds' fds f t ys e,
      subfds_fds fds' fds ->
      subfds_fds fds' (Fcons f t ys e fds)
| subfds_cons:
    forall fds f t ys e, subfds_fds fds (Fcons f t ys e fds).

Definition subfds_or_eq: fundefs -> fundefs -> Prop :=
  fun fds' fds => subfds_fds fds' fds \/ fds' = fds.

Definition subfds_e: fundefs -> exp -> Prop := 
  fun fds  e =>
    exists fds' e', subterm_or_eq (Efun fds' e') e /\  subfds_or_eq fds fds'.

Definition subfds_or_eq_left:
  forall fds' fds fds'',
    subfds_fds fds fds' -> subfds_or_eq fds' fds'' -> subfds_or_eq fds fds''.
Proof.
  induction fds'; intros.
  - inversion H; subst. eapply IHfds'. apply H3. admit. admit.
Admitted.  

Theorem subfds_e_subfds:
  forall fds e fds', subfds_fds fds' fds -> subfds_e fds e -> subfds_e fds' e.
Proof.
  destruct fds; intros.
  - destruct H0; destructAll. exists x. exists x0. split.
    assumption.  eapply subfds_or_eq_left. apply H. assumption.
  - inversion H. 
Qed.


Definition num_occur_list (lv:list var) (v:var) : nat :=
  fold_right (fun v' n => if (var_dec v v') then 1 + n
                          else n) 0 lv.

(* number of time var occurs in exp (free or not)*)
Inductive num_occur: exp -> var -> nat -> Prop :=
| Num_occ_constr:
  forall x t c ys e v n,
    num_occur e v n ->
    num_occur (Econstr x t c ys e) v (n + (num_occur_list ys v))
| Num_occ_prim:
    forall x t f ys e v n,
      num_occur e v n ->
      num_occur (Eprim x t f ys e) v (n + (num_occur_list ys v))
| Num_occ_case:
    forall v' cl v n,
      num_occur_case cl v n -> 
      num_occur (Ecase v' cl) v (num_occur_list [v'] v + n)
| Num_occ_proj:
    forall e v n  y v' t n',
      num_occur  e v n ->
      num_occur (Eproj v' t n' y e) v (num_occur_list [y] v + n)
| Num_occ_app:
    forall f ys v,
                 num_occur (Eapp f ys) v (num_occur_list (f::ys) v)
| Num_occ_fun:
    forall e v n m fl,
      num_occur e v n ->
      num_occur_fds fl v m ->
      num_occur (Efun fl e) v (n + m )
with num_occur_fds: fundefs -> var -> nat -> Prop :=
     | Num_occ_nil :
         forall v,
           num_occur_fds Fnil v 0
     | Num_occ_cons :
         forall v t n v' ys e fds' m,
           num_occur e v n ->
           num_occur_fds fds' v m ->
           num_occur_fds (Fcons v' t ys e fds') v (n + m)
with num_occur_case: list (var * exp) -> var -> nat -> Prop :=
     | Num_occ_cnil:
         forall v,
           num_occur_case [] v 0
     | Num_occur_ccons:
         forall v k cl e n m,
           num_occur e v n ->
           num_occur_case cl v m ->
           num_occur_case ((k,e)::cl) v (n+m).



 (* number of times var occurs in a context *) 
Inductive num_occur_ec: exp_ctx -> var -> nat -> Prop :=
| Noec_hole: forall v, num_occur_ec Hole_c v 0
| Noec_constr: forall c v n x t ys g,
                 num_occur_ec c v n ->
                 num_occur_ec (Econstr_c x t g ys c) v (num_occur_list ys v + n)
| Noec_prim: forall c v n x t f ys,
               num_occur_ec c v n ->
               num_occur_ec (Eprim_c x t f ys c) v (num_occur_list ys v + n )
| Noec_proj: forall  v n y v' t n' c,
               num_occur_ec c v n ->
               num_occur_ec (Eproj_c v' t n' y c) v (num_occur_list [y] v + n)
| Noec_case: forall cl cl' c v n m tg y p,
            num_occur_case cl v n ->
            num_occur_ec c v m ->
            num_occur_case cl' v p ->
            num_occur_ec (Ecase_c y cl tg c cl') v (num_occur_list [y] v + n+m+p)
| Noec_fun1: forall n m fds c v,
               num_occur_ec c v n ->
               num_occur_fds fds v m ->
               num_occur_ec (Efun1_c fds c) v (n+m)
| Noec_fun2: forall n m fdc e v ,
               num_occur e v n ->
               num_occur_fdc fdc v m ->
               num_occur_ec (Efun2_c fdc e) v (n + m)
with num_occur_fdc : fundefs_ctx -> var -> nat -> Prop :=
     | Nofc_fcons1 : forall v n m fds t ys c f,
                       num_occur_ec c v n ->
                       num_occur_fds fds v m ->
                       num_occur_fdc (Fcons1_c f t ys c fds) v  (n + m)
     | Nofc_fcons2 : forall e v n m fdc f t ys,
                       num_occur e v n ->
                       num_occur_fdc fdc v m ->
                       num_occur_fdc (Fcons2_c f t ys e fdc) v (n + m).


Inductive num_binding_e: exp -> var -> nat -> Prop :=
| Ub_constr: forall v t0 t ys e v' m,
               num_binding_e e v m -> 
               num_binding_e (Econstr v' t0 t ys e) v (num_occur_list [v'] v + m)
| Ub_proj: forall v' t n' y e v n, 
    num_binding_e e v n ->
    num_binding_e (Eproj v' t n' y e) v (num_occur_list [v'] v + n)
| Ub_prim: forall e v n x t f ys,
    num_binding_e e v n ->
    num_binding_e (Eprim x t f ys e) v (num_occur_list [x] v + n)
| Ub_app: forall f ys v,
    num_binding_e (Eapp f ys) v 0
| Ub_case: forall l v n y,
    num_binding_l l v n ->
    num_binding_e (Ecase y l ) v n
| Ub_fun: forall fds v n m e,
    num_binding_f fds v n ->
    num_binding_e e v m ->
    num_binding_e (Efun fds e) v (n+m)

with num_binding_l: list (tag*exp) -> var -> nat -> Prop :=
      | Ub_cons: forall e l v n m k,
          num_binding_e e v n ->
          num_binding_l l v m ->
             num_binding_l ((k,e)::l) v (n+m)
        | Ub_nil: forall v,
            num_binding_l [] v 0 
with num_binding_f: fundefs -> var -> nat -> Prop :=
     | Ub_fcons: forall e v n fds v' t ys m,
         num_binding_e e v n ->
         num_binding_f fds v m ->                        
         num_binding_f (Fcons v' t ys e fds) v (num_occur_list (v'::ys) v+n+m)
     | Ub_fnil: forall v,
         num_binding_f Fnil v 0.


Scheme nbe_ind := Induction for num_binding_e Sort Prop
                  with nbl_ind := Induction for num_binding_l Sort Prop
                  with nbf_ind:= Induction for num_binding_f Sort Prop.




Theorem e_num_binding: forall v e,
                       exists n, num_binding_e e v n
                                 with e_num_binding_f: forall v fds,
                                                       exists n, num_binding_f fds v n.                                                                 
Proof.  
  - induction e; destructAll.
     + exists (num_occur_list [v0] v  + x); constructor; auto.
             + assert (exists n, num_binding_l l v n).
               { induction l.
                 exists 0; constructor.
                 destruct a.
                 specialize (e_num_binding v e).
                 destructAll. eexists; constructor; eauto.
               }
               destruct H. exists x; constructor; auto.
             + exists (num_occur_list [v0] v + x); constructor; auto.
    + specialize (e_num_binding_f v f).
      destructAll.
      eexists; constructor; eauto.
    + exists 0; constructor.
    + exists (num_occur_list [v0] v + x); constructor; auto.
  - induction fds.
    + specialize (e_num_binding v e). destructAll.
      eexists; constructor; eauto.
    + exists 0; constructor.
Qed.


    
Definition unique_bindings' e: Prop :=
  forall v,
    exists n,
    num_binding_e e v n /\ n <= 1.

Definition unique_binding_f' fds:Prop :=
  forall v, exists n,
    num_binding_f fds v n /\ n <= 1.



Inductive bv_e: exp -> list var -> Prop :=
| Constr_bv :
    forall e l x t c ys, bv_e e l -> bv_e (Econstr x t c ys e) (x::l)
| Case_bv :
    forall v cl, bv_e (Ecase v cl) []
| Proj_bv:
    forall v t n y e l, bv_e e l -> bv_e (Eproj v t n y e) (v::l)
| Fun_bv:
    forall fl e l1 l2, bv_f fl l1 -> bv_e e l2 -> bv_e (Efun fl e) (l1 ++ l2)
| App_bv :
    forall f ys, bv_e (Eapp f ys) []
| Prim_bv :
    forall x t f ys e l, bv_e e l -> bv_e (Eprim x t f ys e) (x::l)
with bv_f : fundefs -> list var -> Prop :=
     | Cons_bv :
         forall f t ys e fds l1 l2,
           bv_e e l1 ->
           bv_f fds l2 ->
           bv_f (Fcons f t ys e fds) (f::(ys++(l1++l2)))
     | Nil_bv : bv_f Fnil [].

Hint Constructors bv_e bv_f.

Theorem e_bv_e :
  forall e, exists l, bv_e e l
                      with e_bv_f: forall f, exists l, bv_f f l.
Proof.
  induction e; destructAll; clear e_bv_e; eauto.
  specialize (e_bv_f f). destruct e_bv_f. eauto. 
  induction f; destructAll; clear e_bv_f; eauto.
  specialize (e_bv_e e); destruct e_bv_e. eauto.
Qed.

Theorem bv_e_det: forall e l1 l2, bv_e e l1 -> bv_e e l2 -> l1 = l2
                             with bv_f_det: forall f l1 l2, bv_f f l1 -> bv_f f l2 -> l1 = l2.                     
Proof.
  - induction e; clear bv_e_det; intros; auto; inversion H; inversion H0; subst; auto.  
    + specialize (IHe _ _ H7 H14); subst; reflexivity.
    + specialize (IHe _ _ H7 H14); subst; reflexivity.
    + specialize (bv_f_det f _ _ H3 H8); specialize (IHe _ _ H5 H10); subst; reflexivity.
    + specialize (IHe _ _ H7 H14); subst; reflexivity.
  - induction f; clear bv_f_det; intros; auto; inversion H; inversion H0; subst.
    + specialize (bv_e_det e _ _ H7 H15); specialize (IHf _ _ H8 H16); subst; reflexivity.
    + reflexivity.
Qed. *)


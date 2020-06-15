(* M.t utilities. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From CertiCoq.L6 Require Import Ensembles_util set_util functions List_util.
From compcert.lib Require Import Coqlib Maps.
Require Import Libraries.maps_util.

Module M := Maps.PTree. 

Open Scope Ensembles_scope.

Definition key_set {A : Type} (map : M.t A) :=
  [ set x : positive | match M.get x map with
                           | Some x => True
                           | None => False
                         end ]. 
  
Definition sub_map {A : Type} (map1 map2 : M.t A) :=
  forall x v, M.get x map1 = Some v ->
         M.get x map2 = Some v.

Fixpoint xfilter {A : Type} (pred : positive -> A -> bool) (m : M.t A) 
         (i : positive) {struct m} : M.t A :=
  match m with
  | M.Leaf => M.Leaf
  | M.Node l o r =>
    let o' :=
        match o with
        | Some x => if pred (M.prev i) x then o else None
        | None => None
        end
    in
    M.Node' (xfilter pred l (i~0)%positive) o' (xfilter pred r (i~1)%positive)
  end.

Lemma xgfilter (A: Type) (pred : positive -> A -> bool) (m : M.t A) 
      (i j : positive) : 
  M.get i (xfilter pred m j) =
  match M.get i m with
  | Some x => if pred (M.prev (M.prev_append i j)) x then Some x else None
  | None => None
  end.
Proof.
  revert i j. induction m; intros i j; simpl.
  - rewrite !M.gleaf. reflexivity.
  - rewrite M.gnode'.
    destruct i; simpl.
    + rewrite IHm2. reflexivity.
    + rewrite IHm1. reflexivity.
    + destruct o; reflexivity.
Qed.

Definition filter  {A : Type} (pred : positive -> A -> bool) (m : M.t A) : M.t A :=
  xfilter pred m 1.

Lemma gfilter (A: Type) (pred : positive -> A -> bool) (m : M.t A) 
      (i : positive) : 
  M.get i (filter pred m) =
  match M.get i m with
  | Some x => if pred i x then Some x else None
  | None => None
  end.
Proof.
  unfold filter. rewrite xgfilter. simpl. 
  rewrite <- M.prev_append_prev. simpl. 
  rewrite Maps.PTree.prev_involutive. reflexivity. 
Qed.


Instance ToMSet_key_set {A} (rho : M.t A) : ToMSet (key_set rho).
Proof. 
  eexists (@mset (FromList (map fst (M.elements rho))) _).
  rewrite <- mset_eq, FromList_map_image_FromList.
  split; intros x Hin.
  - unfold Ensembles.In, key_set in *.
    destruct (M.get x rho) eqn:Hget. 
    eexists (x, a). split; eauto.
    eapply M.elements_correct. eassumption. 
    exfalso; eauto.
  - destruct Hin as [[z a] [Hin Hget]]; subst.
    unfold Ensembles.In, FromList in Hin. eapply M.elements_complete in Hin.
    simpl. unfold key_set, Ensembles.In. now rewrite Hin.
Qed. 

Definition eq_env_P {A}:  Ensemble M.elt -> M.t A -> M.t A -> Prop :=
  fun S rho1 rho2 =>
    forall x, S x -> M.get x rho1 = M.get x rho2.

Lemma eq_env_P_refl: forall {A} S (r:M.t A), eq_env_P S r r.
Proof.
  intros; intro; intros. reflexivity.
Qed.

Lemma eq_env_P_sym: forall {A} S (r:M.t A) r', eq_env_P S r r' -> eq_env_P S r' r.
Proof.
  intros; intro. intro. apply H in H0. auto.
Qed.

Lemma eq_env_P_trans: forall {A} S (r1:M.t A) r2 r3,
    eq_env_P S r1 r2 -> eq_env_P S r2 r3 -> eq_env_P S r1 r3.
Proof.
  intros. intro. intros.
  specialize (H x H1).
  specialize (H0 x H1).
  rewrite H. auto.
Qed.

Lemma eq_env_P_set_not_in_P_l':
  forall  {A} (x : M.elt) (v : A)
          (P : Ensemble M.elt) (rho1 rho2 : M.t A),
    eq_env_P P  (M.set x v rho1) rho2 ->
    Disjoint M.elt P (Singleton M.elt x) ->
    eq_env_P P  rho1 rho2.
Proof.
  intros. intro; intros.
  specialize (H x0 H1).
  rewrite M.gso in H. auto.
  intro.
  inv H0.
  specialize (H3 x).
  apply H3; auto.
Qed.

Fixpoint get_list {A} (xs: list M.elt) (rho: M.t A) : option (list A) :=
  match xs with
  | x :: xs' => match M.get x rho, get_list xs' rho with
               | Some v, Some vs => Some (v::vs)
               | _, _ => None
               end
  | nil => Some nil
  end.

Fixpoint set_lists {A} (xs: list M.elt) (vs: list A) (rho: M.t A) : option (M.t A) :=
  match xs, vs with
  | x::xs', v::vs' => match set_lists xs' vs' rho with
                     | Some rho' => Some (M.set x v rho')
                     | None => None
                     end
  | nil, nil => Some rho
  | _, _ => None
  end.

Definition set_list {A:Type}  (l : list (M.elt * A)) (map: M.t A) : M.t A :=
  fold_right (fun xv cmap => M.set (fst xv) (snd xv) cmap ) map l.

(** Lemmas about [get_list] *)
Lemma get_list_In {A} (rho : M.t A) ys x vs :
  get_list ys rho = Some vs ->
  List.In x ys ->
  exists v, M.get x rho = Some v.
Proof.
  revert x vs. induction ys; intros x vs Hget H. inv H.
  inv H; simpl in Hget.
  - destruct (M.get x rho) eqn:Heq; try discriminate; eauto.
  - destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
    destruct (get_list ys rho) eqn:Heq'; try discriminate; eauto.
Qed.

Lemma In_get_list {A} (xs : list M.elt) (rho : M.t A) :
  (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
  exists vs, get_list xs rho = Some vs.
Proof.
  intros H. induction xs.
  - eexists; simpl; eauto.
  - edestruct IHxs.
    + intros x Hin. eapply H. now constructor 2.
    + edestruct H. now constructor.
      eexists. simpl. erewrite H1, H0.
      reflexivity.
Qed.

Lemma get_list_nth_get {A} (xs : list M.elt) (vs : list A) rho (x : M.elt) N :
  get_list xs rho = Some vs ->
  nthN xs N = Some x ->
  exists v, nthN vs N = Some v /\ M.get x rho = Some v.
Proof.
  revert vs N; induction xs; intros vs N Hget Hnth.
  - inv Hnth.
  - simpl in Hget.
    destruct (M.get a rho) eqn:Hget'; try discriminate.
    destruct (get_list xs rho) eqn:Hget_list'; try discriminate.
    inv Hget. destruct N.
    + inv Hnth. eexists; simpl; eauto.
    + edestruct IHxs as [v' [Hnth1 Hget1]]; eauto.
Qed.

Lemma get_list_set_neq {A} xs x (v : A) rho :
  ~ List.In x xs ->
  get_list xs (M.set x v rho) = get_list xs rho.
Proof.
  intros Hin.
  revert rho. induction xs; intros rho.
  - reflexivity.
  - simpl. rewrite M.gso.
    + rewrite IHxs. reflexivity.
      intros Hin'. eapply Hin. now constructor 2.
    + intros Heq; subst. eapply Hin. now constructor.
Qed.

Lemma get_list_set_lists {A} xs (vs : list A) rho rho' :
  NoDup xs ->
  set_lists xs vs rho = Some rho' ->
  get_list xs rho' = Some vs.
Proof.
  revert rho' vs; induction xs; intros rho' vs Hnd Hset.
  - inv Hset. destruct vs; try discriminate. reflexivity.
  - inv Hnd. simpl in *.
    destruct vs; try discriminate.
    destruct (set_lists xs vs rho) eqn:Hset'; try discriminate. inv Hset.
    rewrite M.gss. rewrite get_list_set_neq.
    now erewrite IHxs; eauto. eassumption.
Qed.

Lemma get_list_set_lists_Disjoint {A} xs xs' (vs : list A) rho rho' :
  Disjoint _ (FromList xs) (FromList xs') ->
  set_lists xs vs rho = Some rho' ->
  get_list xs' rho' = get_list xs' rho.
Proof with now eauto with Ensembles_DB.
  revert rho' vs; induction xs; intros rho' vs Hd Hset.
  - inv Hset. destruct vs; try discriminate. inv H0; reflexivity.
  - simpl in *.
    destruct vs; try discriminate.
    destruct (set_lists xs vs rho) eqn:Hset'; try discriminate. inv Hset.
    rewrite FromList_cons in Hd.
    rewrite get_list_set_neq.
    erewrite IHxs...
    intros Hc; eapply Hd. constructor; eauto.
Qed.

Lemma get_list_reset {A} σ x y (v : A) rho l :
  M.get (σ x) rho = Some v ->
  ~ y \in (image σ (Setminus _ (FromList l) (Singleton _ x))) ->
  get_list (map σ l) rho = get_list (map (σ { x ~> y }) l) (M.set y v rho).
Proof with now eauto with Ensembles_DB.
  intros Hget Hnin. induction l; eauto.
  simpl. destruct (peq x a); subst.
  - rewrite extend_gss, M.gss, Hget.
    rewrite IHl. reflexivity.
    intros Hc. eapply Hnin.
    rewrite FromList_cons.
    eapply image_monotonic; try eassumption...
  - rewrite extend_gso; eauto.
    rewrite M.gso.
    rewrite IHl. reflexivity.
    intros Hc. eapply Hnin.
    rewrite FromList_cons.
    eapply image_monotonic; try eassumption...
    intros Hc. eapply Hnin.
    subst. rewrite FromList_cons. eexists; split; eauto.
    constructor; eauto.
    intros Hc; inv Hc. congruence.
Qed.

Lemma get_list_reset_neq {A} σ x y (v : A) rho l :
  ~ y \in (image σ (Setminus _ (FromList l) (Singleton _ x))) ->
  ~ List.In x l ->
  get_list (map σ l) rho = get_list (map (σ { x ~> y }) l) (M.set y v rho).
Proof with now eauto with Ensembles_DB.
  intros  Hnin. induction l; intros Hnin'; eauto.
  simpl. destruct (peq x a); subst.
  - exfalso. eapply Hnin'. now constructor.
  - rewrite extend_gso; eauto.
    rewrite M.gso.
    rewrite IHl. reflexivity.
    intros Hc. eapply Hnin.
    rewrite FromList_cons.
    eapply image_monotonic; try eassumption...
    intros Hc. eapply Hnin'. now constructor 2.
    intros Hc. subst. eapply Hnin.
    rewrite FromList_cons. eexists; split; eauto.
    constructor; eauto.
    intros Hc; inv Hc. congruence.
Qed.

Lemma get_eq_get_list_eq {A} (rho rho' : M.t A) xs :
  (forall z, M.get z rho = M.get z rho') ->
  get_list xs rho = get_list xs rho'.
Proof.
  induction xs; intros H; eauto.
  simpl; f_equal.
  rewrite IHxs; eauto.
  rewrite H. reflexivity.
Qed.

Lemma get_list_app {A} m l1 l2 (v1 v2 : list A) :
  get_list l1 m = Some v1 ->
  get_list l2 m = Some v2 ->
  get_list (l1 ++ l2) m = Some (v1 ++ v2).
Proof.
  revert v1. induction l1; intros v1 Hget1 Hget2; simpl in *.
  - inv Hget1. eauto.
  - destruct (M.get a m) eqn:Hgeta; try discriminate.
    destruct (get_list l1 m) eqn:Hget; try discriminate.
    inv Hget1. simpl. erewrite IHl1; eauto.
Qed.

Lemma get_list_length_eq {A} l (vs : list A) rho :
  get_list l rho = Some vs ->
  length l = length vs.
Proof.
  revert vs; induction l; intros vs Hget.
  - inv Hget. eauto.
  - simpl in Hget. destruct (M.get a rho); try discriminate.
    destruct (get_list l rho); try discriminate.
    inv Hget. simpl. f_equal; eauto.
Qed.

Lemma app_get_list {A} l1 l2 (vs : list A) rho :
  get_list (l1 ++ l2) rho = Some vs ->
  exists vs1 vs2,
    get_list l1 rho = Some vs1 /\
    get_list l2 rho = Some vs2 /\
    vs = vs1 ++ vs2.
Proof.
  revert vs. induction l1; intros vs Hget.
  - simpl in Hget. repeat eexists; eauto.
  - simpl in Hget.
    destruct (M.get a rho) eqn:Hgeta; try discriminate.
    destruct (get_list (l1 ++ l2) rho) eqn:Hgetl; try discriminate.
    inv Hget.
    edestruct IHl1 as [vs1 [vs2 [Hget1 [Hget2 Heq]]]].
    reflexivity.
    repeat eexists; eauto. simpl.
    rewrite Hgeta, Hget1. reflexivity.
    simpl. congruence.
Qed.

Lemma get_list_In_val {A} (rho : M.t A) ys v vs :
  get_list ys rho = Some vs ->
  List.In v vs ->
  exists x, List.In x ys /\ M.get x rho = Some v.
Proof.
  revert v vs. induction ys; intros x vs Hget H.
  - inv Hget. now inv H.
  - simpl in *.
    destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
    destruct (get_list ys rho) eqn:Heq'; try discriminate; eauto.
    inv Hget. inv H; eauto.
    edestruct IHys as [y [Hin Hget]]; eauto.
Qed.


(** Lemmas about [set_lists]  *)

Lemma set_lists_Forall2_get {A} (P : A -> A -> Prop)
      xs vs1 vs2 rho1 rho2 rho1' rho2' x :
  Forall2 P vs1 vs2 ->
  set_lists xs vs1 rho1 = Some rho1' ->
  set_lists xs vs2 rho2 = Some rho2' ->
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
      destruct (set_lists xs vs1 rho1) eqn:Heq1;
        destruct (set_lists xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall.
      repeat eexists; try rewrite M.gss; eauto.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (set_lists xs vs1 rho1) eqn:Heq1;
        destruct (set_lists xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall. inv Hin; try congruence.
      edestruct IHxs as [v1 [v2 [Hget1 [Hget2 HP]]]]; eauto.
      repeat eexists; eauto; rewrite M.gso; eauto.
Qed.

Lemma get_set_lists_In_xs {A} x xs vs rho rho' :
  x \in (FromList xs) ->
  set_lists xs vs rho = Some rho' ->
  exists v : A, M.get x rho' = Some v.
Proof.
  revert rho rho' vs. induction xs; intros rho rho' vs Hin Hset.
  - rewrite FromList_nil in Hin. exfalso.
    eapply not_In_Empty_set. eassumption.
  - rewrite FromList_cons in Hin.
    destruct vs; try discriminate.
    simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset_lists; try discriminate.
    inv Hset. inv Hin.
    + inv H. eexists. rewrite M.gss. reflexivity.
    + destruct (Coqlib.peq x a); subst.
      * eexists. now rewrite M.gss.
      * edestruct IHxs; eauto.
        eexists. simpl. rewrite M.gso; eauto.
Qed.

Lemma set_lists_not_In {A} (xs : list M.elt) (vs : list A)
      (rho rho' : M.t A) (x : M.elt) :
  set_lists xs vs rho = Some rho' ->
  ~ List.In x xs ->
  M.get x rho = M.get x rho'.
Proof.
  revert vs rho'.
  induction xs; simpl; intros vs rho' Hset Hin.
  - destruct vs; congruence.
  - destruct vs; try discriminate.
    destruct (set_lists xs vs rho) eqn:Heq1; try discriminate. inv Hset.
    rewrite M.gso; eauto.
Qed.

Lemma set_lists_length {A} (rho rho' rho1 : M.t A)
      (xs : list M.elt) (vs1 vs2 : list A) :
  length vs1 = length vs2 ->
  set_lists xs vs1 rho = Some rho1 ->
  exists rho2, set_lists xs vs2 rho' = Some rho2.
Proof.
  revert vs1 vs2 rho1.
  induction xs as [| x xs IHxs ]; intros vs1 vs2 rho1 Hlen Hset.
  - inv Hset. destruct vs1; try discriminate. inv H0.
    destruct vs2; try discriminate. eexists; simpl; eauto.
  - destruct vs1; try discriminate. destruct vs2; try discriminate.
    inv Hlen. simpl in Hset.
    destruct (set_lists xs vs1 rho) eqn:Heq2; try discriminate.
    edestruct (IHxs _ _ _ H0 Heq2) as  [vs2' Hset2].
    eexists. simpl; rewrite Hset2; eauto.
Qed.

Lemma set_permut {A} rho x y (v1 v2 : A) z :
  x <> y ->
  M.get z (M.set x v1 (M.set y v2 rho)) =
  M.get z (M.set y v2 (M.set x v1 rho)).
Proof.
  intros Hnin. destruct (peq z x); subst.
  - rewrite M.gss, M.gso, M.gss; eauto.
  - rewrite (@M.gso _ z x); eauto.
    destruct (peq z y); subst.
    + rewrite !M.gss; eauto.
    + rewrite !M.gso; eauto.
Qed.

Lemma set_set_lists_permut {A} rho rho' y ys (v : A) vs :
  set_lists ys vs rho = Some rho' ->
  ~ List.In y ys ->
  exists rho'',
    set_lists ys vs (M.set y v rho) = Some rho'' /\
    (forall z, M.get z (M.set y v rho') = M.get z rho'').
Proof.
  revert vs rho'.
  induction ys; intros vs rho' Hset Hin;
  destruct vs; try discriminate.
  - inv Hset. eexists; split; simpl; eauto.
  - simpl in Hset.
    destruct (set_lists ys vs rho) eqn:Heq; try discriminate.
    inv Hset. edestruct IHys as [rho'' [Hset Hget]]; eauto.
    intros Hc; eapply Hin; now constructor 2.
    eexists; split.
    simpl. rewrite Hset. reflexivity.
    intros z. rewrite set_permut.
    destruct (peq z a); subst.
    + rewrite !M.gss; eauto.
    + rewrite !(@M.gso _ z a); eauto.
    + intros Hc. eapply Hin.
      constructor; eauto.
Qed.

Lemma set_lists_length3 {A} (rho : M.t A) xs vs :
  length xs = length vs ->
  exists rho', set_lists xs vs rho = Some rho'.
Proof.
  revert vs; induction xs; intros vs Hlen; destruct vs; try discriminate.
  - eexists; simpl; eauto.
  - inv Hlen.
    edestruct IHxs as [rho' Hset]. eassumption.
    eexists. simpl. rewrite Hset. reflexivity.
Qed.

Lemma set_lists_app {A} xs1 xs2 (vs1 vs2 : list A) rho rho' :
  set_lists (xs1 ++ xs2) (vs1 ++ vs2) rho = Some rho' ->
  length xs1 = length vs1 ->
  exists rho'',
    set_lists xs2 vs2 rho = Some rho'' /\
    set_lists xs1 vs1 rho'' = Some rho'.
Proof.
  revert vs1 rho'. induction xs1; intros vs1 rho' Hset Hlen.
  - destruct vs1; try discriminate.
    eexists; split; eauto.
  - destruct vs1; try discriminate.
    inv Hlen. simpl in Hset.
    destruct (set_lists (xs1 ++ xs2) (vs1 ++ vs2) rho) eqn:Heq; try discriminate.
    inv Hset. edestruct IHxs1 as [rho'' [Hset1 Hset2]].
    eassumption. eassumption.
    eexists. split. eassumption. simpl; rewrite Hset2; reflexivity.
Qed.


Lemma set_lists_length_eq {A} rho rho' xs (vs : list A) :
  set_lists xs vs rho = Some rho' ->
  length xs = length vs.
Proof.
  revert rho' vs; induction xs; intros rho' vs Hset.
  - destruct vs; try discriminate. reflexivity.
  - destruct vs; try discriminate.
    simpl in Hset.
    destruct (set_lists xs vs rho) eqn:Heq; try discriminate.
    simpl. f_equal. inv Hset. eauto.
Qed.

Lemma get_list_reset_lst {A} σ xs ys (vs : list A) rho rho' l  :
  set_lists ys vs rho = Some rho' ->
  get_list (map σ xs) rho = Some vs ->
  Disjoint _ (image σ (FromList l)) (FromList ys) ->
  length xs = length ys ->
  NoDup xs -> NoDup ys ->
  get_list (map σ l) rho = get_list (map (σ <{ xs ~> ys }>) l) rho'.
Proof with now eauto with Ensembles_DB.
  revert σ ys vs rho' rho. induction xs as [| x xs IHxs ];
    intros σ ys vs rho' rho Hset Hget HD Hlen Hnd1 Hnd2.
  - destruct ys; try discriminate.
    inv Hget. inv Hset. reflexivity.
  - destruct ys; try discriminate. simpl in *.
    inv Hlen. destruct vs as [| v vs]; try discriminate.
    destruct (set_lists ys vs rho) eqn:Hset'; try discriminate.
    destruct (M.get (σ x) rho) eqn:Hget'; try discriminate.
    destruct (get_list (map σ xs) rho) eqn:Hgetl; try discriminate.
    inv Hget. inv Hset. inv Hnd1. inv Hnd2. rewrite !FromList_cons in HD.
    assert (H : get_list (map ((σ <{ xs ~> ys }>) {x ~> e}) l) (M.set e v t) =
                get_list (map ((σ <{ xs ~> ys }>)) l) t).
    { destruct (in_dec peq x l).
      - rewrite <- get_list_reset; try reflexivity.
        rewrite extend_lst_gso; eauto.
        erewrite <- set_lists_not_In. eassumption. eassumption.
        intros Hc. eapply HD. constructor; eauto.
        eexists; split; eauto.
        intros Hc.
        apply image_extend_lst_Included in Hc; eauto.
        inv Hc; eauto. eapply HD. constructor; eauto.
        eapply image_monotonic; [| eassumption ]...
      - rewrite map_extend_not_In; eauto.
        erewrite get_list_set_neq. reflexivity.
        intros Hc. eapply in_map_iff in Hc.
        destruct Hc as [x' [Heq Hin]].
        destruct (in_dec peq x' xs).
        + edestruct (extend_lst_gss σ) as [y' [Hin' Heq']]; eauto.
          rewrite Heq in Hin'. subst.
          subst. eauto.
        + rewrite extend_lst_gso in Heq; eauto.
          eapply HD. constructor; eauto.
          eexists; eauto. }
    rewrite H.
    erewrite <- IHxs; eauto.
    now eauto with Ensembles_DB.
Qed.


Lemma proper_get_list: forall A rho rho',
    map_get_r A rho rho' ->
    forall vs, get_list vs rho = get_list vs rho'.
Proof.
  intros A rho rho' Hp.
  induction vs; auto.
  simpl. rewrite IHvs. rewrite Hp. reflexivity.
Qed.


Lemma eq_env_P_set_not_in_P_l (A : Type) (x : map_util.M.elt) (v : A)
      (P : Ensemble map_util.M.elt) (rho1 rho2 : map_util.M.t A) : 
  eq_env_P P rho1 rho2 ->
  ~ x \in P ->
          eq_env_P P (map_util.M.set x v rho1) rho2.
Proof.
  intros Heq Hnin z Hin.
  rewrite M.gso; eauto.
  intros Hc; subst; contradiction. 
Qed.



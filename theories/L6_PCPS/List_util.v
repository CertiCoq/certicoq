(* List library utilities. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)


From Coq Require Import Lists.List Relations.Relations Classes.RelationClasses
         omega.Omega Numbers.BinNums Structures.OrdersEx Sets.Ensembles
         Lists.SetoidList ZArith Arith Sorting.Permutation.

From L6 Require Import Ensembles_util.

Import ListNotations.

Ltac inv H := inversion H; clear H; subst.


(* returns [n, n+m[ *)
 Fixpoint fromN (n:N) (m:nat): list N :=
  match m with
  | 0 => nil
  | S m'  => n::(fromN (BinNat.N.succ n)  m')
  end.
 
(** Definition of [nthN]. Same as [nth_error] but the argument is
  * of type [N] instead of [nat] *)
Function nthN {A: Type} (al: list A) (n: N) : option A :=
  match al, n with
    | a::al', 0%N => Some a
    | a::al', _ => nthN al' (n-1)%N
    | _, _ => None
  end.

(** map a function to a list of option type *)
Fixpoint mapopt {A} (al: list (option A)) : option (list A) :=
  match al with 
    | Some a :: al' => match mapopt al' with
                         | Some bl' => Some (a::bl')
                         | None => None
                       end
    | None :: _ => None
    | nil => Some nil
  end.

(** Asymmetric version of Forall2 *) 
Inductive Forall2_asym {A} (R : relation A) : list A -> list A -> Prop :=
| Forall2_asym_nil : forall l, Forall2_asym R [] l
| Forall2_asym_cons :
    forall x y l l', R x y -> Forall2_asym R l l' -> Forall2_asym R (x :: l) (y :: l').

Hint Constructors Forall2_asym.


(** Lemmas about [Forall2] and [Forall2_asym] *)
Lemma Forall2_length {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  Forall2 R l1 l2 -> length l1 = length l2. 
Proof.
  revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
  - inv H; eauto.
  - inv H. simpl. f_equal. eauto.
Qed.

Lemma Forall2_asym_length {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  Forall2_asym R l1 l2 -> length l1 <= length l2. 
Proof.
  revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
  - inv H; simpl. omega.
  - inv H. simpl. eapply IHxs in H4. omega.
Qed.

Lemma Forall2_monotonic {A} (R R' : A -> A -> Prop) (l1 l2 : list A) :
  (forall x1 x2, R x1 x2 -> R' x1 x2) ->
  Forall2 R l1 l2 ->
  Forall2 R' l1 l2.
Proof.
  intros H. revert l2.
  induction l1 as [| x xs IHxs ]; intros l2 Hall.
  - inv Hall; eauto. 
  - destruct l2; inv Hall. constructor; eauto.
Qed.

Lemma Forall2_monotonic_strong (A : Type) (R R' : A -> A -> Prop) (l1 l2 : list A) :
  (forall x1 x2 : A, List.In x1 l1 -> List.In x2 l2 -> R x1 x2 -> R' x1 x2) ->
  Forall2 R l1 l2 -> Forall2 R' l1 l2.
Proof.
  revert l2.
  induction l1 as [| x xs IHxs ]; intros l2 H Hall.
  - inv Hall; eauto. 
  - destruct l2; inv Hall. constructor; eauto.
    eapply H; eauto. now constructor. now constructor.
    eapply IHxs; eauto. intros. eapply H.
    now constructor; eauto. now constructor; eauto.
    eassumption.
Qed.

Lemma Forall2_asym_monotonic {A} (R R' : A -> A -> Prop) (l1 l2 : list A) :
  (forall x1 x2, R x1 x2 -> R' x1 x2) ->
  Forall2_asym R l1 l2 ->
  Forall2_asym R' l1 l2.
Proof.
  intros H. revert l2.
  induction l1 as [| x xs IHxs ]; intros l2 Hall.
  - inv Hall; eauto. 
  - destruct l2; inv Hall. constructor; eauto.
Qed.

Lemma Forall2_refl {A} (R : A -> A -> Prop) (l : list A) :
  Reflexive R ->
  Forall2 R l l.
Proof.
  intros H. induction l as [| x l IHl]; eauto.
Qed.

Lemma Forall2_asym_refl {A} (R : A -> A -> Prop) (l : list A) :
  Reflexive R ->
  Forall2_asym R l l.
Proof.
  intros H. induction l as [| x l IHl]; eauto.
Qed.

Lemma Forall2_symm (A : Type) (R : A -> A -> Prop) (l1 l2 : list A) : 
  Symmetric R -> Forall2 R l1 l2 -> Forall2 R l2 l1.
Proof.
  intros H Hall; induction Hall; eauto.
Qed.

Lemma Forall2_symm_strong (A : Type) (R1 R2 : A -> A -> Prop) (l1 l2 : list A) : 
  (forall l1 l2, R1 l1 l2 -> R2 l2 l1) -> Forall2 R1 l1 l2 -> Forall2 R2 l2 l1.
Proof.
  intros H Hall; induction Hall; eauto.
Qed.

Lemma Forall2_Forall {A} (P : A -> A -> Prop) l :
  Forall2 P l l ->
  Forall (fun x => P x x) l.
Proof.
  intros H. induction l; eauto.
  inv H. constructor; eauto.
Qed.

Lemma Forall_Forall2 {A} (P : A -> A -> Prop) l :
  Forall (fun x => P x x) l  ->
  Forall2 P l l.
Proof.
  intros H. induction l; eauto.
  inv H. constructor; eauto.
Qed.
  
Lemma Forall2_trans {A} (R : A -> A -> Prop) (l1 l2 l3 : list A) :
  Transitive R ->
  Forall2 R l1 l2 ->
  Forall2 R l2 l3 ->
  Forall2 R l1 l3.
Proof.
  intros Htrans.
  revert l2 l3. induction l1 as [| x l IHl ]; intros l2 l3 H1 H2.
  - inv H1. inv H2. constructor.
  - inv H1. inv H2. constructor; eauto.
Qed.      

Lemma Forall2_asym_trans {A} (R : A -> A -> Prop) (l1 l2 l3 : list A) :
  Transitive R ->
  Forall2_asym R l1 l2 ->
  Forall2_asym R l2 l3 ->
  Forall2_asym R l1 l3.
Proof.
  intros Htrans.
  revert l2 l3. induction l1 as [| x l IHl ]; intros l2 l3 H1 H2.
  - inv H1. inv H2; eauto.
  - inv H1. inv H2; eauto.
Qed.      

Lemma Forall2_trivial {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  (forall x y, R x y) ->
  (length l1 = length l2) -> 
  Forall2 R l1 l2.
Proof.
  intros H.
  revert l2; induction l1 as [| x l IHl]; intros l2 Hlen;
  destruct l2; try discriminate; eauto.
Qed.

Lemma Forall2_asym_trivial {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  (forall x y, R x y) ->
  (length l1 <= length l2) -> 
  Forall2_asym R l1 l2.
Proof.
  intros H.
  revert l2; induction l1 as [| x l IHl]; intros l2 Hlen; eauto.
  destruct l2; simpl in *; try omega. constructor; eauto.
  eapply IHl; omega.
Qed.

Lemma Forall2_same {A} (R : A -> A -> Prop) l:
  (forall x, List.In x l -> R x x) ->
  Forall2 R l l.
Proof.
  induction l; intros H; constructor.
  - apply H. constructor; eauto.
  - apply IHl. intros. apply H. constructor 2; eauto.
Qed.

Lemma Forall2_asym_same {A} (R : A -> A -> Prop) l:
  (forall x, List.In x l -> R x x) ->
  Forall2_asym R l l.
Proof.
  induction l; intros H; constructor.
  - apply H. constructor; eauto.
  - apply IHl. intros. apply H. constructor 2; eauto.
Qed.

Theorem Forall2_Equiv:
  forall (X:Type) (R:relation X), Equivalence R -> Equivalence (Forall2 R).
Proof.
  intros. inversion H. constructor.
  + red. intros. induction x. constructor. constructor.
    apply Equivalence_Reflexive. assumption.
  + red. intro x. induction x; intros. inversion H0. constructor.
    inversion H0; subst.   apply IHx in H5. constructor.
    apply (Equivalence_Symmetric _ _ H3). assumption.
  + red. induction x; intros.
    * inversion H0; subst; inversion H1. constructor.
    * inversion H0; subst; inversion H1; subst. constructor.
      eapply Equivalence_Transitive. apply H4. assumption.
      apply (IHx _ _ H6) in H8. assumption.
Qed.

Lemma Forall2_trans_strong (A : Type) (R1 R2 R3 : A -> A -> Prop) (l1 l2 l3 : list A) : 
  (forall l1 l2 l3, R1 l1 l2 -> R2 l2 l3 -> R3 l1 l3) ->
  Forall2 R1 l1 l2 -> Forall2 R2 l2 l3 -> Forall2 R3 l1 l3.
Proof.
  intros H Hall1; revert l3; induction Hall1; intros l3 Hall2 ; eauto.
  - inv Hall2. constructor.
  - inv Hall2. constructor; eauto.
Qed.

Lemma Forall2_forall (A B : Type) (R : A -> B -> B -> Prop) (l1 l2 : list B) :
  inhabited A ->
  (forall k, Forall2 (R k) l1 l2) ->
  Forall2 (fun x1 x2 => forall k, R k x1 x2) l1 l2.
Proof.
  intros [w]. revert l2. induction l1; intros l2 Hyp.
  - specialize (Hyp w).
    inversion Hyp; subst. now constructor.
  - assert (Hyp' := Hyp w). inversion Hyp'.
    subst. constructor. intros k.
    specialize (Hyp k). inv Hyp. eassumption.
    eapply IHl1. intros k.
    specialize (Hyp k). inv Hyp. eassumption.
Qed.

Lemma Forall2_conj (A : Type) (R1 R2 : A -> A -> Prop) (l1 l2 : list A) :
  Forall2 R1 l1 l2 ->
  Forall2 R2 l1 l2 ->
  Forall2 (fun x1 x2 => R1 x1 x2 /\ R2 x1 x2) l1 l2.
Proof.
  intros H1 H2. induction H1.
  - constructor.
  - inv H2; constructor; now eauto.
Qed.

Lemma Forall2_flip (A : Type) (R : A -> A -> Prop) (l1 l2 : list A) :
  Forall2 (fun x1 x2 => R x2 x1) l2 l1 ->
  Forall2 R l1 l2.
Proof.
  intros Hall. induction Hall.
  - now constructor.
  - constructor; eassumption.
Qed.

(** Lemmas about [nthN] *)

Lemma In_nthN (A : Type) (l : list A) (v : A) :
  List.In v l -> exists n, nthN l n = Some v .
Proof.
  intros Hin. induction l.
  - inv Hin.
  - inv Hin.
    + exists 0%N. eauto.
    + destruct IHl as [n Hnth].
      eassumption. 
      exists (n+1)%N. simpl. destruct (n + 1)%N eqn:Heq; eauto. 
      zify. omega. 
      rewrite <- Heq. rewrite N_as_OT.add_sub.
      eassumption.
Qed.

Lemma nthN_In {A} (l : list A) n v :
  nthN l n = Some v ->
  List.In v l.
Proof. 
  revert n v. induction l; intros n v Hnth.
  - inv Hnth.
  - destruct n. inv Hnth.
    now constructor.
    constructor 2. eapply IHl. eauto. 
Qed.

Lemma nthN_app {A} (l1 l2 : list A) N :
  (nthN (l1 ++ l2) N = nthN l1 N) \/
  (nthN (l1 ++ l2) N = nthN l2 (N - N.of_nat (length l1))%N /\ (N.of_nat (length l1) <= N)%N).
Proof. 
  revert N; induction l1; intros N.
  - right. rewrite app_nil_l, N.sub_0_r. split; eauto. simpl. zify; omega.
  - destruct N; [now eauto |].
    destruct (IHl1 ((N.pos p)-1)%N) as [H1 | [H2 H3]].
    now eauto.
    replace (N.of_nat (length (a :: l1))) with (1 + N.of_nat (length l1))%N.
    replace (N.pos p - (1 + N.of_nat (length l1)))%N with
    (N.pos p - 1 - N.of_nat (length l1))%N.
    right. split. now eauto. zify. omega. 
    zify; omega. 
    simpl (length _). rewrite Nnat.Nat2N.inj_succ.
    zify. omega. 
Qed.

Lemma nthN_app_geq {A} (l1 l2 : list A) N :
  (N.of_nat (length l1) <= N)%N ->
  nthN (l1 ++ l2) N = nthN l2 (N - N.of_nat (length l1))%N.
Proof.
  revert N. induction l1; intros N Heq.
  - simpl. rewrite N.sub_0_r. reflexivity.
  - simpl length in *. 
    destruct N. 
    zify. omega.
    rewrite Nnat.Nat2N.inj_succ.
    rewrite <- N.add_1_l, N_as_DT.sub_add_distr. 
    rewrite <- IHl1.
    reflexivity. zify. omega. 
Qed.

Lemma nthN_is_Some_app {A} (l1 l2 : list A) N x :
  nthN l1 N = Some x ->
  nthN (l1 ++ l2) N = Some x.
Proof.
  revert N. induction l1; intros N Heq.
  - inv Heq.
  - destruct N. inv Heq. reflexivity.
    simpl. eauto.
Qed.

Lemma nthN_length {A B} (l1 : list A) (l2 : list B) (n : N) (v1 : A) :
  length l1 <= length l2 ->
  nthN l1 n = Some v1 ->
  exists v2,
    nthN l2 n = Some v2.
Proof.
  revert l2 n.
  induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
  - inv Hnth.
  - destruct n as [| n]; destruct l2; try discriminate.
    + simpl in H. omega.
    + simpl in Hnth. inv Hnth.
      eexists. split; simpl; eauto.
    + simpl in H. omega.
    + edestruct IHxs with (l2 := l2) as [v2 Hnth2]; eauto.
      simpl in H. omega.
Qed.

Lemma nthN_is_Some_length {A} (l : list A) N x :
  nthN l N = Some x ->
  (N < N.of_nat (length l))%N.
Proof. 
  revert N. induction l; intros N Heq.
  - inv Heq. 
  - destruct N. inv Heq.
    unfold length. rewrite Nnat.Nat2N.inj_succ. zify. omega. 
    assert (Hlt : ((N.pos p)-1 < N.of_nat (length l))%N) by eauto.
    simpl (length _). rewrite Nnat.Nat2N.inj_succ.
    zify. omega. 
Qed.

Lemma Forall2_nthN {A B} (R : A -> B -> Prop) l1 l2
      (n : N) (v1 : A):
  Forall2 R l1 l2 ->
  nthN l1 n = Some v1 ->
  exists v2,
    nthN l2 n = Some v2 /\
    R v1 v2.
Proof.
  revert l2 n.
  induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
  - inv H. discriminate.
  - inv H. destruct n as [| n].
    + simpl in Hnth. inv Hnth.
      eexists. split; simpl; eauto.
    + edestruct IHxs as [v2 [Hnth2 Hr]]; eauto.
Qed.

Lemma Forall2_asym_nthN {A} (R : A -> A -> Prop) (l1 l2 : list A)
      (n : N) (v1 : A):
  Forall2_asym R l1 l2 ->
  nthN l1 n = Some v1 ->
  exists v2,
    nthN l2 n = Some v2 /\
    R v1 v2.
Proof.
  revert l2 n.
  induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
  - inv H. discriminate.
  - inv H. destruct n as [| n].
    + simpl in Hnth. inv Hnth.
      eexists. split; simpl; eauto.
    + edestruct IHxs as [v2 [Hnth2 Hr]]; eauto.
Qed.

(** Compute the maximum of a list with positives *)
Fixpoint max_list ls acc : positive :=
  match ls with
    | nil => acc
    | cons x xs => max_list xs (Pos.max x acc)
  end.

Lemma max_list_spec1 l z :
  (z <= max_list l z)%positive.
Proof.
  revert z. induction l; intros z.
  - simpl. zify; omega.
  - simpl. eapply Pos.le_trans; [| now eapply IHl ].
    zify; omega. 
Qed.

Lemma max_list_spec2 l z x :
  List.In x l -> (x <= max_list l z)%positive.
Proof.
  revert z. induction l; intros z Hin.
  - inv Hin.
  - inv Hin; simpl. 
    + eapply Pos.le_trans; [| now eapply max_list_spec1 ].
      zify; omega.
    + now apply IHl.
Qed.

Lemma max_list_acc_mon z1 z2 l :
  (z1 <= z2)%positive ->
  (max_list l z1 <= max_list l z2)%positive.
Proof.
  revert z1 z2; induction l; intros z1 z2 Hleq.
  - eassumption.
  - simpl. eapply IHl. zify; omega.
Qed.

(** * Lemmas about [NoDup] *)

Lemma NoDup_app {A} xs ys :
  NoDup xs -> NoDup ys ->
  Disjoint A (FromList xs) (FromList ys) ->
  NoDup (xs ++ ys).
Proof with now eauto with Ensembles_DB.
  revert ys; induction xs; intros ys Hnd1 Hnd2 HD; simpl; eauto.
  inv Hnd1. rewrite FromList_cons in HD.
  constructor. intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
  now eapply HD; constructor; eauto.
  eapply IHxs; eauto...
Qed.

Lemma NoDupA_NoDup {A} l :
  NoDupA (@eq A) l -> NoDup l.
Proof.
  intros H. induction H; constructor; eauto.
  intros Hc. eapply H. eapply In_InA.
  now eauto with typeclass_instances.
  eassumption.
Qed.

Lemma NoDup_cons_l {A} (l1 l2 : list A):
  NoDup (l1 ++ l2) ->
  NoDup l1.
Proof.
  induction l1; simpl; intros H; constructor; eauto.
  - inv H. firstorder.
  - inv H; firstorder.
Qed.

Lemma NoDup_cons_r {A} (l1 l2 : list A):
  NoDup (l1 ++ l2) ->
  NoDup l2.
Proof.
  revert l2; induction l1; intros l2 H; simpl in *; eauto.
  inv H; eauto.
Qed.

(** Lemmas about [fold_left] *)

Lemma fold_left_monotonic {A} f1 f2 (l : list A) n1 n2 :
  (forall x1 x1' x2 ,
     x1 <= x1' -> f1 x1 x2 <= f2 x1' x2) ->
  n1 <= n2 ->
  fold_left f1 l n1 <= fold_left f2 l n2.
Proof.
  revert n1 n2; induction l; eauto.
Qed.

Lemma fold_left_extensive {A} f (l : list A) n :
  (forall c x, x <= f x c) ->
  n <= fold_left f l n.
Proof.
  revert n; induction l; eauto; intros n H.
  simpl. eapply le_trans. now eapply H.
  now eapply IHl.
Qed.

Lemma fold_left_comm {A B} (f : A -> B -> A) (l : list B) n m :
  (forall x y z, f (f x y) z = f (f x z) y) ->
  fold_left f l (f n m) = f (fold_left f l n) m.
Proof.
  revert n; induction l; eauto; intros n Hyp; simpl.
  rewrite <- IHl; eauto. f_equal. eauto.
Qed.

(** Max of list given a measure function and corresponding lemmas *)

Definition max_list_nat_with_measure {A} (f : A -> nat) i (ls : list A) : nat :=
  fold_left (fun c v => max c (f v)) ls i.

Lemma max_list_nat_spec1 {A} (f : A -> nat) l z :
  z <= max_list_nat_with_measure f z l.
Proof. 
  eapply fold_left_extensive. 
  intros. eapply Nat.le_max_l. 
Qed.

Lemma max_list_nat_spec2 {A} (f : A -> nat) l z x :
  List.In x l -> (f x <= max_list_nat_with_measure f z l)%nat.
Proof.
  revert z. induction l; intros z Hin.
  - inv Hin.
  - inv Hin; simpl. 
    + eapply le_trans; [| now eapply max_list_nat_spec1 ].
      eapply Nat.le_max_r.
    + now apply IHl.
Qed.

Lemma max_list_nat_acc_mon {A} (f : A -> nat) l z1 z2  :
  z1 <= z2 ->
  max_list_nat_with_measure f z1 l <= max_list_nat_with_measure f z2 l.
Proof.
  intros. eapply fold_left_monotonic; eauto.
  intros. eapply Nat.max_le_compat_r. eassumption.
Qed.

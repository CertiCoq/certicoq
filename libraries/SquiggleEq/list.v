(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.


Notation LIn := (List.In).
(**
uncomment this and remove the line above if [univ]:=Type

Fixpoint LIn {A : Type} (a:A) (l:list A) : [univ] :=
  match l with
    | nil => False
    | b :: m => (b = a) [+] LIn a m
  end.

Definition In := 9.

*)


(* Move *)
Definition listPad {T} (def:T) (l: list T) (n: nat) : list T :=
l++(repeat def (n-length l)).

Lemma listPad_length  {T} (def:T) (l: list T) (n: nat):
n <= length (listPad  def l n).
Proof using.
  setoid_rewrite app_length.
  rewrite repeat_length.
  omega.
Qed.

SearchAbout NoDup.

Fixpoint ball (l : list bool) : bool :=
  match l with
    | [] => true
    | x :: xs => andb x (ball xs)
  end.

Lemma ball_true :
  forall l,
    ball l = true <=> (forall x,  LIn x l -> x = true).
Proof.
  induction l; simpl; sp.
  rw andb_eq_true.
  trw IHl; split; sp.
Qed.

Lemma ball_map_true :
  forall A,
  forall f : A -> bool,
  forall l : list A,
    ball (map f l) = true <=> forall x,  LIn x l -> f x = true.
Proof.
  induction l; simpl; sp.
  trw andb_eq_true.
  trw IHl; split; sp; subst; sp.
Qed.




  Fixpoint remove {A:Type } `{Deq A} (x : A) (l : list A) : list A :=
    match l with
      | [] => []
      | y::tl => if (decide (x = y)) then remove x tl else y::(remove x tl)
    end.

  Theorem remove_In {A:Type } `{Deq A} : forall (l : list A) (x : A), ~ In x (remove x l).
  Proof.
    induction l as [|x l]; auto. simpl. intro y.
    rewrite decide_decideP.
    cases_if; simpl; auto.
    firstorder.
  Qed.
  
(** l \ lr -- removes the elements of lr from l  *)
Fixpoint diff {T} {eqd:Deq T} (lr:list T) (l:list T) : list T :=
  match lr with
    | [] => l
    | h::t => diff t (remove h l)
  end.

Lemma remove_trivial :
  forall T x eq,
  forall l : list T,
    (! LIn x l)
      -> @remove T eq x l = l.
Proof.
  induction l as [| a l]; simpl; intro H; sp.
  rewrite decide_decideP.
  cases_if as Heq.
  destruct H. left. auto.
  f_equal.
  rewrite IHl.  auto.
  introv Hlin. apply H. auto.
Qed.

Lemma diff_nil :
  forall T eq, forall l : list T, @diff T eq l [] = [].
Proof.
  induction l; simpl; auto.
Qed.

Hint Rewrite diff_nil.

Typeclasses eauto := 2.
Lemma in_remove {T:Type} `{Deq T}:
  forall  x y, forall l : list T,
    LIn x (remove y l) <=> (~ x = y) # LIn x l.
Proof.
  induction l; simpl.
  split; sp. rewrite decide_decideP.
  cases_if; subst; allsimpl; allrw IHl; split; sp; subst; sp.
Qed.

Lemma in_diff :
  forall T,
  forall l1 l2 : list T,
  forall x eq,
    LIn x (@diff T eq l1 l2)
    <=>
    (LIn x l2  # (! LIn x l1)).
Proof.
  induction l1; simpl; sp.
  split; sp. introv. auto.
  trw IHl1; trw in_remove; split; sp; auto.
Qed.

Lemma remove_app {T:Type} `{Deq T}:
  forall x,
  forall l1 l2 : list T,
    remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
Proof.
  induction l1; simpl; sp. repeat rewrite decide_decideP.
  cases_if; subst; rewrite IHl1; auto.
Qed.

(* Move *)

Lemma deq_refl {T:Type} `{Deq T} : forall (x:T), (decide (x=x)) = true.
Proof.
  intros.
  rewrite Decidable_complete; auto.
Qed.

Lemma deqP_refl {T:Type} `{Deq T} : forall (x:T), (decideP (x=x)) = left  eq_refl.
Proof.
  intros. destruct (decideP (x = x)); try discriminate.
- f_equal. apply Eqdep_dec.UIP_dec.
  intros. apply decideP; auto.
- sp.
Qed.

Hint Rewrite (fun T d => @deq_refl T d) (fun T d => @deqP_refl T d) : SquiggleEq.

Lemma remove_comm {T:Type} `{Deq T} :
  forall l : list T,
  forall x y,
    remove x (remove  y l) = remove  y (remove  x l).
Proof.
  induction l; simpl; sp.
  repeat rewrite decide_decideP.
  repeat (cases_if; subst; simpl in *; auto; autorewrite with SquiggleEq; try congruence;
   repeat rewrite decide_decideP).
Qed.

Lemma diff_remove {T:Type} {eq:Deq T} :
  forall l1 l2 : list T,
  forall x,
    @diff T eq l1 (@remove T eq x l2) = @remove _ eq x (@diff _ eq l1 l2).
Proof.
  induction l1; simpl; sp.
  repeat (rewrite IHl1).
  rewrite remove_comm; auto.
Qed.

Lemma diff_comm :
  forall T eq,
  forall l1 l2 l3 : list T,
    @diff _ eq l1 (@diff _ eq l2 l3) = @diff _ eq l2 (@diff _ eq l1 l3).
Proof.
  induction l1; simpl; sp.
  rewrite <- diff_remove.
  rewrite IHl1; auto.
Qed.

Lemma diff_app_r :
  forall T eq,
  forall l1 l2 l3 : list T,
    @diff _ eq l1 (l2 ++ l3) = @diff _ eq l1 l2 ++ @diff _ eq l1 l3.
Proof.
  induction l1; simpl; sp.
  rewrite remove_app.
  rewrite IHl1; auto.
Qed.

Lemma diff_app_l :
  forall T eq,
  forall l1 l2 l3 : list T,
    @diff _ eq l1 (@diff _ eq l2 l3) = @diff _ eq (l1 ++ l2) l3.
Proof.
  induction l1; simpl; sp.
  repeat (rewrite diff_remove).
  rewrite IHl1; auto.
Qed.

Lemma remove_repeat :
  forall T eq x,
  forall l : list T,
    @remove T eq x l = @remove T eq x (@remove T eq x l).
Proof.
  induction l; simpl; sp. repeat rewrite decide_decideP.
  repeat cases_if; auto. simpl.
  repeat rewrite decide_decideP.
  repeat cases_if;  simpl; auto.
  provefalse; apply H; auto.
  rewrite <- IHl; auto.
Qed.

Lemma diff_repeat :
  forall T eq,
  forall l1 l2 : list T,
    @diff _ eq l1 l2 = @diff _ eq l1 (@diff _ eq l1 l2).
Proof.
  induction l1; simpl; sp.
  repeat (rewrite diff_remove).
  rewrite <- remove_repeat.
  rewrite <- IHl1; auto.
Qed.

Lemma remove_dup :
  forall T eq,
  forall l1 l2 : list T,
  forall x,
    LIn x l1
    -> @diff _ eq l1 l2 = @remove T eq x (@diff _ eq l1 l2).
Proof.
  induction l1; simpl; sp; subst.
  rewrite diff_remove.
  rewrite <- remove_repeat; auto.
Qed.

Lemma diff_move :
  forall T eq,
  forall l1 l2 l3 : list T,
  forall x,
    @diff _ eq (l1 ++ x :: l2) l3 = @diff _ eq (x :: l1 ++ l2) l3.
Proof.
  induction l1; simpl; sp.
  rewrite IHl1; simpl.
  rewrite remove_comm; auto.
Qed.

Lemma diff_dup :
  forall T eq,
  forall l1 l2 l3 : list T,
  forall x,
    LIn x (l1 ++ l2)
    -> @diff _ eq (l1 ++ l2) l3 = @diff _ eq (l1 ++ x :: l2) l3.
Proof.
  induction l1; simpl; sp; subst.
  rewrite diff_remove.
  apply remove_dup; auto.
  rewrite diff_move; simpl.
  rewrite <- remove_repeat; auto.
Qed.

Lemma in_app_iff :
  forall A l l' (a:A),
    LIn a (l++l') <=> (LIn a l) [+] (LIn a l').
Proof.
  induction l as [| a l]; introv; simpl; try (rw IHl); split; sp.
Qed.

Lemma in_map_iff :
  forall (A B : Type) (f : A -> B) l b,
    LIn b (map f l) <=> {a : A $ LIn a l # b = f a}.
Proof.
  induction l; simpl; sp; try (complete (split; sp)).
  trw IHl; split; sp; subst; sp.
  exists a; sp.
  exists a0; sp.
  right; exists a0; sp.
Qed.

Lemma diff_dup2 :
  forall T eq,
  forall l1 l2 l3 : list T,
  forall x,
    LIn x l1
    -> @diff _ eq (l1 ++ l2) l3 = @diff _ eq (l1 ++ x :: l2) l3.
Proof.
  intros; apply diff_dup.
  apply in_app_iff; left; auto.
Qed.

Definition null {T} (l : list T) := forall x, !LIn x l.

Lemma null_nil : forall T, null ([] : list T).
Proof.
  unfold null; sp.
Qed.

Hint Immediate null_nil.

Lemma null_nil_iff : forall T, null ([] : list T) <=> True.
Proof.
  split; sp; apply null_nil.
Qed.

Hint Rewrite null_nil_iff.

Hint Resolve decideP : SquiggleEq.
Lemma null_diff :
  forall T,
  forall eq : Deq T,
  forall l1 l2 : list T,
    null (@diff _ eq l1 l2) <=> forall x, LIn x l2 -> LIn x l1.
Proof.
  induction l1; simpl; sp.
  trw IHl1; sp; split; sp.
  assert ({a = x} + {a <> x}) by auto with SquiggleEq; sp.
  right; apply_hyp.
  trw in_remove; sp.
  alltrewrite in_remove; sp.
  apply_in_hyp p; sp; subst; sp.
Qed.

Lemma null_iff_nil : forall T, forall l : list T, null l <=> l = [].
Proof.
  induction l; unfold null; simpl; split; sp.
  assert ((a = a) [+] LIn a l) by (left; auto).
  apply_in_hyp p; sp.
Qed.

Lemma null_cons :
  forall T x,
  forall l : list T,
    !( null (x :: l)).
Proof.
  unfold null; sp.
  assert (LIn x (x :: l)) by (simpl; left; auto).
  apply_in_hyp p; sp.
Qed.
Hint Immediate null_cons.

Lemma null_app :
  forall T,
  forall l1 l2 : list T,
    null (l1 ++ l2) <=> null l1 # null l2.
Proof.
  induction l1; simpl; sp; split; sp;
  try (apply null_nil);
  try(apply null_cons in H); sp;
  try(apply null_cons in H0); sp.
Qed.

Lemma null_map :
  forall A B,
  forall f : A -> B,
  forall l : list A,
    null (map f l) <=> null l.
Proof.
  induction l; simpl; sp; split; sp;
  try (apply null_nil);
  apply null_cons in H; sp.
Qed.


Definition nullb {T} (l : list T) := if l then true else false.

Lemma assert_nullb :
  forall T,
  forall l : list T,
    assert (nullb l) <=> null l.
Proof.
  destruct l; simpl; split; sp.
  apply not_assert in H; sp.
  apply null_cons in H; sp.
Qed.

Definition subsetb {T} (eq : Deq T) (l1 l2 : list T) : bool :=
  nullb (@diff _ eq l2 l1).

Definition eqsetb {T} (eq : Deq T) (l1 l2 : list T) : bool :=
  subsetb eq l1 l2 && subsetb eq l2 l1.

Lemma assert_subsetb :
  forall T eq,
  forall l1 l2 : list T,
    assert (subsetb eq l1 l2)
    <=>
    forall x, LIn x l1 -> LIn x l2.
Proof.
  sp; unfold subsetb.
  trw assert_nullb; trw null_diff; split; sp.
Qed.

Lemma assert_eqsetb :
  forall T eq,
  forall l1 l2 : list T,
    assert (eqsetb eq l1 l2)
    <=>
    forall x,  LIn x l1 <=>  LIn x l2.
Proof.
  sp; unfold eqsetb; trw assert_of_andb;
  repeat (trw assert_subsetb); repeat (split; sp);
  apply_in_hyp p; auto.
Qed.

Fixpoint beq_list {A} (eq : Deq A) (l1 l2 : list A) : bool :=
  match l1, l2 with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | x :: xs, y :: ys => if (decide (x=y)) then beq_list eq xs ys else false
  end.

Lemma assert_beq_list :
  forall A eq,
  forall l1 l2 : list A,
    assert (beq_list eq l1 l2) <=> l1 = l2.
Proof.
  unfold assert.
  induction l1; destruct l2; simpl; repeat rewrite decide_decideP;
     split; sp; try (complete (inversion H)).
  destruct (decideP (a=a0)); subst; sp.
  f_equal. apply IHl1; auto. 
  inversion H. subst.
  autorewrite with SquiggleEq.
  rewrite  IHl1. refl.
Qed.

Global Instance deq_list {A:Type} `{Deq A} : Deq (list A).
Proof.
  intros l1 l2.  exists (beq_list _ l1 l2).
  apply assert_beq_list.
Defined.

Typeclasses eauto :=6.
Lemma beq_list_refl :
  forall A eq,
  forall l : list A,
    beq_list eq l l = true.
Proof.
  induction l; simpl; sp.
  autorewrite with SquiggleEq.
  auto.
Qed.

Lemma eq_lists :
  forall A (l1 l2 : list A) x,
    l1 = l2
    <=>
    (
      length l1 = length l2
       #
      forall n, nth n l1 x = nth n l2 x
    ).
Proof.
  induction l1; sp; destruct l2; sp; split; allsimpl; sp;
  try(inversion H);try(inversion H0); subst; sp.
  gen_some 0; subst.
  assert (l1 = l2) as eq; try (rewrite eq; sp).
  apply IHl1 with (x := x); sp.
  gen_some (S n); sp.
Qed.

(*
Fixpoint memberb' {A} (eq : Deq A) (x : A) (l : list A) : {  LIn x l } + { !  LIn x l} :=
  match l return {  LIn x l } + { !  LIn x l} with
  | [] => right (fun x => x)
  | y :: ys =>
    match eq y x with
      | left e => left (or_introl e)
      | right _ =>
        match memberb' eq x ys with
          | left x => left (or_intror x)
          | right y => right y
        end
    end
  end.
*)

Fixpoint memberb {A : Type} (eq : Deq A) (x : A) (l : list A) : bool :=
  match l with
    | [] => false
    | y :: ys => if decide (y=x) then true else memberb eq x ys
  end.

Theorem assert_memberb :
  forall {T:Type} {eq : Deq T} (a:T) (l: list T),
    assert (memberb eq a l) <=>  LIn a l.
Proof with (repeat rewrite decide_decideP).
  intros. induction l. simpl.
  try (unfold assert; repeat split; intros Hf; auto ; inversion Hf).
  simpl ... cases_if. subst. unfold assert; repeat split; auto.
  repeat split; intros Hlr. right. apply IHl; auto.
  destruct Hlr as [Heq  | Hin]; tauto.
Qed.


Lemma memberb_app :
  forall A eq x,
  forall l1 l2 : list A,
    memberb eq x (l1 ++ l2) = memberb eq x l1 || memberb eq x l2.
Proof with (repeat rewrite decide_decideP).
  induction l1; simpl; sp ...
  destruct (decideP (a = x)); sp.
Qed.

Lemma in_app_deq :
  forall A l1 l2 (a : A) (deq : Deq A),
    LIn a (l1 ++ l2) -> (LIn a l1 + LIn a l2).
Proof.
  introv deq i.
  rw <- (@assert_memberb A deq) in i.
  rw memberb_app in i.
  apply assert_orb in i; sp; allrw (@assert_memberb A deq); sp.
Qed.

Lemma diff_cons_r :
  forall A eq x,
  forall l1 l2 : list A,
    @diff _ eq l1 (x :: l2)
    = if memberb eq x l1
      then @diff _ eq l1 l2
      else x :: @diff _ eq l1 l2.
Proof with (repeat rewrite decide_decideP).
  induction l1; simpl; sp...
  destruct (decideP (a=x)); subst; auto.
Qed.

Lemma diff_cons_r_ni :
  forall A eq x,
  forall l1 l2 : list A,
    !LIn x l2 -> @diff _ eq (x :: l1) l2 = @diff _ eq l1 l2.
Proof with (repeat rewrite decide_decideP).
  induction l1; simpl; sp.
  induction l2; allsimpl; allrw not_over_or; sp...
  destruct (decideP (x=a)); try subst; sp ;
  allrw; sp.
  Locate remove_trivial.
  rw (remove_trivial A x); sp.
Qed.

Fixpoint maxl (ts : list nat) : nat :=
  match ts with
  | nil => 0
  | n :: ns => max n (maxl ns)
  end.

Lemma maxl_prop :
  forall nats n,
     LIn n nats -> n <= maxl nats.
Proof.
  induction nats; simpl; sp; subst.
  apply max_prop1.
  allapply IHnats.
  assert (maxl nats <= max a (maxl nats)) by apply max_prop2.
  omega.
Qed.

Fixpoint addl (ts : list nat) : nat :=
  match ts with
  | nil => 0
  | n :: ns => n + (addl ns)
  end.

Theorem lin_flat_map :
  forall (A B : Type) (f : A -> list B) (l : list A) (y : B),
    LIn y (flat_map f l)
        <=>
        {x : A $ LIn x l # LIn y (f x)}.
Proof.
  induction l; simpl; sp.
  split; sp.
  trw in_app_iff.
  trw IHl.
  split; sp; subst; sp.
  exists a; sp.
  exists x; sp.
  right; exists x; sp.
Qed.

Theorem flat_map_empty:
 forall A B (ll:list A)  (f: A -> list B) , flat_map f ll =[]
   <=> forall a,  LIn a ll -> f a =[].
Proof. sp_iff Case.
 Case "->".
   intros Hmap a Hin; remember (f a) as fa; destruct fa.
   auto. assert ({a: A $ LIn a ll # LIn b (f a)}) as Hass;
    try (apply  lin_flat_map in Hass;
    rewrite Hmap in Hass; inversion Hass).
    exists a. (split; auto).  rewrite <- Heqfa.
   constructor; auto.
 Case "<-".
   intros Hin.
   remember (flat_map f ll) as flat; destruct flat ;auto.
   assert ( LIn b (flat_map f ll)) as Hinbf by
   (rewrite  <- Heqflat; constructor; auto).
   apply lin_flat_map in Hinbf. exrepnd.
   apply Hin in Hinbf1.
   rewrite Hinbf1 in Hinbf0.
   inversion Hinbf0.
Qed.

Lemma flat_map_map :
  forall A B C ,
  forall f : B -> list C,
  forall g : A -> B,
  forall l : list A,
    flat_map f (map g l) = flat_map (compose f g) l.
Proof.
  induction l; simpl; sp.
  rewrite IHl.
  unfold compose; auto.
Qed.

Lemma map_map :
  forall A B C ,
  forall f : B -> C,
  forall g : A -> B,
  forall l : list A,
    map f (map g l) = map (compose f g) l.
Proof.
  induction l; simpl; sp.
  rewrite IHl.
  unfold compose; auto.
Qed.

Lemma eq_flat_maps :
  forall A B,
  forall f g : A -> list B,
  forall l : list A,
    (forall x,  LIn x l -> f x = g x)
    -> flat_map f l = flat_map g l.
Proof.
  induction l; simpl; sp.
  assert (f a = g a).
  apply H; left; auto.
  rewrite H0.
  assert (flat_map f l = flat_map g l).
  rewrite IHl; auto.
  rewrite H1; auto.
Qed.

Lemma eq_maps :
  forall A B,
  forall f g : A -> B,
  forall l : list A,
    (forall x,  LIn x l -> f x = g x)
    -> map f l = map g l.
Proof.
  induction l; simpl; sp.
  assert (f a = g a).
  apply H; left; auto.
  rewrite H0.
  rewrite IHl; auto.
Qed.
Lemma in_nth :
  forall T a (l:list T),
     LIn a l
    -> {n : nat $ (n < length l) # a = nth n l a}.
Proof.
  intros ? ? ?. induction l; intros Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. dorn Hin.
     + intros. subst. exists 0. split; auto. simpl. omega.
     + intros. apply IHl in Hin. exrepnd.
        simpl.
         exists (S n) ;split ; try (simpl; omega).
         fold (app [a0] l);sp.
Qed.

(* stronger one above : no need for decidability
Lemma in_nth :
  forall T a (l:list T),
    Deq T
    ->  LIn a l
    -> {n : nat $ (n < length l) # a = nth n l a}.
Proof.
  intros ? ? ? deq. induction l; intros Hin.
 - simpl in Hin. contradiction.
 - case (deq a a0).
   + intros. subst. exists 0. split; auto. simpl. omega.
   + intros Hneq. simpl in Hin.
     destruct Hin as [Heq  | Hin].
     * symmetry in Heq. apply Hneq in Heq. contradiction.
     * apply IHl in Hin. clear Hneq. destruct Hin as [m Hp]. repnd.
       exists (S m) ;split ; try (simpl; omega).
       fold (app [a0] l).
       rewrite app_nth2. simpl.  assert (m-0 =m) as Hrew by omega.
       rewrite Hrew. auto. simpl. omega.
Qed.
*)

Lemma nth_in :
  forall A n (l : list A) d,
    n < length l
    -> LIn (nth n l d) l.
Proof.
  intros A n l d H; revert n H.
  induction l; simpl; sp.
  destruct n; sp.
  allapply S_lt_inj; sp.
Qed.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons v nil
  | cons h t => cons h (snoc t v)
  end.

Lemma length_snoc :
  forall T,
  forall n : T,
  forall l : list T,
    length (snoc l n) = S (length l).
Proof.
  intros; induction l; simpl; sp.
Qed.

Lemma snoc_as_append :
  forall T, forall l : list T, forall n,
    snoc l n = l ++ [n].
Proof.
  intros; induction l; simpl; sp.
  rewrite IHl; sp.
Qed.

Lemma snoc_append_r :
  forall T, forall l1 l2 : list T, forall v : T,
    (snoc l1 v) ++ l2 = l1 ++ (v :: l2).
Proof.
  intros; induction l1; simpl; sp.
  rewrite IHl1; sp.
Qed.

Lemma snoc_append_l :
  forall T, forall l1 l2 : list T, forall v : T,
    l2 ++ (snoc l1 v) = snoc (l2 ++ l1) v.
Proof.
  intros; induction l2; simpl; sp.
  rewrite IHl2; sp.
Qed.

Lemma in_snoc :
  forall T,
  forall l : list T,
  forall x y : T,
     LIn x (snoc l y) <=> (LIn x l [+] x = y).
Proof.
  induction l; simpl; sp.
  split; sp.
  trw IHl.
  apply sum_assoc.
Qed.

Hint Rewrite in_snoc.

Lemma snoc_cases :
  forall T,
  forall l : list T,
    l = [] [+] {a : T $ {k : list T $ l = snoc k a}}.
Proof.
  induction l.
  left; auto.
  sp; subst.
  right; exists a; exists (@nil T); simpl; auto.
  right.
  exists a0; exists (a :: k); simpl; auto.
Qed.

Lemma snoc_inj :
  forall T,
  forall l1 l2 : list T,
  forall x1 x2 : T,
    snoc l1 x1 = snoc l2 x2 -> l1 = l2  #  x1 = x2.
Proof.
  induction l1; simpl; intros.
  destruct l2; simpl in H; inversion H; subst; auto.
  inversion H.
  destruct l2; simpl in H1; inversion H1.
  destruct l2; simpl in H.
  inversion H.
  destruct l1; simpl in H2; inversion H2.
  inversion H.
  apply IHl1 in H2. sp; subst; auto.
Qed.

Lemma map_snoc :
  forall A B l x,
  forall f : A -> B,
    map f (snoc l x) = snoc (map f l) (f x).
Proof.
  induction l; simpl; sp.
  rewrite IHl; sp.
Qed.

Open Scope nat_scope.

Lemma length_app :
  forall T,
  forall l1 l2 : list T,
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; simpl; sp.
Qed.

Lemma nil_snoc_false :
  forall T, forall a : list T, forall b : T, [] = snoc a b -> False.
Proof.
  intros.
  assert (length ([] : list T) = length (snoc a b)).
  rewrite H; auto.
  simpl in H0.
  rewrite length_snoc in H0.
  inversion H0.
Qed.


Definition subset {T} (l1 l2 : list T) :=
  forall x,  LIn x l1 ->  LIn x l2.

Lemma fold_subset :
  forall T l1 l2,
    (forall x : T,  LIn x l1 ->  LIn x l2) = subset l1 l2.
Proof. sp. Qed.

Lemma null_diff_subset :
  forall T,
  forall eq : Deq T,
  forall l1 l2 : list T,
    null (@diff _ eq l1 l2) <=> subset l2 l1.
Proof.
  sp; apply null_diff; unfold subset; split; sp.
Qed.

Lemma subsetb_subset :
  forall T eq,
  forall l1 l2 : list T,
    assert (subsetb eq l1 l2) <=> subset l1 l2.
Proof.
  intros.
  apply assert_subsetb; unfold subset; split; sp.
Qed.

Lemma subset_refl :
  forall T,
  forall l : list T,
    subset l l.
Proof.
  unfold subset; sp.
Qed.

Hint Immediate subset_refl.

Lemma subset_refl_iff :
  forall T,
  forall l : list T,
    subset l l <=> True.
Proof.
  unfold subset; sp; split; sp.
Qed.

Hint Rewrite subset_refl_iff.

Lemma subset_nil_l :
  forall T, forall s : list T, subset [] s.
Proof.
  unfold subset; simpl; sp.
Qed.

Hint Immediate subset_nil_l.

Lemma subset_nil_l_iff :
  forall T, forall s : list T, subset [] s <=> True.
Proof.
  unfold subset; simpl; sp; split; sp.
Qed.

Hint Rewrite subset_nil_l_iff.

(* same as subset_nil_l *)
Lemma nil_subset :
  forall T, forall l : list T, subset [] l.
Proof.
  auto.
Qed.

(* same as subset_nil_l_iff *)
Lemma nil_subset_iff :
  forall T,
  forall l : list T,
    subset [] l <=> True.
Proof.
  sp; autorewrite with core; sp.
Qed.

Lemma cons_subset :
  forall T,
  forall x : T,
  forall l1 l2 : list T,
    subset (x :: l1) l2
    <=>  LIn x l2  #  subset l1 l2.
Proof.
  unfold subset; simpl; sp; split; sp; subst; auto.
Qed.

Tactic Notation "trewritec" constr(H) :=
       build_and_rewrite H.

Lemma singleton_subset :
  forall T,
  forall x : T,
  forall l : list T,
    subset [x] l <=>  LIn x l.
Proof.
  intros.
  remember (cons_subset T x [] l) as Htr.
  trewrite Htr.
  split; sp.
Qed.


Lemma app_subset :
  forall T,
  forall l1 l2 l3 : list T,
    subset (l1 ++ l2) l3 <=> subset l1 l3  #  subset l2 l3.
Proof.
  induction l1; simpl; sp; try(split; sp; fail).
  trw cons_subset. trw cons_subset.  
  split; introv Hlin; repnd; 
  try(trw IHl1); try(trw_h IHl1  Hlin; repnd);
  repeat(auto;split;auto).
Qed.

Lemma subset_trans :
  forall T,
  forall l1 l2 l3 : list T,
    subset l1 l2
    -> subset l2 l3
    -> subset l1 l3.
Proof.
  unfold subset; sp.
Qed.

Lemma subset_cons_nil :
  forall T x,
  forall l : list T,
    ! subset (x :: l) [].
Proof.
  unfold subset; sp.
  assert ( LIn x (x :: l)) by (simpl; left; auto).
  apply_in_hyp p; allsimpl; sp.
Qed.

Lemma subset_cons1 :
  forall T,
  forall x : T,
  forall l1 l2 : list T,
    subset l1 l2
    -> subset l1 (x :: l2).
Proof.
  unfold subset; simpl; sp.
Qed.

Lemma subset_cons2 :
  forall T,
  forall x : T,
  forall l1 l2 : list T,
    subset l1 l2
    -> subset (x :: l1) (x :: l2).
Proof.
  unfold subset; simpl; sp.
Qed.

Lemma subset_app_r :
  forall T,
  forall l1 l2 l3 : list T,
    subset l1 l2 -> subset l1 (l2 ++ l3).
Proof.
  unfold subset; intros.
  apply (@in_app_iff T).
  left; auto.
Qed.

Lemma subset_app_l :
  forall T,
  forall l1 l2 l3 : list T,
    subset l1 l3 -> subset l1 (l2 ++ l3).
Proof.
  unfold subset; intros.
  apply in_app_iff.
  right; auto.
Qed.

Lemma subset_app :
  forall T,
  forall l1 l2 l3 : list T,
    subset (l1 ++ l2) l3 <=> subset l1 l3  #  subset l2 l3.
Proof.
  unfold subset; sp; split; sp.
  apply_hyp; apply in_app_iff; left; auto.
  apply_hyp; apply in_app_iff; right; auto.
  allrw in_app_iff; sp.
Qed.

Lemma subset_snoc_r :
  forall T x,
  forall l1 l2 : list T,
    subset l1 l2 -> subset l1 (snoc l2 x).
Proof.
  unfold subset; intros.
  apply in_snoc.
  left; auto.
Qed.

Lemma subset_snoc_l :
  forall T x,
  forall l1 l2 : list T,
    (forall y,  LIn y l1 -> y = x)
    -> subset l1 (snoc l2 x).
Proof.
  unfold subset; sp.
  apply in_snoc.
  apply_in_hyp p; sp.
Qed.

Lemma null_subset :
  forall T,
  forall l1 l2 : list T,
    subset l1 l2
    -> null l2
    -> null l1.
Proof.
  unfold subset, null; sp.
  apply_in_hyp p; sp.
Qed.

Lemma subset_cons_l :
  forall T v,
  forall vs1 vs2 : list T,
    subset (v :: vs1) vs2 <=>  LIn v vs2  #  subset vs1 vs2.
Proof.
  unfold subset; simpl; sp; split; sp; subst; auto.
Qed.

Lemma in_subset :
  forall T (s1 s2 : list T) x,
    subset s1 s2
    ->  LIn x s1
    ->  LIn x s2.
Proof.
  intros T s1 s2 x.
  unfold subset; sp.
Qed.

Lemma not_in_subset :
  forall T (s1 s2 : list T) x,
    subset s1 s2
    ->  LIn x s1
    -> !  LIn x s2
    -> False.
Proof.
  intros T s1 s2 x.
  unfold subset; sp.
Qed.



Lemma subset_flat_map :
  forall A B,
  forall f : A -> list B,
  forall l k,
    subset (flat_map f l) k
    <=>
    forall x,  LIn x l -> subset (f x) k.
Proof.
  induction l; simpl; sp.
  trw nil_subset_iff; split; sp.
  trw app_subset; split; sp; subst; sp; alltrewrite IHl; sp.
Qed.

Global Instance in_deqq {A:Type} `{Deq A} (x:A) l: Decidable (LIn x l).
Proof.
  intros.
  exists (memberb _ x l).
  apply assert_memberb.
Defined.

(* Require Import Morphisms. *)



Lemma in_deq :
  forall A,
  forall eq : Deq A,
  forall x : A,
  forall l,
     LIn x l + !LIn x l.
Proof.
  induction l; simpl; sp; try (complete (right; sp)).
  destruct (decideP (a=x)); subst; sp.
  right; sp.
Defined.

Lemma subset_diff :
  forall A eq,
  forall l1 l2 l3 : list A,
    subset (@diff _ eq l1 l2) l3
    <=>
    subset l2 (l3 ++ l1).
Proof.
  unfold subset; sp; split; sp.
  apply in_app_iff.
  assert (LIn x l1 + !LIn x l1) by (apply in_deq; auto); sp.
  left; apply_hyp; apply in_diff; sp.
  allrw in_diff; sp.
  apply_in_hyp p.
  allrw in_app_iff; sp.
Qed.

Definition disjoint {T} (l1 l2 : list T) :=
  forall t, LIn t l1 -> !LIn t l2.

Lemma disjoint_nil_r :
  forall T,
  forall l : list T,
    disjoint l [].
Proof.
  unfold disjoint; sp.
Qed.

Hint Immediate disjoint_nil_r.

Lemma disjoint_nil_r_iff :
  forall T,
  forall l : list T,
    disjoint l [] <=> True.
Proof.
  unfold disjoint; sp; split; sp.
Qed.

Hint Rewrite disjoint_nil_r_iff.

Lemma disjoint_nil_l :
  forall T,
  forall l : list T,
    disjoint [] l.
Proof.
  unfold disjoint; sp.
Qed.

Hint Immediate disjoint_nil_l.

Lemma disjoint_nil_l_iff :
  forall T,
  forall l : list T,
    disjoint [] l <=> True.
Proof.
  unfold disjoint; sp; split; sp.
Qed.

Hint Rewrite disjoint_nil_l_iff.

Lemma disjoint_sym_impl :
  forall T,
  forall l1 l2 : list T,
    disjoint l1 l2 -> disjoint l2 l1.
Proof.
  unfold disjoint; sp.
  apply_in_hyp p; sp.
Qed.

Lemma disjoint_sym :
  forall T,
  forall l1 l2 : list T,
    disjoint l1 l2 <=> disjoint l2 l1.
Proof.
  sp; split; sp; apply disjoint_sym_impl; auto.
Qed.

Lemma disjoint_cons_r :
  forall T x,
  forall l1 l2 : list T,
    disjoint l1 (x :: l2)
    <=> disjoint l1 l2 # !LIn x l1.
Proof.
  unfold disjoint; sp; split; sp;
  apply_in_hyp p; allsimpl; sp; subst; sp.
Qed.

Lemma disjoint_cons_l :
  forall T x,
  forall l1 l2 : list T,
    disjoint (x :: l1) l2
    <=> disjoint l1 l2  #  !  LIn x l2.
Proof.
  intros; sp.
  trw disjoint_sym.
  trw disjoint_cons_r.
  trw disjoint_sym; split; auto.
Qed.

Lemma disjoint_iff_diff :
  forall T eq,
  forall l1 l2 : list T,
    disjoint l2 l1 <=> @diff _ eq l1 l2 = l2.
Proof.
  induction l1; simpl; sp.
  trw disjoint_cons_r.
  trw IHl1.

  sp_iff Case; intros; exrepd.

  - Case "->".
  rewrite remove_trivial; auto.

  - Case "<-".
    assert (!LIn a l2)
    by (intro i; rw <- H in i;
        allrw in_diff; sp;
        allrw in_remove; sp).
    rewrite remove_trivial in H; auto.
Qed.

Lemma disjoint_snoc_r :
  forall T,
  forall l1 l2 : list T,
  forall x : T,
    disjoint l1 (snoc l2 x)
    <=> (disjoint l1 l2  #  !  LIn x l1).
Proof.
  unfold disjoint; sp; split; intros.

  - sp; apply_in_hyp p; trw_h in_snoc p; trw_h not_over_or p; sp.
  - sp.
    allrw in_snoc; sp; subst; sp.
    apply_in_hyp p; sp.
Qed.

Lemma disjoint_snoc_l :
  forall T,
  forall l1 l2 : list T,
  forall x : T,
    disjoint (snoc l1 x) l2
    <=> (disjoint l1 l2 # !LIn x l2).
Proof.
  intros; trw disjoint_sym.
  trw disjoint_snoc_r; split; sp; trw disjoint_sym; sp.
Qed.

Lemma subset_disjoint :
  forall T,
  forall l1 l2 l3 : list T,
    subset l1 l2
    -> disjoint l2 l3
    -> disjoint l1 l3.
Proof.
  unfold subset, disjoint; intros; auto.
Qed.

Lemma disjoint_singleton_l :
  forall A (x : A) s,
    disjoint [x] s <=> ! LIn x s.
Proof.
  unfold disjoint; simpl; split; intros; auto; sp; subst; sp.
Qed.

Lemma disjoint_singleton_r :
  forall A (x : A) s,
    disjoint s [x] <=> ! LIn x s.
Proof.
  unfold disjoint; split; simpl; sp; subst; sp.
  apply_in_hyp p; sp.
Qed.

Lemma disjoint_app_l :
  forall A,
  forall l1 l2 l3 : list A,
    disjoint (l1 ++ l2) l3
    <=> (disjoint l1 l3  #  disjoint l2 l3).
Proof.
  induction l1; simpl; sp; split; sp.
  alltrewrite disjoint_cons_l;  trw_h IHl1 H; sp.
  alltrewrite disjoint_cons_l; trw_h IHl1  H; sp.
  alltrewrite disjoint_cons_l; sp.
  trw IHl1; sp.
Qed.

Lemma disjoint_app_r :
  forall A,
  forall l1 l2 l3 : list A,
    disjoint l1 (l2 ++ l3)
    <=> (disjoint l1 l2  #  disjoint l1 l3).
Proof.
  intros; trw disjoint_sym.
  trw disjoint_app_l.
  split; sp; trw disjoint_sym; sp.
Qed.

Lemma disjoint_flat_map_l :
  forall A B,
  forall f : A -> list B,
  forall l1 : list A,
  forall l2 : list B,
    disjoint (flat_map f l1) l2
    <=>
    (forall x,  LIn x l1 -> disjoint (f x) l2).
Proof.
  induction l1; simpl; sp.
  split; sp.
  trw disjoint_app_l.
  trw IHl1.
  split; sp; subst; sp.
Qed.

Lemma disjoint_flat_map_r :
  forall A B,
  forall f : A -> list B,
  forall l1 : list A,
  forall l2 : list B,
    disjoint l2 (flat_map f l1)
    <=>
    (forall x,  LIn x l1 -> disjoint l2 (f x)).
Proof.
  sp.
  rw disjoint_sym.
  rw disjoint_flat_map_l; split; sp;
  rw disjoint_sym; sp.
Qed.


Lemma disjoint_remove_l :
  forall A eq x,
  forall l1 l2 : list A,
    disjoint (@remove _ eq x l1) l2 <=> disjoint l1 (@remove _ eq x l2).
Proof.
  intros. 
  unfold disjoint.
  setoid_rewrite in_remove.
  firstorder.
Qed.

Lemma disjoint_diff_l :
  forall A eq,
  forall l1 l2 l3 : list A,
    disjoint (@diff _ eq l1 l2) l3 <=> disjoint l2 (@diff _ eq l1 l3).
Proof.
  induction l1; simpl; sp.
  trw IHl1.
  rewrite diff_remove.
  trw disjoint_remove_l. split; sp.
Qed.

Lemma length0 :
  forall T, forall l : list T,
    length l = 0 <=> l = [].
Proof.
  destruct l; simpl; sp; split; sp; inversion H.
Qed.

Lemma rev_list_indT :
  forall (A : Type) (P : list A -> [univ]),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  intros.
  assert ({n | length l = n}) as e by (exists (length l); auto); sp.
  revert l e.
  induction n; intros.
  apply length0 in e; subst; sp.
  generalize (snoc_cases A l); sp; subst; auto.
  apph (apply IHn).
  allrewrite length_snoc; allapply S_inj; auto.
Qed.

Lemma rev_list_dest :
  forall T,
  forall l : list T,
    l = [] [+] {u : list T $ {v : T $ l = snoc u v}}.
Proof.
  induction l using rev_list_indT.
  left; auto.
  right; auto.
  exists l a; auto.
Qed.

Lemma rev_list_dest2 :
  forall {T} (l : list T),
    l = [] [+] {u : list T $ {v : T $ l = snoc u v}}.
Proof.
  induction l using rev_list_indT.
  left; auto.
  right; auto.
  exists l a; auto.
Qed.

Ltac rev_list_dest l :=
  let name := fresh "or" in
  generalize (rev_list_dest2 l);
    intro name;
    destruct name;
    try exrepd;
    subst.

Lemma rev_list_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  intros.
  assert ({n : nat $ length l = n}) as p by (exists (length l); auto).
  destruct p as [n e].
  revert l e.
  induction n; intros.
  apply length0 in e; subst; sp.
  generalize (snoc_cases A l); sp; subst; auto.
  apply H0.
  apply IHn.
  allrewrite length_snoc; allapply S_inj; auto.
Qed.

Lemma combine_in_left : forall T1 T2 (l1: list T1) (l2: list T2),
 (length l1=length l2) -> forall u1, ( LIn u1 l1)  -> {u2 : T2 $ LIn (u1,u2) (combine l1 l2)}.
Proof. induction l1; intros ? Hlen ?   Hin; inverts Hin as Hin; simpl in Hlen;
  destruct l2 ; simpl in Hlen; inversion Hlen.
 -  subst.  exists t. simpl. left; auto.
 - apply IHl1 with l2 u1 in Hin; auto. parallel u2 Hcom.
   simpl. right; auto.
Qed.

Lemma combine_in_left2 : forall T1 T2 (l1: list T1) (l2: list T2),
 (length l1 <= length l2) -> forall u1, ( LIn u1 l1)  -> {u2 : T2 $ LIn (u1,u2) (combine l1 l2)}.
Proof. induction l1; intros ? Hlen ?   Hin. inverts Hin as Hin; simpl in Hlen.
  destruct l2 ; simpl in Hlen. omega. inverts Hin as Hin.
 -  subst.  exists t. simpl. left; auto.
 - apply IHl1 with l2 u1 in Hin; auto. parallel u2 Hcom.
   simpl. right; auto. omega.
Qed.

Lemma cons_as_app :
  forall T (a : T) (b : list T),
    a :: b = [a] ++ b.
Proof. sp. Qed.

Lemma length1 :
  forall T, forall l : list T,
    length l = 1 <=> {x : T $ l = [x]}.
Proof.
  destruct l; simpl; sp.
  split; sp; inversion H.
  split; sp; try (inversion H); subst.
  destruct l; simpl in H1; inversion H1.
  exists t; auto.
  invs; sp.
Qed.

Lemma snoc1 :
  forall T,
  forall a : list T,
  forall b x : T,
    snoc a b = [x] <=> a = []  #  b = x.
Proof.
  destruct a; simpl; sp; split; sp; subst; auto.
  inversion H; auto.
  inversion H; subst; auto.
  destruct a; simpl in H2; inversion H2.
  inversion H; subst; auto.
  destruct a; simpl in H2; inversion H2.
Qed.


Theorem in_single: forall T (a b : T),  LIn a [b] -> a=b.
Proof. introv H. invertsn H. auto. inversion H.
Qed.


Lemma in_list2 : forall T (x a b :T),
 ( LIn x [a,b]) -> (x=a [+]  x=b).
Proof. introv H. invertsn H. left; auto.
       invertsn H;  right; auto.
       inverts H.
Qed.

Tactic Notation "dlist2"  ident(h) :=
 apply in_list2 in h; destruct h.

Lemma in_list2_elim : forall T ( a b :T) (P: T-> Prop),
 (forall x, ( LIn x [a,b]) -> P x) -> (P a  #   P b).
Proof. introv H. split; apply H; simpl; auto.
Qed.

Lemma in_list1 :
  forall T (x a :T),
     LIn x [a] -> x = a.
Proof.
  introv H. invertsn H. auto.
  inverts H.
Qed.

Lemma in_list1_elim : forall T (x a b :T) (P: T-> Prop),
 (forall x, ( LIn x [a]) -> P x) -> (P a).
Proof. intros. apply H; simpl; auto.
Qed.

Tactic Notation "dlist" ident(l) ident(cs) "as" simple_intropattern(I) :=
 destruct l as I;
  [ Case_aux cs "nilcase"
  | Case_aux cs "conscase"
  ].

Lemma app_split :
  forall T,
  forall l1 l2 l3 l4 : list T,
    length l1 = length l3
    -> l1 ++ l2 = l3 ++ l4
    -> l1 = l3  #  l2 = l4.
Proof.
  induction l1; simpl; sp.
  destruct l3; allsimpl; auto.
  inversion H.
  destruct l3; allsimpl; auto.
  inversion H.
  destruct l3; allsimpl; auto.
  inversion H.
  inversion H0; subst.
  apply IHl1 in H3; sp; subst; auto.
  inversion H0; subst.
  destruct l3; allsimpl; auto.
  inversion H.
  inversion H0; subst.
  apply IHl1 in H4; sp; subst; auto.
Qed.
Lemma cons_eq :
  forall A a,
  forall b c : list A,
    b = c -> a :: b = a :: c.
Proof.
  sp; subst; sp.
Qed.

Lemma cons_app :
  forall T (x : T) l1 l2,
    x :: (l1 ++ l2) = (x :: l1) ++ l2.
Proof.
  sp.
Qed.

Lemma cons_snoc :
  forall T (x y : T) l,
    x :: (snoc l y) = snoc (x :: l) y.
Proof.
  sp.
Qed.

Lemma cons_inj :
  forall A (a c : A) b d,
    a :: b = c :: d -> a = c  #  b = d.
Proof.
  sp; inversion H; sp.
Qed.

Lemma in_combine :
  forall A B a b,
  forall l1 : list A,
  forall l2 : list B,
     LIn (a,b) (combine l1 l2)
    ->  LIn a l1  #   LIn b l2.
Proof.
  induction l1; introv Hlin; simpl; sp; destruct l2; allsimpl; sp;
    allapply pair_inj; repnd; subst; sp; apply_in_hyp p; sp.
Qed.

Lemma implies_in_combine :
  forall A B (l1 : list A) (l2 : list B) x,
    length l1 = length l2
    ->  LIn x l1
    -> {y : B $ LIn (x, y) (combine l1 l2)}.
Proof.
  induction l1; simpl; sp; destruct l2; allsimpl; subst; sp;
  invertsn H.
  exists b; sp.
  apply IHl1  with(x:=x) in H; sp.
  exists y; sp.
Qed.

Lemma in_repeat : forall T n (u t:T),  LIn u (repeat t n) -> u=t.
Proof. induction n; introv H; simpl. inverts H.
 simpl in H. destruct H; auto.
Qed.

Lemma combine_app_eq: forall A B (l1:list A) (l21 l22: list B),
 length l1 <= length l21 -> combine l1 l21 = combine l1 (l21 ++ l22).
Proof. induction l1;
 intros ? ? Hle; simpl; auto.
 destruct l21; simpl. inverts Hle.
 rewrite <- IHl1; allsimpl; try omega; auto.
Qed.

Lemma combine_nil :
  forall A B (l : list A),
    combine l (@nil B) = nil.
Proof.
  induction l; simpl; auto.
Qed.

Hint Rewrite combine_nil.

Lemma firstn_nil:
  forall n T , firstn n nil = @nil T.
Proof.
  induction n; intros; simpl; auto.
Qed.

Hint Rewrite firstn_nil.

Lemma app_eq_nil_iff :
  forall T (l1 l2 : list T),
    l1 ++ l2 = [] <=> (l1 = []  #  l2 = []).
Proof.
  sp; split; sp; subst; sp; destruct l1; destruct l2; allsimpl; sp.
Qed.

Lemma combine_app_app :
  forall A B (l1:list A) (l21 l22: list B),
    length l21 <= length l1
    -> combine l1 (l21 ++ l22) =
       combine l1 l21
               ++
               combine (skipn (length l21) l1) (firstn  (length l1-length l21) l22).
Proof.
  induction l1; intros ? ? Hle. inverts Hle. trw_h length0  H0. subst.
  simpl. auto.
  simpl. destruct l21; destruct l22; simpl; auto; try omega.
  - fold (app nil l22). rewrite IHl1. rewrite combine_nil. simpl.
    assert (length l1 - 0 =length l1) as Hmin by omega. rewrite Hmin. auto.
    simpl. omega.
  - rewrite app_nil_r. rewrite firstn_nil. rewrite combine_nil. rewrite app_nil_r. auto.
  - simpl in Hle. simpl. rewrite  IHl1; auto; omega.
Qed.

Lemma in_firstn : forall T n a (l: list T),
 n>0 ->  LIn a (firstn n l) ->  LIn a l.
Proof. induction n;  intros ? ? Hgt Hin.
 inverts Hin. destruct l. inverts Hin.
 simpl in Hin. dorn Hin. left; auto.
 right; auto. destruct n. inverts Hin. apply IHn; auto. omega.
Qed.

(* Counter-example: al = [0;1], a = 1, n = 1, t = 0, then ( LIn 1 al) is true
 * but  LIn (1,0) (combine al (repeat n t)) is  LIn (1,0) [(0,0)] is false.
 * It is true if length al = n though. *)
Lemma false_in_combine_repeat :
  forall A B (al : list A) (t : B) n,
    n > 0
    -> forall a,  LIn a al ->  LIn (a,t) (combine al (repeat t n)).
Abort.

Lemma in_combine_repeat :
  forall A B (al : list A) (t : B) n,
    length al <= n
    -> forall a,  LIn a al ->  LIn (a,t) (combine al (repeat t n)).
Proof.
  induction al; simpl; sp; subst; destruct n; try omega;
  allapply S_le_inj; simpl; sp.
Qed.

Lemma length_filter :
  forall T f (l : list T),
    length (filter f l) <= length l.
Proof.
  induction l; simpl; sp.
  destruct (f a); simpl; omega.
Qed.

Lemma filter_snoc :
  forall T f (l : list T) x,
    filter f (snoc l x)
    = if f x then snoc (filter f l) x else filter f l.
Proof.
  induction l; simpl; sp.
  destruct (f a); simpl; rewrite IHl; destruct (f x); sp.
Qed.

Theorem eq_list
     : forall (A : Type) (x : A) (l1 l2 : list A),
       l1 = l2 <=>
       length l1 = length l2  #  (forall n : nat, nth n l1 x = nth n l2 x).
Proof.
  intros. apply eq_lists.
Qed.

Theorem nat_compare_dec: forall m n, (n < m [+]  m <= n ).
Proof. induction m. destruct n. right. auto. 
    right. omega. intros.  destruct (IHm n); 
    destruct (eq_nat_dec n m); subst;
    try( left; omega);    
    try( right; omega).    
Qed. 

Theorem eq_list2
     : forall (A : Type) (x : A) (l1 l2 : list A),
       l1 = l2 <=>
       length l1 = length l2  #  (forall n : nat, n<length l1 -> nth n l1 x = nth n l2 x).
Proof.
  intros. split ; introv H. 
  eapply eq_list  in H. repnd. split; auto.
  repnd. eapply  eq_list; split; eauto.
  intros. assert (n < length l1 \/  length l1 <= n ) as Hdic by omega.
  destruct Hdic. apply H; auto. repeat (rewrite nth_overflow ); auto.
  rewrite <- H0; auto.
Qed.

Lemma singleton_as_snoc :
  forall T (x : T),
    [x] = snoc [] x.
Proof.
  sp.
Qed.

Theorem map_eq_length_eq :
  forall A B (f g : A -> B) la1 la2,
    map f la1 = map g la2
    -> length la1 = length la2.
Proof.
   introv Hmap. apply (apply_eq (@length B)) in Hmap.
   repeat (rewrite map_length in Hmap); trivial.
Qed.

Theorem  nth2 : forall {A:Type} (l:list A) (n:nat) (ev: n < length l) , A .
Proof. induction l; simpl. intros. provefalse.
 inversion ev.
  intros.
  destruct (eq_nat_dec n 0). subst.
  exact a.
  apply IHl with (n:=(n-1)).
  destruct n. destruct n0. reflexivity.
  omega.
Qed.

Theorem  nth3 : forall {A:Type} (l:list A) (n:nat) (ev: n < length l) , {x:A | nth n l x =x} .
Proof. induction l; simpl. intros. provefalse.
 inversion ev.
  intros.
  destruct n . subst.
  exact (exist (eq a) a eq_refl ).
  apply IHl with (n:=(n)).
  omega.
Qed.


Definition eq_set {A} (l1 l2: list A) := subset l1 l2  #  subset l2 l1.
Definition eq_set2 {A} (l1 l2: list A) := forall a ,  LIn a l1 <=>  LIn a l2.

Theorem eq_set_iff_eq_set2 :
  forall {A} (l1 l2: list A),
    eq_set l1 l2 <=> eq_set2 l1 l2.
Proof.
  unfold eq_set, eq_set2, subset.
  repeat(split;sp); apply_hyp; auto.
Qed.

Theorem eq_set_refl : forall {A} (l: list A) , eq_set l l.
Proof. split; apply subset_refl.
Qed.

Theorem eq_set_refl2: forall (A : Type) (l1 l2 : list A), (l1=l2) -> eq_set l1 l2.
Proof. intros. rewrite H. apply eq_set_refl.
Qed.

Theorem eq_set_empty :
  forall {A} (l1 l2: list A),
    eq_set l1 l2
    -> l1 = []
    -> l2 = [].
Proof.
  introv Heqs Heql. apply null_iff_nil. introv v. apply eq_set_iff_eq_set2 in Heqs.
  apply Heqs in v. subst. inverts v.
Qed.

Theorem nth2_equiv :
  forall (A:Type) (l:list A) (n:nat) (def:A)
         (ev: n < length l),
    (nth n l def) = nth2 l n ev.
Abort.

Theorem len_flat_map: forall {A B} (f:A->list B)  (l: list A),
    length (flat_map f l) = addl (map (fun x => length (f x)) l) .
Proof. induction l; auto. simpl. rewrite length_app. f_equal. auto.
Qed.

(** renaming due to some name clash
Lemma rev_list_ind2 :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  intros.
  assert (texists n, length l = n) by (exists(length l); auto); sp.
  revert l H1.
  induction n; intros.
  destruct l; simpl in H1; auto; inversion H1.
  assert (l = [] [+] exists(a : A), exists(k : list A), l = snoc k a) by apply snoc_cases.
  sp; subst; auto.
  apply H0.
  apply IHn.
  rewrite length_snoc in H1; inversion H1; auto.
Qed.
*)
Notation no_repeats := NoDup (only parsing).


Theorem last_snoc: forall A (l:list A) (a d:A) ,
  nth (length l) (snoc l a) d= a.
Proof. 
    induction l ; introv . refl. 
    rewrite snoc_as_append. rewrite app_nth2. 
    simpl. asserts_rewrite (length l - length l=0); try omega. 
    auto. omega. 
Qed. 

Theorem eq_maps2:
  forall (A B C: Type) (f : A -> B) (g  : C -> B) (la : list A) (lc : list C) defa defc,
  length la = length lc
  -> (forall n ,  n < length la -> f  (nth n la defa) = g ( nth  n lc defc)) 
  -> map f la = map g lc.
Proof. induction la using rev_list_ind; introv Hleq Hp. 
  invertsn Hleq. symmetry in Hleq. rw length0 in Hleq. subst. 
  reflexivity. allrewrite snoc_as_append. rewrite map_app. 
  rewrite length_app in Hleq. allsimpl. rev_list_dest lc. invertsn Hleq. 
  omega. allrewrite snoc_as_append. rewrite map_app. allsimpl. 
  rewrite length_app in Hleq. allsimpl. 
  assert (length la = length u) as Hleq1 by omega.
  f_equal. eapply IHla; eauto. 
  intros. assert (n < length (la++[a])) as Hla. rewrite length_app. 
  omega. apply Hp in Hla. 
  rewrite app_nth1 in Hla; auto.  rewrite app_nth1 in Hla; auto.
  eauto. rewrite <- Hleq1; auto. 
  instlemma (Hp (length la)) as Hle.
  rewrite <- snoc_as_append in Hle. 
  rewrite <- snoc_as_append in Hle. 
  rewrite last_snoc in Hle. 
  rewrite Hleq1 in Hle. 
  rewrite last_snoc in Hle. 
  f_equal; auto. apply Hle. 
  rewrite <- Hleq1. 
  rewrite length_snoc; omega. 
Qed.


(**generalized map where the mapping function takes
  evidence of elements being in the list *)
Lemma gmap:  forall {A B : Type} (l: list A) (f : forall a, LIn a l -> B),
    list B.
Proof. induction l as [| a  l maprec]; introv f. exact nil.
   pose proof f a as Hb. lapply Hb;[ intro b | left; auto].
   assert ( forall a0 : A, LIn a0 (l) -> B) as frec. introv Hin.
   eapply f. right. eauto.
   pose proof (maprec frec) as brec.
   exact (b::brec).
Defined.

Lemma map_gmap_eq : forall {A B : Type} (l: list A) 
  (f : forall a, LIn a l -> B) (g: A->B),
  (forall a (p: LIn a l), f a p = g a)
   -> map g l = gmap l f. 
Proof. induction l as [| a l Hind]; introv Heq;[reflexivity | ]. 
  simpl. f_equal. rewrite Heq. reflexivity. 
  apply Hind. intros. rewrite Heq; reflexivity. 
Qed.

Fixpoint appl {A: Type} (l: list (list A)) : list A :=
 match l with
 | [] => []
 | h::t => h ++ appl t
 end.

Theorem flat_map_as_appl_map:
 forall {A B:Type} (f: A->list B) (l : list A),
   flat_map f l = appl (map f l).
Proof.
 induction l; auto. 
 simpl. rw IHl; auto. 
Qed.

Lemma gmap_length : forall (A B : Type) (l : list A)
  (f:(forall a : A, LIn a l -> B)),
    length (gmap l f)= length l.
Proof.
  induction l; auto.
  intros. simpl. f_equal.
  rewrite IHl; auto.
Qed.

Lemma map_eq_injective:  forall {A B: Type} (f: A->B) (pinj: injective_fun f)
  (lvi lvo: list A),
  map f lvi = map f lvo -> lvi = lvo.
Proof.
  induction lvi as [| vi lvi Hind]; introv Hm; destruct lvo; (try invertsn Hm); auto.
  apply pinj in Hm. f_equal; auto.
Qed.

Tactic Notation "cases_if_sum"  simple_intropattern(newname) :=
  cases_if; clears_last;
   let H:= get_last_hyp tt in rename H into newname.

Lemma map_remove_commute: forall {A B : Type} (eqa : Deq A)
(eqb : Deq B) (f: A->B) (r: A) (lvi: list A) (fi : injective_fun f),
  map f (@remove _ eqa r lvi)
  = @remove _ eqb (f r) (map f lvi).
Proof.
  intros. induction lvi; auto.
 simpl. symmetry. repeat rewrite decide_decideP. simpl.
  cases_if as Ha; cases_if as Hb; subst; sp.
 - apply fi in Ha. subst; sp.
 - simpl. f_equal; auto.
Qed.

Lemma map_diff_commute: forall {A B : Type} (eqa : Deq A)
(eqb : Deq B) (f: A->B) (lvr lvi: list A) (fi : injective_fun f),
  map f (@diff _ eqa lvr lvi)
  = @diff _ eqb (map f lvr) (map f lvi).
Proof.
  induction lvr as [| ? lvr IHlvr]; intros; try(repeat (rewrite diff_nil)); auto;[].
  simpl. rewrite IHlvr; auto.  f_equal; auto.
  apply map_remove_commute; auto.
Qed.

Lemma memberb_din :
  forall (S T : Type)
         (deq : Deq S)
         (v : S)
         (lv : list S)
         (ct cf : T),
    (if memberb deq v lv then ct else cf)
    = (if in_deq _ deq v lv then ct else cf).
Proof.
  intros. cases_if  as Hb; auto; cases_if_sum Hd ; auto; subst.
  apply assert_memberb in Hb. sp.
  rw <- (@assert_memberb S deq) in Hd.
  rewrite Hd in Hb.
  sp.
Qed.

Theorem fst_split_as_map: forall {A B :Type} (sub : list (A * B)),
    fst (split sub) = map (fun p=> fst p) sub.
Proof.
  intros. induction sub as [| vt sub Hind]; auto.
  simpl. destruct vt as [v t].
  simpl. destruct (split sub). allsimpl.
  f_equal. auto.
Qed.

Theorem snd_split_as_map: forall {A B :Type} (sub : list (A * B)),
    snd (split sub) = map (fun p=> snd p) sub.
Proof.
  intros. induction sub as [| vt sub Hind]; auto.
  simpl. destruct vt as [v t].
  simpl. destruct (split sub). allsimpl.
  f_equal. auto.
Qed.

Lemma combine_in_right : forall T1 T2 (l2: list T2) (l1: list T1),
 (length l2 <= length l1) 
  -> forall u2, ( LIn u2 l2) 
  -> {u1 : T1 $ LIn (u1,u2) (combine l1 l2)}.
Proof. induction l2; intros ? Hlen ?   Hin. inverts Hin as Hin; 
  simpl in Hlen.
  destruct l1 ; simpl in Hlen. omega. inverts Hin as Hin.
 -  subst.  exists t. simpl. left; auto.
 - apply IHl2 with l1 u2 in Hin; auto. parallel u Hcom.
   simpl. right; auto. omega.
Qed.

(** nth_error was aleady in the library. *)
Definition select {A:Type} (n:nat) (l:list A): option A  :=
nth_error l n.

Lemma nth_select1: forall {A:Type} (n:nat) (l:list A)  (def: A),
  n < length l -> select  n l= Some (nth n l def).
Proof.
  induction n as [|n Hind]; introv Hl; destruct l;try (inverts Hl;fail); simpl; auto.
  allsimpl. erewrite Hind; eauto. omega.
Qed.

Lemma nth_select2: forall {A:Type} (n:nat) (l:list A) ,
  n >= length l <=> select  n l= None.
Proof.
  induction n as [|n Hind];  destruct l; allsimpl; try (split;sp;omega;fail).
  split;intro H.
  apply Hind; auto. omega.
  apply Hind in H; auto. omega. 
Qed.
  
Lemma first_index {A: Type} (l: list A) (a:A) (deq : Deq A): 
  {n:nat $ n < length l # nth n l a= a #(forall m, m<n -> nth m l a <>a)}
     [+] (! (LIn a l)).
Proof.
  induction l as [| h l Hind]; [right;sp;fail|].
  destruct (decideP (h=a)); subst; allsimpl;[left ; exists 0; sp; omega | ].
  dorn Hind. 
  + exrepnd. left. exists (S n0). split; auto; try omega; split; auto.
     introv Hlt. destruct m; auto. apply Hind0; omega.
  + right. intro Hc; sp.
Defined.

Lemma split_length_eq: forall {A B :Type} (sub : list (A * B)),
  let (la,lb):= split sub in
    length la=length lb # length la= length sub.
Proof.
  intros. destructr (split sub) as [la lb].
  assert(la=fst (la,lb)) as h99 by (simpl;auto).
  rewrite h99. rewrite HeqHdeq. rewrite split_length_l. clear h99.
  assert(lb=snd (la,lb)) as h99 by (simpl;auto).
  rewrite h99. rewrite HeqHdeq. rewrite split_length_r.
  sp.
Qed.


Ltac disjoint_reasoning :=
match goal with
| [  |- disjoint _ (_ ++ _) ] => apply disjoint_app_r;split
| [  |- disjoint (_ ++ _) _ ] => apply disjoint_app_l;split
| [  |- disjoint _ (_ :: _) ] => apply disjoint_cons_r;split
| [  |- disjoint (_ :: _) _ ] => apply disjoint_cons_l;split
| [  |- disjoint _ _ ] => (sp;fail  || apply disjoint_sym; sp;fail)
(** important to leave it the way it was .. so that repeat progress won't loop*)
| [ H: disjoint _ (_ ++ _) |- _ ] => apply disjoint_app_r in H;sp
| [ H: disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H;sp
| [ H: disjoint _ (_ :: _) |- _ ] => apply disjoint_cons_r in H;sp
| [ H: disjoint (_ :: _) _ |- _ ] => apply disjoint_cons_l in H;sp
| [ H: !(disjoint  _ []) |- _ ] => provefalse; apply H; apply disjoint_nil_r
| [ H: !(disjoint  [] _) |- _ ] => provefalse; apply H; apply disjoint_nil_l
| [ H: (disjoint  _ []) |- _ ] => clear H
| [ H: (disjoint  [] _) |- _ ] => clear H
end.


Lemma select_lt : forall {A:Type} (l: list A) (a:A) n,
  select n l = Some a -> n < length l.
Proof.
  introv Heq. 
  assert (n<length l \/ n>=length l ) as XX by omega.
  dorn XX; auto. apply nth_select2 in XX. rewrite XX in Heq.
  inverts Heq.
Qed.

Lemma select_in : forall {A:Type} (l: list A) (a:A) n,
  select n l = Some a -> LIn a l.
Proof.
  introv Heq. duplicate Heq. apply select_lt in Heq.
  pose proof (nth_select1 _ _ a Heq) as XX.
  rewrite XX in Heq0. invertsn Heq0.
  pose proof (nth_in _ _ l a Heq) as XXX.
  auto.
Qed.

Lemma no_repeats_index_unique: forall {T:Type} 
  (a:T) (n1 n2:nat) (l:list T),
  no_repeats l
  -> select n1 l = Some a
  -> select n2 l = Some a
  -> n1 = n2.
Proof.
  induction n1 as [| n1 Hind]; introv Hnr H1s H2s; auto; destruct l as [| h l].

  inverts H1s.

  allsimpl. inverts Hnr. destruct n2; auto.
  allsimpl. invertsn H1s.
  apply select_in in H2s. sp.

  destruct n2; inverts H2s.

  allsimpl. destruct n2.
  inverts H2s. inverts Hnr. apply select_in in H1s. sp.
  f_equal. allsimpl. 
  apply Hind with (l:=l); eauto.
  inverts Hnr; auto.
Qed.
  
Lemma nth_select3:
  forall (A : Type) (n : nat) (l : list A) (a def : A),
  n < length l
  -> (nth n l def) =a
  ->  select n l = Some a.
Proof.
  introv K1 K2.
  pose proof (nth_select1  n l def K1).
  congruence.
Qed.


Lemma no_repeats_index_unique2: forall {T:Type} (l:list T)
  (a:T) (n1 n2:nat) (def1 def2: T),
  no_repeats l
  ->  n1 < length l
  ->  n2 < length l
  -> (nth n1 l def1 =a)
  -> (nth n2 l def2 =a)
  -> n1 = n2.
Proof.
  introv K1 K2 K3 K4 K5.
  apply nth_select3 in K4; auto.
  apply nth_select3 in K5; auto.
  pose proof (no_repeats_index_unique _ _ _ _ K1 K4 K5). trivial.
Qed.


Lemma length_combine_eq : forall {A B: Type} (la:list A) (lb: list B), 
  length la =length lb
  -> length (combine la lb) = length la.
Proof.
  introv XX. rewrite combine_length.
  rewrite XX. apply Min.min_idempotent.
Qed.

Lemma nth_in2:
  forall (A : Type) (n : nat) (l : list A) (a d : A),
  n < length l -> (nth n l d) = a -> LIn a l.
Proof.
  introns XX. pose proof (nth_in _ n l d XX) as XY. congruence.
Qed.

Definition not_in_prefix {A: Type} (la : list A) (a:A) (n:nat) :=
               (forall m : nat,
                     m < n -> nth m la a <> a).

  
 Definition lforall {A:Type} (P: A-> [univ]) (l:list A) :=
  forall a:A, LIn a l -> P a.

Lemma implies_lforall : forall {A:Type} (P Q: A->[univ]),
  (forall (a b :A), P a -> Q a)
   -> forall l,  lforall P l-> lforall Q l.
Proof.
  unfold lforall. sp.
Defined.

Lemma lforall_subset : forall {A:Type} (P: A->[univ]) (la lb : list A),
 subset la lb
 -> lforall P lb
 -> lforall P la.
Proof.
  unfold lforall, subset.
  firstorder.
Qed.

(* for an application, see alphaeq.change_bvars_alpha_spec_varclass *)
Lemma lforall_flatmap : forall {A B :Type} (P: B->[univ]) (fa fb : A -> list B) (la: list A),
 (forall a, LIn a la -> lforall P (fa a) -> lforall P (fb a) )
 -> lforall P (flat_map fa la)
 -> lforall P (flat_map fb la).
Proof.
  unfold lforall, subset.
  setoid_rewrite in_flat_map.
  intros.
  firstorder.
  eauto.
Qed.

Lemma  lforallApp : forall {A:Type} (lv1 lv2 :list A) P,
lforall P (lv1++lv2)
<-> ((lforall P lv1) # (lforall P lv2)).
Proof using.
  unfold lforall.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma combine_eq : forall {A B: Type} 
  (l1a l2a: list A) (l1b l2b: list B),
  combine l1a l1b = combine l2a l2b
  -> length l1a = length l1b
  -> length l2a = length l2b
  -> l1a=l2a # l1b=l2b.
Proof.
  induction l1a as [|a1 l1a Hind]; auto; introv Hc He1 He2;
  allsimpl; destruct l1b; destruct l2b; destruct l2a;  
   try(invertsn He1); try(invertsn He2); allsimpl; try(invertsn Hc); auto.
  pose proof (Hind _ _ _ Hc He1 He2) as Xr. repnd.
  rewrite Xr. rewrite Xr0; split; sp.
Qed.

Definition binrel_list {T}
           (def : T)
           (R : @bin_rel T)
           (tls trs : list T) : [univ] :=
  length tls = length trs
  # (forall (n : nat),
       n < length tls
       -> R (nth n tls def) (nth n trs def)).

Lemma length2 :
  forall (T : Type) (l : list T),
    length l = 2 -> {x, y : T $ l = [x,y]}.
Proof.
  introv Hl. destruct l; try(destruct l); try(destruct l); inverts Hl.
  eexists; eauto.
Qed.

Lemma length3 :
  forall (T : Type) (l : list T),
    length l = 3 -> {x, y, z : T $ l = [x,y,z]}.
Proof.
  introv Hl. destruct l; try(destruct l); try(destruct l);  try(destruct l); inverts Hl.
  repeat(eexists); eauto.
Qed.

Lemma length4 :
  forall (T : Type) (l : list T),
    length l = 4 -> {x, y, z , u : T $ l = [x,y,z,u]}.
Proof.
  introv Hl. destruct l; try(destruct l); try(destruct l);
      try(destruct l);  try(destruct l);  inverts Hl.
  repeat(eexists); eauto.
Qed.

Definition is_first_index {T:Type} (l: list T) (t:T) (n:nat) :=
  n< length l # nth n l t = t # not_in_prefix l t n.
 
Lemma is_first_index_unique : forall {T:Type} (l: list T) (t:T) (n1 n2 :nat),
  is_first_index l t n1
  -> is_first_index l t n2
  -> n1 = n2.
Proof.
  unfold is_first_index, not_in_prefix. introv s1s s3s.
  repnd.
  assert (n1<n2 \/ n1=n2 \/ n2<n1) as Htri by omega.
  (dorn Htri);[|(dorn Htri)]; sp;
  try (apply s1s in Htri); sp;
  try (apply s3s in Htri); sp.
Qed.

Lemma disjoint_app_lr : forall {A:Type} (l1 l2 r1 r2 : list A),
  disjoint (l1 ++ l2) (r1 ++ r2)
    <=>
  (disjoint l1 r1 # disjoint l1 r2) # disjoint l2 r1 # disjoint l2 r2.
Proof.
   introv. rw disjoint_app_l. rw disjoint_app_r.
    rw disjoint_app_r. apply t_iff_refl.
Qed.

Lemma dec_disjoint :
  forall {T:Type} (deqt: Deq T) (la lb: list T),
    disjoint la lb + (!disjoint la lb).
Proof.
  induction la as [|a la IHla]; sp.
  simpl. destruct (IHla lb) as [dd|nd];[|right].
  - destruct (in_deq T deqt a lb);[right|left];sp;disjoint_reasoning;sp.
  - sp. apply nd. disjoint_reasoning; sp.
Defined.

Ltac simpl_list :=
  match goal with
    | [ H : context[length (map _ _)] |- _] => rewrite map_length in H
    | [ |-  context[length (map _ _)] ] => rewrite map_length
    | [ H : LIn ?x [?h] |- _ ] => apply in_single in H; subst
  end.

Lemma bin_rel_list_refl :
  forall {T} (R: bin_rel T) (def:T),
    refl_rel R -> refl_rel (binrel_list def R).
Proof.
  introv HR. intro l. split; sp.
Qed.

Lemma pairInProofsCons :
  forall {A:Type} (l: list A) (h:A),
    {a: A $ LIn a l}
    -> {a: A $ LIn a (h::l)}.
Proof.
  introv ph. exrepnd.
  exists a.
  right. trivial.
Defined.

Lemma pairInProofs: forall {A:Type} (l: list A) , list {a: A $ LIn a l}.
Proof.
  induction l as [| a l Hind];[exact []|].
  pose proof (map (pairInProofsCons l a) Hind) as Hind'.
  exact (exI(a,injL(eq_refl a))::Hind').
Defined.

Theorem in_single_iff: forall T (a b : T),  LIn a [b] <=> a=b.
Proof. split.
  - introv H. invertsn H. auto. inversion H.
  - introv H. constructor. sp.
Qed.

Lemma lin_lift: forall {A B:Type} (a:A) (lv: list A) (f:A->B),
  LIn a lv ->  LIn (f a) (map f lv).
Proof.
  induction lv as [| v lv Hind] ; [sp | ]; introv Hin. simpl.
  dorn Hin;subst;spc.
Qed.

Lemma flat_map_app:
  forall (A B : Type) (f : A -> list B) (l l' : list A),
  flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.
Proof.
  induction l as [| a l Hind]; introv;sp.
  simpl. rw <- app_assoc.
  f_equal. sp.
Qed.

Hint Resolve deq_list.

Ltac get_element_type listtype :=
match listtype with
list ?T => T
end.

Ltac apply_length  H :=
  match goal with
      [ H: (?l = ?r) |- _ ] =>
      let T:= (type of l) in
      let Tin := get_element_type T in
      let Hn := fresh H "len" in
      apply_eq (@length Tin) H Hn; try (rw map_length in Hn)
  end.

Lemma filter_app :
  forall T f (l1 l2 : list T),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; simpl; sp.
  rw IHl1.
  destruct (f a); sp.
Qed.

Lemma subset_singleton_r :
  forall T (l : list T) x,
    subset l [x] <=> forall y, LIn y l -> y = x.
Proof.
  unfold subset; introv; simpl; split; sp; apply_in_hyp p; sp.
Qed.

Lemma split_eta :
  forall A B (l : list (A * B)),
    split l = (fst (split l), snd (split l)).
Proof.
  induction l; simpl; sp.
  rw IHl; simpl; sp.
Qed.

Lemma split_cons :
  forall A B a b (l : list (A * B)),
    split ((a, b) :: l) = (a :: fst (split l), b :: (snd (split l))).
Proof.
  simpl; sp.
  rw split_eta; simpl; sp.
Qed.

Lemma simpl_fst :
  forall A B (a : A) (b : B), fst (a, b) = a.
Proof. sp. Qed.

Fixpoint gmapd {A B : Type} (l : list A) : (forall a, LIn a l -> B) -> list B :=
  match l with
    | [] => fun f => []
    | x :: xs =>
      fun (f : forall a, LIn a (x::xs) -> B) =>
        (f x (injL(eq_refl))) :: gmapd xs (fun a i => f a (injR(i)))
  end.

Lemma gmap_eq_d :
  forall A B (l : list A) (f : forall a : A, LIn a l -> B),
    gmap l f = gmapd l f.
Proof.
  induction l; simpl; sp.
  rw IHl; sp.
Qed.

Lemma eq_gmaps :
  forall A B,
  forall l : list A,
  forall f g : (forall a : A, LIn a l -> B),
    (forall a (i : LIn a l), f a i = g a i)
    -> gmap l f = gmap l g.
Proof.
  induction l; simpl; sp.
  generalize (H a (injL(eq_refl))); intro e.
  rewrite e.
  apply cons_eq; sp.
Qed.

Lemma eq_gmapds :
  forall A B,
  forall l : list A,
  forall f g : (forall a : A, LIn a l -> B),
    (forall a (i : LIn a l), f a i = g a i)
    -> gmapd l f = gmapd l g.
Proof.
  intros.
  repeat (rw <- gmap_eq_d).
  apply eq_gmaps; sp.
Qed.

Lemma combine_cons :
  forall A B (x : A) (y : B) l k,
    combine (x :: l) (y :: k) = (x, y) :: combine l k.
Proof. sp. Qed.

Lemma map_cons :
  forall A B (x : A) (f : A -> B) l,
    map f (x :: l) = (f x) :: map f l.
Proof. sp. Qed.

Lemma Lin_eauto1 : forall {T:Type} (a:T) (l: list T),
  LIn a (a::l).
Proof.
  intros. simpl. left; sp.
Qed.

Lemma Lin_eauto2 : forall {T:Type} (a b:T) (l: list T),
  LIn b l -> LIn b (a::l).
Proof.
  intros. simpl. right; sp.
Qed.

Hint Resolve Lin_eauto1 Lin_eauto2 : slow.

Ltac disjoint_lin_contra :=
    match goal with 
    [ H1 : LIn ?t ?lv1 , H2 : LIn ?t ?lv2, H3 : (disjoint ?lv1 ?lv2) |- _ ]
      => apply H3 in H1; sp ; fail
  |  [ H1 : LIn ?t ?lv1 , H2 : LIn ?t ?lv2, H3 : (disjoint ?lv2 ?lv1) |- _ ]
      => apply H3 in H1; sp ;fail
     end.

Lemma in_nth3 :
  forall T a def (l:list T),
     LIn a l
    -> {n : nat $ (n < length l) # a = nth n l def}.
Proof.
  introv Hin. apply in_nth in Hin.
  exrepnd.
  exists n.
  dands; sp.
  rewrite nth_indep with (d':=a); sp.
Qed.

Lemma le_binrel_list_un : forall {T:Type} (def : T) 
   (R: @bin_rel T) (Rul Rur: T -> [univ]),
   le_bin_rel R (indep_bin_rel Rul Rur) 
   -> forall (la lb : list T), binrel_list def R la lb
          -> (forall x:T , LIn x la -> Rul x) # (forall x:T , LIn x lb -> Rur x).
Proof.
  introv Hle Hb. repnud Hle. repnud Hb. unfold indep_bin_rel in Hle.
  split;
  introv Hin; apply in_nth3 with (def:=def) in Hin; exrepnd;
    subst; dimp (Hb n); spc;
    apply Hle in hyp; sp.
Qed.

Lemma binrel_list_nil : forall {T : Type } R (def :T ), binrel_list def R nil nil.
Proof.
  introv. split;[sp | introv Hlt; simpl in Hlt; omega].
Qed.

Tactic Notation "spcf" :=
  try(spc;fail).

Lemma binrel_list_cons : forall {T : Type} R (def a b :T ) ta tb,
   (binrel_list def R ta tb # R a b)
   <=> (binrel_list def R (a::ta) (b :: tb)).
Proof.
  split; introv hyp; unfold binrel_list in hyp; unfold binrel_list.
  - repnd. 
    simpl. dands;spcf;[]. introv Hlt. destruct n; spc.
    dimp (hyp0 n); spc; omega.
  - allsimpl. repnd. dands ;spcf.
    + introv Hlt. dimp (hyp (S n));sp; omega.
    + dimp (hyp 0); spc; omega.
Qed.

Lemma in_combine_left_eauto :
  forall (A B : Type) a b,
  forall l1 : list A,
  forall l2 : list B,
     LIn (a,b) (combine l1 l2)
    ->  LIn a l1.
Proof.
  introv Hin. apply in_combine in Hin; spc.
Qed.
Ltac in_reasoning :=
match goal with 
| [ H : context [LIn _ [_]] |- _] => trw_h in_single_iff  H
| [ H : LIn _ (_::_) |- _ ] => simpl in H
| [ H : LIn _ (_++_) |- _ ] => apply in_app_iff
| [ H : _ [+] _ |- _] => destruct H as [H | H]
end.

Lemma in_combine_right_eauto :
  forall (A B : Type) a b,
  forall l1 : list A,
  forall l2 : list B,
     LIn (a,b) (combine l1 l2)
    ->  LIn b l2.
Proof.
  introv Hin. apply in_combine in Hin; spc.
Qed.

Ltac dLin_hyp :=
  repeat
   match goal with
   | H:forall x : ?T, ?L = x \/ ?R -> ?C
     |- _ =>
         let Hyp := fresh "Hyp" in
         pose proof (H L (or_introl eq_refl)) as Hyp; specialize (fun x y => H x (or_intror y))
   | H:forall x y, _ = _ \/ ?R -> ?C
     |- _ =>
         let Hyp := fresh "Hyp" in
         pose proof (H _ _ (or_introl eq_refl)) as Hyp; specialize
          (fun x z y => H x z (or_intror y))
   | H:forall x : ?T, False -> _ |- _ => clear H
   end.
   
   
Ltac dlist_len_name ll name :=
repeat match goal with
[  H : length ll  = _ |- _ ]=> symmetry in H 
|[ H :  0 = length ll |- _ ]  => destruct ll; inversion H
|[ H :  S _ = length ll |- _ ]  => 
    let ename:= fresh name in
    destruct ll as [| ename ll]; simpl in H; inverts H
|[ H :  0 = length [] |- _ ]  => clear H
end.

Ltac dlist_len ll := dlist_len_name ll ll.

Ltac dlists_len :=
repeat match goal with
|[ H :  0 = length ?ll |- _ ]  => dlist_len ll
|[ H :  S _ = length ?ll |- _ ]  => dlist_len ll
end.

Hint Resolve in_combine_left_eauto : slow.
Hint Resolve in_combine_right_eauto : slow.

Ltac destFind := match goal with
   [  |- context[find ?s ?v]] => 
  let sns := fresh v "s" in
  remember (find s v) as sn;
  let H := get_last_hyp tt in
  let H' := fresh H "l" in
  (destruct sn as [sns |];
  symmetry in H;
  try (pose proof (@find_some _ _ _ _  H) as H');
  try (pose proof (@find_none _ _ _  H) as H'))
  end.

Lemma no_repeats_as_disjoint : forall {A} (h:A) t,
  no_repeats (h::t)
  -> disjoint [h] t /\ no_repeats t.
Proof.
  intros ? ? ? Hnr.
  inverts Hnr.
  split; auto.
  intros ?. rewrite in_single_iff. intro H.
  subst. assumption.
Qed.

Lemma repeat_map_len : forall A B (b:B) (vs: list A) ,
  map (fun _ => b) vs = repeat b  (Datatypes.length vs).
Proof.
  induction vs; auto; simpl; f_equal; auto.
Qed.

Lemma map_eq_repeat_implies : forall A B (b:B) f (vs: list A) n,
  map f vs = repeat b n
  -> forall v, LIn v vs -> f v = b.
Proof.
  induction vs; intros; [simpl in *; tauto|].
  applydup (f_equal  (@length B)) in H.
  rewrite repeat_length in H1.
  simpl in *. destruct n;[omega|].
  simpl in *. inverts H. in_reasoning; subst; eauto.
Qed.

Lemma list_find_same_compose {A B: Type} (f : A -> bool) 
  (h : A -> B) (g : B -> bool) :
(forall a, (compose g h) a = f a)
-> forall (s1 def: A) (l1 l2: list A) ,
  (map h l1 = map h l2)
  -> find f l1 = Some s1
  -> exists n, n < length l2 /\ find f l2 = Some (nth n l2 def)
      /\ s1 = nth n l1 def /\ f s1 = true /\ f (nth n l2 def) = true.
Proof.
  intros Hc ? ? ?.
  induction l1 as [|h1 t1]; intros ? Hm Hf;
    destruct l2 as [|h2 t2]; inverts Hm as Hm;[inverts Hf|].
  specialize (IHt1 _ H2). clear H2.
  simpl in *. 
  apply (f_equal g) in Hm.
  setoid_rewrite Hc in Hm.
  rewrite <- Hm.
  remember (f h1) as fh.
  destruct fh.
  - inverts Hf. exists 0. split; auto. omega.
  - apply_clear IHt1 in Hf. exrepnd. exists (S n).
    split; auto. omega. 
Qed.

Lemma find_map_same_compose {A B: Type} (f : A -> bool) 
  (h : A -> B) (g : B -> bool) :
(forall a, (compose g h) a = f a)
-> forall (s : A) (l: list A),
  find f l = Some s
  -> find g (map h l) = Some (h s).
Proof.
  intros Hc ?.
  induction l; auto; intros Hf;[inverts Hf|].
  simpl in *. unfold compose in Hc.
  rewrite Hc.
  destruct (f a); auto.
  inverts Hf. refl.  
Qed.

Lemma combine_map {A B C: Type} (f:A->B) (g: A->C) (la:list A):
combine (map f la) (map g la)
= map (fun x => (f x, g x)) la.
Proof.
  induction la; simpl; congruence.
Qed.

Lemma iff_t_iff : forall A B : Prop, A <-> B <-> (A <=> B).
Proof.
  firstorder.
Qed.


Lemma eqsetv_prop {A}:
  forall (vs1 vs2 : list A),
    eq_set vs1 vs2 <=> forall x, LIn x vs1 <=> LIn x vs2.
Proof.
  sp.
  unfold subset.  firstorder.
Qed.

Lemma eqsetv_sym {A} :
  forall (s1 s2 : list A), eq_set s1 s2 <=> eq_set s2 s1.
Proof.
  introv. unfold eq_set. tauto.
Qed.

Lemma eqsetv_disjoint {A}:
  forall (s1 s2 s3 : list A),
    eq_set s1 s2
    -> disjoint s1 s3
    -> disjoint s2 s3.
Proof.
   unfold disjoint, subset.
   firstorder.
Qed.



Lemma eqsetv_trans {A}: forall (lva lvb lvc : list A),
  eq_set lva lvb
  -> eq_set lvb lvc
  -> eq_set lva lvc.
Proof.
  introv He1 He2.
  rewrite (eqsetv_prop) in *.
  split; intro Hin;
  repeat (try(apply He1 in Hin); try(apply He2 in Hin); auto).
Qed.

Lemma eq_vars_sym {A}: forall (lv1 lv2 : list A),
  eq_set lv1 lv2 -> eq_set lv2 lv1.
Proof.
  introv. rewrite eqsetv_prop. rewrite eqsetv_prop.
  intros X x. rw X.
  dtiffs2. split; auto.
Qed.

Notation lremove := diff.

Lemma subset_flat_map_r {A B:Type} (f: A-> list B): forall la a,
  LIn a la-> subset (f a) (flat_map f la).
Proof.
  intros ? ? Hin1 ? Hin2.
  apply in_flat_map; eauto.
Qed.

Global Instance subsetRefl {A} : Reflexive (@subset A).
Proof.
   eauto.
Qed.

Global Instance subsetTrans {A} : Transitive (@subset A).
Proof.
   intros ? ? ? ? ?. eapply subset_trans; eauto.
Qed.


Global Instance equivEqsetv {A}: Equivalence (@eq_set A).
Proof.
  constructor; eauto using eqsetv_trans, eq_vars_sym.
  constructor; unfold subset; tauto.
Qed.

(* Require Import Morphisms. *)

Global Instance properEqsetvLin {A} : Proper (eq ==> eq_set ==> iff ) (@LIn A).
Proof.
  intros ? ? ? ? ? ?. apply iff_t_iff. subst. apply eqsetv_prop; assumption.
Qed.

Global Instance properEqsetvNull {A} : Proper (eq_set ==> iff ) (@null A).
Proof.
  intros ? ? H. unfold null. split; intros; [rewrite <- H| rewrite H]; eauto.
Qed.

Global Instance properEqsetvApp {A}: Proper (eq_set ==> eq_set ==> eq_set ) (@app A).
Proof.
  intros ? ? H1 ? ? H2. apply eqsetv_prop. setoid_rewrite in_app_iff.
  setoid_rewrite H1. setoid_rewrite H2. tauto.
Qed.

Global Instance properEqsetvRemove {A:Type} `{Deq A}: Proper (eq_set ==> eq_set ==> eq_set) (@lremove A _).
Proof.
  intros ? ? H1 ? ? H2. apply eqsetv_prop.
  setoid_rewrite in_diff.
  setoid_rewrite H1. setoid_rewrite H2. tauto.
Qed.

Global Instance properEqsetvSubsetv {A} : Proper (eq_set ==> eq_set ==> iff ) (@subset A).
Proof.
  intros ? ? ? ? ? Heq.  subst. apply iff_t_iff.  unfold subset.
  repeat setoid_rewrite Heq. setoid_rewrite H. reflexivity.
Qed.

Global Instance transSubsetv {A}: Transitive (@subset A).
Proof.
  intros ? ? ?. apply subset_trans.
Qed.

(* TODO : generalize over P*)
Global Instance properEqsetvlforall {A} P : Proper (eq_set ==> iff ) (@lforall A P).
Proof.
  intros ? ? Heq. unfold lforall. setoid_rewrite Heq.
  refl.
Qed.


Global Instance proper_memberb {A:Type} `{Deq A} :
Proper (eq ==> eq_set ==>eq) (@memberb A _).
Proof.
  intros ? ? ? ? ? ?.
  pose proof (@proper_decider2 A _ (@LIn A) eq eq_set in_deqq properEqsetvLin).
  simpl in H2.
  apply H2; auto.
Qed.

Lemma  flat_map_monotone:
  forall (A B : Type) (f : A -> list B) (la lb : list A),
  subset la lb -> subset (flat_map f la) (flat_map f lb).
Proof.
  intros.
  rewrite subset_flat_map.
  intros ? Hin.
  apply subset_flat_map_r.
  auto.
Qed.

Lemma  map_monotone:
  forall (A B : Type) (f : A -> B) (la lb : list A),
  subset la lb -> subset (map f la) (map f lb).
Proof.
  intros.
  unfold subset in *.
  setoid_rewrite in_map_iff.
  firstorder.
Qed.

Lemma flat_map_fapp:
  forall {A B : Type} (f g : A -> list B) (l : list A), 
  eq_set
    (flat_map (fun x => (f x) ++ (g x)) l)
    ((flat_map f l) ++ (flat_map g l)).
Proof.
  intros.
  apply eqsetv_prop. repeat setoid_rewrite in_app_iff.
  repeat setoid_rewrite in_flat_map.
  setoid_rewrite in_app_iff. 
  firstorder.
Qed.

Global Instance properDisjoint {A} : Proper (eq_set ==> eq_set ==> iff ) (@disjoint A).
Proof.
  intros ? ? ? ? ? Heq.  subst. apply iff_t_iff.  unfold disjoint.
  repeat setoid_rewrite Heq. setoid_rewrite H. reflexivity.
Qed.

Lemma subsetvAppLR {A} : forall a b c d,
  subset a c
  -> subset b d
  -> @subset A (a++b) (c++d).
Proof.
  intros ? ? ? ? H1s H2s.
  apply app_subset.
  split; eauto using subset_app_l, subset_app_r.
Qed.

Lemma eqset_flat_maps
     : forall (A B : Type) (f g : A -> list B) (l : list A),
       (forall x : A, LIn x l -> eq_set (f x) (g x))
         -> eq_set (flat_map f l)  (flat_map g l).
Proof.
  induction l; intros; simpl; [refl|].
  rewrite H;[| sp].
  simpl in *.
  rewrite IHl;[| spc].
  refl.
Qed.

Lemma disjoint_sym_eauto
     : forall (T : Type) (l1 l2 : list T), disjoint l1 l2 -> disjoint l2 l1.
Proof using.
  intros. apply disjoint_sym. assumption.
Qed.

Lemma eqset_app_comm : forall {A} (a b: list A),
eq_set (a++b) (b++a).
Proof using.
  intros ? ? ?. rewrite eqsetv_prop. intro. repeat rewrite in_app_iff.
  tauto.
Qed.

Global Instance properNil {A}: Proper (eq_set ==> iff) (@eq (list A) nil).
Proof using. 
  intros ? ? H. rewrite eqsetv_prop in H.
  split; intros Hh; subst; simpl in H; firstorder;[destruct y | destruct x]; simpl in *;
   try tauto; specialize (H a); try tauto.
Qed.

SearchAbout ((?A -> ?B)-> (?A -> ?B) -> Prop).

(* allows rewriting in maps using functional extensionality *)
Global Instance properMapExt {A B}: Proper ((eq ==> eq) ==>  eq  ==> eq) (@map A B).
Proof.
  intros ? ? H1 ? ? H2. subst. apply eq_maps.
  auto.
Qed.

(* maps on lists interpreted as bags *)
Global Instance properEquivMap {A B}: Proper ((eq ==> eq) ==>  eq_set  ==> eq_set) (@map A B).
Proof.
  intros f g H1 ? ? H2.
  apply eqsetv_prop.
  setoid_rewrite in_map_iff.
  intros.
  setoid_rewrite H2.
  firstorder; subst; eexists; split;  eauto; try apply H1.
  symmetry. apply H1. auto. 
Qed.

(* flat_maps on lists interpreted as bags *)
Global Instance properEquivFlatMap {A B}: Proper ((eq ==> eq_set) ==>  eq_set  ==> eq_set) (@flat_map A B).
Proof.
  intros f g H1 ? ? H2.
  apply eqsetv_prop.
  setoid_rewrite in_flat_map.
  intros.
  setoid_rewrite H2.
  firstorder; subst; eexists; split;  eauto; try apply H1.
Qed.

Lemma subsetv_nil_r {A}:
  forall vs,
    @subset A vs [] <=> vs = [].
Proof.
  introv; split; intro k; allrw; sp.
  unfold subset in *.
  apply null_iff_nil.
  unfold null; introv i.
  discover; sp.
Qed.

Hint Rewrite @subsetv_nil_r : SquiggleEq.


Lemma disjoint_neq_iff {A} {a b : A} :
  disjoint [a] [b]
  <-> a <> b.
Proof using.
  split; intros; simpl in *;
  repeat disjoint_reasoning;
  simpl in *;
  tauto.
Qed.

Lemma disjoint_neq {A} {a b : A} :
  disjoint [a] [b]
  -> a <> b.
Proof using.
  intros Hd.
  intros Hc.
  subst.
  repeat disjoint_reasoning.
  simpl in *.
  tauto.
Qed.



  Hint Resolve @subset_flat_map_r : subset.

Lemma combine_map_fst2 {A B}: forall la lb,
  length la <= length lb
  -> la = map fst (@combine A B la lb).
Proof.
  induction la; auto;[].
  simpl. intros lb Hle.
  destruct lb;[ inverts Hle |].
  simpl in *. apply le_S_n in Hle.
  f_equal; auto.
Qed.

Lemma combine_map_fst {A B}: forall la lb,
  length la = length lb
  -> la = map fst (@combine A B la lb).
Proof.
  intros ? ? Hl.
  apply combine_map_fst2. rewrite Hl. reflexivity. 
Qed.

Lemma combine_map_snd2 {A B}: forall lb la,
  length lb <= length la
  -> lb = map snd (@combine A B la lb).
Proof.
  induction lb; auto;
  simpl; intros la Hle; try rewrite combine_nil; auto.
  destruct la;[ inverts Hle |].
  simpl in *. apply le_S_n in Hle.
  f_equal; auto.
Qed.

Lemma combine_map_snd {A B}: forall la lb,
  length la = length lb
  -> lb = map snd (@combine A B la lb).
Proof.
  intros ? ? Hl.
  apply combine_map_snd2. rewrite Hl. reflexivity. 
Qed.


Fixpoint seq {T:Type} (next: T->T) (start : T) (len : nat) {struct len} : list T :=
match len with
| 0 => []
| S len0 => start :: seq next (next start) len0
end.

Fixpoint fn {A:Type} (f: A->A) (n:nat) : A -> A :=
match n with
| O => id
| S n' => compose (fn f n') f
end.

Lemma fn_shift2 {A B:Type} (fa: A->A) (fb : B -> B) (ab : A -> B) :
(forall a, ab (fa a) = fb (ab a))
->  forall x start,
fn fb x (ab start) = ab (fn fa x start).
Proof using.
  induction x; auto.
  simpl. unfold compose. intros.
  congruence.
Qed.


Lemma fn_shift {A:Type} (f: A->A) : forall x start,
fn f x (f start) = f (fn f x start).
Proof using.
  induction x; auto.
  simpl. unfold compose. auto.
Qed.


Lemma seq_spec {A:Type} (f: A->A)  :
  forall (len:nat) (start:A), 
    (seq f start len) = map (fun n => (fn f n) start) (List.seq 0 len).
Proof using Type.
  induction len; intros ?; auto.
  simpl. f_equal. rewrite <- seq_shift.
  rewrite map_map. unfold compose. simpl.
  eauto.
Qed.


Lemma seq_map {A B:Type} (fa: A->A) (fb : B -> B) (ab : A -> B)  :
(forall a, ab (fa a) = fb (ab a))
->
  forall (len:nat) (start:A), 
    (seq fb (ab start) len) = map ab (seq fa start len).
Proof using Type.
  intros.
  do 2 rewrite seq_spec.
  rewrite map_map. unfold compose.
  apply eq_maps.
  intros ? _.
  apply fn_shift2. assumption.
Qed.

Lemma seq_shift {A:Type} (f: A->A)  :
  forall (len:nat) (start:A), 
    (seq f (f start) len) = map f (seq f start len).
Proof using Type.
  intros.
  do 2 rewrite seq_spec.
  rewrite map_map. unfold compose.
  apply eq_maps.
  intros ? _.
  apply fn_shift.
Qed.

Lemma seq_length A (f:A->A) n x : length (seq f x n) = n.
Proof using.
  intros.
  rewrite seq_spec, map_length, seq_length. refl.
Qed.


Require Import Psatz.

Lemma NoDupInjectiveMap {A B : Type} (f:A->B) :
injective_fun f
-> forall l, NoDup l -> NoDup (map f l).
Proof.
  intros Hin. induction l; [simpl; constructor |].
  intros Hnd. inversion Hnd.
  simpl. constructor; auto.
  intros Hl.
  apply in_map_iff in Hl. subst.
  exrepnd.
  apply Hin in Hl0.
  subst. contradiction.
Qed.
  

Lemma fn_plusN : forall (n:nat) (m:N), (fn N.succ n) m = ((N.of_nat n) + m)%N.
Proof using Type.
  induction n; auto.
  intros.
  rewrite Nnat.Nat2N.inj_succ. simpl.
  unfold compose. simpl.
  rewrite IHn.
  lia.
Qed.

Lemma in_seq_Nplus :   forall len (start n : N),
   LIn n (seq N.succ start len) <-> (start <= n /\ n < start + N.of_nat len)%N.
Proof using.
  intros.
  rewrite seq_spec.
  rewrite in_map_iff.
  setoid_rewrite fn_plusN.
  setoid_rewrite in_seq.
  split; intro H.
- exrepnd. lia.
- repnd. exists (N.to_nat (n-start)).
  lia.
Qed.

Definition maxlp :  (list positive) -> positive  -> positive :=
  fold_left Pos.max.

Lemma maxlp_le2 : forall  lp p1 p2, 
  (p1 <= p2 -> maxlp lp p1 <= maxlp lp p2)%positive.
Proof using.
  induction lp; auto.
  intros ? ? Hle. simpl.
  apply IHlp.
  apply Pos.max_le_compat_r. assumption.
Qed.


(* using MathClasses, this lemma can be stated more generally *)
Lemma maxlp_le : forall  x lp p, 
  (In x (p::lp) -> x <= maxlp lp p)%positive.
Proof.
  induction lp; intros ? Hin.
- apply in_single_iff in Hin. subst. reflexivity.
- simpl in *. dorn Hin;[| dorn Hin]; subst; auto.
  + eapply transitivity;[apply IHlp; left; refl | apply maxlp_le2, Pos.le_max_l].
  + eapply transitivity;[apply IHlp; left; refl | apply maxlp_le2, Pos.le_max_r].
Qed.


Lemma select_map {A B}: forall (f: A->B)  la n a,
  select n la = Some a
  -> select n (map f la) = Some (f a).
Proof using.
  induction la; simpl;destruct n;  introv H; simpl in *; try congruence.
  auto.
Qed.

Lemma move_snd_out {A B C}: forall (p: A*B) (f : B->C),  
  f (snd p) = snd ((fun x => (fst x, f (snd x))) p).
Proof using.
  intros. destruct p. refl.
Qed.

Hint Resolve  flat_map_monotone map_monotone : subset.

Lemma combineeq {A}: forall la lb,
  @length A la = length lb
  -> (forall x y, LIn (x,y) (combine la lb) -> x=y)
  -> la = lb.
Proof.
  induction la; intros ? Hl Hin; simpl in *; dlist_len_name lb b;[refl|].
  simpl in *.
  dLin_hyp. simpl in *. subst.
  f_equal; auto.
Qed.

Lemma list_pair_ext {A B} : forall (la lb : list (A *B)),
  map fst la = map fst lb
  -> map snd la = map snd lb
  -> la = lb.
Proof.
  induction la as [| a la Hind]; intros ? H1m H2m; destruct lb as [| b lb]; inverts H1m; auto.
  inverts H2m. destruct a. destruct b.
  simpl in *. subst.
  f_equal. auto.
Qed.

Lemma eqset_repeat {A B} la (lb: list B) :
la <> []
-> eq_set (flat_map (fun _ : A => lb) la) lb.
Proof.
  intros ?. apply eqsetv_prop.
  intros.
  rewrite in_flat_map.
  destruct la; [ congruence|]. simpl.
  firstorder.
  eexists; split; eauto.
Qed.

Lemma repeat_nil {A B} la  :
(flat_map (fun _ : A => []) la) = @nil B.
Proof.
  induction la; auto.
Qed.

Hint Rewrite @repeat_nil : SquiggleEq.

Ltac rwsimpl He1 :=
  repeat progress (autorewrite with list core SquiggleEq in He1; simpl in He1).

Ltac rwsimplAll :=
  repeat progress (autorewrite with list core SquiggleEq in *; simpl in *).

Ltac rwsimplC :=
  repeat progress (autorewrite with list core SquiggleEq; simpl).

Lemma disjoint_map {A B} (f:A->B) (l1 l2: list A):
  disjoint (map f l1) (map f l2)
  -> disjoint l1 l2.
Proof using.
  intros Hd.
  intros ? Hin.
  apply (in_map f) in Hin.
  apply Hd in Hin.
  intros Hc. apply Hin. apply in_map. assumption.
Qed.


Lemma nodup_map {A B} (f:A->B) (l: list A):
  NoDup (map f l)
  -> NoDup l.
Proof using.
  induction l;
  intros Hd;  [ constructor |].
  inverts Hd as Hin Hinb. constructor; auto.
  clear Hinb IHl. intros Hc. apply Hin. apply in_map. assumption.
Qed.

(* Move to Coq.Lists.List ? *)
Lemma seq_add : forall n m s,
  List.seq s (n+m) = (List.seq s n)++(List.seq (s+n) m).
Proof using.
  intros ?. induction n; simpl; intros m s;
    [ rewrite <- plus_n_O; reflexivity | ].
  f_equal. rewrite IHn. f_equal. simpl.
  rewrite plus_n_Sm. reflexivity.
Qed.

(* Move to Coq.Lists.List ? *)
Lemma fold_right_map {A B C: Type} 
  (f: B -> C -> C) (m: A->B) (s:C) (l: list A) :
fold_right f s (map m l)
= fold_right (fun a c => f (m a) c) s l.
Proof using.
  induction l; simpl;congruence.
Qed.

Require Import Coq.Unicode.Utf8.
Lemma  fold_left_right_rev:
  ∀ (A B : Type) (f : A → B → B) (l : list A) (i : B),
  fold_right f i l = fold_left (λ (x : B) (y : A), f y x) (rev l) i.
Proof.
  intros.
  rewrite <- (rev_involutive l) at 1.
  apply fold_left_rev_right.
Qed.

(* Move *)
Lemma map_nth2:
  forall (A B : Type) (f : A -> B) (l : list A) (d : A)  (db: B) (n : nat),
  n < length l
  -> nth n (map f l) db = f (nth n l d).
Proof using.
  intros. rewrite nth_indep with (d':= (f d));[| rewrite map_length; assumption].
  apply map_nth.
Qed.


Require Import PArith.
Require Import NArith.

Open Scope N_scope.

Lemma Nseq_add : forall (n m:nat) (s:N),
  (seq N.succ s (n+m) = (seq N.succ s n)++(seq N.succ (s+N.of_nat n) m)).
Proof using.
  intros ?. induction n; intros m s;
    [ rewrite N.add_0_r ; reflexivity | ].
  rewrite Nat2N.inj_succ. simpl.
  f_equal. rewrite IHn. do 2 f_equal.
  lia.
Qed.

(* move to list.v *)
Definition NLength {A:Type} (lv: list A) : N := N.of_nat (length lv).

Lemma NLength_length {A:Type} (lv: list A) : 
  N.to_nat (NLength lv)
  = length lv.
Proof using.
  unfold NLength.
  lia.
Qed.

  Lemma seq_NoDup len start : NoDup (seq N.succ start len).
  Proof using.
    clear.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq_Nplus. intros (H,_).
    lia.
  Qed.

Lemma seq_rev_N : forall l n,
  rev (seq N.succ n l) = map (fun x => n + n + N.of_nat l-x-1) (seq N.succ n l).
Proof using.
  clear.
  induction l; auto.
  intro.
  replace (S l) with (l + 1)%nat at 1 by omega.
  rewrite Nnat.Nat2N.inj_succ.
  rewrite Nseq_add. simpl.
  rewrite rev_app_distr. simpl.
  f_equal;[ lia |].
  rewrite IHl.
  rewrite  seq_shift.
  rewrite map_map. unfold compose. simpl.
  apply eq_maps. intros ? ?.
  lia.
Qed.

Hint Rewrite @NLength_length : list.
Hint Rewrite @NLength_length : SquiggleEq.

Close Scope N_scope.

Lemma flat_map_single {A B:Type} (f: A->B) (l:list A) :
flat_map (fun x => [f x]) l
= map f l.
Proof using.
  induction l;auto.
Qed.


Lemma combine_app : forall {A B} (la1 la2 : list A) {lb1 lb2 : list B},
  length la1 = length lb1
  ->
  combine (la1 ++ la2) (lb1 ++ lb2)
  = (combine la1 lb1) ++ (combine la2 lb2).
Proof using.
  induction la1; intros ? ? ? Heq; destruct lb1 as [| b1 lb1]; invertsn Heq;[refl|].
  rewrite combine_cons.
  do 3 rewrite <- app_comm_cons.
  rewrite combine_cons.
  f_equal. eauto.
Qed.




(* Move *)
Lemma lforall_rev {A:Type} (P: A -> Prop):
  forall l, lforall P l -> lforall P (rev l).
Proof using.
  intros ?. unfold lforall. setoid_rewrite <- in_rev.
  tauto.
Qed.

(* Move *)
Lemma rev_combine {A B:Type} : forall (la : list A) (lb: list B),
length la = length lb
-> rev (combine la lb) = combine (rev la) (rev lb).
Proof using.
  induction la; intros ? Heq; destruct lb as [|b lb]; invertsn Heq; [refl|].
  simpl. rewrite combine_app;[| autorewrite with list; assumption].
  rewrite IHla by assumption.
  refl.
Qed.

(* Move *)
Lemma option_map_id {T:Type}: forall (k:option T), 
  option_map id k = k.
Proof using.
  intros. destruct k; refl.
Qed.



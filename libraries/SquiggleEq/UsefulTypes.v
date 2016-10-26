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


(*Require Import SfLib.*)
Require Import Coq.Init.Notations.
Require Import tactics.
Require Import Peano.
Require Import Basics.
Require Import Coq.Bool.Bool.
Require Import Arith.
Require Import Arith.EqNat.
Require Import Omega.

Require Import eq_rel.
Require Import universe.
Require Import LibTactics.


(* Prop/Type exists depending on the switch universe-type.v/universe-prop.v *)
Notation "{ a , b : T $ P }" :=
  {a : T $ {b : T $ P}}
    (at level 0, a at level 99, b at level 99).
Notation "{ a , b , c : T $ P }" :=
  {a : T $ {b : T $ {c : T $ P}}}
    (at level 0, a at level 99, b at level 99, c at level 99).
Notation "{ a , b , c , d : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ P}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99).
Notation "{ a , b , c , d , e : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ {e : T $ P}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99).
Notation "{ a , b , c , d , e , f : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ {e : T $ {f : T $ P}}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99, f at level 99).


(* Some extra notation from SfLib *)
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

(* Some lemmas from SfLib *)
Theorem beq_nat_sym :
  forall (n m : nat),
    beq_nat n m = beq_nat m n.
Proof.
  induction n; sp.
  unfold beq_nat; destruct m; sp.
  simpl; destruct m; simpl; sp.
Qed.

Require Import Coq.Classes.DecidableClass.
Global Instance DecConj A B (_: Decidable A) (_ :Decidable B) : Decidable (A /\ B).
Proof.
  exists (andb (decide A) (decide B)).
  unfold decide.
  destruct H.
  destruct H0.
  rewrite Bool.andb_true_iff.
  unfold DecidableClass.Decidable_witness. tauto.
Defined.

Definition decideP (P:Prop) `{Decidable P} : {P} + {~P}.
  remember (decide P) as dec. 
  destruct dec; [left | right];
  symmetry in Heqdec;
  unfold decide in Heqdec;
  pose proof Decidable_spec; try tauto.
  intro Hc.
  rewrite <- H0 in Hc. congruence.
Defined.

Lemma decide_decideP  {P:Prop }`{Decidable P} {R:Type} (a b : R) :
(if (decide P) then  a else b) = (if (decideP P) then  a else b).
Proof.
  symmetry. unfold decide.
  cases_if.  
- rewrite Decidable_complete; auto.
- rewrite Decidable_sound_alt; auto.
Qed.

Class Deq T := deceq :> forall (a b:T), Decidable (a=b).

Class DecidableSumbool (P:Prop) := decSumbool : {P} + {!P}.

Global Instance  decAsSumbool {P:Prop} `{DecidableSumbool P} : Decidable P.
Proof.
  destruct H;[exists true | exists false]; try tauto.
  split; congruence.
Defined.

Class DeqSumbool T := deceqSumbool :> forall (a b:T), DecidableSumbool (a=b).

Global Instance  deqAsSumbool {T:Type} `{DeqSumbool T} : Deq T.
Proof.
   intros ? ?.  eauto with typeclass_instances.
Defined.

Global Instance deq_prod {A B : Type} `{Deq A} `{Deq B}
 : Deq (A*B).
Proof using.
  intros  x y. destruct x. destruct y.
  exists (decide (a=a0 /\ b = b0)).
  rewrite Decidable_spec.
  split; intros Hyp; auto; inversion Hyp; auto.
  congruence.
Defined.

Global Instance deq_nat  : Deq nat.
Proof using.
  intros x y. exists (beq_nat x y).
  apply Nat.eqb_eq.
Defined.

Require Import Morphisms.

Lemma proper_decider2 {A B} (P: A -> B -> Prop) R1 R2
  (d: forall a b, Decidable (P a b))
  (p: Proper (R1 ==> R2 ==> iff) P ) : Proper (R1 ==> R2 ==> eq) (fun a b => @Decidable_witness _ (d a b)).
Proof.
  intros ? ? h1e ? ? H2e.
  apply eq_true_iff_eq.
  unfold decide.
  do 2 rewrite Decidable_spec.
  apply p; auto.
Qed.

Definition assert (b : bool) : Prop := b = true.

Lemma fold_assert :
  forall b,
    (b = true) = assert b.
Proof.
  unfold assert; auto.
Qed.

Lemma assert_orb :
  forall a b,
    assert (a || b) -> assert a + assert b.
Proof.
  destruct a; destruct b; sp.
Qed.

Lemma assert_andb :
  forall a b,
    assert (a && b) <-> assert a /\ assert b.
Proof.
  destruct a; destruct b; sp; split; sp.
Qed.

Lemma assert_of_andb :
  forall a b,
    assert (a && b) <=> assert a # assert b.
Proof.
  destruct a; destruct b; sp; split; sp.
Qed.

Lemma not_assert :
  forall b, b = false <-> ~ assert b.
Proof.
  destruct b; unfold assert; simpl; split; sp.
Qed.

Lemma not_of_assert :
  forall b, b = false <=> ! assert b.
Proof.
  destruct b; unfold assert; simpl; split; sp.
Qed.

Lemma andb_true :
  forall a b,
    a && b = true <-> a = true /\ b = true.
Proof.
  destruct a; destruct b; simpl; sp; split; sp.
Qed.

Lemma andb_eq_true :
  forall a b,
    a && b = true <=> a = true # b = true.
Proof.
  destruct a; destruct b; simpl; sp; split; sp.
Qed.


(* ------ useful stuff ------ *)

Lemma max_prop1 :
  forall a b, a <= max a b.
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto.
  assert (a <= max a b); auto; omega.
Qed.

Lemma max_prop2 :
  forall a b, b <= max a b.
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto; try omega.
  assert (b <= max a b); auto; omega.
Qed.

Lemma max_or :
  forall a b,
    (max a b = a) \/ (max a b = b).
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto.
  assert (max a b = a \/ max a b = b) by apply IHa; sp.
Qed.

Theorem comp_ind:
  forall P: nat -> Prop,
    (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
    -> forall n:nat, P n.
Proof.
 intros P H n.
 assert (forall n:nat , forall m:nat, m < n -> P m).
 intro n0. induction n0 as [| n']; intros.
 inversion H0.
 assert (m < n' \/ m = n') by omega.
 sp; subst; sp.
 apply H0 with (n := S n); omega.
Qed.

Theorem comp_ind_type :
  forall P: nat -> Type,
    (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
    -> forall n:nat, P n.
Proof.
 intros P H n.
 assert (forall n:nat , forall m:nat, m < n -> P m).
 intro n0. induction n0 as [| n']; intros.
 omega.
 destruct (eq_nat_dec m n'); subst; auto.
 apply IHn'; omega.
 apply H; apply X.
Qed.

(*
Print NTerm_ind.

Print eq_refl.

Require Import Eqdep.

Axiom dec_eq_eq :
  forall (A : Type),
    (forall a b : A, {a = b} + {a <> b})
    -> forall a b : A,
       forall e e' : a = b,
         e = e'. (* Proved in Eqdep_dec. *)

Definition eq_dep_eq_dec'
           (A : Type)
           (dec_eq : forall a b : A, {a = b} + {a <> b})
           (X : A -> Type)
           (a : A)
           (x y : X a)
           (e : eq_dep A X a x a y) : x = y
 := (match e in eq_dep _ _ _ _ a' y' return
          forall e' : a = a',
            (match e' in _ = a' return X a' with
                eq_refl => x
            end) = y'
    with
    | eq_dep_intro =>
      fun e : a = a =>
        match dec_eq_eq A dec_eq a a (eq_refl a) e
              in _ = e
              return match e in _ = a' return X a' with eq_refl => x end = x with
          | eq_refl => eq_refl x
        end
    end) (eq_refl a).
*)



Lemma trivial_if :
  forall T,
  forall b : bool,
  forall t : T,
    (if b then t else t) = t.
Proof.
  intros;  destruct b; auto.
Qed.

Hint Rewrite trivial_if.

Lemma minus0 :
  forall n, n - 0 = n.
Proof.
  destruct n; auto.
Qed.

Lemma pair_inj :
  forall A B,
  forall a c : A,
  forall b d : B,
    (a, b) = (c, d) -> a = c /\ b = d.
Proof.
  sp; inversion H; sp.
Qed.

Lemma S_inj :
  forall a b, S a = S b -> a = b.
Proof.
  auto.
Qed.

Lemma S_le_inj :
  forall a b, S a <= S b -> a <= b.
Proof.
  sp; omega.
Qed.

Lemma S_lt_inj :
  forall a b, S a < S b -> a < b.
Proof.
  sp; omega.
Qed.

Lemma not_or :
  forall a b,
    ~ (a \/ b) -> ~ a /\ ~ b.
Proof.
  sp; apply H; sp.
Qed.

Lemma not_over_or :
  forall a b,
    !(a [+] b) <=> !a # !b.
Proof.
  sp; split; sp.
Qed.

Theorem apply_eq :
  forall {A B} (f: A -> B) {a1 a2:A},
    a1 = a2 -> f a1 = f a2.
Proof. intros. rewrite H. reflexivity.
Qed.

Theorem iff_push_down_forall : forall A (P Q: A-> Prop) ,
  (forall a, P a <=> Q a) -> ((forall a, P a) <=> (forall a, Q a)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Theorem iff_push_down_forallT : forall A (P Q: A-> [univ]) ,
  (forall a, P a <=> Q a) -> ((forall a, P a) <=> (forall a, Q a)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Theorem iff_push_down_impliesT : forall P Q R,
  (R -> (P <=> Q)) -> ((R -> P) <=> (R -> Q)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Lemma sum_assoc :
  forall a b c,
    (a [+] (b [+] c)) <=> ((a [+] b) [+] c).
Proof.
  sp; split; sp.
Qed.


(* ========= DEPENDENT PAIRS ========= *)

Definition eq_existsT (A : Type)
                      (B : A -> Type)
                      (a a' : A)
                      (b : B a)
                      (b' : B a')
                      (ea : a = a')
                      (eb : match ea in _ = a' return B a' with eq_refl => b end = b')
  : existT B a b = existT B a' b'
  := match ea as ea
              in _ = a'
        return forall b' : B a',
                 match ea in _ = a' return B a' with eq_refl => b end = b'
                 -> existT B a b = existT B a' b'
     with
       | eq_refl => fun b' eb => match eb with eq_refl => eq_refl (existT B a b) end
     end b' eb.

Lemma dep_pair_eq :
  forall {T : Type} {a b : T} (eq : a = b) (P : T -> Prop) (pa : P a) (pb : P b),
    @eq_rect T a P pa b eq = pb
    -> exist P a pa = exist P b pb.
Proof.
  intros.
  rewrite <- H.
  rewrite <- eq.
  reflexivity.
Qed.



Ltac apply_tiff_f H1 H2 :=
  let H3 := fresh in (
    (pose proof (fst (H1) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3)).

Ltac apply_tiff_b H1 H2 :=
  let H3 := fresh in (
    (pose proof (snd (H1) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3)).

Tactic Notation "apply_tiff"  constr(H1) constr(H2) :=
 (apply_tiff_f H1 H2 || apply_tiff_b H1 H2) .


Tactic Notation "refl" := reflexivity.


Theorem and_tiff_compat_l:
 forall A B C : [univ], (B <=> C) -> (A # B <=> A # C).
Proof. 
 introv Hiff. rw Hiff. apply t_iff_refl. 
Qed.

Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
@eq_rect T a P pa b eq.

Definition injective_fun {A B: Type} (f: A->B)  :=
  forall (a1 a2: A), (f a1= f a2) -> a1=a2.

Lemma min_eq : forall n1 n2,
  n1=n2 -> min n1 n2 = n2.
Proof.
  introv H. rewrite  H.
  apply Min.min_idempotent.
Qed.

Lemma negb_eq_true :
  forall b, negb b = true <=> ! (assert b).
Proof.
  intro.
  unfold assert; destruct b; simpl; split; sp.
Qed.

Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Type :=
 forall s: S , (g (f s)) = s.

Definition bijection  {S T : Type} (f: S -> T) (g: T-> S) : Type
 := prod (left_identity f g)  (left_identity g f). 

Definition injection {S T : Type} (f: S -> T) :=
  forall (s1 s2 : S), (f s1 = f s2) -> s1=s2.

Lemma left_id_injection: forall {S T : Type} (f: S -> T) (g: T-> S),
  left_identity f g -> injection f.
Proof.
  introv lid feq.
  apply_eq g feq ffeq.
  rw lid in ffeq.
  rw lid in ffeq.
  trivial.
Qed.

Lemma prod_assoc :
  forall a b c,
    (a # b) # c <=> a # (b # c).
Proof.
  sp; split; sp.
Qed.

Lemma prod_comm :
  forall a b,
    a # b <=> b # a.
Proof.
  sp; split; sp.
Qed.

Lemma or_true_l :
  forall t, True [+] t <=> True.
Proof. sp. Qed.

Lemma or_true_r :
  forall t, t [+] True <=> True.
Proof. sp. Qed.

Lemma or_false_r : forall t, t [+] False <=> t.
Proof. sp; split; sp. Qed.

Lemma or_false_l : forall t, False [+] t <=> t.
Proof. sp; split; sp. Qed.

Lemma and_true_l :
  forall t, True # t <=> t.
Proof. sp; split; sp. Qed.

Lemma not_false_is_true : !False <=> True.
Proof. sp; split; sp. Qed.

Lemma forall_num_lt_d : forall m (P : nat -> [univ]),
  (forall n, n < S m -> P n)
  -> P 0 # (forall n, n <  m -> P (S n) ).
Proof.
  introv Hlt.
  dimp (Hlt 0); auto; [omega|].
  dands; auto.
  introv Hgt.
  apply lt_n_S in Hgt.
  eauto.
Qed.
Ltac dforall_lt_hyp name := 
  repeat match goal with
  [ H : forall  n : nat , n< S ?m -> ?C |- _ ] => 
    apply forall_num_lt_d in H;
    let Hyp := fresh name in
    destruct H as [Hyp H]
  | [ H : forall  x : ?T , _ < 0 -> _ |- _ ] => clear H
  end.

Lemma and_true_r :
  forall t, t # True <=> t.
Proof. sp; split; sp. Qed.

Definition opExtract {A:Type} (def:A) (oa: option A) : A :=
match oa with
| Some name => name
| None  => def
end.

Definition isSome {A:Type} (sop : option A) : Prop  := 
match sop with
| Some s => True
| None => False
end.




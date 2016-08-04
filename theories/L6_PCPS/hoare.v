Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad
        Coq.Classes.Morphisms Coq.Lists.List.
Require Import functions.
Import MonadNotation ListNotations.

Open Scope monad_scope.

Ltac inv H := inversion H; clear H; subst.

Definition triple {A S} (pre : S -> Prop) (e : state S A)
           (post : S -> A -> S -> Prop) : Prop :=
  forall i, pre i ->
       let (v, i') := runState e i in
       post i v i'.

Notation "{{ p }} e {{ q }}" :=
  (triple p e q) (at level 90, e at next level).


(** Some extra combinators *)
Fixpoint mapM {M : Type -> Type} {A B : Type} `{Monad M} (f : A -> M B)
         (l : list A)  : M (list B) :=
  match l with
    | [] => ret []
    | x :: xs =>
      let sx' := f x in
      x' <- sx';;
      xs' <- mapM f xs ;;
      ret (x' :: xs')
  end.

Fixpoint sequence {M : Type -> Type} {A : Type} `{Monad M}
         (l : list (M A))  : M (list A) :=
  match l with
    | [] => ret []
    | x :: xs =>
      x' <- x ;;
         xs' <- sequence xs ;;
         ret (x' :: xs')
  end.

(** Extensional equality for computations in the state monad *) 
Definition st_eq {A S} (s1 s2 : state S A) := f_eq (runState s1) (runState s2).

Instance triple_Proper {A S} : Proper (Logic.eq ==> st_eq ==> Logic.eq ==> iff) (@triple A S).
Proof.
  intros P1 P2 Heq1 m1 m2 Hfeq P3 P4 Heq2; subst; split; intros H.
  - intros s HP2. rewrite <- Hfeq. eapply H. eauto.
  - intros s HP2. rewrite  Hfeq. eapply H. eauto.
Qed.

Instance bind_Proper_l {A B S} : Proper (st_eq ==> Logic.eq ==> st_eq)
                                        (@bind (state S) (Monad_state S) A B).
Proof. 
  intros m1 m2 Hfeq f1 f2 Heq m; subst.
  unfold bind, Monad_state. simpl. rewrite Hfeq. reflexivity.
Qed.

Instance bind_Proper_r {A B S} : Proper (Logic.eq ==> (fun f1 f2 => forall x, st_eq (f1 x) (f2 x)) ==> st_eq)
                                        (@bind (state S) (Monad_state S) A B).
Proof. 
  intros m1 m2 Hfeq f1 f2 Heq m; subst.
  unfold bind, Monad_state. simpl.
  destruct (runState m2 m). rewrite Heq. reflexivity.
Qed.

Instance st_eq_Proper_l {A S} : Proper (st_eq ==> Logic.eq ==> iff) (@st_eq A S).
Proof. 
  intros m1 m2 Heq1 m3 m4 Heq2; subst.
  split; intros Heq s. now rewrite <- Heq1, Heq. now rewrite Heq1, Heq. 
Qed.

Instance st_eq_Proper_r {A S} : Proper (Logic.eq ==> st_eq ==> iff) (@st_eq A S).
Proof. 
  intros m1 m2 Heq1 m3 m4 Heq2; subst.
  split; intros Heq s. now rewrite <- Heq2, Heq. now rewrite Heq2, Heq. 
Qed.

(** * Monad Laws *)

Lemma left_id {A B S} (x : A) (f : A -> state S B) :
  st_eq (bind (ret x) f) (f x).
Proof.
  intros m1. reflexivity.
Qed.

Lemma right_id {A S} (m : state S A) :
  st_eq (bind m ret) m.
Proof.
  intros m1. unfold bind, ret, Monad_state. simpl.
  destruct (runState m m1). reflexivity.
Qed.

Lemma assoc {A B C S} (m : state S A) (f : A -> state S B)  (g : B -> state S C) :
  st_eq (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
Proof.
  intros m1. unfold bind, ret, Monad_state. simpl.
  destruct (runState m m1). reflexivity.
Qed.


(** * Usefull lemmas about triples *)

Lemma pre_strenghtening {A S} (P P' : S -> Prop) (Q : S -> A -> S -> Prop) e :  
  (forall i, P' i -> P i) ->
  {{ P }} e {{ Q }} ->
  {{ P' }} e {{ Q }}.
Proof.
  intros H. unfold triple. intros; eauto. eapply H0. eauto.
Qed.

Lemma post_weakening {A S} (P : S -> Prop) (Q Q' : S -> A -> S -> Prop) e :  
  (forall i x i', P i -> Q i x i' -> Q' i x i') ->
  {{ P }} e {{ Q }} ->
  {{ P }} e {{ Q' }}.
Proof.
  intros H. unfold triple. intros.
  specialize (H0 i). destruct (runState e i). eapply H; eauto.
Qed.

Lemma pre_post_mp_l {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e:
  {{ fun i => True }} e {{ fun i x i' => P i -> Q i x i' }} ->
  {{ fun i => P i }} e {{ fun i x i' => Q i x i' }}.
Proof.
  intros H.
  eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
  simpl; eauto. 
Qed.

Lemma pre_post_mp_r {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e:
  {{ fun i => P i }} e {{ fun i x i' => Q i x i' }} ->
  {{ fun i => True }} e {{ fun i x i' => P i -> Q i x i' }}.
Proof.
  unfold triple.
  intros H i HP'. specialize (H i). destruct (runState e i) as [x i'].
  eauto.
Qed.

Lemma pre_eq_state_l {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e :
  (forall i, P i -> {{ fun i' => i = i' }} e {{ Q }}) ->
  {{ P }} e {{ Q }}.
Proof.
  intros H i HP. specialize (H i HP). 
  unfold triple in H. eapply H. eauto. 
Qed.

Lemma pre_eq_state_r {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e :
  {{ P }} e {{ Q }} ->
  (forall i, P i -> {{ fun i' => i = i' }} e {{ Q }}).
Proof.
  intros H i HP.  intros i' Heq; subst. now eapply H.
Qed.

Lemma post_eq_l {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e i1 x i2 :
  {{ P }} e {{ fun i1' x' i2' => i1 = i1' /\ x = x' /\ i2 = i2'  }} ->
  Q i1 x i2 ->
  {{ P }} e {{ Q }}.
Proof.
  intros H HQ i HP. specialize (H i HP). 
  unfold triple in H. destruct runState.
  inv H. inv H1. eauto.
Qed.

Lemma post_eq_r {A S} (P : S -> Prop) (Q : S -> A -> S -> Prop) e i1 x i2 :
  {{ P }} e {{ Q }} ->
  {{ P }} e {{ fun i1' x' i2' => i1 = i1' /\ x = x' /\ i2 = i2' }} ->
  P i1 ->
  Q i1 x i2.
Proof.
  intros H H' HP. specialize (H i1 HP). specialize (H' i1 HP). 
  destruct runState.
  inv H'. inv H1. eauto.
Qed.

Lemma post_conj {A S} (P : S -> Prop) (Q1 Q2 : S -> A -> S -> Prop) e :
  {{ P }} e {{ Q1 }} ->
  {{ P }} e {{ Q2 }} ->
  {{ P }} e {{ fun i x i' => Q1 i x i' /\ Q2 i x i' }}.
Proof.
  unfold triple. intros.
  specialize (H i); specialize (H0 i).
  destruct (runState e i); eauto.
Qed.

Lemma post_trivial { A S} (P : S -> Prop)  (e : state S A) :
  {{ P }} e {{ fun _ _ _ => True }}.
Proof.
  unfold triple. intros; destruct (runState _ _); eauto.
Qed.

Lemma frame_rule { A S} (Pre : S -> Prop) (Post : S -> A -> S -> Prop)
      (P : S -> Prop) (e : state S A) :
  {{ Pre }} e {{ Post }} ->
  {{ fun i => P i /\ Pre i }} e {{ fun i x i' => P i /\ Post i x i' }}.
Proof.
  unfold triple. intros.
  specialize (H i). destruct (runState _ _). destruct H0; split; eauto.
Qed.


Lemma frame_rule_trivial_pre { A S} (Post : S -> A -> S -> Prop)
      (P : Prop) (e : state S A) :
  (P -> {{ fun _ => True }} e {{ Post }}) ->
  {{ fun i => P }} e {{ fun i x i' => P /\ Post i x i' }}.
Proof.
  intros H. unfold triple in *; intros. specialize (H H0 i).
  destruct (runState e i); split; eauto. 
Qed.

Lemma frame_rule_trivial { A S} (P : S -> Prop) (e : state S A) :
  {{ fun i => P i }} e {{ fun i _ _ => P i }}.
Proof.
  eapply post_weakening; [| eapply pre_strenghtening;
                            [| eapply frame_rule with (Pre := (fun _ => True));
                               eapply post_trivial]]; simpl in *.
  intros. destruct H0; eauto.
  intros; eauto.
Qed.

Lemma pre_existential {A B S} (Pre : B -> S -> Prop) (Post : S -> A -> S -> Prop) e :
  (forall b, {{ Pre b }} e {{ Post }}) ->
  ({{ fun s => exists b, Pre b s }} e {{ Post }}).
Proof.
  intros Hb s [b' Hre]. eapply Hb. eassumption.
Qed.    

Lemma pre_curry_r {A S} (Pre : S -> Prop) (Post : S -> A -> S -> Prop) (P : Prop) e :
  (P -> {{ Pre }} e {{ Post }}) ->
  {{ fun s => Pre s /\ P }} e {{ Post }}.
Proof.
  intros Hyp s [Hpre HP]. eapply Hyp; eauto.
Qed.

Lemma pre_curry_l {A S} (Pre : S -> Prop) (Post : S -> A -> S -> Prop) (P : Prop) e :
  (P -> {{ Pre }} e {{ Post }}) ->
  {{ fun s => P /\ Pre s }} e {{ Post }}.
Proof.
  intros Hyp s [Hpre HP]. eapply Hyp; eauto.
Qed.

(** * Lemmas about monadic combinators *)

Lemma return_triple {A S} (x : A) (Pre : S -> Prop) (Post : S -> A -> S -> Prop) :
  (forall i, Pre i -> Post i x i) ->
  {{ Pre }} (ret x) {{ Post }}.
Proof.
  unfold triple. auto.
Qed.

Lemma bind_triple {A B S} (m : state S A) (f : A -> state S B)
      (pre : S -> Prop) (post : S -> B -> S -> Prop)
      (post' : S -> A -> S -> Prop):
  {{ pre }} m {{ post' }} ->
  (forall (x : A) i, {{ post' i x }} f x {{ fun i' => post i }}) -> 
  {{ pre }} bind m f {{ post }}.
Proof.
  simpl. unfold triple; simpl. 
  intros H1 H2 i Pre.
  destruct (runState m i) eqn:Heq. eapply H2.
  specialize (H1 i). rewrite Heq in H1. eapply H1; eauto.
Qed.

Lemma get_triple {S} :
  {{ fun (i : S) => True }}
    get
  {{ fun (i : S) (x : S) (i' : S) =>
       x = i /\ i = i' }}.
Proof.
  unfold triple; intros. simpl. eauto.
Qed.

Lemma put_triple {S} x :
  {{ fun (i : S) => True }}
    put x
  {{ fun (_ : S) (_ : unit) (i' : S) =>
       x = i' }}.
Proof.
  unfold triple; intros. simpl. eauto.
Qed.

Lemma sequence_triple {A S} (Pre : S -> Prop) (P : A -> Prop) (l : list (state S A)) :
  Forall (fun e => {{ Pre }} e {{ fun _ e' s' => P e' /\ Pre s' }}) l ->  
  {{ Pre }} sequence l {{fun _ l' s' => Forall P l' /\ Pre s' }}.
Proof.     
  induction l; intros Hall.
  - inv Hall. apply return_triple.     
    intros i Hp. split; eauto.
  - inv Hall. eapply bind_triple.
    eassumption. 
    intros x s. eapply bind_triple.
    eapply frame_rule. eapply IHl; eassumption.
    intros x' s'. eapply return_triple.
    intros s'' [HP [Hall Hpre]]. split; eauto.
Qed.


Lemma map_sequence_triple {A S} (Pre : S -> Prop) (P : A -> A -> Prop) (f : A -> state S A) (l : list A) :
  Forall (fun e => {{ Pre }} f e {{ fun _ e' s' => P e e' /\ Pre s' }}) l ->  
  {{ Pre }} sequence (map f l) {{fun _ l' s' => Forall2 P l l' /\ Pre s' }}.
Proof.     
  induction l; intros Hall.
  - inv Hall. apply return_triple.     
    intros i Hp. split; eauto.
  - inv Hall. eapply bind_triple.
    eassumption. 
    intros x s. eapply bind_triple.
    eapply frame_rule. eapply IHl; eassumption.
    intros x' s'. eapply return_triple.
    intros s'' [HP [Hall Hpre]]. split; eauto.
Qed.

Opaque triple bind ret.
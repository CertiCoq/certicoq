Require Import ZArith.
Require Import Znumtheory.
Require Import Recdef.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Import Nnat.
Ltac inv H := inversion H; clear H; subst.

Arguments iter {A} n fl def.

Definition terminate {A: Type}(F: (A->A)->(A->A)) :=
  forall x: A, 
  {y : A | exists  p : nat, forall k: nat,
    (p < k)%nat ->
   forall default: A -> A,
   iter k F default x = y}.

Definition function {A} {F: (A->A)->(A->A)} (H: terminate F) :=
   fun x : A => let (v, _) := H x in v.

Definition id {A} (x: A) := x.
Lemma succ_lt: forall i, (i < S i)%nat.
Proof. intros; omega. Qed.
Lemma succ_lt2: forall i, (i < S (S i))%nat.
Proof. intros; omega. Qed.

Lemma terminate_equation:
 forall {A: Type} {F} (H: terminate F) (x:A),
  function H x = F (function H) x.
Admitted.  (* How to prove this? *)

Lemma case_splitter:
forall (A: Type) (f: A -> option A) (T: Type) s s'
    (H: f s = Some s')
    (J: forall s' : A, f s = Some s' -> T)
    (K: f s = None -> T),
match f s as o return (f s = o -> T) with
| Some s'0 => J s'0
| None => K
end eq_refl = 
 J s' H.
Proof.
intros.
 revert J K; rewrite H. intros. auto.
Qed.

Section SMALLSTEP.

Variable state : Type.
Variable stepf: state -> option state.

Fixpoint stepn (n: nat) (s: state) {struct n} : state :=
  match n with
  | O => s
  | S n' => match stepf s with 
                 | Some s' => stepn n' s'
                 | None => s
                end
  end.

Definition stops (s: state) : Type :=
   { n | stepf (stepn n s) = None /\ 
           forall i, (i<n)%nat -> stepf (stepn i s) <> None}.

Definition countsteps {s} (r: stops s) : nat := projT1 r.

Lemma stops_after_stepf:
  forall (s: sigT stops) s',
     stepf (projT1 s) = Some s' -> stops s'.
Proof.
intros [s [n [?H ?H]]] s' ?; simpl in *.
destruct n.
elimtype False.
inv H. congruence.
simpl in H. rewrite H1 in H.
exists n; split; auto.
intros.
intro.
apply (H0 (S i)).
omega.
simpl. rewrite H1.
auto.
Defined.

Definition stops_after_stepf' s (H: stops s) s'
     (H0: stepf s = Some s') : stops s' :=
  (stops_after_stepf (existT stops s H) s' H0).

Lemma stepn_stops (n: nat) (s: state) (H: stops s) : 
    stops (stepn n s).
Proof.
destruct H as [k [H H']].
exists (k-n)%nat.
revert s H H' n ; induction k; intros.
inv H. simpl.
rewrite H1.
split.
clear H'; revert s H1; induction n; simpl; intros; auto.
rewrite H1; auto.
intros. inv H.
simpl in *.
destruct n.
simpl. auto.
destruct (stepf s) eqn:?.
specialize (IHk _ H).
assert (forall i : nat, (i < k)%nat -> stepf (stepn i s0) <> None).
intros. intro. apply (H' (S i)). omega. simpl. rewrite Heqo. auto.
specialize (IHk H0); clear H0.
specialize (IHk n).
destruct IHk.
simpl.
rewrite Heqo.
split; auto.
simpl.
rewrite H.
split.
clear - H.
induction (k-n)%nat; simpl; auto.
rewrite H. auto.
intros.
apply H'.
omega.
Qed.

Definition run_F_Some (F: sigT stops -> sigT stops)
            (s: state) (H: stops s) (s': state) (H0: stepf s = Some s') :=
     F (existT stops s' (stops_after_stepf' s H s' H0)).

Definition stops0 s (H: stepf s = None) : stops s.
 refine (exist _ O (conj H _)).
intros. inv H0.
Defined.

Definition run_F_None s (H: stepf s = None) : sigT stops :=
       existT stops s (stops0 s H).

Definition run_F (F: sigT stops -> sigT stops) (x: sigT stops) : sigT stops :=
  match x with existT s H =>
  match
      stepf s as o  return (stepf s = o -> sigT stops)
   with
       | Some s' => run_F_Some F s H s'
       | None => run_F_None s
       end eq_refl
  end.

Lemma existT_stops_ext:
 forall s1 s2 H1 H2,
  s1=s2 -> existT stops s1 H1 = existT stops s2 H2.
Proof.
intros.
subst s2.
f_equal.
destruct H1 as [n1 [H1 H1']]; destruct H2 as [n2 [H2 H2']].
assert (n1=n2).
revert n2 s1 H1 H1' H2 H2'; induction n1; destruct n2; intros; auto.
clear - H1 H2'.
simpl in H1.
contradiction (H2' O); omega.
clear - H1' H2.
simpl in H2.
contradiction (H1' O); omega.
f_equal.
specialize (IHn1 n2).
simpl in H1, H2.
destruct (stepf s1) eqn:?.
specialize (IHn1 s).
apply IHn1; auto.
intros. intro. apply (H1' (S i)); simpl; auto. omega. rewrite Heqo; auto.
intros; intro. apply (H2' (S i)); simpl; auto. omega. rewrite Heqo; auto.
apply (IHn1 s1).
clear - Heqo.
induction n1; simpl; auto. rewrite Heqo; auto.
intros; intro. apply (H1' (S i)); simpl; intros. omega. rewrite Heqo; auto.
clear - Heqo.
induction n2; simpl; auto. rewrite Heqo; auto.
intros; intro. apply (H2' (S i)); simpl; intros. omega. rewrite Heqo; auto.
subst n2.
f_equal.
apply PI.proof_irrelevance.
Qed.

Lemma run_terminate: terminate run_F.
Proof.
hnf; intros.
destruct x as [s [n [H H']]]; simpl in *.
revert s H H'; induction n; intros.
* (* n=O *)
simpl in H.
exists (existT stops s (stops0 _ H)), O.
intros.
change (exist (fun n : nat => stepf (stepn n s) = None) 0%nat H)
  with (stops0 s H).
destruct k. inv H0. clear H0.
simpl.
replace (exist
         (fun n : nat =>
          stepf (stepn n s) = None /\
          (forall i : nat, (i < n)%nat -> stepf (stepn i s) <> None)) 0%nat
         (conj H H'))
  with (stops0 _ H)
 by (unfold stops0; f_equal; apply PI.proof_irrelevance).
clear H'.
fold ((run_F_Some (iter k run_F default) s (stops0 s H))).
generalize (run_F_Some (iter k run_F default) s (stops0 s H)) as J.
replace (run_F_None s) with (fun _ : stepf s = None => existT stops s (stops0 s H)).
pattern (stepf s).
rewrite H at 1.
auto.
unfold run_F_None.
apply functional_extensionality_dep.
intro.
f_equal.
f_equal.
apply PI.proof_irrelevance.
* (* n = S _ *)
simpl in H.
assert (H9: stepf (stepn n (stepn 1 s)) = None).
clear - H.
destruct (stepf s) eqn:?; simpl in *; auto.
rewrite Heqo. auto.
rewrite H.
clear - H; induction n; simpl; auto. rewrite H; auto.
specialize (IHn _ H9).
assert (H8: forall i : nat,
             (i < n)%nat -> stepf (stepn i (stepn 1 s)) <> None).
clear - H H'.
intros.
specialize (H' (S i)).
simpl in H'.
intro. apply H'; clear H'. omega.
simpl in *.
destruct (stepf s); auto.
specialize (IHn H8).
destruct IHn as [y IHn].
exists y.
destruct IHn as [p ?].
exists (S p).
destruct k; intros.
inv H1.
assert (p < k)%nat by omega.
specialize (H0 k H2 default).
clear H1 H2 p .
simpl.
assert ({s' | stepf s = Some s'} + {stepf s = None}).
destruct (stepf s); eauto.
generalize (exist
         (fun n0 : nat =>
          stepf (stepn n0 s) = None /\
          (forall i : nat, (i < n0)%nat -> stepf (stepn i s) <> None)) 
         (S n) (conj H H')) as J.
change {n0 : nat |
      stepf (stepn n0 s) = None /\
      (forall i : nat, (i < n0)%nat -> stepf (stepn i s) <> None)} with (stops s).
intro.
destruct X as [[s' ?H] | ?H].
assert (stepf (stepn n s') = None).
rewrite H1 in H; auto.
clear H.
rewrite (case_splitter state stepf (sigT stops) s s' H1).
unfold run_F_Some.
rewrite <- H0.
f_equal.
apply existT_stops_ext.
simpl. rewrite H1. auto.
elimtype False.
clear - H1 H'.
apply (H' O).
omega.
simpl.
auto.
Qed.

Definition run : sigT stops -> sigT stops :=
       function run_terminate.

Definition run' (s: state) (H: stops s) :=
  projT1 (run (existT stops s H)).

End SMALLSTEP.




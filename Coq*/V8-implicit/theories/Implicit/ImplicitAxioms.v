Set Implicit Arguments.

Require Import Logic.
Require Import Specif.

Section Proof_Irrelevence.

(* The Axiom: justified by the proof-irrelevent model of Miquel.
   There exists an object that belong to any true proposition
 *)
Axiom impl_PI : forall [A:Prop], [A] -> A.

Lemma proof_irrelevance : forall [P:Prop] [x y:P], x = y.
intros.
pose (px := impl_PI (existT (fun z => x=z:>P) x (refl_equal x))). 
pose (py := impl_PI (existT (fun z => z=y:>P) y (refl_equal y))).
(* px and py are convertable *)
transitivity (projT1 px).
 apply (projT2 px).
 apply (projT2 py).
Qed.

Lemma False_rect': forall [P:Type], [False] -> P.
intros.
apply False_rect.
apply (@impl_PI False); trivial.
Defined.
Lemma impl_neg : forall [A : Prop], [~A] -> [A] -> False.
intros.
apply False_rect';auto.
Qed.

Lemma eq_rect':
  forall [A:Type] [x:A] [P:A->Type], P x -> forall [y : A], [x = y] -> P y.
intros.
apply eq_rect with (1:=X).
apply (@impl_PI (x=y)); trivial.
Defined.

Definition proj2_sig [A] [P:A->Prop] (x:sig P) : P (proj1_sig x) :=
  match x as s return P (proj1_sig s) with
    exist x H => impl_PI H
  end.


(* With surjective pairing, s could be implicit *)
Lemma sig2_ext : forall [A] [P:A->Prop] s,
  s = exist P (proj1_sig s) (proj2_sig s).
Proof.
destruct s; trivial.
Qed.

(* With surjective pairing, impl_PI would not be needed *)
Lemma sig_rect' : forall [A] [P] [P0 : sig P -> Type],
       (forall [x : A] [p : P x], P0 (exist [P] x [p])) ->
       forall [s : sig P], P0 s.
intros.
rewrite (@impl_PI (_=_) (sig2_ext s)).
trivial.
Defined.

  Lemma Choice : forall S S' R,
   (forall x:S, sig (fun y:S' => R x y)) ->
   sig (fun f:S -> S' => forall z:S, R z (f z)).
Proof.
intros S S' R H.
exists (fun z => proj1_sig (H z)).
intro z; destruct (H z); simpl.
apply (@impl_PI (R z x)); trivial.
Qed.

  Lemma sumbool_or : forall [A B:Prop], {A}+{B} -> A \/ B.
destruct 1; apply impl_PI; auto.
Qed.

  Lemma sumbool_ind' : forall [A B:Prop] [P:{A}+{B}->Prop],
    (forall a:A, P (left B a)) ->
    (forall b:B, P (right A b)) ->
    forall s:{A}+{B}, P s.
destruct s; apply impl_PI; trivial.
Qed.


End Proof_Irrelevence.

Section Smash.

Inductive smash (A:Prop) : Prop := Smash [_:A].
Scheme smash_indd := Induction for smash Sort Type.


Lemma smash_unit : forall A (p1 p2 : smash A), p1=p2.
intros.
elim p1 using smash_indd; intros.
elim p2 using smash_indd; intros.
reflexivity.
Qed.

Hint Resolve Smash : core.

Lemma smash_impl : forall A B:Prop, (A->B) -> smash A -> smash B.
destruct 2; auto.
Qed.

Lemma smash_choice : forall (A:Type) (B:A->Prop),
  (forall x:A, smash (B x)) -> smash (forall x:A, B x).
constructor; intros.
elim (H x); intros.
apply (@impl_PI (B x)); trivial.
Qed.
End Smash.

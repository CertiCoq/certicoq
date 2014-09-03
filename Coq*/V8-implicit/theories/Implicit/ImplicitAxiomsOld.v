Set Implicit Arguments.

Require Import Logic.
Require Import Specif.

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

(*Lemma smash_comm1 : forall (A:Type) (B:A->Prop),
  (forall x:A, smash (B x)) -> smash (forall x:A, B x).
Admitted.

Lemma smash_comm2 : forall (A:Type) (B:A->Prop),
  smash (forall x:A, B x) -> forall x:A, smash (B x).
destruct 1;auto.
Qed.

Require Import Logic.

Parameter trivial_type : Type -> Prop.
Parameter trivial_unit : forall A:Type, (forall x y:A, x=y) -> trivial_type A.

Lemma trivial_False : trivial_type False.
apply trivial_unit.
destruct x.
Qed.


(*
Parameter trivial_prod : forall (A:Type) (B:A->Type),
  (forall x, trivial_type (B x)) -> trivial_type (forall x, B x)
*)

Axiom trivial_implicit : forall [A:Type], [trivial_type A] -> [A] -> A.


Lemma trivial_neg : forall A : Type, (A->False) -> [A] -> False.
intros.
apply trivial_implicit.
 apply trivial_False.

 auto.
Qed.

Lemma trivial_neg' : forall A : Prop, ~A -> [A] -> False.
Proof (fun A:Prop => trivial_neg A).

Axiom False_rect': forall [P:Type], [False] -> P.

(*
Lemma trivial_neg : forall A : Type, (A->False) -> [A] -> False.
intros.
apply False_rect'.
auto.
Qed.
*)

Axiom eq_rect':
  forall [A:Type] [x:A] [P:A->Type], P x -> forall [y : A], [x = y] -> P y.

Lemma trivial_eq : forall [A : Type] [x y:A], [x=y] -> x=y.
intros.
apply eq_rect' with (2 := H).
reflexivity.
Qed.
*)
(*
Lemma trivial_singl : forall [A : Type], [forall x y:A, x=y] -> [A] -> A.
*)
End Smash.

Section Proof_Irrelevence.
(*
Axiom proof_irrelevence : forall [A:Prop], trivial_type A.
*)
Axiom impl_PI : forall [A:Prop], [A] -> A.
(*Proof fun [A] => trivial_implicit _ (proof_irrelevence A).*)


Lemma False_rect': forall [P:Type], [False] -> P.
intros.
apply False_rect.
apply (@impl_PI False); trivial.
Defined.
Lemma impl_neg : forall A : Prop, ~A -> [A] -> False.
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

  Lemma sumbool_ind' : forall [A B:Prop] [P:{A}+{B}->Prop],
    (forall a:A, P (left B a)) ->
    (forall b:B, P (right A b)) ->
    forall s:{A}+{B}, P s.
destruct s; apply impl_PI; trivial.
Qed.

Lemma smash_choice : forall (A:Type) (B:A->Prop),
  (forall x:A, smash (B x)) -> smash (forall x:A, B x).
constructor; intros.
elim (H x); intros.
apply (@impl_PI (B x)); trivial.
Qed.

End Proof_Irrelevence.




Section Obj.

(*
Inductive obj : Type :=
  repr : forall [A], A -> obj.
*)
Definition obj := forall [P:Type], (forall [A], A -> P) ->P.
Definition repr : forall [A], A -> obj :=
  fun [A] x [P] f => f A x.
Definition repr_elim [P] (f:forall [A], A -> P) (x:obj) : P :=
  x P f.

(*
Lemma discr_repr : repr 0 <> repr 1.
red; intro.
unfold repr in H.
assert (forall [P] f (F G:forall[P:Type](f:forall [A:Type],A->P),P),
        F=G -> F P f = G P f).
intros.
rewrite H0.
trivial.

set (Ty_dec := forall [X:Type], forall [Q], (X=nat->Q)->(X<>nat->Q)->Q).
set (F :=
  fun [A : Type] (X : A) (X0 : Ty_dec) =>
         X0 [A] [nat]
           (fun H1 : A = nat :> Type =>
            eq_rect [A] [fun X1 : Type => X1] X [nat] H1)
           (fun _ : A <> nat => 0)
).
generalize (H0 (Ty_dec->nat) F _ _ H).
unfold F.
intro.

assert (forall [A], A -> Ty_dec -> nat).
intros.
apply (X0 A); intro.
change ((fun X:Type=>X) nat).
apply eq_rect with (2:=H1).
exact X.
exact 0.
Show Proof.

fun [A : Type] (X : A) (X0 : Ty_dec) =>
         X0 [A] [nat]
           (fun H1 : A = nat :> Type =>
            eq_rect [A] [fun X1 : Type => X1] X [nat] H1)
           (fun _ : A <> nat => 0)


rewrite <- H1.

destruct (H1 A). 


apply (H0 in H.
*)
(* NO
Definition repr_elim' [P] (f:forall [A], [A] -> P) [x:obj] : P := ?
*)

Definition untyped_eq [A] (x:A) [B] (y:B) :=
  repr x = repr y.

End Obj.

Section Equality.

Definition impl_ieq [A:Type] (x:A) [B:Type] (y:B) :=
  forall [P:forall [C:Type], C -> Prop],
  P A x -> P B y.

Inductive ieq [A:Type] (x:A) : forall [B:Type], B -> Prop :=
  ieq_refl : ieq x x.

Lemma ieq_untyped : forall [A B] (x:A) (y:B),
  ieq x y <-> untyped_eq x y.
split; intro.
 elim H.
 red; reflexivity.

 change (repr_elim (fun [A] x => ieq x y) (repr x)).
 rewrite H.
 compute; reflexivity.
Qed.

Notation "x == y" := (ieq x y) (at level 70, no associativity).

(*
Axiom K : forall [A] [x y:A], x == y -> x = y.

Lemma ieq_rect' :
  forall [A:Type] [x] [y] [P:A->Type], [x==y] -> P x -> P y.
Proof.
intros.
elim (K _ _ _ (impl_PI _ H)).
trivial.
Defined.
*)
Lemma eq_rect_id : forall [A x] [P:A->Type] [H] [y] [e],
  eq_rect x P H y e == H.
Proof.
intros.
generalize [H]; clear H.
apply impl_PI.
case e.
reflexivity.
Qed.

(*
Lemma ieq_rect'_id : forall [A] [x] [y] [P] [H] [p],
  ieq_rect' A x y P H p == p.
Proof.
intros.
unfold ieq_rect'.
apply eq_rect_id.
Qed.
*)

Lemma eq_rect'_id : forall [A] (x:A) [P H y:_] [e:x=y],
  eq_rect' P H e == H.
Proof.
intros.
generalize [H]; clear H.
unfold eq_rect'.
case (impl_PI e).
reflexivity.
Qed.

Lemma sig_rect'_def : forall [A P P0 f s],
  @sig_rect' A P P0 f s == f (proj1_sig s) (proj2_sig s).
Proof.
intros.
unfold sig_rect'.
unfold eq_rect_r.
apply eq_rect_id.
Qed.

End Equality.

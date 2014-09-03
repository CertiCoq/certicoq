Require Import ImplicitAxioms.
Require Import ImplicitLogic.

Definition id := fun [A] (x:A) => x.
Print Extraction id.

Print Extraction
  (fix F (x:nat) :=
    match x with 0 => 0 | S k => F k + G k + x end
   with G (y:nat) :=
    match y with 0 => 1 | S k => y + F k + G k end for F).


(* TODO: understand this type... *)
Inductive obj : Type :=
  repr : forall [A:Type], A -> obj.

(* not satisfactory: Pi1 can be any type which contains an object
   equal (i.e. with same representation) to the second proj of o... *)
Definition Pi1 (o:obj) : Type :=
  forall [A:Type] [x:A], o = repr [A] x -> A.

(* We can extract a bool from object 0 because they have the same
   representation. *)
Definition Pi1_example : Pi1 (repr _ 0) -> bool :=
  fun x => x bool true (refl_equal (repr _ 0)).
Check repr.


(* Desired property (are there more?):
Lemma repr_inj : forall (A:Type(*_i*)) x y, repr [A] x = repr [A] y -> x=y.
 *)

(*
Lemma Pi2 : forall (o:obj), Pi1 o.
red; intros.
destruct o.
*)

Definition noselect (b:bool) :=
  if b then nat else nat.
Inductive nosum : Set :=
  injnat : forall [b:bool], noselect b -> nosum.

(* We should be allowed to have b implicit! *)
Lemma noselect_cst : forall b, noselect b = nat.
destruct b; trivial.
Defined.

Lemma injbak : nosum -> nat.
destruct 1.
replace nat with (noselect b); trivial.
apply impl_PI; apply noselect_cst.
Defined.
Print injbak.

Require Import ImplicitLogic.

(*
Lemma myK : forall A (x:A) p, p = refl_equal x.
intros; apply K.
change ((fun y (e:x=y) => e === refl_equal x) x p).
case p.
apply hrefl.
Qed.

Lemma inj_inj : forall n, injbak (injnat true n) = n.
unfold injbak; simpl.
rewrite (myK _ _ (impl_PI (refl_equal nat))).
reflexivity.
Qed.
*)

Definition select (b:bool) :=
  if b then nat else bool.

(* union of nat and bool (with injsum 0 = injsum true) ? *)
Inductive sum : Set :=
  injsum : forall [b:bool], select b -> sum.

Lemma merge_true_0 : injsum [true] 0 = injsum [false] true.
reflexivity.
Qed.

(*
Definition injbak2 : sum -> nat.
destruct 1.
generalize s.
apply bool_elim_imp with (P:=fun b => select b -> nat); simpl; intros.
exact H.
*)

(*
Lemma injsum_inj : forall b m n,
  injsum [b] m = injsum [b] n -> m=n.
intros.
apply K.
change (match injsum [b] m with
  injsum [b] m => m === n
 end).
rewrite H.
apply hrefl.
Qed.
*)

(*
Lemma injsum_inj : forall (m n:nat),
  injsum [true] m = injsum [true] n -> m=n.
intros.
change 
(match (injsum [true]
*)



(*
Definition smash (A:Type) := forall [Q:Type], ([A]->Q)->Q.
Definition Smash [A:Type] [x:A] : smash A := fun [Q] f => f x.
*)

(* Heterogeneous equality *)
Parameter heq : forall [A B:Type], A -> B -> Prop.
Print Extraction (forall [A B:Type], A -> B -> Prop).
Parameter hrefl : forall [A x], heq A A x x.
Parameter heq_elim :
  forall [A] [B] [x] [y] [P:forall [B] (y:B), heq _ _ x y -> Type]
         [H : heq _ _ x y],
  P A x (hrefl _ x) -> P B y H.

Lemma heq_sym : forall [A B x y], [heq A B x y] -> heq B A y x.
intros.
apply (heq_elim A B x y (fun [B0] y0 H' => heq B0 A y0 x) H).
apply hrefl.
Qed.

Definition coe [A B:Type] (H:A=B) (x:A) : B :=
  eq_rect A (fun X => X) x B H.


Definition heq_elim2 :=
  fun [A] [x] => heq_elim A A x .

Lemma heq_K : forall [A B x y] [H : heq A B x y], heq _ _ H (hrefl _ x).
intros.
change ((fun [B] (y:B) (H:heq A B x y) =>
         heq (heq A B x y) (heq A A x x) H (hrefl A x))
        B y H).
apply heq_elim.
apply hrefl.
Qed.
Lemma heq_ind :
  forall [A] [x] [y] [P:forall (y:A), heq _ _ x y -> Type]
         [H : heq _ _ x y],
  P x (hrefl _ x) -> P y H.
intros.
Admitted.

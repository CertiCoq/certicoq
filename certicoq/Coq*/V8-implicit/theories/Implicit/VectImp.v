(*Require Import Implicit.*)

Parameter A : Set .

Definition vect n :=
  forall [P:nat->Set], P 0 -> (forall [n], A -> P n -> P (S n)) -> P n.

Definition nil : vect 0 := fun [P] f g => f.

Definition cons [n] x (v:vect n) : vect (S n) :=
  fun [P] f g => g n x (v P f g).

Definition list :=
  forall [P:Set], P -> (A -> P -> P) -> P.

Definition vect2list [n] (v:vect n) : list :=
  fun [P] f g => v (fun _ => P) f (fun [_] x l => g x l).

Print Extraction vect2list.

Definition lnil : list := fun [P] f g => f.
Definition lcons x (l:list) : list :=
  fun [P] f g => g x (l P f g).

Require Import ImplicitLogic.

Definition heq_nil : nil === lnil :=
  hrefl nil.

Definition heq_cons : cons === lcons :=
  hrefl cons.


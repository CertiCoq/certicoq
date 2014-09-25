Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Traversable (T : Type -> Type) : Type :=
{ mapT : forall {F} {Ap:Applicative F} {A B}, (A -> F B) -> T A -> F (T B) }.

Section traversable.
  Context {T} {Tr:Traversable T} {F} {Ap:Applicative F}.

  Definition sequence {A} : T (F A) -> F (T A) := mapT (@id _).
  Definition forT {A B} (aT:T A) (f:A -> F B) : F (T B) := mapT f aT.
End traversable.

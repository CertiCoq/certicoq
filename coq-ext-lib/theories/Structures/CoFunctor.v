Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Section functor.
  Variable F : Type -> Type.

  Class CoFunctor : Type :=
  { cofmap : forall A B, (B -> A) -> F A -> F B }.

  Definition ID {T : Type} (f : T -> T) : Prop :=
    forall x, f x = x.

  Class CoPFunctor : Type :=
  { CoFunP : Type -> Type
  ; copfmap : forall {A B} {P : CoFunP B}, (B -> A) -> F A -> F B
  }.

  Existing Class CoFunP.
  Hint Extern 0 (@CoFunP _ _ _) => progress (simpl CoFunP) : typeclass_instances.

  Global Instance CoPFunctor_From_CoFunctor (F : CoFunctor) : CoPFunctor :=
  { CoFunP := Any
  ; copfmap := fun _ _ _ f x => cofmap f x
  }.
End functor.


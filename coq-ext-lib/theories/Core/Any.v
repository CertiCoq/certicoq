Set Implicit Arguments.
Set Strict Implicit.

(** This class should be used when no requirements are needed **)
Class Any (T : Type) : Type.

Global Instance Any_a (T : Type) : Any T.


Definition RESOLVE (T : Type) : Type := T.

Existing Class RESOLVE.

Hint Extern 0 (RESOLVE _) => unfold RESOLVE : typeclass_instances.

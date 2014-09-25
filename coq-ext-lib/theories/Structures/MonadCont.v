Require Import Monad.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class Cont (m : Type -> Type) : Type :=
{ callCC : forall a b, ((a -> m b) -> m a) -> m a }.
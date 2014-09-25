Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Identity.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section laws.
  Variable F : Type -> Type.
  Variable Functor_F : Functor F.

  Variable Feq : type1 F.

  Class FunctorLaws : Type :=
  { fmap_id : forall T (tT : type T),
    typeOk tT -> forall (f : T -> T),
    IsIdent f ->
    equal (fmap f) (@id (F T))
  ; fmap_compose : forall T U V (tT : type T) (tU : type U) (tV : type V),
    typeOk tT -> typeOk tU -> typeOk tV ->
    forall (f : T -> U) (g : U -> V),
    proper f -> proper g ->
    equal (fmap (compose g f)) (compose (fmap g) (fmap f))
  ; fmap_proper :> forall T U (tT : type T) (tU : type U),
    typeOk tT -> typeOk tU ->
    proper (@fmap _ _ T U)
  }.
End laws.
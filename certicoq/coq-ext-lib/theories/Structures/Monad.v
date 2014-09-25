Require Import ExtLib.Core.Any.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Strict Implicit.

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {t}, t -> m t
; bind : forall {t u}, m t -> (t -> m u) -> m u
}.

Class PMonad (m : Type -> Type) : Type :=
{ MonP : Type -> Type
; pret : forall {t} {Pt : MonP t}, t -> m t
; pbind : forall {t u} {Pu : MonP u}, m t -> (t -> m u) -> m u
}.

Existing Class MonP.
Hint Extern 0 (@MonP _ _ _) => progress (simpl MonP) : typeclass_instances.

Global Instance PMonad_Monad m (M : Monad m) : PMonad m :=
{ MonP := Any
; pret := fun _ _ x => ret x
; pbind := fun _ _ _ c f => bind c f
}.

Section monadic.
  Variable m : Type -> Type.
  Context {M : Monad m}.

  Definition liftM T U (f : T -> U) : m T -> m U :=
    fun x => bind x (fun x => ret (f x)).

  Definition liftM2 T U V (f : T -> U -> V) : m T -> m U -> m V :=
    Eval cbv beta iota zeta delta [ liftM ] in
      fun x y => bind x (fun x => liftM (f x) y).

  Definition liftM3 T U V W (f : T -> U -> V -> W) : m T -> m U -> m V -> m W :=
    Eval cbv beta iota zeta delta [ liftM2 ] in
      fun x y z => bind x (fun x => liftM2 (f x) y z).

  Definition apM {A B} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => liftM f aM).
End monadic.

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@pbind _ _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@pbind _ _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

End MonadNotation.

Instance Functor_Monad {m} {M:Monad m} : Functor m :=
{ fmap := @liftM _ _ }.

Instance PFunctor_PMonad {m} {M : PMonad m} : PFunctor m :=
{ FunP := MonP
; pfmap := fun _ _ _ f a =>
  pbind a (fun x => pret (f x))
}.

Instance PApplicative_PMonad {m} {M:PMonad m} : PApplicative m :=
{ AppP := MonP
; ppure := fun _ _ x => pret x
; pap := fun _ _ _ f x =>
  pbind f (fun f => pbind x (fun x => pret (f x)))
}.

Instance Applicative_Monad {m} {M:Monad m} : Applicative m :=
{ pure := @ret _ _
; ap := @apM _ _
}.

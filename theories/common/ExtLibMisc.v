Require Import ExtLib.Structures.Monads.

Import Monad.MonadNotation.
Open Scope monad_scope.
Require Import Coq.Lists.List.
Import ListNotations.


Definition flatten {m} {A: Type} `{Monad m} (lm:list (m A)) : m (list A) :=
fold_right (fun a l => l <- l;; 
                       a <- a;; 
                      ret (a :: l))
          (ret []) 
          lm.


Require Import ExtLib.Data.Monads.OptionMonad.

(*
Eval vm_compute in flatten ([Some 1; Some 2]).
Some [1; 2]

fold_left results in a reverse order.
*)
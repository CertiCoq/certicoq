From Stdlib Require Import Arith List String.
Require Import ExtLib.Structures.Monad.
From CertiRocq.Plugin Require Import CertiRocq.

Import MonadNotation.
Open Scope monad_scope.

Class IO_Types : Type :=
  { IO : Type -> Type }.

Class IO_Impl `{IO_Types} : Type :=
  { io_ret : forall (A : Type), A -> IO A
  ; io_bind : forall (A B : Type), IO A -> (A -> IO B) -> IO B
  }.

Instance IO_Monad `{IO_Impl} : Monad IO :=
  { ret  := io_ret
  ; bind := io_bind
  }.

Class StringFFI `{IO_Impl} : Type :=
  { print_string : string -> IO unit
  ; scan_string : IO string
  }.

Definition prog `{StringFFI} : IO unit :=
  print_string "What's your name?" ;;
  name <- scan_string ;;
  print_string ("Hello " ++ name ++ "!").

CertiRocq FFI IO_Impl.
CertiRocq FFI StringFFI.
CertiRocq Compile -cps prog.

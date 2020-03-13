Require Import Arith List String.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.StateMonad.
From CertiCoq.Plugin Require Import CertiCoq.

Import MonadNotation.
Open Scope monad_scope.

Module Type IO_Type.
  Parameter World : Type.
  Parameter IO : Type -> Type.
  Parameter IO_Monad : Monad IO.
End IO_Type.

Module IO_Defs <: IO_Type.
  Axiom World : Type.
  (* Definition World := unit. *)
  Definition IO (A : Type) : Type := World -> A * World.
  Instance IO_Monad : Monad IO :=
    { ret  := fun _ v => fun s => (v, s)
    ; bind := fun _ _ c1 c2 => fun s => let (v, s) := c1 s in (c2 v) s
    }.
End IO_Defs.

Import IO_Defs.

Instance IO_Monad : Monad IO := IO_Monad.

Class FFI : Type :=
  Build_FFI
    { print_string : string -> IO unit
    ; scan_string : IO string
    ; print_time : IO unit
    }.

Definition prog {ffi : FFI} : IO unit :=
  print_string "What's your name?" ;;
  name <- scan_string ;;
  print_string ("Hello " ++ name ++ "!").

CertiCoq Compile prog.
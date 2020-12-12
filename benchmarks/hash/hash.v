Require Import Arith List String.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Functor.
From CertiCoq.Plugin Require Import CertiCoq.

Import MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

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

Class Eq (A : Type) : Type :=
  { eqb : A -> A -> bool }.

Instance nat_eq : Eq nat :=
  {| eqb := Nat.eqb |}.

Instance string_eq : Eq string :=
  {| eqb := String.eqb |}.

Class Hashable (A : Type) : Type :=
  { hash : A -> nat }.

Instance hashable_nat : Hashable nat :=
  {| hash n := n |}.

Instance hashable_string : Hashable string :=
  {| hash s := String.length s |}.

Class Hash_Types : Type :=
  { HashTable : Type -> Type -> Type }.

Class HashFFI `{IO_Impl} `{Hash_Types} : Type :=
  { new    : forall {k v}, IO (HashTable k v)
  ; lookup : forall {k v} `{Eq k} `{Hashable k},
                HashTable k v -> k -> IO (option v)
  ; insert : forall {k v} `{Eq k} `{Hashable k},
                HashTable k v -> k -> v -> IO unit
  ; delete : forall {k v} `{Eq k} `{Hashable k},
                HashTable k v -> k -> IO unit
  }.

Definition prog
           `{IO_Types}
           `{@IO_Impl _}
           `{@StringFFI _ _}
           `{Hash_Types}
           `{@HashFFI _ _ _} : IO unit :=
  h <- new ;;
  insert h "Joomy" "Turkey" ;;
  insert h "Ana" "Ukraine" ;;
  insert h "Andrew" "USA" ;;

  let origin (k : string) :=
    v <- lookup h k ;;
    print_string (match v with
                  | None => "Couldn't find " ++ k
                  | Some v => k ++ " is from " ++ v
                  end) in

  origin "Joomy" ;;
  origin "Andrew".

CertiCoq FFI IO_Impl.
CertiCoq FFI StringFFI.
CertiCoq FFI HashFFI.
CertiCoq Compile -cps prog.

Recursive Extraction False_rect.
(* the False argument was not erased. the type argument was erased *)


Recursive Extraction eq_rect.

Definition f1 (a:2=3) : nat := 0.

Recursive Extraction f1.


Definition f2 (a:True) : nat := 0.

(* the argument [a] could have been erased. 
In general, arguments whose types are inhabited propositions can be erased.
So can arguments whose types' parametricity relations are 
complete, e.g. Type, nat->Type.
In future, arguments of types marked as ImplicitSet should also be erased.*)
Recursive Extraction f2. 

Definition f3 (A:Type) : nat := 0.

(* turns off removal of args:
Set Extraction Conservative Types. 
 *)

Recursive Extraction f3.

Definition f4 (A:nat -> Type) : nat := 0.

Recursive Extraction f4.

Definition f5 (b:bool) (A: if b then Type else Type) : nat := 0.

(* [A] is not erased. why? *)
Recursive Extraction f5.

Definition f6 (b:bool) (A: Type) : nat := 0.

Recursive Extraction f6.

Definition f7 (b:bool) :=
  match b return if b then Type->nat else nat with
  | true => fun (a:Type) => 0 (* not erased, because it is not a top-level lambda? *)
  |false => 0
  end.

Recursive Extraction f7.

(** Existential types become Obj.t *)

Definition xx := {T:Type & T-> T ->T}.

Recursive Extraction xx.

Inductive ExistentialType : Type:=
ext : forall (T:Set), (T->T->T) -> ExistentialType.

Recursive Extraction ExistentialType.



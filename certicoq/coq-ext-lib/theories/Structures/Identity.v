Require Import ExtLib.Core.Type.

Set Implicit Arguments.
Set Strict Implicit.

Section ident.
  Variable A : Type.
  Context {tA : type A}.
  Context {tokA : typeOk tA}.

  Class IsIdent (f : A -> A) : Prop :=
    isId : forall x, proper x -> equal (f x) x.

  Global Instance IsIdent_id : IsIdent id.
  Proof.
    unfold id. eapply equiv_prefl; auto.
  Qed.

  Global Instance IsIdent_id' : IsIdent (fun x => x) := IsIdent_id.

End ident.


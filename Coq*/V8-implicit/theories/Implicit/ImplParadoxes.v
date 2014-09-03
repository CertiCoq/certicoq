
Section NoImplicitProductDomain.

(* The first argument of product cannot be implicit *)

Variable Pi : forall [A:Type], (A -> Type) -> Type.
Variable Lam : forall [A] [B], (forall (x:A), B x) -> Pi A B.
Variable App : forall [A] [B], Pi A B -> forall (x:A), B x.

(* F is a predicate False on domain A (implicit) *)
Definition F [A] := Pi A (fun _ => False).

Lemma Ftrue : F False.
red.
apply Lam.
trivial.
Qed.

Lemma Ffalse : F True -> False.
unfold F; intro.
apply (App _ _ X I).
Qed.

(* ... but F True and F False are convertible *)

Lemma noImplicitProductDomain : False.
Proof Ffalse Ftrue.

End NoImplicitProductDomain.

(* MUST FAIL:
Inductive E [A:Type] (x:A) : A -> Prop := e : E A x x.
(equality on an implicit type: invalid in the model, but inconsistent ?)
Inductive F [A:Type] (P:A->Prop) : Prop := f : (forall (x:A), P x) -> F A P.
(F would imply the above paradox)
*)

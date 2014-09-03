
Set Implicit Arguments.

(* TODO: understand this type: it is equivalent to Leibniz equality on Implicit.obj.
   So heq might well be always true... *)
Inductive heq [A:Type] (x:A) : forall [B:Type], B -> Prop :=
  hrefl : heq x x.

Infix "===" := heq (at level 70).

Lemma eq_true_0 : true === 0.
exact (hrefl 0).
Qed.


(* Probably inconsistent since === might be always true... 
Axiom K : forall [A:Type] (x y:A), x === y -> x=y.
*)
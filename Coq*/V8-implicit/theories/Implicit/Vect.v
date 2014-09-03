Require Import ImplicitLogic.

Parameter A : Set.

Inductive vect : nat -> Set :=
  nil : vect 0
| cons : forall [n], A -> vect n -> vect (S n).

Definition head : forall [n], vect (S n) -> A.
intros n v.
generalize (refl_equal (S n)).
pattern (S n) at 1 2, v; case v.
 intro; discriminate.
 intros n' x v' _; exact x.
Defined.

Print head.
Print Extraction head.
Definition head' := Eval compute in head.
Print Extraction head'.
(*
fun v =>
  match v with
  | nil => fun H => match let () := H in I with
                    end
  | cons x v' => fun H => x
  end refl_equal
*)
Extraction vect.
Extraction head.

Require Import ImplicitAxioms.

(* Using axiom impl_PI to get rid of the equality proof *)
Definition head2 : forall [n], vect (S n) -> A.
intros n v.
generalize [refl_equal (S n)].
pattern (S n) at 2, v; case v.
 intro; apply False_rec.
 apply impl_PI.
 discriminate.

 intros n' x v' _; exact x.
Defined.
Definition head2' := Eval compute in head2.
Print Extraction head2'.
(*
fun v => match v with
         | nil => match impl_PI with
                  end
         | cons x v' => x
         end
*)
Extraction head2'.

Definition append [m] [n] (v1:vect m) (v2:vect n) : vect (m+n).
intros.
induction v1; intros.
 exact v2.

 simpl.
 constructor.
  exact a.
  exact IHv1.
Defined.
Print Extraction append.
Definition append' := Eval compute in append.
Print Extraction append'.
(*
fun v1 v2 =>
  (fix F/1 v := match v with
                | nil => v2
                | cons a v0 => cons a (F v0)
                end) v1
*)
Extraction append.


Inductive list : Set :=
  lnil : list
| lcons : A -> list -> list.

Definition heq_nil : nil === lnil :=
  hrefl nil.

Fixpoint vect2list [n] (v:vect n) {struct v} : list :=
  match v with
  | nil => lnil
  | cons [_] x v' => lcons x (vect2list _ v')
  end.

Print Extraction vect2list.

Lemma vect2list_id : forall n (v:vect n),
  vect2list _ v === v.
(*Proof (fun n (v:vect n) => hrefl v).*)
intros.
unfold vect2list.
exact (hrefl v).
Qed.

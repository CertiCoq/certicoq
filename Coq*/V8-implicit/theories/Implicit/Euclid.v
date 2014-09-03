(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Euclid.v 9245 2006-10-17 12:53:34Z notin $ i*)

Require Import Peano_dec.
Require Import Arith.
Require Import Omega.

Open Local Scope nat_scope.

Implicit Types a b n q r : nat.

Inductive diveucl a b : Set :=
  divex : forall q r, [b > r] -> [a = q * b + r] -> diveucl a b.


Lemma eucl_dev : forall n, [n > 0] -> forall m:nat, diveucl m n.
Proof.
  induction m.
   exists 0 0; abstract (simpl; trivial).

   destruct IHm.
   elim (eq_nat_dec n (S r)); intros.
    exists (S q) 0; trivial.
    abstract (rewrite e; rewrite a; ring).

    exists q (S r); abstract omega.
Defined.

Print eucl_dev.
(* The complete proof term:
eucl_dev = 
fun n [H : n > 0] (m : nat) =>
nat_rec [fun m0 : nat => diveucl m0 n]
  (divex [0] [n] 0 0 [eucl_dev_subproof n H] [eucl_dev_subproof0 n H])
  (fun (m0 : nat) (IHm : diveucl m0 n) =>
   match IHm with
   | divex q r [g] [e] =>
       sumbool_rec [fun _ : {n = S r} + {n <> S r} => diveucl (S m0) n]
         (fun [a : n = S r] =>
          divex [S m0] [n] (S q) 0 [H] [eucl_dev_subproof1 n H m0 q r g e a])
         (fun [b : n <> S r] =>
          divex [S m0] [n] q (S r) [eucl_dev_subproof4 n H m0 q r g e b]
            [eucl_dev_subproof5 n H m0 q r g e b]) (eq_nat_dec n (S r))
   end) m
     : forall n, [n > 0] -> forall m : nat, diveucl m n
*)
Print Extraction eucl_dev.
(* The extracted term looks better with some unfolding *)
Definition eucl_dev' :=
 Eval lazy beta iota delta
   [eucl_dev nat_rec nat_rect sumbool_rec sumbool_rect] in eucl_dev.
Print Extraction eucl_dev'.
(* The extracted program:
fun n m =>
  (fix F/1 n0 :=
     match n0 with
     | 0 => divex 0 0
     | S n1 => let (q,r) := F n1 in
               match eq_nat_dec n (S r) with
               | left => divex (S q) 0
               | right => divex q (S r)
               end
     end) m
*)

(* Proving that the result does not depend upon the input proof: *)
Lemma test1 : forall a b (p p' : b>0),
  eucl_dev b p a = eucl_dev b p' a.
(* This line is to abstract eucl_dev, so the result does not rely on the
   way eucl_dev was proven. *)
generalize eucl_dev; intro.
reflexivity.
Qed.

Require Import ImplicitLogic.

(* 13 / 5 = (2,3) = 11 / 4 *)
Lemma test2 : forall (p4 : 4>0) (p5 : 5>0),
  eucl_dev 5 p5 13 === eucl_dev 4 p4 11.
intros.
exact (hrefl (eucl_dev 5 p5 13)).
Qed.


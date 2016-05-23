(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import UsefulTypes.

Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.


Definition bin_rel (T : Type) := T -> T -> [univ].

Definition trans_rel {T} (R : bin_rel T) :=
  forall x y z, R x y -> R y z -> R x z.

Definition symm_rel {T} (R : bin_rel T) :=
  forall x y, R x y -> R y x.

Definition refl_rel {T} (R : bin_rel T) :=
  forall x, R x x.


(** defines when a binary relation is Less or Equal*)
Definition le_bin_rel {T:Type} (R1 R2: @bin_rel T) : [univ] :=
  forall (a b : T), R1 a b -> R2 a b.

Definition eq_bin_rel {T} (R1 R2 : bin_rel T) :=
  le_bin_rel R1 R2 # le_bin_rel R2 R1.


Definition is_ge_any_rel_sat {T:[univ]} (R: @bin_rel T)
   (C: (@bin_rel T)->[univ]) : [univ] :=
  forall (Rp: @bin_rel T), C Rp -> le_bin_rel Rp R.

Definition is_greatest_rel_sat {T:[univ]} (R: @bin_rel T)
           (C: (@bin_rel T)->[univ]) : [univ] :=
  C R # is_ge_any_rel_sat R C.

Definition bin_rel_and {T} (R1 R2:bin_rel T ):=
  fun x y => R1 x y # R2 x y.

Definition  indep_bin_rel {T:Type} (Rl Rr: T -> [univ]) : ( @bin_rel T)
  := fun x y => (Rl x # Rr y).

Lemma lift_bin_rel_if : forall {T:[univ]} (R : bin_rel T) (b:bool)
     nl1 nl2 nr1 nr2,
  R nl1 nr1
  -> R nl2 nr2
  -> R (if b then nl1 else nl2) (if b then nr1 else nr2).
Proof.
  intros. cases_if; sp.
Qed.


(* do not change the Prop in Pl Pr. they will be used for things 
    of standard library in prop*)
Lemma lift_bin_rel_ifdp : forall {T:[univ]} {Pl Pr : Prop} (R : bin_rel T) 
    (b: (@sumbool Pl  Pr))
     nl1 nl2 nr1 nr2,
  R nl1 nr1
  -> R nl2 nr2
  -> R (if b then nl1 else nl2) (if b then nr1 else nr2).
Proof.
  intros. cases_if; sp.
Qed.

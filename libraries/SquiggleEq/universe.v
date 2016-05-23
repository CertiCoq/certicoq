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

(** 
To ensure that our definitions are predicative, we try to ensure that our development compiles
when we replace uses of Prop by Type. Therefore, we use the notation [univ] which can be defined
as either Prop or Type, depending on how much we trust impredicativity on a given day!
*)

Notation "[univ]" := Prop.

Notation "! x" := (not x)%type (at level 75, right associativity).
Notation "T # U" := (T /\ U)%type (at level 80, right associativity).
Notation "T [+] U" := (T \/ U)%type (at level 80, right associativity).

Notation "{ a : T $ P }" :=
  (exists (a : T), P)
    (at level 0, a at level 99).

Notation projDep1 := proj1_sig.


Notation "injL( a )" := (or_introl a) (at level 0).
Notation "injR( a )" := (or_intror a) (at level 0).
Notation "exI( a , b )" := (ex_intro _ a b) (at level 0).
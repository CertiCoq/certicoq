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


Require Import list.

Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.


(** generalization of Substitution*)
Definition lmap (A B: Type ): Type := list (A * B).

Lemma lmap_find :
  forall {A B: Type}
         (eqdec: Deq A) (sub: lmap A B) (a : A) ,
    { b: B & LIn (a,b) sub}
    + !(LIn a (fst (split sub))).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - destruct (decideP (a'= a)) as [Hc|Hc]; subst.
      + left. exists b'. left; refl.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. right; auto.
          * intro Hf. apply Hr. simpl in Hf. destruct (split sub).
              dorn Hf; sp.
Defined.

Definition dom_lmap {A B: Type} (sub : lmap A B) : list A := map (fun x => fst x) sub.

(**same as above, but the impelemtation is guaranteed to return the first match*)
Lemma lmap_find_first: forall {A B: Type}
  (eqdec: Deq A) (sub: lmap A B) (a : A) ,
    { b: B & {n:nat & n < length sub
            # nth n sub (a,b) = (a,b)
            # (forall m, m<n ->  (nth m (dom_lmap sub) a) <> a) } }
       + !LIn a (dom_lmap sub).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - destruct (decideP (a'=a)) as [Hc|Hc]; subst.
      + left. exists b'. exists 0. split; simpl; auto. apply  lt_0_Sn.
        split; auto. introv Hm; inverts Hm.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. exists (S n). repeat(split); auto; simpl. apply lt_n_S. auto.
            introv Hlt. destruct m; auto. apply Hl1. apply lt_S_n; auto.
          * introv Hf. apply Hr. simpl in Hf. 
              dorn Hf; sp. 
Defined.

(*
Lemma lmap_find_sub_find_some: forall (lvi lvo: list NVar)
  (v b : NVar) (ev: LIn (v, b) (combine lvi lvo)),
  lmap_find deq_nvar (combine lvi lvo) v = inl (existT _ b ev)
   -> sub_find (var_ren lvi lvo) v = Some (vterm b).
AXdmitted.

Lemma lmap_find_sub_find_none: forall (lvi lvo: list NVar)
  (v: NVar) r,
  lmap_find deq_nvar (combine lvi lvo) v = inr r
   -> sub_find (var_ren lvi lvo) v = None.
AXdmitted.

Lemma lmap_apply_cons : 
  forall {A : Set} (eqdec: Deq A) (v vi vo: A) 
    (sub: lmap A A), 
  lmap_apply eqdec ((vi, vo) :: sub) v=
   if eqdec vi v
   then 
      vo
   else 
      lmap_apply eqdec sub v.
Proof.
 intros.
  unfold lmap_apply.
  simpl. destruct (eqdec vi v); subst; simpl;auto.
  destruct (lmap_find eqdec sub v).
  destruct s; auto. refl.
Qed.


Lemma lmap_apply_filter_eta : forall {A:Set}
  (deq: Deq A) (lvi lvo lv: list A) (v:A),
  !(LIn v lv)
  -> lmap_apply deq 
    (lmap_filter deq (combine lvi lvo) lv) v
     = lmap_apply deq (combine lvi lvo) v.
Proof.
  induction lvi as [| vi lvi Hind]; auto.
  introv Hnl. simpl. 
  destruct lvo as [|vo lvo]; auto.
  simpl. cases_if_sum Hd; simpl; auto.
  - rewrite Hind; auto. rewrite lmap_apply_cons.
    destruct (deq vi v);
    [subst; sp; fail | ]; auto.
  - repeat (rewrite lmap_apply_cons).
    destruct (deq vi v); auto.
Qed.
*)

(*
Lemma lmap_filter_commute_sub:
  forall lvi lvo lvr v, 
    length lvi=length lvo
    -> !(LIn v lvr)
    -> lmap_filter deq_nvar (combine lvi lvo) lvr =
        combine (fst (split (sub_filter (var_ren lvi lvo) lvr)))
          (get_sub_dom_vars (sub_filter (var_ren lvi lvo) lvr) 
             ((allvars_sub_filter lvi lvo lvr)) ).
Proof.
  induction lvi as [|vi lvi Hind]; auto. 
  introv Hleq Hnl. simpl. destruct lvo as [| vo lvo]; [inverts Hleq;fail | ].
  simpl. cases_if_sum Hd.
  pose proof (snd (assert_memvar _ _) Hd ) as Hrw.
  repnud Hrw. symmetry in Hrw.
  pose proof
  ((allvars_sub_filter (vi :: lvi) (vo :: lvo) lvr)).
  simpl in X.
  pose proof (
fun b : bool =>
 lmap_filter deq_nvar (combine lvi lvo) lvr =
 combine
   (fst
      (split
         (if b
          then sub_filter (combine lvi (map vterm lvo)) lvr
          else (vi, vterm vo) :: sub_filter (combine lvi (map vterm lvo)) lvr)))
   (get_sub_dom_vars
      (if b
       then sub_filter (combine lvi (map vterm lvo)) lvr
       else (vi, vterm vo) :: sub_filter (combine lvi (map vterm lvo)) lvr)
     ( 

     match b return 
     (
allvars_sub
    (if b
     then sub_filter (combine lvi (map vterm lvo)) lvr
     else (vi, vterm vo) :: sub_filter (combine lvi (map vterm lvo)) lvr)
     ) with
  | true => (allvars_sub_filter (vi :: lvi) (vo :: lvo) lvr)
  | false => (allvars_sub_filter (vi :: lvi) (vo :: lvo) lvr)
   end ))).

  rewrite <- Hrw.

  pose proof (@transport _ _ _ 
   (
fun b : bool =>
 lmap_filter deq_nvar (combine lvi lvo) lvr =
 combine
   (fst
      (split
         (if b
          then sub_filter (combine lvi (map vterm lvo)) lvr
          else (vi, vterm vo) :: sub_filter (combine lvi (map vterm lvo)) lvr)))
   (get_sub_dom_vars
      (if b
       then sub_filter (combine lvi (map vterm lvo)) lvr
       else (vi, vterm vo) :: sub_filter (combine lvi (map vterm lvo)) lvr)
      (match b return 
        (allvars_sub
    (if b
     then sub_filter (combine lvi (map vterm lvo)) lvr
     else (vi, vterm vo) :: 
       sub_filter (combine lvi (map vterm lvo)) lvr))
         with
       | true => (allvars_sub_filter  lvi lvo lvr)
       | false => (allvars_sub_filter_cons
             lvi lvo lvr vi vo)
        end)
)) Hrw) as Hrrw.
 allsimpl. apply Hrrw.
*)


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
Require Import list.

Require Import Recdef.
Require Import Eqdep_dec.
Require Import varInterface.
Require Import terms.
Require Import terms2.
Require Import AssociationList.
(** printing #  $\times$ #×# *)
(** printing $  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing &  $\times$ #×# *)

(* ---- substitution: td[x\ts] *) (*(\x.x+1)(x+2)*)

(*(\y.y+z)[z->y]*)
(** The goal of this section is to formalize the notion of simultaneous
    substitution([ssubst]) and alpha equality [alpha_eq].
    We needed many properties about substitution and alpha equality
    to formalize all of Nuprl. Proofs of all these properties run into
    several thousands of lines and took us several weeks to finish.
    These proofs are independent
    of the operators of the language and will work unchanged
    even if we formalize some different language, e.g. first order logic
    by merely changing the definition of [Opid]. Thus, we believe
    that we have accidentally created a fairly general-purpose
    library for nominal reasoning about virtually any language. *)


(** ** Substitution*)
(** The Substitution operation
    is a key concept in functional languages.
    Among other things, it is required to define the
    computation system and the semantics of dependent types.
    The goal of this subsection is to formalize [ssubst], a function
    that simultaneously substitutes some variables for some terms.

    We define a Substitution as a list of pairs:

[[
Definition Substitution   : Type := list (NVar # NTerm).
]]
 *)
 Local Opaque beq_var.
Generalizable Variable Opid.

Section SubstGeneric.

Context {NVar VarClass} {deqnvar : Deq NVar} {varcl freshv} 
{varclass: @VarType NVar VarClass deqnvar varcl freshv}
  `{hdeq: Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).
Notation WTerm := (@WTerm NVar Opid).
Notation CTerm := (@CTerm NVar _ Opid gts).
Notation oterm := (@oterm NVar Opid).
Notation bterm := (@bterm NVar Opid).
Notation vterm := (@vterm NVar Opid).

Definition Substitution   : Type := AssocList NVar NTerm.
Definition WfSubstitution : Type := lmap NVar WTerm.
Definition CSubstitution  : Type := lmap NVar  CTerm.

(** % \noindent %
  The function [var_ren] below provides a way to 
  define the specialized substitutions that are 
  variable renamings (substituting one variable for another).
  The %\coqslibref{combine}{Coq.Lists.List}{\coqdocdefinition{combine}}% function
  from the standard library takes two lists and zips them up.
 *)

Definition var_ren (lvo lvn : list NVar) : Substitution :=
  combine lvo (map vterm lvn).


(** % \noindent \\* %
The domain and range of a substitution are defined as follows:

[[
Definition dom_sub  (sub : Substitution) : list NVar := map (fun x => fst x) sub.
]]

*)

Definition Sub  := Substitution.
Definition CSub := CSubstitution.

Definition dom_sub : Substitution -> (list NVar):= @ALDom NVar NTerm.
Definition dom_csub   (sub : CSubstitution)  := map (fun x => fst x) sub.
Definition wf_dom_sub (sub : WfSubstitution) := map (fun x => fst x) sub.

Definition range  (sub : Substitution)  : list NTerm := map (fun x => snd x) sub.

(** % \noindent \\*%
  We need to define some helper functions before defining the
  substitution function that simultaneously substitutes the
  in the first component([NVar]s) of the pairs with the second ones([NTerm]s).
*)

Definition crange (sub : CSubstitution) : list CTerm := map (fun x => snd x) sub.
Lemma deq_in_sub :
  forall v t (sub : Substitution),
    LIn (v,t) sub + !LIn (v,t) sub.
Proof using deqnvar hdeq.
  introv.
  apply in_deq; sp.
  apply deq_prod; sp; try (apply deq_nvar); try (apply deq_nterm).
Qed.

Definition sub_range_sat (sub: Substitution) (P: NTerm -> [univ]) :=
  forall v t, LIn (v,t) sub -> P t.

Definition sub_range_satb (sub: Substitution) (P: NTerm -> [univ]) :=
  forall t, assert (memberb _ t (range sub)) -> P t.

Lemma in_range :
  forall t (sub: Substitution), LIn t (range sub) -> {v : NVar $ LIn (v,t) sub}.
Proof using.
  induction sub; allsimpl; sp; allsimpl; subst.
  exists a0; sp.
  exists v; sp.
Qed.

Lemma in_range_t :
  forall t (sub: Substitution), LIn t (range sub) -> {v : NVar & LIn (v,t) sub}.
Proof using deqnvar hdeq.
  introv i.
  rw <- (@assert_memberb NTerm _) in i.
  induction sub; allsimpl; sp; allsimpl.
  unfold assert in i; sp.
  rewrite decide_decideP in i.
  destruct (decideP (a=t)); subst; sp.
  exists a0; sp.
  exists v; sp.
Qed.

Lemma sub_range_sat_implies_b :
  forall (sub: Substitution) P, sub_range_sat sub P -> sub_range_satb sub P.
Proof using deqnvar.
  unfold sub_range_sat, sub_range_satb; introv s a.
  rw (@assert_memberb NTerm _) in a.
  allapply in_range_t; sp.
  discover; sp. eapply s; eauto.
Qed.

Lemma sub_range_sat_implies :
  forall (P Q : NTerm -> [univ]),
    (forall t, P t -> Q t)
    -> forall (sub: Substitution),
         sub_range_sat sub P
         -> sub_range_sat sub Q.
Proof using.
  introv Himp Hsat Hin. apply Hsat in Hin.
  apply Himp in Hin. sp.
Qed.

Definition prog_sub (sub : Substitution) := sub_range_sat sub isprogram.

Definition wf_sub (sub : Substitution) := sub_range_sat sub nt_wf.

Require Import list.
(* will not specialize this lemma.. those are always trivial*)
Lemma sub_app_sat :
  forall (P : NTerm -> [univ]) sub1 sub2,
    sub_range_sat sub1 P
    -> sub_range_sat sub2 P
    -> sub_range_sat (sub1 ++ sub2) P.
Proof using.
  introv sat1 sat2 Hin.
  apply in_app_iff in Hin.
  dorn Hin; [ apply sat1 in Hin | apply sat2 in Hin]; trivial.
Qed.

Lemma sub_app_sat_if :
  forall (P : NTerm -> [univ]) sub1 sub2,
    sub_range_sat (sub1 ++ sub2) P
    -> sub_range_sat sub1 P # sub_range_sat sub2 P.
Proof using.
  introv  Hsat.
  split;
    introv Hin;
    assert (LIn (v, t) (sub1 ++ sub2))
      as Hx
        by (apply in_app_iff;((left;sp;fail) || (right;sp;fail)));
    apply Hsat in Hx;sp.
Qed.

Definition sub_find : forall (sub : Substitution) (var : NVar), option NTerm :=
 @ALFind NVar NTerm _.


Lemma fold_var_ren :
  forall lvo lvn,
    combine lvo (map vterm lvn) = var_ren lvo lvn.
Proof using. sp.
Qed.



Definition lmap_apply {A : Type} (eqdec: Deq A) (sub: lmap A A) (a:A): A :=
  match lmap_find eqdec sub a with
    | inl (existT _ a' _) =>  a'
    | inr _ => a
  end.

Definition  lmap_lapply {A : Type} (eqdec: Deq A) (sub: lmap A A)  (la:list A): list A :=
  map (fun a:A =>  lmap_apply eqdec sub a) la.

Definition  lvmap_lapply  (sub: lmap NVar NVar)  (la:list NVar): list NVar :=
  map (fun a:NVar =>  lmap_apply deq_nvar sub a) la.


Hint Rewrite deqP_refl.
Hint Rewrite deq_refl.
Hint Rewrite deqP_refl:SquiggleEq.
Hint Rewrite deq_refl:SquiggleEq.
Lemma sub_lmap_find: forall (sub: Substitution) v, sub_find sub v =
        proj_as_option (lmap_find deq_nvar sub v).
Proof using.
  clear hdeq.
  induction sub as [| a]; intros ; auto; simpl. 
  destruct a.
  Locate beq_deq.
 rewrite (@beq_deq NVar). simpl.
  destruct (decideP (n = v));
  subst; autorewrite with SquiggleEq; simpl in *; auto.
  rewrite IHsub. destruct ((lmap_find deq_nvar sub v)); simpl;
  try(destruct s; simpl); auto. 
Qed.


Lemma sub_lmap_find_first: forall (sub: Substitution) v, sub_find sub v =
        proj_as_option (lmap_find_first deq_nvar sub v).
Proof using.
  induction sub as [| a]; intros ; auto; simpl. 
  destruct a. repeat rewrite beq_deq.  simpl in *.
  destruct (decideP (n = v));
  simpl; subst; autorewrite with SquiggleEq;  subst; auto.
  rewrite IHsub. destruct ((lmap_find_first deq_nvar sub v)); simpl;
  exrepnd; auto.
Qed.

(*
Lemma match_sub_lmap_find: forall sub v cs cn, 
  match (sub_find sub v)
  | Some t => cs t
  | None => cn
  end
    =
  match (sub_find sub v)
  | Some t => cs t
  | None => cn
  end
*)  


Definition csub2sub (sub : CSubstitution) : Substitution :=
  map (fun x => (fst x, get_cterm (snd x))) sub.

Lemma csub2sub_app :
  forall sub1 sub2,
    csub2sub sub1 ++ csub2sub sub2 = csub2sub (sub1 ++ sub2).
Proof using.
  unfold csub2sub; sp.
  rewrite <- map_app; sp.
Qed.

Lemma csub2sub_snoc :
  forall sub v t,
    csub2sub (snoc sub (v, t)) = snoc (csub2sub sub) (v, get_cterm t).
Proof using.
  unfold csub2sub; sp.
  rewrite map_snoc; sp.
Qed.

Lemma in_csub2sub :
  forall sub : CSubstitution,
  forall v : NVar,
  forall u : NTerm,
    LIn (v, u) (csub2sub sub)
    -> isprogram u.
Proof using.
  induction sub; simpl; sp; destruct a; allsimpl.
  inj.
  allrw @isprogram_eq; sp.
  apply_in_hyp p; sp.
Qed.


(**

  We say that a term [t] is covered by a list of variables [vs] if the
  free variables of [t] are all in [vs].

*)

Definition covered (t : NTerm) (vs : list NVar) :=
  assert (sub_vars (free_vars t) vs).

Definition over_vars (vs : list NVar) (sub : CSubstitution) :=
  assert (sub_vars vs (dom_csub sub)).

(**

  A term [t] is covered by a substitution [sub] if the free variables
  of [t] are all in the domain of [sub].

*)

Definition cover_vars (t : NTerm) (sub : CSubstitution) :=
  over_vars (free_vars t) sub.

(**

  We sometimes need the slightly more general definition that
  expresses that a term [t] is covered by a substitution [sub] up to a
  set of variables [vs], meaning that the free variables of [t] have
  to either be in [vs] or in the domain of [sub].  Such a concept is
  needed to deal with type families such as function or W types.

*)

Definition cover_vars_upto (t : NTerm) (sub : CSub) (vs : list NVar) :=
  assert (sub_vars (free_vars t) (vs ++ dom_csub sub)).




(* filters out the mappings whose domain lies in vars *)
Fixpoint lmap_filter {A B: Type}
  (eqdec: Deq A) (sub: lmap A B)  (vars : list A) : lmap A B :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if in_deq A eqdec  v vars
      then lmap_filter eqdec xs vars
      else (v, t) :: lmap_filter eqdec xs vars
  end.

(* removes from sub the variables from vars *)

Definition sub_filter : 
   forall (sub : Substitution) (vars : list NVar), Substitution :=
 @ALFilter NVar NTerm _.


Lemma sub_filter_subset :
  forall (sub: Substitution) vars,
    subset (sub_filter sub vars) sub.
Proof using.
  induction sub; simpl; sp.
  destruct (memvar a0 vars).
  apply subset_cons1; auto.
  apply subset_cons2; auto.
Qed.

Lemma sub_filter_nil_r :
  forall sub, sub_filter sub [] = sub.
Proof using.
  induction sub; simpl; sp.
  rewrite IHsub; auto.
Qed.

Lemma in_sub_filter :
  forall v t (sub: Substitution) vars,
    LIn (v, t) (sub_filter sub vars)
    <=>
    (
      LIn (v, t) sub
      #
      ! LIn v vars
    ).
Proof using.
  induction sub; simpl; sp.
  split; sp.
  boolvar; simpl; allrw; split; sp; cpx.
Qed.

Lemma sub_filter_sat :  forall P (sub: Substitution) lv,
  sub_range_sat  sub P
  -> sub_range_sat (sub_filter sub lv) P.
Proof using. introv Hall hsub. apply in_sub_filter in hsub. repnd.
  apply Hall in hsub0; auto.
Qed.


Lemma sub_filter_app :
  forall sub1 sub2 vars,
    sub_filter (sub1 ++ sub2) vars = sub_filter sub1 vars ++ sub_filter sub2 vars.
Proof using.
  induction sub1; simpl; sp.
  rewrite IHsub1; auto.
  destruct (memvar a0 vars); sp.
Qed.

Lemma sub_filter_snoc :
  forall (sub: Substitution) v t vars,
    sub_filter (snoc sub (v, t)) vars
    = if memvar v vars
      then sub_filter sub vars
      else snoc (sub_filter sub vars) (v, t).
Proof using.
  induction sub; simpl; sp; allsimpl.
  rewrite IHsub.
  destruct (eq_var_dec a0 v); subst.
  destruct (memvar v vars); sp.
  destruct (memvar v vars); sp.
  destruct (memvar a0 vars); sp.
Qed.

Lemma dom_sub_sub_filter :
  forall l (sub: Substitution),
    remove_nvars l (dom_sub sub) = dom_sub (sub_filter sub l).
Proof using.
  induction sub; simpl; sp; allsimpl.
  apply remove_nvars_nil_r.
  rewrite remove_nvars_cons_r.
  destruct (memvar a0 l); auto.
  rewrite IHsub.
  simpl; auto.
Qed.


Lemma sub_filter_app_r :
  forall (sub: Substitution) vs1 vs2,
    sub_filter sub (vs1 ++ vs2)
    = sub_filter (sub_filter sub vs1) vs2.
Proof using.
  induction sub; simpl; sp.
  rewrite memvar_app.
  destruct (memvar a0 vs1); simpl.
  apply IHsub.
  destruct (memvar a0 vs2); simpl.
  apply IHsub.
  rewrite IHsub; auto.
Qed.


Lemma cover_vars_proof_irrelevance :
  forall t sub,
  forall x y  : cover_vars t sub,
    x = y.
Proof using.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma cover_vars_upto_proof_irrelevance :
  forall t sub vs,
  forall x y  : cover_vars_upto t sub vs,
    x = y.
Proof using.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.


Lemma dom_sub_snoc :
  forall s v t,
    dom_sub (snoc s (v, t)) = snoc (dom_sub s) v.
Proof using.
  induction s; simpl; sp; simpl; allrw; sp.
Qed.

Lemma dom_csub_snoc :
  forall sub x,
    dom_csub (snoc sub x) = snoc (dom_csub sub) (fst x).
Proof using.
  induction sub; simpl; sp.
  rewrite IHsub; sp.
Qed.




Lemma dom_csub_app :
  forall sub1 sub2,
    dom_csub (sub1 ++ sub2) = dom_csub sub1 ++ dom_csub sub2.
Proof using.
  unfold dom_csub; sp.
  rewrite map_app; sp.
Qed.

Lemma dom_csub_eq :
  forall sub,
    dom_sub (csub2sub sub) = dom_csub sub.
Proof using.
  induction sub; simpl; sp.
  rewrite IHsub; sp.
Qed.


Lemma in_dom_sub :
  forall v t sub,
    LIn (v, t) sub
    -> LIn v (dom_sub sub).
Proof using.
  unfold dom_sub; sp.
  rw in_map_iff.
  exists (v, t); sp.
Qed.

Lemma dom_sub_app :
  forall sub1 sub2,
    dom_sub (sub1 ++ sub2) = dom_sub sub1 ++ dom_sub sub2.
Proof using.
  unfold dom_sub, ALDom; intros; rw map_app; auto.
Qed.


Lemma in_dom_sub_exists :
  forall v sub,
    LIn v (dom_sub sub)
    -> {t : NTerm $ sub_find sub v = Some t}.
Proof.
  induction sub; simpl; sp; allsimpl; subst; simpl; boolvar.
  exists a; sp.
  exists a; sp.
  exists a; sp.
  exists t; sp.
Qed.



Definition insub sub var : bool :=
  match sub_find sub var with
    | Some _ => true
    | None => false
  end.

Lemma sub_find_some :
  forall sub : Substitution,
  forall v : NVar,
  forall u : NTerm,
    sub_find sub v = Some u
    -> LIn (v, u) sub.
Proof using.
  induction sub; simpl; sp.
  inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H; subst.
  apply beq_var_eq in Heqb; subst.
  left; auto.
  apply IHsub in H; right; auto.
Qed.

Lemma sub_find_some_eq :
  forall sub : Substitution,
  forall v : NVar,
  forall u t : NTerm,
    sub_find sub v = Some t
    -> sub_find sub v = Some u
    -> t = u.
Proof using.
  induction sub; simpl; sp.
  inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H; subst.
  inversion H0; subst.
  auto.
  apply IHsub with (t := t) in H0; auto.
Qed.

Lemma sub_find_app :
  forall v sub1 sub2,
    sub_find (sub1 ++ sub2) v
    = match sub_find sub1 v with
        | Some t => Some t
        | None => sub_find sub2 v
      end.
Proof using.
  induction sub1; simpl; sp.
  destruct (beq_var a0 v); auto.
Qed.

Lemma sub_find_snoc :
  forall v sub x t,
    sub_find (snoc sub (x, t)) v
    = match sub_find sub v with
        | Some t => Some t
        | None => if beq_var x v then Some t else None
      end.
Proof using.
  induction sub; simpl; sp; allsimpl.
  destruct (beq_var a0 v); auto.
Qed.

Lemma sub_find_some_app :
  forall v t sub1 sub2,
    sub_find sub1 v = Some t
    -> sub_find (sub1 ++ sub2) v = Some t.
Proof using.
  intros.
  rw sub_find_app.
  rw H; auto.
Qed.

Lemma sub_find_none :
  forall sub : Substitution,
  forall v : NVar,
  forall u : NTerm,
    sub_find sub v = None
    -> forall u, ! LIn (v, u) sub.
Proof using.
  induction sub; simpl; sp; inj.
  rw <- @beq_var_refl in H; sp.
  remember (beq_var a0 v).
  destruct b; sp.
  apply IHsub with (u0 := u0) in H; auto.
Qed.

Lemma sub_find_none2 :
  forall sub v,
    sub_find sub v = None
    -> ! LIn v (dom_sub sub).
Proof using.
  induction sub; simpl; sp; subst; allsimpl.
  rw <- @beq_var_refl in H; inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H.
  apply IHsub in H; auto.
Qed.

Lemma sub_find_none_iff :
  forall sub v,
    sub_find sub v = None
    <=> ! LIn v (dom_sub sub).
Proof using.
  induction sub; simpl; sp; subst; split; sp; allsimpl; subst.
  rw <- @beq_var_refl in H; inversion H.
  remember (beq_var a0 v); destruct b.
  inversion H.
  rw IHsub in H; auto.
  remember (beq_var a0 v); destruct b.
  provefalse; apply H.
  apply beq_var_eq in Heqb; left; auto.
  symmetry in Heqb.
  apply beq_var_false_not_eq in Heqb.
  rw IHsub; intro.
  apply H; right; auto.
Qed.

(* computes the set of free variables occurring in the co-domain of sub *)
Fixpoint sub_free_vars (sub : Substitution) : list NVar :=
  match sub with
  | nil => nil
  | (v, t) :: xs => free_vars t ++ sub_free_vars xs
  end.

Lemma in_sub_free_vars :
  forall sub v,
    LIn v (sub_free_vars sub)
    -> {x : NVar $ {t : NTerm $
         LIn (x,t) sub # LIn v (free_vars t) }}.
Proof using.
  induction sub; simpl; sp; allsimpl.
  allrw in_app_iff; sp.
  exists a0 a; sp. apply IHsub in H. sp.
  exists x t; sp.
Qed.

Lemma in_sub_free_vars_iff :
  forall sub v,
    LIn v (sub_free_vars sub)
    <=> {x : NVar $ {t : NTerm $
         LIn (x,t) sub # LIn v (free_vars t)}}.
Proof using.
  induction sub; simpl; sp.
  split; sp.
  rw in_app_iff.
  rw IHsub; split; sp; inj; sp.
  exists a0 a; sp.
  exists x t; sp.
  right; exists x t; sp.
Qed.

Lemma subset_free_vars_mem :
  forall v t sub,
    LIn (v, t) sub
    -> subset (free_vars t) (sub_free_vars sub).
Proof using.
  induction sub; simpl; sp; inj.
  apply subset_app_r; apply subset_refl.
  apply subset_app_l; auto.
Qed.

Lemma subset_sub_free_vars :
  forall sub1 sub2,
    subset sub1 sub2
    -> subset (sub_free_vars sub1) (sub_free_vars sub2).
Proof using.
  induction sub1; simpl; sp.
  destruct sub2.
  allapply subset_cons_nil; sp.
  destruct p.
  simpl.
  allrw cons_subset; allsimpl; sp; inj.
  rw app_subset; sp.
  apply subset_app_r; apply subset_refl.
  apply_in_hyp p; allsimpl; sp.
  rw app_subset; sp.
  apply subset_app_l.
  apply subset_free_vars_mem with (v := a0); auto.
  apply_in_hyp p; allsimpl; sp.
Qed.

Lemma sub_free_vars_isprogram :
  forall sub,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> null (sub_free_vars sub).
Proof using.
  induction sub; simpl; intros k; sp.
  rw null_app; sp.
  generalize (k a0 a); intro i.
  dest_imp i hyp.
  unfold isprogram, closed in i; sp.
  allrw; sp.
  apply IHsub; sp.
  apply k with (v := v); sp.
Qed.

Definition sub_mk_rename (var : NVar) (fvars : list NVar) : NVar :=
  if memvar var fvars
  then fresh_var fvars
  else var.

(** chose new variables if for bvars if they are in fvars.
    if new variables have to be chose, make sure that
    the new choices are disjoint from lva.

    need not choose a new var if it is in lva but not in fvars.
    This is to avoid renamings as much as possible
*)
Fixpoint sub_mk_renames2 (bvars : list NVar) (fvars : list NVar)
          (lva: list NVar): (list NVar) * Substitution :=
  match bvars with
  | nil => (nil, nil)
  | v :: vs =>
     let (vars, sub) := sub_mk_renames2 vs fvars lva in
     if memvar v fvars
     then let u := fresh_var (vars ++ fvars ++ lva) in
          (u :: vars, (v, vterm u) :: sub)
     else (v :: vars, sub)
  end.

(* generates renamings for all the variables in bvars that also occur in fvars *)
Fixpoint sub_mk_renames (bvars : list NVar) (fvars : list NVar) :
    (list NVar) * Substitution :=
  match bvars with
  | nil => (nil, nil)
  | v :: vs =>
     let (vars, sub) := sub_mk_renames vs fvars in
     if memvar v fvars
     then let u := fresh_var (vars ++ fvars) in
          (u :: vars, (v, vterm u) :: sub)
     else (v :: vars, sub)
  end.


Lemma sub_mk_renames_eta :
  forall vs frees,
    sub_mk_renames vs frees
    = (fst (sub_mk_renames vs frees), snd (sub_mk_renames vs frees)).
Proof using.
  induction vs; simpl; sp.
  rw IHvs; simpl.
  destruct (memvar a frees).
  simpl; auto.
  simpl; auto.
Qed.

Lemma sub_mk_renames2_eta :
  forall vs frees lva,
    sub_mk_renames2 vs frees lva
    = (fst (sub_mk_renames2 vs frees lva), snd (sub_mk_renames2 vs frees lva)).
Proof using.
  induction vs; simpl; sp.
  rw IHvs; simpl.
  destruct (memvar a frees).
  simpl; auto.
  simpl; auto.
Qed.

Lemma sub_mk_renames_snd_vterm :
  forall bvars fvars v t,
    LIn (v,t) (snd (sub_mk_renames bvars fvars))
    -> {x : NVar $ t = vterm x}.
Proof using.
  induction bvars; simpl; introv k; sp.
  rw sub_mk_renames_eta in k; allsimpl.
  destruct (memvar a fvars); allsimpl; sp; inj.
  exists (fresh_var (fst (sub_mk_renames bvars fvars) ++ fvars)); auto.
  discover; sp.
  apply IHbvars in H. sp.
  apply IHbvars in k. sp.
Qed.

Lemma sub_mk_renames2_snd_vterm :
  forall bvars fvars v t lva,
    LIn (v,t) (snd (sub_mk_renames2 bvars fvars lva))
    -> {x : NVar $ t = vterm x}.
Proof using.
  induction bvars; simpl; introv k; sp.
  rw sub_mk_renames2_eta in k; allsimpl.
  destruct (memvar a fvars); allsimpl; sp; inj.
  eexists; eauto.
  apply IHbvars in H. sp.
  apply IHbvars in k. sp.
Qed.

Lemma sub_mk_renames2_nil :
  forall vs lva,
    sub_mk_renames2 vs [] lva = (vs, []).
Proof using.
  induction vs; simpl; sp.
  rw IHvs. sp.
Qed.

Lemma sub_mk_renames_nil :
  forall vs,
    sub_mk_renames vs [] = (vs, []).
Proof using.
  induction vs; simpl; sp.
  rw sub_mk_renames_eta.
  rw IHvs; simpl; auto.
Qed.

Lemma sub_mk_renames_length :
  forall vs frees,
    length (fst (sub_mk_renames vs frees)) = length vs.
Proof using.
  induction vs; simpl; sp.
  rw sub_mk_renames_eta; simpl.
  destruct (memvar a frees); simpl; rw IHvs; auto.
Qed.

Lemma sub_mk_renames2_length :
  forall vs frees lva,
    length (fst (sub_mk_renames2 vs frees lva)) = length vs.
Proof using.
  induction vs; simpl; sp.
  
  rw sub_mk_renames2_eta; simpl.
  destruct (memvar a frees); simpl; rw IHvs; auto.
Qed.

Lemma in_snd_sub_mk_renames :
  forall v t bvars fvars,
    LIn (v, t) (snd (sub_mk_renames bvars fvars))
    ->
    (
      LIn v bvars
      #
      LIn v fvars
      #
      {x : NVar $ (t = vterm x # ! LIn x fvars)}
    ).
Proof using.
  induction bvars; simpl; introv k; sp.

  - rw sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp;
    apply_in_hyp p; sp.

  - rw sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp.
    symmetry in Heqb.
    rw fold_assert in Heqb.
    rw @assert_memvar in Heqb; auto.
    apply_in_hyp p; sp.
    apply_in_hyp p; sp.

  - rw sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp.
    symmetry in Heqb.
    rw fold_assert in Heqb.
    rw @assert_memvar in Heqb; auto.
    exists (fresh_var (fst (sub_mk_renames bvars fvars) ++ fvars)); sp.
    assert (! (LIn (fresh_var (fst (sub_mk_renames bvars fvars) ++ fvars))
                  (fst (sub_mk_renames bvars fvars) ++ fvars))) as nin
      by apply fresh_var_not_in.
    apply nin.
    rw in_app_iff; sp.
    apply_in_hyp p; sp.
    apply_in_hyp p; sp.
Qed.



Lemma sub_find_sub_filter :
  forall sub vars n,
    LIn n vars -> sub_find (sub_filter sub vars) n = None.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 vars); destruct b; simpl; symmetry in Heqb.
  apply_in_hyp p; sp.
  remember (beq_var a0 n); destruct b.
  apply beq_var_eq in Heqb0; subst.
  rw not_of_assert in Heqb.
  rw @assert_memvar in Heqb; sp.
  apply_in_hyp p; sp.
Qed.



Definition disjoint_bv_sub (nt:NTerm) (sub: Substitution) :=
  sub_range_sat sub (fun t => disjoint (free_vars t) (bound_vars nt)).

Theorem prog_sub_disjoint_bv_sub:
    forall nt sub, prog_sub sub -> disjoint_bv_sub nt sub.
Proof using. intros nt. apply sub_range_sat_implies.
  introv Hpr. invertsn Hpr.
  rw Hpr. introv Hin. inverts Hin.
Qed.


Definition disjoint_bvbt_sub (bt:BTerm) (sub: Substitution) :=
  sub_range_sat sub (fun t => disjoint (free_vars t) (bound_vars_bterm bt)).

(* Eval simpl in (ssubst (mk_lam nvarx (vterm nvary)) [(nvarz,vterm nvarx)]). 
 This was a bug in ssubst. it will return \lambda y.y because
 the new variables were not disjoint from the fvars of the body
*)

(*
Lemma disjoint_bvbt_sub_ot : forall op lbt bt sub,
  LIn bt lbt 
  -> disjoint_bv_sub (oterm op lbt) sub
  -> disjoint_bvbt_sub bt sub.
AdCmitted.

Fixpoint ssubstd (t : NTerm) (sub : Substitution) (p: disjoint_bv_sub t sub): NTerm :=
  (*if nullb sub then t else*)
  match t with
  | vterm var =>
      match sub_find sub var with
      | Some t => t
      | None => t
      end
  | oterm op bts => let btsp := pairInProofs bts in
      let f:= (fun ppp => match ppp with 
                         | existT bt  pp => ssubst_btermc bt sub _ 
                            (disjoint_bvbt_sub_ot _ _ _ _ pp p)
                         end) in
                            
    oterm op (map f bts)
  end
 with ssubst_btermc (bt : BTerm) (sub : Substitution) (p:disjoint_bvbt_sub bt sub): BTerm :=
  match bt with
  | bterm lv nt =>
      bterm lv (ssubstc nt (sub_filter sub lv) _)
  end.
*)


(** % \noindent \\* %
    The following function is an auxilliary one that performs a
    [Substitution] on an [NTerm] assuming that its bound
    variables of are already disjoint from the free variables
    of the range of the [Substitution].
    
  *)
  (*if nullb sub then t else*)

End SubstGeneric.

Ltac false_disjoint :=
match goal with
| [ H: !( disjoint  _ _) |- _] => provefalse; apply H; clear H; disjoint_reasoningv
end.

(** clear_irr removes the duplicates of proofs of propositions that
 * have proof irrelevance. *)
Ltac clear_irr :=
  repeat match goal with
           | [ H1 : cover_vars ?a ?b, H2 : cover_vars ?a ?b |- _ ] =>
             assert (H2 = H1) by apply cover_vars_proof_irrelevance; subst
           | [ H1 : cover_vars_upto ?a ?b ?c, H2 : cover_vars_upto ?a ?b ?c |- _ ] =>
             assert (H2 = H1) by apply cover_vars_upto_proof_irrelevance; subst
           | [ H1 : wf_term ?a, H2 : wf_term ?a |- _ ] =>
             assert (H2 = H1) by apply wf_term_proof_irrelevance; subst
           | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
             assert (H2 = H1) by apply isprog_proof_irrelevance; subst
         end.

Fixpoint ssubst_aux {NVar} `{Deq NVar} {Opid} (nt : @NTerm NVar Opid) (sub : Substitution) 
  : (@NTerm NVar Opid):=
  match nt with
  | vterm var =>
      match sub_find sub var with
      | Some t => t
      | None => nt
      end
  | oterm op bts => oterm op (map (fun t => ssubst_bterm_aux t sub) bts)
  end
 with ssubst_bterm_aux {NVar} `{Deq NVar} {Opid} (bt : @BTerm NVar Opid) (sub : Substitution) 
  : (@BTerm NVar Opid):=
  match bt with
  | bterm lv nt => bterm lv (ssubst_aux nt (sub_filter sub lv))
  end.


(** % \noindent \\* % 
  To define the actual substitution function, we just have to pre-process [t]
  such that its bound variables have been renamed to avoid
  the free variables of the range of [sub]. 
  Here is a function that does that. 
*)


Fixpoint change_bvars_alpha {NVar VarCl : Type}
`{Deq NVar}
    {fv : FreshVars NVar VarCl}
    {vc : VarClass NVar VarCl}
{Opid} (lv : list NVar ) (t : (@NTerm NVar Opid)) 
: (@NTerm NVar Opid) :=
match t with
| vterm v => vterm v
| oterm o lbt => oterm o (map (@change_bvars_alphabt NVar _  _ fv vc Opid lv) lbt)
end
with change_bvars_alphabt {NVar VarCl : Type} 
`{Deq NVar}    {fv: FreshVars NVar VarCl}
    {vc : VarClass NVar VarCl}
  {Opid} lv 
(bt: @BTerm NVar Opid) 
: (@BTerm NVar Opid):=
match bt with
| bterm blv bnt => 
    let bnt' := change_bvars_alpha lv bnt in
  (* All boundvars are produced by the [freshReplacements] function,
    which produces unique (no_repeats) variables.
    Also, these variables are disjoint from the bound variables of
    the subterm bnt'.
    So all occurrences of bound variables in the result are distinct.
    *)
    let lvn := freshReplacements blv (lv++(all_vars bnt')) in
         bterm lvn (ssubst_aux bnt' (var_ren blv lvn))
end.



(** % \noindent \\* %
  When we define alpha equality in the next section, we prove that
[change_bvars_alpha] returns a term which is alpha equal to the input.
Finally, here is the function that safely perfoms
  a [Substitution] on an [NTerm].

*)
(*
Fixpoint makeBvarsUnique1 {NVar VarClass : Type}
{gts : GenericTermSig} (lv : list NVar ) (t : (@NTerm NVar gts)) 
: (@NTerm NVar gts * list NVar) :=
match t with
| vterm v => (vterm v, [])
| oterm o lbt => 
  let lbt_bv := (map (@makeBvarsUniqueBt1 NVar _ _ _ _ lv) lbt) in 
  (oterm o (map fst lbt_bv), 

end
with makeBvarsUniqueBt1 {NVar VarClass : Type} `{VarType NVar VarClass}  
{gts : GenericTermSig} lv  (bt: @BTerm NVar gts) 
: (@BTerm NVar gts  * list NVar):=
match bt with
| bterm blv bnt => 
    let bnt' := @makeBvarsUnique NVar _ _ _ _  lv bnt in
    let bvars := bound_vars bnt in
    let lvn := freshReplacements blv (lv++(all_vars bnt')) in
         bterm lvn (ssubst_aux bnt' (var_ren blv lvn))
end. 
*)
Class FreeVars (T V:Type) := freevars : T -> list V.

Fixpoint ssubst {NVar VarCl} {d : Deq NVar}
    {fv : FreshVars NVar VarCl}
    {vc : VarClass NVar VarCl}
{Opid}
  (t : @NTerm NVar Opid) (sub : @Substitution NVar Opid) : @NTerm NVar Opid:=
match t with
| terms.vterm var =>
    match sub_find sub var  with
    | Some st => st
    | None => t
    end
| oterm op bts => oterm op (map (fun t => @ssubst_bterm NVar VarCl d _ _ Opid t sub) bts)
end
with ssubst_bterm  {NVar VarCl}  {d : Deq NVar}
    {fv : FreshVars NVar VarCl}
    {vc : VarClass NVar VarCl}
   {Opid}
  (bt : @BTerm NVar Opid) (sub : Substitution) : @BTerm  NVar Opid :=
  match bt with
  | bterm [] nt => bterm [] (ssubst nt sub)
  | bterm lv nt => 
      let bt :=
         let sfr := flat_map free_vars (range sub) in
        if dec_disjointv (lv++bound_vars nt) sfr 
        then bt 
        else change_bvars_alphabt sfr bt
        in ssubst_bterm_aux bt sub
      (** doing alpha renaming recursively can be costly *)
  end.



Section SubstGeneric2.
Typeclasses eauto :=10.
Context {NVar VarClass} {deqnvar : Deq NVar} {varcl freshv} 
{varclass: @VarType NVar VarClass deqnvar varcl freshv} 
 `{hdeq : Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).
Notation WTerm := (@WTerm NVar Opid _).
Notation CTerm := (@CTerm NVar _  Opid).
Notation Substitution := (@Substitution NVar).

(*Notation oterm := (@oterm NVar gts).
Notation bterm := (@bterm NVar gts).
Notation vterm := (@vterm NVar gts). *)
Global Instance FreeVarsNTerm : FreeVars NTerm NVar := free_vars.
Global Instance FreeVarsBTerm : FreeVars BTerm NVar := free_vars_bterm.
Global Instance FreeVarsSub : FreeVars (@Substitution Opid) NVar := 
  fun s => flat_map free_vars (range s).

(*
Definition ssubst  (t : NTerm) (sub : Substitution) : NTerm :=
  let sfr := flat_map free_vars (range sub) in
    if dec_disjointv (bound_vars t) sfr
    then ssubst_aux t sub
    else ssubst_aux (change_bvars_alpha  sfr t) sub.
*)



(** %\noindent% The following definition will be useful while
    defining the computation system.

*)

Definition apply_bterm  (bt :BTerm) (lnt: list NTerm) : NTerm :=
  ssubst (get_nt bt) (combine (get_vars bt) lnt).

(** %\noindent \\*% The formalization of Nuprl requires many lemmas about [ssubst].
    Because [ssubst] often renames bound variables, we
    need alpha equality to state many useful properties of substitution.
    We will first define alpha equality and then list some useful properties
    that we proved about [ssubst].
 *)

Hint Rewrite @sub_filter_nil_r : SquiggleEq.


Lemma ssubst_ssubst_aux_nb : 
  (forall (t:NTerm) sub, 
  disjoint (bound_vars t) (flat_map free_vars (range sub))
  -> ssubst t sub = ssubst_aux t sub)
  *
  (forall (t:BTerm) sub, 
  disjoint (bound_vars_bterm t) (flat_map free_vars (range sub))
  -> ssubst_bterm t sub = ssubst_bterm_aux t sub).
Proof using.
  apply NTerm_BTerm_ind;[simpl; refl| |].
- intros ? ? Hind ? Hdis.
  simpl in *.
  f_equal.
  apply eq_maps. intros. apply Hind; auto.
  rewrite disjoint_flat_map_l in Hdis. auto.
- intros ? ? Hind ? Hdis.
  simpl in *.
  destruct lv;
    [f_equal; autorewrite with SquiggleEq; 
       apply Hind; auto; 
       disjoint_reasoningv; fail
     | clear Hind].
  cases_if;[| contradiction].
  simpl. refl.
Qed.


Definition ssubst_ssubst_aux := fst ssubst_ssubst_aux_nb.


(*
Lemma isprogram_ssubst_vars_implies :
  forall t sub vars,
    isprogram (ssubst_vs vars t sub)
    -> forall v,
         LIn v (free_vars t)
         -> ! LIn v vars
         -> exists u, sub_find sub v = Some u # isprogram u.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    sp; subst.
    remember (sub_find sub v); destruct o; symmetry in Heqo.
    exists n; sp.
    rw isprogram_vterm in H; sp.

  - Case "oterm".
    rw in_flat_map in H1; sp.
    destruct x.
    simpl in H3.
    rw in_remove_nvars in H3; sp.
    apply H with (nt := n) (lv := l) (vars := vars ++ l); auto.
    unfold isprogram, closed in H0; sp; allsimpl.
    rw flat_map_empty in H0.
    inversion H5; subst.
    rw map_map in H9.
    unfold compose in H9.

    generalize (H0 (ssubst_vs_bterm vars (bterm l n) sub)).
    generalize (H8 (ssubst_vs_bterm vars (bterm l n) sub)).
    simpl.
    rw bvar_renamings_subst_eta.
    rw in_map_iff.
    sp.

    assert (exists x,
              ssubst_vs_bterm vars x sub =
              bterm (fst (fst (bvar_renamings_subst l sub)))
                    (ssubst_vs (vars ++ fst (fst (bvar_renamings_subst l sub))) n
                               (snd (fst (bvar_renamings_subst l sub)) ++
                                    snd (bvar_renamings_subst l sub))) #
              LIn x lbt) by
        (exists (bterm l n); simpl; rw bvar_renamings_subst_eta; simpl; auto).

    applydup H6 in H10.
    applydup H7 in H10.
    allsimpl.

    unfold isprogram, closed.
Abort.
*)




Lemma ssubst_aux_nil :
  forall (t:NTerm), ssubst_aux t [] = t.
Proof using.
  nterm_ind t Case; simpl; auto.
  assert (map (fun t : BTerm => ssubst_bterm_aux t []) lbt = lbt);
  try (rw H0; auto).
  induction lbt; simpl; auto.
  rw IHlbt; auto.
  destruct a; simpl.
    f_equal; sp.
    f_equal; sp.
    eapply H; eauto.
    left; auto.

    intros. eapply H; eauto.
 right;sp.
 eauto.

Qed.


Lemma ssubst_nil :
  forall (t:NTerm), ssubst t [] = t.
Proof using.
  intros.
  rewrite ssubst_ssubst_aux.
  - apply ssubst_aux_nil.
  - simpl. disjoint_reasoning.
Qed.



Hint Rewrite ssubst_nil.

Lemma ssubst_aux_trivial_cl :
  forall (t:NTerm) (sub: @Substitution Opid),
    (forall v u, LIn (v, u) sub -> closed u # ! LIn v (free_vars t))
    -> ssubst_aux t sub = t.
Proof using.
  unfold ssubst.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    allunfold isprogram; unfold closed in *; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply_in_hyp p; sp.
    allrw not_over_or; sp.

  - Case "oterm".
    assert (map (fun t : BTerm => ssubst_bterm_aux t sub) lbt = lbt) as eq;
    try (rw eq; auto).
    induction lbt; simpl; auto.
    rw IHlbt; sp.
    + destruct a; simpl.
      f_equal. f_equal. 
      rewrite H with (lv := l); sp.
      rewrite @in_sub_filter in *; sp.
      apply_in_hyp p; sp.
      allrw @in_sub_filter; sp.
      apply_in_hyp p; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
      allrw @in_remove_nvars; sp.
    + rewrite H with (lv := lv); sp.
    + apply_in_hyp p; sp.
    + apply_in_hyp p; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
Qed.

Lemma ssubst_aux_trivial :
  forall (t:NTerm) (sub: @Substitution Opid),
    (forall v u, LIn (v, u) sub -> isprogram u # ! LIn v (free_vars t))
    -> ssubst_aux t sub = t.
Proof using.
  clear varclass varcl freshv.
  intros.
  apply ssubst_aux_trivial_cl.
  unfold isprogram in *. 
  firstorder.
Qed.




Lemma prog_sub_flatmap_range : forall (sub : @Substitution Opid), prog_sub sub
    -> flat_map free_vars (range sub) =[].
Proof using.
  unfold prog_sub, isprogram,closed . introv Hps. apply flat_map_empty. cpx.
  introv Hin. rw in_map_iff in Hin. exrepnd. subst.
  simpl.
  apply Hps in Hin1. cpx.
Qed.

Lemma closed_sub_flatmap_range : forall (sub : @Substitution Opid), sub_range_sat sub closed
    -> flat_map free_vars (range sub) =[].
Proof using.
  unfold prog_sub, isprogram,closed . introv Hps. apply flat_map_empty. cpx.
  introv Hin. rw in_map_iff in Hin. exrepnd. subst.
  simpl.
  apply Hps in Hin1. cpx.
Qed.

Theorem dom_range_is_split_snd :
  forall (sub: @Substitution Opid), range sub = snd (split sub).
Proof using.
  induction sub; auto. allsimpl.
  destruct (split sub) as [lv lnt].
  destruct (a) as [v nt].
  allsimpl. f_equal. auto.
Qed.

Theorem dom_range_combine :
  forall lv (lnt : list NTerm),
    length lv = length lnt
    -> range (combine lv lnt) = lnt.
Proof using.
  intros. rw  dom_range_is_split_snd.
  rewrite combine_split; auto.
Qed.

Lemma sub_eta : forall (sub : @Substitution Opid),
  sub = combine (dom_sub sub) (range sub).
Proof using.
  induction sub as [| (v,t) Hind]; auto;simpl;congruence.
Qed.

Lemma sub_eta_length : forall (sub : @Substitution Opid),
  length (dom_sub sub) = length (range sub).
Proof using.
  induction sub as [| (v,t) Hind]; auto;simpl;congruence.
Qed.

Lemma in_sub_eta : forall (sub : @Substitution Opid) v t,
  LIn (v,t) sub -> (LIn v (dom_sub sub)) # (LIn t (range sub)).
Proof using.
  introns HH.
  pose proof (sub_eta sub) as XX.
  rw XX in HH.
  apply in_combine in HH.
  trivial.
Qed.

Lemma disjoint_sub_as_flat_map: forall (f: NTerm -> (list NVar)) sub lvd,
(forall (v : NVar) (u : NTerm),
  LIn (v, u) sub -> disjoint (f u) lvd)  
 <=> disjoint (flat_map f (range sub)) lvd.
Proof using.
  introv. sp_iff Case.
  Case "->".
  - introv Hin. apply disjoint_flat_map_l.
    intros nt Hinr. pose proof (sub_eta_length sub) as XXX.
    apply combine_in_right with (l1:=dom_sub sub) in Hinr;[| omega];[].
    exrepnd. rewrite <- sub_eta in Hinr0.
    apply Hin in Hinr0. sp.
  - introv Hdis. introv Hin. apply in_sub_eta in Hin. repnd.
    rw disjoint_flat_map_l in Hdis.
    apply Hdis in Hin. sp.
Qed.

Lemma range_var_ren : forall lvi lvo,
  length lvi=length lvo 
  -> range (var_ren lvi lvo) = map (@vterm NVar Opid) lvo.
Proof using.
  induction lvi as [|? ? Hind]; introv Hlen; allsimpl; destruct lvo; inverts Hlen;sp;[];simpl.
  f_equal. apply Hind; sp.
Qed.

Lemma flat_map_free_var_vars_range: forall lvi lvo, 
  length lvi=length lvo 
  -> flat_map (@free_vars NVar _ Opid) (range (var_ren lvi lvo)) = lvo.
Proof using.
  intros. rw range_var_ren;sp. apply  flat_map_free_var_vterm.
Qed.


Lemma flat_map_bound_var_vars_range: forall lvi lvo, 
  length lvi=length lvo 
  -> flat_map (@bound_vars  NVar _ Opid) (range (var_ren lvi lvo)) = [].
Proof using.  intros. rw range_var_ren;sp. apply  flat_map_bound_var_vterm.
Qed.

Theorem dom_sub_is_split_snd :
  forall (sub : @Substitution Opid), dom_sub sub = fst (split sub).
Proof using.
 induction sub; auto. allsimpl. 
 destruct (split sub) as [lv lnt].
 destruct (a) as [v nt].
 allsimpl. f_equal. auto. 
Qed.

Theorem dom_sub_combine :
  forall lv (lnt: list NTerm),
    length lv = length lnt
    -> dom_sub (combine lv lnt) = lv.
Proof using.
  intros.
  rw dom_sub_is_split_snd.
  revert lnt H; induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  rw split_eta; simpl; allrw; sp; omega.
Qed.

Theorem dom_sub_combine_le :
  forall lv (lnt: list NTerm),
    length lv <= length lnt
    -> dom_sub (combine lv lnt) = lv.
Proof using.
  intros.
  rw dom_sub_is_split_snd.
  revert lnt H; induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  rw split_eta; simpl; allrw; sp; omega.
Qed.


Lemma prog_sub_csub2sub :
  forall sub, prog_sub (csub2sub sub).
Proof using.
  introv hn; allapply in_csub2sub; sp.
Qed.
Hint Immediate prog_sub_csub2sub.

Definition hide_csub2sub (sub :@CSubstitution NVar _ Opid _) := csub2sub sub.

Ltac simpl_sub :=
(match goal with
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
end).

Tactic Notation  "spcl" := spc;simpl_list.
Tactic Notation  "spcls" := repeat(simpl_list);sp;repeat(simpl_sub).

Ltac change_to_ssubst_aux4 :=
  allunfold @disjoint_bv_sub;
  allunfold @hide_csub2sub;
  allunfold @prog_sub;
  allunfold @sub_range_sat;
  (repeat match goal with
            | [ |- context [csub2sub ?sub] ] =>
              let name := fresh "ps_csub2sub" in
              pose proof (prog_sub_csub2sub sub) as name;
              fold (hide_csub2sub sub)
            | [ H:( forall _ _, LIn (_, _) _
                                -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
              apply @disjoint_sub_as_flat_map in H;apply @disjoint_sym in H
          end);
  let tac:=
  (repeat match goal with
            | [ H:(forall _ _, LIn (_, _) _ -> isprogram _) |- _ ] =>
              progress(rewrite (prog_sub_flatmap_range _ H))
            | [ H:(forall _ _, LIn (_, _) _ -> closed _) |- _ ] =>
              progress(rewrite (closed_sub_flatmap_range _ H))
          end); (try sp; try disjoint_reasoningv; try spcls; try disjoint_reasoningv) in
  tac; repeat (rewrite @ssubst_ssubst_aux;[|tac]).


Lemma ssubst_trivial :
  forall (t:NTerm) (sub: @Substitution Opid),
    (forall v u, LIn (v, u) sub -> isprogram u # ! LIn v (free_vars t))
    -> ssubst t sub = t.
Proof using.
  introv Hpr. assert (prog_sub sub). introv Hin. apply Hpr in Hin;sp.
  change_to_ssubst_aux4;[].
  apply ssubst_aux_trivial;sp.
Qed.


(* This is not true because ssubst might renames some bound variables of t
that occur in the free variables of sub.

Lemma ssubst_trivial1 :
  forall t sub,
    (forall v u, LIn (v, u) sub -> ! LIn v (free_vars t))
    -> ssubst t sub = t.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    allunfold isprogram; allunfold closed; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply H in Heqo; sp.
    provefalse; apply Heqo; left; auto.

  - Case "oterm".
    assert (map (fun t : BTerm => ssubst_bterm t sub) lbt = lbt);
    try (rw H1; auto).
    induction lbt; simpl; auto.
    rw IHlbt; sp.

    + destruct a; simpl.
      assert (bterm (snd (bvar_renamings_subst l sub))
                    (ssubst n (fst (bvar_renamings_subst l sub)))
              = bterm l n).

    + rw H with (lv := lv); sp; simpl.
      right; auto.

    + apply H0 in H1; sp.
      simpl in H1; rw in_app_iff in H1.
      apply H1; right; auto.
Qed.
*)

Lemma ssubst_aux_trivial2_cl :
  forall (t:NTerm) (sub : @Substitution Opid),
    (forall v u, LIn (v, u) sub -> closed u)
    -> closed t
    -> ssubst_aux t sub = t.
Proof using.
  introv k isp; apply ssubst_aux_trivial_cl; introv ins.
  apply_in_hyp p.
  dands; try (complete sp).
  intro ivt.
  rw isp in ivt; sp.
Qed.

Lemma ssubst_aux_trivial2 :
  forall t (sub : @Substitution Opid),
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> isprogram t
    -> ssubst_aux t sub = t.
Proof using.
  clear varclass varcl freshv.
  intros. apply @ssubst_aux_trivial2_cl;  unfold isprogram in *;
  firstorder.
Qed.

Lemma ssubst_trivial2_cl :
  forall (t:NTerm) sub,
    (forall v u, LIn (v, u) sub -> closed u)
    -> closed t
    -> ssubst t sub = t.
Proof using.
  intros. change_to_ssubst_aux4.
  apply ssubst_aux_trivial2_cl;sp.
Qed.

Lemma ssubst_trivial2 :
  forall t sub,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> isprogram t
    -> ssubst t sub = t.
Proof using varclass.
  intros. apply ssubst_trivial2_cl;  unfold isprogram in *;
  firstorder.
Qed.

Theorem disjoint_lbt_bt2 : forall vs lbt lv (nt:NTerm),
    disjoint vs (flat_map bound_vars_bterm lbt)
    -> LIn (bterm lv nt) lbt
    -> disjoint vs lv # disjoint vs (bound_vars nt).
Proof using. introv Hink1 Hin. apply disjoint_sym in Hink1;rw disjoint_flat_map_l in Hink1.
   apply Hink1 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd.
   split; apply disjoint_sym; trivial.
Qed.


Ltac disjoint_flat := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  repeat match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map free_vars (range ?sub)) 
      (flat_map bound_vars_bterm ?lbt))  |- _ ] => 
    pose proof (disjoint_lbt_bt2 _ _ _ _ H2 H); apply hide_hyp in H2
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map bound_vars_bterm ?lbt)
      (flat_map free_vars (range ?sub)))  |- _ ] => 
      pose proof (disjoint_lbt_bt2 _ _ _ _ (disjoint_sym_impl _ _ _ H2) H);
      apply hide_hyp in H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end ; allrw <- hide_hyp.


Theorem disjoint_sub_filter_r_flatmap : forall {T:Type} lvi lnt lvis lnts lv 
  (ld: list T) (f:NTerm-> list T),
   sub_filter (combine lvi lnt) lv = combine lvis lnts
   -> length lvi =length lnt
   -> length lvis =length lnts
   -> disjoint (flat_map f lnt) ld
   -> disjoint (flat_map f lnts) ld.
Proof using.
  introv Hsf Hlen Hle1n Hdis. introv Hin Hc.
  apply lin_flat_map in Hin. exrepnd.
  apply combine_in_right with (l1:=lvis) in Hin1; auto; [| omega];[].
  rename Hin1 into Hinc. exrepnd. rw <- Hsf in Hinc0.
  apply in_sub_filter in Hinc0. repnd. apply in_combine in Hinc1. repnd.
  assert({x : NTerm $ LIn x lnt # LIn t (f x)}) as XX by(eexists; eauto).
  allrw <- lin_flat_map.
  apply Hdis in XX. sp.
Qed.

Theorem disjoint_sub_filter_r_flatmap2 : forall {T:Type} sub lv
  (ld: list T) (f:NTerm-> list T),
   disjoint (flat_map f (range sub)) ld
   -> disjoint (flat_map f (range (sub_filter sub lv))) ld.
Proof using.
  introv.   pose proof (sub_eta (sub_filter sub lv)) as YY.
  pose proof (sub_eta sub) as XX.
  rewrite XX  in YY at 1.
  pose proof (sub_eta_length sub).
  pose proof (sub_eta_length (sub_filter sub lv)).
  eapply disjoint_sub_filter_r_flatmap; eauto.
Qed.


Ltac disjoint_flat_sf :=
repeat match goal with
| [|- disjoint (flat_map _ (range (sub_filter _ _))) _] =>
    apply disjoint_sub_filter_r_flatmap2
| [|- disjoint _ (flat_map _ (range (sub_filter _ _)))] =>
    apply disjoint_sym; apply disjoint_sub_filter_r_flatmap2
end.

Lemma simple_ssubst_aux_app :
  forall t (sub1 sub2 : @Substitution Opid),
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> ssubst_aux (ssubst_aux t sub1) sub2 = ssubst_aux t (sub1 ++ sub2).
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    remember (sub_find sub1 n); destruct o; symmetry in Heqo; simpl; sp.
    + rewrite sub_find_some_app with (t := n0); sp.
      apply sub_find_some in Heqo.
      apply_in_hyp p.
      rw ssubst_aux_trivial2; sp.

    + rw @sub_find_app.
      rw Heqo; auto.

  - Case "oterm". f_equal.
    induction lbt; simpl; auto.
    rw IHlbt; sp;
    try (rewrite H with (lv := lv); sp; simpl; sp).
    f_equal.
    destruct a; simpl.
    rewrite H with (lv := l); sp.
    rw @sub_filter_app; auto.
    allrw @in_sub_filter; sp.
    apply_in_hyp p; sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp p; sp.
Defined.


Lemma simple_ssubst_app :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> ssubst (ssubst t sub1) sub2 = ssubst t (sub1 ++ sub2).
Proof using.
  intros. assert(prog_sub (sub1++sub2)) by (apply sub_app_sat;sp).
  change_to_ssubst_aux4.
  apply simple_ssubst_aux_app; sp.
Qed.


(* This is not true because ssubst might renames some bound variables of t
that occur in the free variables of sub.
Lemma ssubst_isprogram :
  forall t sub,
    isprogram t
    -> ssubst t sub = t.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    rw isprogram_vterm in H; sp.

  - Case "oterm".
Qed.
*)

Definition subst_aux (t : NTerm) (v : NVar) (u : NTerm) : NTerm :=
  ssubst_aux t [(v,u)].

Definition subst (t : NTerm) (v : NVar) (u : NTerm) : NTerm :=
  ssubst t [(v,u)].



(* in a separate commit, we might want to make everything compatible with
Notation apply_bterm  (bt :BTerm) (lnt: list NTerm) : NTerm :=
  match bt with
  | bterm lv nt => ssubst nt (combine lv lnt)
  end.
*)


Lemma apply_bterm_nobnd :
  forall t,
    apply_bterm (nobnd t) [] = t.
Proof using.
  unfold apply_bterm, get_nt, nobnd; simpl; sp.
  rw ssubst_nil; auto.
Qed.


Lemma num_bvars_bterm :
  forall (bt:BTerm) sub,
    num_bvars (ssubst_bterm_aux bt sub) = num_bvars bt.
Proof using.
  destruct bt; unfold num_bvars; simpl; sp.
Qed.

Lemma map_num_bvars_bterms :
  forall bts sub,
    map num_bvars (map (fun t : BTerm => ssubst_bterm_aux t sub) bts) =
    map num_bvars bts.
Proof using.
  induction bts; simpl; sp.
  rw num_bvars_bterm; rw IHbts; auto.
Qed.

Lemma remove_nvars_comb :
  forall (sub : @Substitution Opid) l vars,
    remove_nvars (l ++ dom_sub (sub_filter sub l)) vars
    = remove_nvars (l ++ dom_sub sub) vars.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 l); destruct b; symmetry in Heqb; simpl.
  rw fold_assert in Heqb.
  rw @assert_memvar in Heqb.
  rw IHsub.
  rw <- @remove_nvars_dup; auto.
  repeat (rw @remove_nvars_move).
  repeat (rw @remove_nvars_cons).
  rw IHsub; auto.
Qed.


Lemma fvars_ssubst_aux1 :
  forall t : NTerm,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> closed u)
    -> free_vars (ssubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  nterm_ind t as [| o lbt ind] Case; simpl; introv k.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl.
    + apply sub_find_some in Heqo.
      apply_in_hyp p.
      unfold isprogram, closed in p; sp.
      allrw.
      symmetry; rw <- null_iff_nil.
      rw @null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqo; sp.
    + sp.
      apply sub_find_none2 in Heqo.
      symmetry.
      rw <- @remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".

      rw flat_map_map; unfold compose.
      rw @remove_nvars_flat_map; unfold compose.
      apply eq_flat_maps; introv i.
      destruct x; simpl.
      simpl in i.
      apply ind with (sub := sub_filter sub l) in i; sp.

      rewrite i.
      rw @remove_nvars_app_l.
      rw @remove_nvars_comm.
      rw @remove_nvars_app_l.
      rw remove_nvars_comb; auto.

      apply k with (v := v).
      assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
      unfold subset in s.
      discover; sp.
Qed.

(* TODO : reuse the above lemma *)
Lemma isprogram_ssubst_aux1 :
  forall t : NTerm,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> nt_wf (ssubst_aux t sub)
       # free_vars (ssubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  nterm_ind t as [| o lbt ind] Case; simpl; introv wf k.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl.
    + apply sub_find_some in Heqo.
      apply_in_hyp p.
      unfold isprogram, closed in p; sp.
      allrw.
      symmetry; rw <- null_iff_nil.
      rw @null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqo; sp.
    + sp.
      apply sub_find_none2 in Heqo.
      symmetry.
      rw <- @remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".
    inversion wf; subst; sp.
    + constructor.
      introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl.
      constructor.
      apply ind with (sub := sub_filter sub l) in i1; sp.
      apply_in_hyp p.
      inversion p; subst; auto.
      apply k with (v := v).
      assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
      unfold subset in s.
      apply_in_hyp p; sp.
      allrw <-.
      apply map_num_bvars_bterms.

    + auto.
      rw flat_map_map; unfold compose.
      rw @remove_nvars_flat_map; unfold compose.
      apply eq_flat_maps; introv i.
      destruct x; simpl.
      apply_in_hyp p.
      inversion p as [vs t w]; subst.

      apply ind with (sub := sub_filter sub l) in i; sp.

      allrw.
      rw @remove_nvars_app_l.
      rw @remove_nvars_comm.
      rw @remove_nvars_app_l.
      rw @remove_nvars_comb; auto.

      apply k with (v := v).
      assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
      unfold subset in s.
      discover; sp.
Qed.


Lemma fvars_ssubst1 :
  forall t : NTerm,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> closed u)
    ->    free_vars (ssubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  intros. change_to_ssubst_aux4.
  apply fvars_ssubst_aux1;sp.
  SearchAbout flat_map free_vars.
Qed.

Definition ssubsthide (t:NTerm) sub
  := if dec_disjointv (bound_vars t) (flat_map free_vars (range sub))
    then ssubst_aux t sub
    else ssubst t sub.

Lemma ssubst_ssubst_aux_hide : forall t sub,
ssubst t sub = ssubsthide t sub.
Proof.
  intros. unfold ssubsthide.
  cases_if; auto.
  rewrite ssubst_ssubst_aux; auto.
Qed.

Ltac change_to_ssubst_aux8 :=
  repeat rewrite ssubst_ssubst_aux_hide;
  unfold ssubsthide;
  allunfold disjoint_bv_sub;
  (repeat match goal with
            | [ |- context [csub2sub ?sub] ] =>
              let name := fresh "ps_csub2sub" in
              pose proof (prog_sub_csub2sub sub) as name;
            fold (hide_csub2sub sub)
          end);
  allunfold hide_csub2sub;
  allunfold prog_sub;
  allunfold sub_range_sat;
  (repeat match goal with
            | [ H:(forall _ _, LIn (_, _) _ -> isprogram _) |- _ ] =>
              progress(rw (prog_sub_flatmap_range _ H))
            | [ H:(forall _ _, LIn (_, _) _ -> closed _) |- _ ] =>
              progress(rw (closed_sub_flatmap_range _ H))
            | [ H:( forall _ _, LIn (_, _) _
                                -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
              apply disjoint_sub_as_flat_map in H;apply disjoint_sym in H
          end);
  repeat(cases_if;clears_last; [|sp;disjoint_reasoningv;spcls;try(false_disjoint)]).

Lemma isprogram_ssubst1 :
  forall t : NTerm,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> nt_wf (ssubst t sub)
       # free_vars (ssubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  intros. change_to_ssubst_aux8.
  apply isprogram_ssubst_aux1;sp.
Qed.

Lemma isprogram_ssubst_aux2 :
  forall t : NTerm,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> free_vars (ssubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  nterm_ind t as [| o lbt ind ] Case; simpl; introv k.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl.
    + apply sub_find_some in Heqo.
      discover.
      applydup k in Heqo. 
      unfold isprogram, closed in *; sp.
      allrw.
      symmetry. 
      rw <- null_iff_nil.
      rw @null_remove_nvars; simpl; sp; subst.
      eapply in_dom_sub; eauto.
    + apply sub_find_none2 in Heqo.
      symmetry.
      rw <- @remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".
    auto.
    rw flat_map_map; unfold compose.
    rw @remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.

    apply ind with (sub := sub_filter sub l) in i; sp.

    allrw.
    rw @remove_nvars_app_l.
    rw @remove_nvars_comm.
    rw @remove_nvars_app_l.
    rw @remove_nvars_comb; auto.

    apply k with (v := v).
    assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
    unfold subset in s.
    discover; sp.
Qed.

Lemma isprogram_ssubst2 :
  forall t : NTerm,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> free_vars (ssubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof using.
  intros. change_to_ssubst_aux4.
  apply isprogram_ssubst_aux2;sp.
Qed.



Lemma isprogram_ssubst :
  forall t : NTerm,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> (forall v, LIn v (free_vars t) -> LIn v (dom_sub sub))
    -> isprogram (ssubst t sub).
Proof using.
  introv w k1 k2.
  unfold isprogram.
  apply isprogram_ssubst1 with (sub := sub) in w; sp.
  unfold closed.
  allrw.
  rw <- null_iff_nil.
  rw @null_remove_nvars; simpl; sp.
Qed.

(*
Lemma isprogram_lcsubst0 :
  forall vs  : list NVar,
  forall t   : CVTerm vs,
  forall sub : CSubOver vs,
    isprogram (ssubst (get_cvterm vs t) (csubo2sub vs sub)).
Proof using.
  sp.
  destruct t, sub; allunfold dom_csubo; allunfold csubo2sub; allsimpl.
  allrw isprog_vars_eq; sp.
  apply isprogram_ssubst; allsimpl; sp.
  apply in_csub2sub in H1; sp.
  allrw subsetv_prop.
  apply H in H1.
  allrw over_vars_eq.
  allrw subsetv_prop.
  apply o in H1.
  allapply in_dom_csub_exists; sp.
  allapply sub_find_some.
  exists t; sp.
Qed.

Lemma isprog_lcsubst0 :
  forall vs  : list NVar,
  forall t   : CVTerm vs,
  forall sub : CSubOver vs,
    isprog (ssubst (get_cvterm vs t) (csubo2sub vs sub)).
Proof using.
  sp; rw isprog_eq; apply isprogram_lcsubst0.
Qed.

Definition ssubstc0 (vs  : list NVar)
                    (t   : CVTerm vs)
                    (sub : CSubOver vs) : CTerm :=
  exist isprog
         (ssubst (get_cvterm vs t) (csubo2sub vs sub))
         (isprog_lcsubst0 vs t sub).
*)

Lemma subst_preserves_program :
  forall (t : NTerm) (v :NVar) u ,
    nt_wf t
    -> (forall x, LIn x (free_vars t) -> x = v)
    -> isprogram u
    -> isprogram (subst t v u).
Proof using.
  introv w k isp.
  apply isprogram_ssubst with (sub := [(v,u)]) in w; allsimpl; sp; inj; sp.
  apply_in_hyp p; subst; sp.
Qed.

Lemma subst_preserves_isprog :
  forall t : NTerm,
  forall v : NVar,
  forall u : NTerm,
    isprog_vars [v] t
    -> isprog u
    -> isprog (subst t v u).
Proof using.
  intros t v u.
  repeat (rw <- @isprogram_eq).
  unfold isprog_vars.
  rw andb_eq_true.
  fold (wf_term t).
  repeat (rewrite <- @nt_wf_eq).
  rw fold_assert.
  rw @assert_sub_vars; allsimpl; sp.
  apply @subst_preserves_program; sp.
  symmetry; apply_in_hyp p; sp.
Qed.
Hint Resolve subst_preserves_isprog : isprog.

Definition substc (u : CTerm) (v : NVar) (t : CVTerm [v]) : CTerm :=
  let (a,x) := t in
  let (b,y) := u in
    exist isprog (subst a v b) (subst_preserves_isprog a v b x y).

Tactic Notation "allrwxxx" constr(T) :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
          end.

Tactic Notation "allrwxxx" ident(T) :=
  let t := type of T in
  repeat match goal with
           | [ H1 : t, H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
         end.

(** the ssubst version of this is best done after 
   we have the lemma that alpha_equality preserves wf 
    ssubst_wf_iff is proved in alphaeq.v*)

Lemma ssubst_aux_preserves_wf :
  forall t : NTerm,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> nt_wf u)
    -> nt_wf (ssubst_aux t sub).
Proof using.
  nterm_ind1 t as [? | o lbt Hind]Case; simpl; introv HX hwf.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    apply sub_find_some in Heqo.
    apply_in_hyp p; sp.

  - Case "oterm".
    invertsna HX  Hwf; subst.
    allrw in_map_iff; sp; subst.
    constructor.
    Focus 2. rw map_num_bvars_bterms;sp;fail.
    intros bt Hin.
    apply in_map_iff in Hin; exrepnd; destruct a as [lv nt].
    allsimpl. subst.
    constructor.
    eapply Hind; eauto;[|].
    + apply Hwf in Hin1.
      invertsn Hin1;sp.
    + introv Hin. apply in_sub_filter in Hin. sp.
      discover; sp. eauto.
Qed.

(**This is a trivial consequence of the fact that
  its output is alpha equal to input. But lemma that comes
  way too late in alpha_eq.v. Hence, a direct proof here*)
Lemma change_bvars_alpha_preserves_wf:
  forall nt lv,
    nt_wf nt
    -> nt_wf (change_bvars_alpha lv nt).
Proof using.
  nterm_ind1 nt as [v | o lbt Hind] Case; introv HX;[sp|];[].
    invertsna HX  Hwf; subst.
    allrw in_map_iff; sp; subst.
    simpl. constructor.
Abort.


Definition wf_ssubst_to_ssubst (sub : WfSubstitution) : Substitution :=
  map (fun x => (fst x, get_wterm (snd x))) sub.

(** TODO: non aux version *)
Lemma ssubst_aux_preserves_wf_term :
  forall t : NTerm,
  forall sub : Substitution,
    wf_term t
    -> (forall v u, LIn (v, u) sub -> wf_term u)
    -> wf_term (ssubst_aux t sub).
Proof using.
  sp.
  rewrite <- nt_wf_eq.
  apply ssubst_aux_preserves_wf; sp.
  rewrite nt_wf_eq; auto.
  apply_in_hyp p.
  rewrite nt_wf_eq; auto.
Qed.


(** TODO: non aux version *)
Lemma ssubst_aux_preserves_wf_term' :
  forall t : NTerm,
  forall sub : Substitution,
    wf_term t
    -> assert (ball (map (fun x => wft (snd x)) sub))
    -> wf_term (ssubst_aux t sub).
Proof using.
  intros.
  apply ssubst_aux_preserves_wf_term; sp.
  rw <- fold_assert in H0.
  rw ball_map_true in H0.
  apply_in_hyp p.
  allfold (wf_term u); auto.
Qed.

(*
Definition wf_ssubst (t : WTerm) (sub : WfSubstitution) : WTerm :=
  let (a,w) := t in
  let s := wf_ssubst_to_ssubst sub in
    exist
      wf_term
      (ssubst a s)
      (ssubst_preserves_wf_term'
         a
         s
         w
         (eq_refl (ball (map (fun x => snd x) sub)))).
*)

(** TODO: non aux version *)
Lemma subst_aux_preserves_wf :
  forall t : NTerm,
  forall v : NVar,
  forall u : NTerm,
    nt_wf t
    -> nt_wf u
    -> nt_wf (subst_aux t v u).
Proof using.
  introv wt wu.
  apply ssubst_aux_preserves_wf with (sub := [(v,u)]) in wt; allsimpl; sp; inj.
Qed.

(** TODO: non aux version *)
Lemma subst_aux_preserves_wf_term :
  forall t : NTerm,
  forall v : NVar,
  forall u : NTerm,
    wf_term t
    -> wf_term u
    -> wf_term (subst_aux t v u).
Proof using.
  intros t v u.
  repeat (rewrite <- nt_wf_eq); sp.
  apply subst_aux_preserves_wf; auto.
Qed.

(** TODO: non aux version *)
Definition substwf (t : WTerm) (v : NVar) (u : WTerm) : WTerm :=
  let (a,x) := t in
  let (b,y) := u in
    exist wf_term (subst_aux a v b) (subst_aux_preserves_wf_term a v b x y).

(*

Lemma isprogram_bt_iff :
  forall vs t,
    (forall sub,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> (forall v, LIn v vs -> exists u, LIn (v, u) sub)
    -> isprogram (ssubst t sub))
    <=> isprogram_bt (bterm vs t).
Proof using.
  unfold isprogram_bt, closed_bt, isprogram, closed; simpl; sp.
  rw <- null_nil.
  rw <- null_nil in H1.
  rw null_remove_nvars; sp.
  aXdmit.
  aXdmit.
Qed.

*)


Lemma isprogram_bt_implies2 :
  forall (bt:BTerm),
    isprogram_bt bt
    -> forall lnt : list NTerm,
         (forall nt : NTerm, LIn nt lnt -> isprogram nt)
         -> num_bvars bt <= length lnt
         -> isprogram (apply_bterm bt lnt).
Proof using.
 intros ? Hprog ?  Hprognt Hlen. inverts Hprog as Hclos Hwf.
 inverts Hwf. unfold num_bvars in Hlen. simpl in Hlen.
 unfold apply_bterm. simpl. apply isprogram_ssubst; auto.
 -  intros ? ? Htemp. apply in_combine in Htemp; sp.
 -  intros ?  Hin.
    inverts Hclos as Hrem.
    apply null_iff_nil in Hrem.
    unfold remove_nvars in Hrem. rw null_diff in Hrem.
    assert (LIn v lnv) as Hinv by (apply Hrem; auto).
    apply in_nth in Hinv; try (apply deq_nvar).
    destruct Hinv as [n Hp].
    rw dom_sub_combine_le; sp.
Qed.

Lemma isprogram_bt_implies :
 forall (bt:BTerm),
   isprogram_bt bt
   -> forall lnt : list NTerm,
        (forall nt : NTerm, LIn nt lnt -> isprogram nt)
        -> num_bvars bt = length lnt
        -> isprogram (apply_bterm bt lnt).
Proof using.
  intros ? Hprog ?  Hprognt Hlen. apply isprogram_bt_implies2; auto. omega.
Qed.

Lemma closed_bt_implies :
  forall (bt:BTerm),
    closed_bt bt
    -> forall lnt : list NTerm,
         (forall nt : NTerm, LIn nt lnt -> closed nt)
         -> num_bvars bt <= length lnt
         -> closed (apply_bterm bt lnt).
Proof using.
 intros ? Hprog ?  Hprognt Hlen.
 unfold num_bvars in Hlen. simpl in Hlen.
 unfold apply_bterm. simpl. destruct bt as [lv nt]. simpl.
 unfold closed.
 rewrite fvars_ssubst1; auto.
 rw dom_sub_combine_le; sp.
 intros ? ? Hin. apply in_combine_r in Hin. cpx.
Qed.

(*
Lemma isprogram_ssubst_implies :
  forall t sub,
    isprogram (ssubst t sub)
    -> forall v u,
         alpha_eq [] t u
         -> LIn v (free_vars u)
         -> exists u, sub_find sub v = Some u # isprogram u.
Proof using.


  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    unfold ssubst in H; simpl in H.
    sp; subst.
    remember (sub_find sub v); destruct o; symmetry in Heqo.
    exists n; sp.
    rw isprogram_vterm in H; sp.

  - Case "oterm".
    rw isprogram_ot_iff in H0; sp.
    rw in_flat_map in H1; sp.
    destruct x.
    simpl in H3.
    rw in_remove_nvars in H3; sp.
    generalize (H2 (ssubst_bterm (bterm l n) sub)); sp.
    dimp H5.
    rw in_map_iff. exists (bterm l n); sp.
    apply isprogram_bt_implies with (lnt := map (fun v => mk_axiom) (fst (fst (bvar_renamings_subst l sub)))) in hyp; sp.
    unfold apply_bterm in hyp.

    simpl in hyp.
    rw bvar_renamings_subst_eta in hyp.
    apply isprogram_bt_implies with (lnt := map (fun v => mk_axiom) (fst (fst (bvar_renamings_subst l sub)))) in hyp; sp.

    unfold apply_bterm in hyp; simpl in hyp.

    apply H with (lv := ) in hyp.

    rw in_map_iff in H6; sp; subst.
    apply isprogram_axiom.

    rw num_bvars_on_bterm.
    rw map_length; auto.


    apply H with (nt := n) (lv := l); auto.
Abort.
*)

Lemma subset_free_vars_sub_aux_app :
  forall t (sub1 sub2 : Substitution),
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> isprogram t)
    -> disjoint (free_vars t) (dom_sub sub2)
    -> ssubst_aux t (sub1 ++ sub2) = ssubst_aux t sub1.
Proof using.
  nterm_ind t Case; simpl; introv k d.

  - Case "vterm".
    allrw disjoint_singleton_l; sp.
    remember (sub_find sub1 n); destruct o; symmetry in Heqo.
    apply sub_find_some_app with (sub4 := sub2) in Heqo.
    rw Heqo; auto.
    rw @sub_find_none_iff in Heqo.
    assert (! LIn n (dom_sub (sub1 ++ sub2))) as nin
      by (rewrite dom_sub_app; rewrite in_app_iff; intro; sp).
    rw <- @sub_find_none_iff in nin.
    rw nin; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.
    try (sp; apply X with (v := v); rw in_app_iff; sp).
    rw @sub_filter_app.

    rewrite H with (lv := l); sp.
    apply k with (v := v).
    allrw in_app_iff.
    allrw @in_sub_filter; sp.
    allrw disjoint_flat_map_l.
    apply_in_hyp p.
    allsimpl.
    rw @disjoint_remove_nvars_l in p.
    rw <- @dom_sub_sub_filter; auto.
Qed.


Lemma subset_free_vars_sub_app :
  forall t (sub1 sub2 : Substitution),
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> isprogram t)
    -> disjoint (free_vars t) (dom_sub sub2)
    -> ssubst t (sub1 ++ sub2) = ssubst t sub1.
Proof using.
  introv Hpr. applydup (@sub_app_sat_if NVar Opid isprogram) in Hpr. repnd.
  allfold (prog_sub sub1). intros.
  change_to_ssubst_aux4.
  eapply subset_free_vars_sub_aux_app;sp.
Qed.

Lemma sub_find_member :
  forall sub1 sub2 x (t:NTerm),
    ! LIn x (dom_sub sub1)
    -> sub_find (sub1 ++ (x, t) :: sub2) x = Some t.
Proof using.
  induction sub1; simpl; sp.
  rw <- @beq_var_refl; auto; allsimpl.
  remember (beq_var a0 x); destruct b.
  apply beq_var_eq in Heqb; subst.
  provefalse; apply H; left; auto.
  symmetry in Heqb.
  apply beq_var_false_not_eq in Heqb.
  apply IHsub1; sp.
Qed.

Print Substitution.
Definition map_sub_range {gtsi} {gtso} (f : @terms.NTerm _ gtsi -> @terms.NTerm _ gtso) 
  (sub : @Substitution gtsi): @Substitution gtso :=
  map (fun p => (fst p, f (snd p))) sub.


Lemma sub_filter_map_trivial_vars :
  forall vars (l: list NVar),
    @sub_filter NVar _ Opid (map (fun v : NVar => (v, vterm v)) vars) l
    = map (fun v : NVar => (v, vterm v)) (remove_nvars l vars).
Proof using.
  induction vars; simpl; sp.
  rw @remove_nvars_nil_r; simpl; auto.
  rw IHvars.
  rw @remove_nvars_cons_r.
  destruct (memvar a l); auto.
Qed.

Lemma sub_find_sub_filter_some :
  forall l v (t:NTerm) sub,
    (sub_find (sub_filter sub l) v = Some t)
    <=> (sub_find sub v = Some t # ! LIn v l).
Proof using.
  induction sub; simpl; sp; split; sp; allsimpl.

  remember (beq_var a0 v); destruct b.

  apply beq_var_eq in Heqb; subst.

  remember (memvar v l); destruct b; allsimpl.
  rw IHsub in H; sp.
  symmetry in Heqb.
  rw fold_assert in Heqb.
  rw @assert_memvar in Heqb; sp.
  rw <- @beq_var_refl in H; allsimpl; sp.

  symmetry in Heqb.
  applydup @beq_var_false_not_eq in Heqb.
  remember (memvar a0 l); destruct b; allsimpl.
  rw IHsub in H; sp.
  rw Heqb in H.
  rw IHsub in H; sp.

  remember (memvar a0 l); destruct b; allsimpl.
  rw IHsub in H; sp.

  symmetry in Heqb.
  rw not_of_assert in Heqb.
  rw @assert_memvar in Heqb.
  remember (beq_var a0 v); destruct b.
  apply beq_var_eq in Heqb0; subst; sp.
  rw IHsub in H; sp.

  remember (memvar a0 l); destruct b; allsimpl.

  symmetry in Heqb; rw fold_assert in Heqb; rw @assert_memvar in Heqb.
  rw IHsub; sp.
  remember (beq_var a0 v); destruct b; sp.

  apply beq_var_eq in Heqb0; subst; sp.

  remember (beq_var a0 v); destruct b; sp.
  rw IHsub; sp.
Qed.

Lemma sub_find_sub_filter_none :
  forall l v (sub : @Substitution Opid),
    (sub_find (sub_filter sub l) v = None)
    <=> (sub_find sub v = None [+] LIn v l).
Proof using.
  induction sub; simpl; sp; split; sp; allsimpl;
  remember (memvar a0 l); destruct b; allsimpl;
  duplicate Heqb as eq;
  symmetry in Heqb;
  try (rw @fold_assert in Heqb; rw @assert_memvar in Heqb);
  try (rw @not_of_assert in Heqb; rw @assert_memvar in Heqb);
  remember (beq_var a0 v); destruct b;
  duplicate Heqb0 as eq2;
  try (apply @beq_var_eq in Heqb0; subst);
  try (symmetry in Heqb0; apply @beq_var_false_not_eq in Heqb0); sp;
  try (complete (apply IHsub; auto)).
Qed.

Lemma sub_filter_swap :
  forall l1 l2 (sub : @Substitution Opid),
    sub_filter (sub_filter sub l1) l2
    = sub_filter (sub_filter sub l2) l1.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 l1); destruct b; remember (memvar a0 l2); destruct b; simpl; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw IHsub; sp.
Qed.

Notation assert_memvar := (@assert_memvar NVar).
Lemma sub_filter_app_as_remove_nvars :
  forall (sub : @Substitution Opid) (l1 l2 : list NVar),
    sub_filter sub (l1 ++ l2)
    = sub_filter sub (l1 ++ remove_nvars l1 l2).
Proof using.
  induction sub; simpl; sp; allsimpl.
  remember (memvar a0 (l1 ++ l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw @assert_memvar in Heqb.
  rw in_app_iff in Heqb; sp.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb.
  apply not_over_or in Heqb; sp.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb.
  apply not_over_or in Heqb; repnd.
  allrw @in_remove_nvars.
  provefalse; apply Heqb; sp.

  rw @not_of_assert in Heqb; rw @assert_memvar in Heqb; rw @in_app_iff in Heqb.
  apply not_over_or in Heqb; repnd.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb1; destruct b.

  rw fold_assert in Heqb1; rw assert_memvar in Heqb1; rw in_app_iff in Heqb1; sp.
  allrw @in_remove_nvars; sp.

  rw <- IHsub; sp.
Qed.

Notation in_remove_nvars := (@in_remove_nvars NVar).

(** TODO : use the stronger lemma ssubst_aux_sub_filter2 for a smaller and
    more maintainable proof*)
Lemma ssubst_aux_sub_filter :
  forall t (sub : Substitution) l,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> disjoint (free_vars t) l
    -> ssubst_aux t (sub_filter sub l) = ssubst_aux t sub.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    remember (sub_find (sub_filter sub l) n); symmetry in Heqo; destruct o.
    rw @sub_find_sub_filter_some in Heqo; sp.
    allrw; sp.
    rw sub_find_sub_filter_none in Heqo; sp.
    allrw; sp.
    allrw disjoint_singleton_l; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    allrw disjoint_flat_map_l.
    apply_in_hyp p; allsimpl.
    allrw @disjoint_remove_nvars_l.

    repeat (rw @bvar_renamings_subst_isprogram; sp).
    repeat (rw @app_nil_l).
    rw sub_filter_swap.
    rw <- @sub_filter_app_r.
    rw sub_filter_app_as_remove_nvars.
    rw @sub_filter_app_r.
    rewrite H with (lv := l0); sp.

    allrw @in_sub_filter; sp.
    discover; sp. eauto.
Qed.

Lemma ssubst_sub_filter :
  forall t sub l,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> disjoint (free_vars t) l
    -> ssubst t (sub_filter sub l) = ssubst t sub.
Proof using.
  introv Hpr. duplicate Hpr. eapply sub_filter_sat with (lv:=l) in Hpr; eauto.
  change_to_ssubst_aux4.
  apply ssubst_aux_sub_filter;sp.
Qed.


(* XXXXXXXXXXXXXXXXXXX switch XXXXXXXXXXXXXXXXXXX *)

Lemma ssubst_aux_trivial_vars :
  forall (t:NTerm) vars,
    ssubst_aux t (map (fun v => (v, vterm v)) vars) = t.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    remember (sub_find (map (fun v : NVar => (v, vterm v)) vars) n); destruct o; auto.
    symmetry in Heqo.
    applydup @sub_find_some in Heqo; rw in_map_iff in Heqo0; sp; inj.

  - Case "oterm".
    f_equal.
    induction lbt; simpl; sp.
    rw IHlbt; sp; try (rewrite H with (lv := lv); sp; simpl; sp).
    destruct a; simpl.
    f_equal. f_equal.
    rw sub_filter_map_trivial_vars.
    rewrite H with (lv := l); sp.
Qed.

Lemma apply_bterm_append_program_id:
  forall bt lnt lnta ,
    (isprogram (apply_bterm bt lnt))  ->
    (forall nt, LIn nt lnt -> isprogram nt) ->
    (forall nt, LIn nt lnta -> isprogram nt) ->
    (apply_bterm bt lnt = apply_bterm bt (lnt++lnta)).
Proof using varclass.
 intros ?  ? ? Hisp Hnt Hnta. destruct bt as [lv nt].
  unfold apply_bterm. simpl.
  assert(length lv <= length lnt \/ length lnt < length lv ) as Hdi by omega.
  destruct Hdi. rw <- combine_app_eq; auto.
  rw combine_app_app; auto; try omega.
  rw <- simple_ssubst_app.
  unfold apply_bterm in Hisp.
  apply ssubst_trivial2 with
   (sub:= (combine (skipn (length lnt) lv) (firstn (length lv - length lnt) lnta)))
   in Hisp; auto.
  - intros ? ? Hin. apply in_combine in Hin; exrepnd.
    apply in_firstn in Hin; try omega; auto.
  - intros ? ? Hin. apply in_combine in Hin. sp.
  - intros ? ? Hin. apply in_combine in Hin. exrepnd.
    apply in_firstn in Hin; try omega; auto.
Qed.

Lemma ssubst_aux_nt_wf :
  forall t (sub : Substitution),
    nt_wf (ssubst_aux t sub)
    -> nt_wf t.
Proof using.
  nterm_ind t as [|o lbt ind] Case; simpl; introv w.

  - Case "vterm"; sp.

  - Case "oterm".
    inversion w as [|op lnt k e]; subst.
    constructor.

    + introv i; destruct l.
      generalize (k (ssubst_bterm_aux (bterm l n) sub)); intro j.
      dest_imp j hyp.
      rw in_map_iff.
      exists (bterm l n); sp.
      simpl in j.
      inversion j; subst.

      apply ind with (sub := (sub_filter sub l)) in i; auto.

    + rw <- e; rw map_map; unfold compose.
      rewrite eq_maps with (g := fun x : BTerm => num_bvars (ssubst_bterm_aux x sub)); sp.
      destruct x.
      unfold num_bvars. simpl;refl.
Qed.


(*
Lemma isprog_lcsubst_pi2 :
  forall t sub1 sub2 w1 w2 c1 c2,
    isprog_lcsubst (csubst t sub1) sub2 w1 c1
    = isprog_lcsubst t (sub1 ++ sub2) w2 c2.
Proof using.
Qed.
*)

(*
Lemma isprog_lcsubst_pi2 :
  forall t1 t2 : NTerm,
  forall sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall e : t1 = t2,
    match e with eq_refl => isprog_lcsubst t1 sub w1 c1 end
    = isprog_lcsubst t2 sub w2 c2.
Proof using.
  sp.
  apply isprog_proof_irrelevance.
Qed.
*)



Lemma ssubst_aux_snoc_dup :
  forall t (sub : Substitution) v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> isprogram u
    -> LIn v (dom_sub sub)
    -> ssubst_aux t (snoc sub (v, u)) = ssubst_aux t sub.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    rw @sub_find_snoc.
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    applydup @sub_find_none2 in Heqo.
    remember (beq_var v n); destruct b; sp.
    apply beq_var_true in Heqb; subst; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (complete (sp; allrw in_snoc; sp; allapply pair_inj; sp; subst; sp; apply_in_hyp p; sp)).

    rw @sub_filter_snoc.
    remember (memvar v l); symmetry in Heqb; destruct b; sp.
    rewrite H with (lv := l); sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp p; sp.
    rw <- @dom_sub_sub_filter.
    rw @in_remove_nvars; sp.
    rw not_of_assert in Heqb.
    rw assert_memvar in Heqb; sp.
Qed.

Lemma ssubst_snoc_dup :
  forall t sub v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> isprogram u
    -> LIn v (dom_sub sub)
    -> ssubst t (snoc sub (v, u)) = ssubst t sub.
Proof using.
  introv k isp i. assert(prog_sub (snoc sub (v,u))). introv Hin.
  apply in_snoc in Hin. dorn Hin; auto.
  - apply k in Hin. sp.
  - inverts Hin. subst.  trivial.
  - change_to_ssubst_aux4.
    apply ssubst_aux_snoc_dup ;sp.
Qed.



Lemma ssubst_aux_swap:
  forall t (sub : Substitution) v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> isprogram u
    -> ! LIn v (dom_sub sub)
    -> ssubst_aux t ((v, u) :: sub) = ssubst_aux t (snoc sub (v, u)).
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    rw @sub_find_snoc.
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    remember (beq_var v n); destruct b; sp.
    apply beq_var_true in Heqb; subst; sp.
    apply sub_find_some in Heqo.
    apply in_dom_sub in Heqo; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    try (complete (sp; allrw in_snoc; sp; allapply pair_inj; sp; subst; sp; apply_in_hyp p; sp)).

    rw @sub_filter_snoc.
    remember (memvar v l); symmetry in Heqb; destruct b; sp; simpl.
    rewrite H with (lv := l); sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp p; sp.
    allrw <- @dom_sub_sub_filter.
    allrw @in_remove_nvars; sp.
Qed.

Lemma ssubst_swap:
  forall t (sub: @Substitution Opid) v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> isprogram u
    -> ! LIn v (dom_sub sub)
    -> ssubst t ((v, u) :: sub) = ssubst t (snoc sub (v, u)).
Proof using.
  introv k isp ni. assert(prog_sub (snoc sub (v,u))).
  - introv Hin.
    apply in_snoc in Hin. dorn Hin; auto.
    + apply k in Hin. sp.
    + inverts Hin. subst.  trivial.
  - assert(prog_sub (cons (v,u) sub)). introv Hin.
    dorn Hin; auto.
    + inverts Hin. subst.  trivial.
    + apply k in Hin. sp.

  + change_to_ssubst_aux4.
    apply ssubst_aux_swap ;sp.
Qed.

Lemma ssubst_aux_shift_nb :
(forall t (sub1 sub2 sub3 : @Substitution Opid),
    disjoint (dom_sub sub1) (dom_sub sub2)
    -> ssubst_aux t (sub1 ++ sub2 ++ sub3) = ssubst_aux t (sub2 ++ sub1 ++ sub3))
*
(forall t (sub1 sub2 sub3 : @Substitution Opid),
    disjoint (dom_sub sub1) (dom_sub sub2)
    -> ssubst_bterm_aux t (sub1 ++ sub2 ++ sub3) = ssubst_bterm_aux t (sub2 ++ sub1 ++ sub3)).
Proof using.
  apply NTerm_BTerm_ind.
- introv d; simpl.
  repeat (rw @sub_find_app).
  remember (sub_find sub1 n); destruct o; symmetry in Heqo; auto.
  apply sub_find_some in Heqo.
  unfold disjoint in d.
  apply in_dom_sub in Heqo.
  apply d in Heqo.
  rw <- @sub_find_none_iff in Heqo; rw Heqo; sp.

- introv Hind d. simpl. f_equal.
  apply eq_maps; introv i. eauto.
- introv Hind d. simpl. f_equal.
  repeat (rw @sub_filter_app).
  apply Hind; eauto.
  allrw in_app_iff; sp; allrw @in_sub_filter; sp.

  repeat (rw <- @dom_sub_sub_filter).
  unfold disjoint; introv i1 i2.
  allrw in_remove_nvars; exrepnd.
  unfold disjoint in d; apply_in_hyp p; sp.
Qed.

Notation ssubst_aux_shift := (fst ssubst_aux_shift_nb).

Lemma ssubst_aux_rev:
forall (sub : @Substitution Opid) t ,
  no_repeats (dom_sub sub) 
    -> ssubst_aux t sub = ssubst_aux t (rev sub).
Proof using.
  induction sub; intros t Hnr;
    [do 2 rewrite ssubst_aux_nil; refl|].
  simpl. rewrite cons_as_app.
  rewrite <- (app_nil_r ([a] ++ sub)).
  simpl in Hnr.
  rewrite <- app_assoc.
  rewrite ssubst_aux_shift with (sub3:=[]);[| noRepDis].
  rewrite app_nil_r.
Abort.


Lemma ssubst_aux_rev:
forall (sub sr: @Substitution Opid) t ,
  no_repeats (dom_sub sub) 
    -> ssubst_aux t (sub++sr) = ssubst_aux t ((rev sub)++sr).
Proof using.
  induction sub; intros ? ? Hnr;
    [refl|].
  simpl. rewrite cons_as_app.
  simpl in Hnr.
  rewrite ssubst_aux_shift;[| noRepDis].
  rewrite <- app_assoc.
  apply IHsub. noRepDis.
Qed.

Lemma ssubst_shift :
  forall t (sub1 sub2 sub3 :@Substitution Opid),
    (forall v t, LIn (v, t) (sub1 ++ sub2 ++ sub3) -> isprogram t)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> ssubst t (sub1 ++ sub2 ++ sub3) = ssubst t (sub2 ++ sub1 ++ sub3).
Proof using.
  introv Hpr. assert (prog_sub (sub2 ++ sub1 ++ sub3)).
  apply sub_app_sat_if in Hpr. repnd.
  apply sub_app_sat_if in Hpr. repnd.
  apply sub_app_sat;sp.
  apply sub_app_sat;sp.
  intros.
  change_to_ssubst_aux4.
  apply ssubst_aux_shift;sp.
Qed.




Fixpoint ssubst_sub (sub1 sub2 : Substitution) : @Substitution Opid :=
  match sub1 with
    | nil => nil
    | (v,t) :: sub => (v,ssubst t sub2) :: ssubst_sub sub sub2
  end.

Lemma ssubst_sub_cons :
  forall v t (sub1 sub2 :@Substitution Opid),
    ssubst_sub ((v, t) :: sub1) sub2
    = (v, ssubst t sub2) :: ssubst_sub sub1 sub2.
Proof using.
  sp.
Qed.

Lemma ssubst_sub_nil :
  forall (sub :@Substitution Opid), ssubst_sub [] sub = [].
Proof using.
  sp.
Qed.

Hint Rewrite ssubst_sub_nil.

Lemma sub_find_ssubst_sub_if_some :
  forall v t sub1 sub2,
    sub_find sub1 v = Some t
    -> sub_find (ssubst_sub sub1 sub2) v = Some (ssubst t sub2).
Proof using.
  induction sub1; simpl; sp; allsimpl.
  remember (beq_var a0 v); destruct b.
  inversion H; subst; sp.
  apply IHsub1 with (sub2 := sub2) in H; sp.
Qed.

Lemma sub_find_ssubst_sub_if_none :
  forall v sub1 sub2,
    sub_find sub1 v = None
    -> sub_find (ssubst_sub sub1 sub2) v = None.
Proof using.
  induction sub1; simpl; sp; allsimpl.
  remember (beq_var a0 v); destruct b; sp.
Qed.

Lemma in_ssubst_sub_implies :
  forall v t sub1 sub2,
    LIn (v, t) (ssubst_sub sub1 sub2)
    -> {u : NTerm $ (LIn (v, u) sub1 # t = ssubst u sub2)}.
Proof using.
  induction sub1; simpl; sp; allsimpl; sp; inj.

  exists a; sp.

  apply_in_hyp p; sp; subst.
  exists u; sp.
Qed.

Lemma sub_filter_ssubst_sub :
  forall sub1 sub2 l,
    sub_filter (ssubst_sub sub1 sub2) l
    = ssubst_sub (sub_filter sub1 l) sub2.
Proof using.
  induction sub1; simpl; sp; allsimpl.
  destruct (memvar a0 l); sp; simpl.
  rw IHsub1; sp.
Qed.

Theorem disjoint_bv_sub_ot: forall o lbt lv nt (sub : @Substitution Opid), disjoint_bv_sub (oterm o lbt) sub 
    -> LIn (bterm lv nt) lbt 
    -> disjoint_bv_sub nt (sub_filter sub lv).
Proof using. unfold disjoint_bv_sub. introv Hdis Hin. introv Hins. 
   apply in_sub_filter in Hins. repnd. apply Hdis in Hins0. simpl in Hins0. 
   eapply disjoint_lbt_bt2 in Hins0. Focus 2. eauto. repnd; auto. 
Qed.

Lemma ssubst_aux_sub_filter2:
  forall t (sub : @Substitution Opid) l,
    disjoint (free_vars t) l
    -> ssubst_aux t (sub_filter sub l) = ssubst_aux t sub.
Proof using.
  nterm_ind1 t as [v| o lbt Hind] Case; simpl; introv Hd.

  - Case "vterm".
    remember (sub_find (sub_filter sub l) v); symmetry in Heqo; destruct o.
    rw sub_find_sub_filter_some in Heqo; sp.
    allrw; sp.
    rw sub_find_sub_filter_none in Heqo; sp.
    allrw; sp.
    allrw disjoint_singleton_l; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]; simpl.
    pose proof (sub_eta_length (sub_filter sub l)) as X99X.

    f_equal. rw sub_filter_swap.
    rw <- @sub_filter_app_r.
    rw sub_filter_app_as_remove_nvars.
    rw @sub_filter_app_r.
    rewrite Hind with (lv := lv); sp.
    eapply disjoint_flat_map_l in Hd;eauto.
    allsimpl. apply disjoint_remove_nvars_l in Hd.
    sp.
Qed.


Lemma ssubst_sub_filter2:
  forall t (sub : @Substitution Opid) l,
    disjoint_bv_sub t sub
    -> disjoint (free_vars t) l
    -> ssubst t (sub_filter sub l) = ssubst t sub.
Proof using.
  intros. change_to_ssubst_aux4.
  apply ssubst_aux_sub_filter2;try(sp;fail);
  try(rw disjoint_sub_as_flat_map;disjoint_reasoning).
  apply disjoint_sym. rw <- disjoint_sub_as_flat_map.
  apply sub_filter_sat.
  rw  disjoint_sub_as_flat_map. disjoint_reasoning.
Qed.

Ltac disjoint_flat2 := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.

Lemma ssubst_sub_sub_filter_disjoint2:
  forall (sub1 sub2 : @Substitution Opid) l,
    disjoint (flat_map bound_vars (range sub1)) (flat_map free_vars (range sub2))
   -> disjoint l (flat_map free_vars (range sub1))
   ->  ssubst_sub (sub_filter sub1 l) (sub_filter sub2 l)
       = ssubst_sub (sub_filter sub1 l) sub2.
Proof using.
  induction sub1 as [|(v,t) sub Hind]; introv H1dis H2dis; allsimpl;sp.
  rw @memvar_dmemvar.
  cases_ifn Hm; allsimpl; rw Hind; disjoint_reasoningv;[].
  f_equal; f_equal;[].
  rw ssubst_sub_filter2;sp; disjoint_reasoningv;[].
  disjoint_flat. disjoint_reasoningv.
Qed.


Lemma ssubst_sub_sub_filter_disjoint:
  forall sub1 sub2 l,
    (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) l)
    -> ssubst_sub (sub_filter sub1 l) (sub_filter sub2 l)
       = ssubst_sub (sub_filter sub1 l) sub2.
Proof using.
  intros. apply ssubst_sub_sub_filter_disjoint2;sp;
  disjoint_flat;
  disjoint_reasoningv;
  change_to_ssubst_aux4.
Qed.

(*
Lemma sub_mk_renames_disjoint :
  forall l1 l2,
    disjoint l1 l2
    -> @sub_mk_renames NVar _ _ _ Opid l1 l2 = (l1, []).
Proof using.
  induction l1; simpl; sp.
  allrw disjoint_cons_l; sp.
  apply_in_hyp p.
  allrw.
  remember (memvar a l2); symmetry in Heqb; destruct b; sp.
  allrw fold_assert.
  rw assert_memvar in Heqb; sp.
Qed.

Lemma sub_mk_renames2_disjoint :
  forall l1 l2 lva,
    disjoint l1 l2
    -> @sub_mk_renames2 NVar _ _ _ Opid l1 l2 lva = (l1, []).
Proof using.
  induction l1; simpl; try (complete sp); introv d.
  allrw disjoint_cons_l; exrepnd.
  apply IHl1 with (lva:=lva) in d0.
  allrw; boolvar; sp.
Qed.
*)


Ltac dsub_find sn :=
  match goal with
    | [  |- context[sub_find ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
    | [ H: context[sub_find ?s ?v] |- _ ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
  end.

Lemma ssubst_aux_app:
  forall t sub1 sub2,
    disjoint (flat_map bound_vars (range sub1)) (flat_map free_vars (range sub2))
    -> disjoint_bv_sub t sub1
    -> disjoint_bv_sub t sub2
    -> ssubst_aux (ssubst_aux t sub1) sub2 = ssubst_aux t (ssubst_sub sub1 sub2 ++ sub2).
Proof using.
  nterm_ind1 t as [v| o lbt Hind] Case; simpl; introns Hss.

  - Case "vterm".
    rw @sub_find_app.
    dsub_find s1v; symmetry in Heqs1v.
    + applydup @sub_find_some in Heqs1v.
      apply sub_find_ssubst_sub_if_some with (sub2 := sub2) in Heqs1v.
      rw Heqs1v; sp. revert Heqs1v. change_to_ssubst_aux4; sp.
      disjoint_flat.
    + apply sub_find_ssubst_sub_if_none with (sub2 := sub2) in Heqs1v.
      rw Heqs1v ; simpl; sp.

  - Case "oterm".
    f_equal. rw map_map.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]. unfold compose. simpl.
    f_equal.
    rw @sub_filter_app.
    rw sub_filter_ssubst_sub.
    assert (ssubst_sub (sub_filter sub1 lv) (sub_filter sub2 lv)
            = ssubst_sub (sub_filter sub1 lv) sub2) as eq.
    + apply ssubst_sub_sub_filter_disjoint2; sp.
      disjoint_flat. disjoint_reasoning.
    + rw <- eq. sp. rewrite Hind with (lv := lv); sp;
      disjoint_flat;
      disjoint_flat_sf; disjoint_reasoningv.
Qed.

Definition subst_aux_sub (s1 s2: @Substitution Opid) :=
  map_sub_range (fun t => ssubst_aux t s2) s1.


Lemma simple_ssubst_aux_ssubst_aux :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> ssubst_aux (ssubst_aux t sub1) sub2
       = ssubst_aux t ((ssubst_sub sub1 sub2) ++ sub2).
Proof using.
  introv H1 H2. apply ssubst_aux_app; disjoint_flat; disjoint_reasoningv;
    change_to_ssubst_aux4; disjoint_reasoningv.
Qed.

Lemma disjoint_bv_sub_ssubst_sub: forall t sub1 sub2, 
  disjoint_bv_sub t sub1
  -> prog_sub sub2
  -> disjoint_bv_sub t (ssubst_sub sub1 sub2).
Proof using.
  introv H1b H2b.
  unfold sub_range_sat. introv Hin. apply in_ssubst_sub_implies in Hin.
  exrepnd.
  subst. introv Hin.
  rw isprogram_ssubst2 in Hin;[|sp;fail]. apply in_remove_nvars in Hin. repnd.
  apply H1b in Hin1. apply Hin1 in Hin0. sp.
Qed.

Lemma simple_ssubst_ssubst :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> ssubst (ssubst t sub1) sub2
       = ssubst t ((ssubst_sub sub1 sub2) ++ sub2).
Proof using.
  introv Hd Hp.
  assert (disjoint_bv_sub t (ssubst_sub sub1 sub2 ++ sub2)).
  apply sub_app_sat;sp.
  - apply disjoint_bv_sub_ssubst_sub;sp.
  - apply prog_sub_disjoint_bv_sub;sp.
  - change_to_ssubst_aux4. apply simple_ssubst_aux_ssubst_aux; [|sp].
    apply disjoint_sub_as_flat_map;sp. disjoint_reasoning.
Qed.


(*
Lemma simple_csubst_ssubst :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> csubst (ssubst t sub1) sub2
       = csubst t ((ssubst_sub sub1 sub2) ++ sub2).
Proof using.
*)

(* keeps the variables from vars *)
Fixpoint sub_keep (sub : Substitution) (vars : list NVar) : @Substitution Opid:=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then (v, t) :: sub_keep xs vars
      else sub_keep xs vars
  end.

Lemma sub_find_sub_keep_some :
  forall sub vs v t,
    sub_find (sub_keep sub vs) v = Some t
    <=> sub_find sub v = Some t
        # LIn v vs.
Proof using.
  induction sub; simpl; sp.
  split; sp.
  boolvar; simpl; allrw; boolvar; sp; split; sp.
Qed.

Lemma sub_find_sub_keep_none :
  forall sub vs v,
    sub_find (sub_keep sub vs) v = None
    <=> sub_find sub v = None
        [+] ! LIn v vs.
Proof using.
  induction sub; simpl; sp.
  boolvar; simpl; allrw; boolvar; sp; split; sp.
Qed.

Lemma sub_filter_sub_keep :
  forall sub vs1 vs2,
    sub_filter (sub_keep sub vs1) vs2
    = sub_keep (sub_filter sub vs2) vs1.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 vs1); remember (memvar a0 vs2).
  symmetry in Heqb; symmetry in Heqb0.
  destruct b; destruct b0; allsimpl;
  try (rw Heqb); try (rw Heqb0); sp.
  rw IHsub; sp.
Qed.

Theorem in_sub_keep:
  forall (sub : Substitution) (v : NVar) (t : NTerm)  (vars : list NVar),
    LIn (v, t) (sub_keep sub vars) <=> LIn (v, t) sub # LIn v vars.
Proof using.
  induction sub. simpl; split; sp.
  simpl. destruct a as [v t]. introv.
  cases_if as Hmv;
    (applydup @assert_memvar in Hmv || applydup @assert_memvar_false in Hmv) ; simpl;
    split; introv Hor.
  - invertsn Hor. invertsn Hor; split; auto.  apply IHsub in Hor; repnd; auto.
  - inverts Hor as Hor Hin. invertsn Hor. invertsn Hor. left; reflexivity.   right. apply IHsub;  auto.
  - apply IHsub in Hor. repnd. split; trivial. right; trivial.
  - inverts Hor as Hor Hin. invertsn Hor. invertsn Hor. destruct Hmv0; trivial. apply IHsub; split; trivial.
Qed.

(* Theorem memvar2 (v:NVar) (vs:list NVar) : {LIn v vs}  + {! LIn v vs} := *)

Notation assert_memvar_false := (@assert_memvar_false NVar).


Theorem sub_keep_nest:
  forall  sub vs1 vs2,
    (forall v, LIn v vs2 -> LIn v vs1 [+] ! LIn v (dom_sub sub))
    -> sub_keep (sub_keep sub vs1) vs2 =sub_keep sub vs2.
Proof using.
  induction sub as [| (hv,ht) sub]; introv Hin; [reflexivity | allsimpl].
  simpl. cases_if as Hmv1; cases_if as Hmv2; simpl; try rw Hmv1; try rw Hmv2; sp;
         (applydup assert_memvar in Hmv1 || applydup assert_memvar_false in Hmv1);
         (applydup assert_memvar in Hmv2 || applydup assert_memvar_false in Hmv2); sp;
         [f_equal | trivial | trivial | trivial] ;
         try(apply IHsub; introv Hinv; applydup Hin in Hinv; invertsn Hinv0;
             [left ;trivial | right; apply not_over_or in Hinv0; repnd; trivial]).
  apply Hin in Hmv3. invertsn Hmv3. apply Hmv0 in Hmv3; sp.
  apply not_over_or in Hmv3. repnd. destruct Hmv4. reflexivity.
Qed.

Lemma simple_ssubst_aux_trim :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> ssubst_aux t sub = ssubst_aux t (sub_keep sub (free_vars t)).
Proof using.
  nterm_ind t Case;  introv Hdis.
  Case "vterm". simpl.
    cases  (sub_find sub n) as Heqs.
    assert (sub_find (sub_keep sub [n]) n = Some n0) as Heqk.
    apply sub_find_sub_keep_some; split; simpl; auto.
    rw Heqk; reflexivity.
    assert (sub_find (sub_keep sub [n]) n = None) as Heqk.
    apply sub_find_sub_keep_none. left; trivial.
    rw Heqk; reflexivity.

  Case "oterm". simpl.  f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    simpl.
    repeat (rw bvar_renamings_subst_disjoint_bound_vars).

    repeat (rw app_nil_l); simpl.
    f_equal. 
    rw sub_filter_sub_keep. 
    symmetry. 
    rewrite H with (lv := lv); eauto. Focus 2.
       introv Hink. rw in_sub_keep in Hink. repnd. apply in_sub_filter in Hink0. repnd. 
       apply Hdis in Hink1. simpl in Hink1. apply disjoint_sym in Hink1;rw disjoint_flat_map_l in Hink1.  
       apply Hink1 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd; apply disjoint_sym. trivial. 

       assert( (sub_keep (sub_keep (sub_filter sub lv) 
        (flat_map free_vars_bterm lbt)) (free_vars nt)) =
           sub_keep (sub_filter sub lv) (free_vars nt)) as Hskeq. 
       + apply sub_keep_nest. introv Hinf. destruct (in_nvar_list_dec v lv). 
          * right. rw <- @dom_sub_sub_filter. intro HC. apply in_remove_nvars in HC. sp. 
          * left. apply lin_flat_map. eexists; split; eauto. simpl. apply in_remove_nvars; split; trivial.  
       + rw Hskeq. 
           symmetry. eapply H; eauto. 
           introv Hinf. apply in_sub_filter in Hinf. repnd. apply  Hdis in Hinf0. 
           simpl in Hinf0. apply disjoint_sym in Hinf0. rw disjoint_flat_map_l in Hinf0. 
           apply Hinf0 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd; apply disjoint_sym. trivial. 
Qed.

Lemma sub_keep_sat :  forall P sub lv,
  sub_range_sat  sub P
  -> sub_range_sat (sub_keep sub lv) P.
Proof using. introv Hall hsub. apply in_sub_keep in hsub. repnd.
  apply Hall in hsub0; auto.
Qed.


Lemma simple_ssubst_trim :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> ssubst t sub = ssubst t (sub_keep sub (free_vars t)).
Proof using.
  introv Hd. duplicate Hd as Hdd.
  apply sub_keep_sat with (lv:=(free_vars t))in Hd.
  change_to_ssubst_aux4.
  apply simple_ssubst_aux_trim;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.


Definition disjoint_bv2_sub (nt1 nt2:NTerm) (sub: Substitution) :=
  forall (v : NVar) (t : NTerm),
    LIn (v, t) sub
    -> disjoint (free_vars t) (bound_vars nt1 ++ bound_vars nt2).

Theorem wf_sub_filter: forall lv sub, wf_sub sub -> wf_sub (sub_filter sub lv).
Proof using.
  unfold wf_sub; introv s.
  introv Hin.
  allrw @in_sub_filter; exrepnd.
  apply s in Hin0; sp.
Qed.

Theorem wf_sub_keep: forall lv sub, wf_sub sub -> wf_sub (sub_keep sub lv).
Proof using.
  unfold wf_sub; introv s.
  introv Hin.
  allrw in_sub_keep; exrepnd.
  apply s in Hin0; sp.
Qed.

Theorem prog_sub_implies_wf : forall sub,
    prog_sub sub -> wf_sub sub.
Proof using.
  introv Hcl. introv Hin. apply Hcl in Hin. repnud Hin; auto.
Qed.

Notation beq_var := (@beq_var NVar).
Notation beq_var_refl := (@beq_var_refl NVar).
Notation not_eq_beq_var_false := (@not_eq_beq_var_false NVar).
Notation eq_var_dec := (@eq_var_dec NVar).
(** TODO : use the stronger lemma free_vars_ssubst_aux2 for a shorter
    and more maintainable proof *)
Theorem free_vars_ssubst_aux:
  forall nt sub,
    disjoint_bv_sub nt sub
    -> forall v,
         LIn v (free_vars (ssubst_aux nt sub))
         -> LIn v (free_vars nt)
            [+] {v' : NVar
                 $ {t : NTerm
                 $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof using. nterm_ind1 nt as [vn | o lbt Hind] Case; introv Hdis Hin.
   Case "vterm". induction sub as [| (vs,ts) sub].
   - rw ssubst_aux_nil in Hin. left;auto.
   - destruct (eq_var_dec vn vs) as [? | Hneq];
      subst;simpl in Hin;
      ((rw <- beq_var_refl in Hin;auto)
          || (rw not_eq_beq_var_false in Hin;auto)).
      + right. exists vs ts. sp; auto.
      + cases (sub_find sub vn) as Hf.
          * applydup @sub_find_some in Hf.
             right; exists vn n; split; auto. right;auto. simpl. split; auto.
          * left; auto.
  - Case "oterm".
    simpl in Hin. rw lin_flat_map in Hin.
    destruct Hin as [bt' Hin]. repnd. apply in_map_iff in Hin0.
    destruct Hin0 as [bt Hin0]. repnd. subst. destruct bt as [lv nt].
    simpl in Hin.
    simpl in Hin. rw in_remove_nvars in Hin. repnd.
    apply Hind with (lv:=lv) in Hin0; auto.
    destruct Hin0 as [Hl | Hr].
    + left. simpl. apply lin_flat_map. eexists; split; eauto. simpl.
      apply in_remove_nvars. split; auto.
    + right. parallel vs Hr. parallel ts Hr. repnd. sp;auto.
      * rw @in_sub_filter in Hr0. repnd; auto.
      * simpl. apply lin_flat_map. eexists; split; eauto. simpl.
        apply in_remove_nvars. split; auto. rw @in_sub_filter in Hr0.
        repnd; auto.
    + eapply disjoint_bv_sub_ot in Hdis; eauto.
Qed.


               

Theorem free_vars_ssubst:
  forall nt sub,
    disjoint_bv_sub nt sub
    -> forall v,
         LIn v (free_vars (ssubst nt sub))
         -> LIn v (free_vars nt)
            [+] {v' : NVar
                 $ {t : NTerm
                 $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof using.
  introns XX. change_to_ssubst_aux8.
  apply free_vars_ssubst_aux;try(sp;fail).
  try(rw disjoint_sub_as_flat_map;disjoint_reasoning).
  revert XX0.
   change_to_ssubst_aux8.
  sp.
Qed.


Theorem free_vars_ssubst_closed: forall nt sub, wf_sub sub
  -> disjoint_bv_sub nt sub
  -> prog_sub sub
  -> subsetv (free_vars (ssubst nt sub)) (free_vars nt).
Proof using.
  introv Hwf Hdis Hcl. apply subsetv_prop. intros v Hin.
  apply free_vars_ssubst with (v:=v )in Hdis; auto.
  dorn Hdis; auto. exrepnd. apply Hcl in Hdis0.
  inverts Hdis0 as  Hpr ?. rw Hpr in Hdis1. inverts Hdis1.
Qed.

 Lemma simple_ssubst_trim2 :
  forall t sub lv,
    disjoint_bv_sub t sub
    -> subsetv (free_vars t) lv
    -> ssubst t sub = ssubst t (sub_keep sub lv).
Proof using.
  introv Hdis Hsub.
  rw simple_ssubst_trim; auto.
  symmetry. rw simple_ssubst_trim; auto.
  rw sub_keep_nest; try reflexivity.
  intros; left. unfold subset in Hsub. auto.
  introv Hin. rw in_sub_keep in Hin. repnd.
  apply Hdis in Hin0; auto.
Qed.



Lemma sub_find_none_if :
  forall (sub: @Substitution Opid) v,
    ! LIn v (dom_sub sub)
    -> sub_find sub v = None.
Proof using.
  intros.
  apply sub_find_none_iff; auto.
Qed.

Lemma ssubst_sub_trivial_closed1 :
  forall sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> ssubst_sub sub1 sub2 = sub1.
Proof using.
  induction sub1; simpl; try (complete sp); introv k1 k2.
  destruct a as [a0 a]; allsimpl.
  rewrite ssubst_trivial; introv.
  rewrite IHsub1; sp.
  apply k1 with (v := v); sp.
  introv i; dands.
  apply k2 with (v := v); sp.
  generalize (k1 a0 a); intros k.
  dest_imp k hyp.
  unfold isprogram, closed in k; destruct k as [c w].
  rw c; sp.
Qed.

Lemma cover_vars_cvterm1 :
  forall v t u,
    cover_vars (get_cvterm [v] t) [(v, u)].
Proof using.
  destruct t; sp; simpl.
  rw isprog_vars_eq in i; sp.
  unfold cover_vars, over_vars.
  rewrite assert_sub_vars.
  unfold subset in *. firstorder.
Qed.


Lemma ssubst_sub_singleton :
  forall x t sub,
    ssubst_sub [(x, t)] sub = [(x, ssubst t sub)].
Proof using.
  sp.
Qed.

Lemma csub2sub_cons :
  forall x a s,
    csub2sub ((x,a) :: s) = (x, get_cterm a) :: csub2sub s.
Proof using.
  sp.
Qed.



Lemma sub_find_varsub :
  forall lvo lvn vo (vnt : NTerm),
    sub_find (var_ren lvo  lvn) vo = Some vnt
    -> {vn : NVar $ vnt = vterm vn # LIn (vo,vn) (combine lvo lvn)}.
Proof using.
  induction lvo as [| hvo  tlvo Hind]; introv Hsome;
  [inverts Hsome | ]. applydup @sub_find_some in Hsome.
  apply in_combine in Hsome0. repnd. apply in_map_iff in Hsome0.
  exrepnd.
  destruct lvn.
  inverts Hsome0. allsimpl.
  dorn Hsome1; subst. eexists; split; eauto. left. f_equal.
  rewrite <- beq_var_refl in Hsome. inverts Hsome. reflexivity.
  cases_if in Hsome as hbeq. invertsn Hsome.
  eexists; split; eauto. left. f_equal. apply beq_var_eq; auto.
  pose proof (Hind _ _ _ Hsome) as Hinds. clear Hind.
  exrepnd. exists vn. split; auto.
Qed.



Definition isvarc (nt: NTerm) : Prop  := 
match nt with
| vterm _ => True
| _ => False
end.


Lemma isvarcImplies  (nt: NTerm) : isvarc nt -> {x:NVar | nt = vterm x}.
Proof using.
  intro Hc.
  destruct nt; simpl in *;[eexists; eauto | contradiction].
Defined.

Definition  allvars_sub (sub: Substitution) : Prop:=
  sub_range_sat sub isvarc.

Lemma sub_find_sat :  forall P (sub : @Substitution Opid) vo vnt,
  sub_range_sat sub P
  -> sub_find sub vo = Some vnt
  -> P vnt.
Proof using. introv Hall hsub. apply sub_find_some in hsub.
  applydup Hall in hsub. exrepnd. subst.  auto.
Qed.

Lemma sub_find_allvars :  forall sub vo vnt,
  allvars_sub sub
  -> sub_find sub vo = Some vnt
  -> {vn : NVar | vnt = vterm vn}.
Proof using.
  intros.
  apply isvarcImplies.
  eapply (sub_find_sat isvarc); eauto.
Qed.


Lemma sub_filter_allvars :  forall sub lv,
  allvars_sub sub
  -> allvars_sub (sub_filter sub lv).
Proof using. exact (sub_filter_sat isvarc).
Qed.


Definition get_sub_dom_vars sub (pall: allvars_sub sub) : list NVar.
  induction sub;[exact []|].
  unfold allvars_sub, sub_range_sat in *.
  apply cons.
  -   destruct a as [v t].
     specialize (pall v t (or_introl eq_refl)). 
    destruct t as [n|];[exact n| contradiction].
  - apply IHsub. clear IHsub. intros vv tt Hyp.
    specialize (pall vv tt (or_intror Hyp)).
    assumption.
Defined.




Lemma sub_mk_renames_allvars :
  forall lv1 lv2 lv sub,
    (lv, sub) = (sub_mk_renames lv1 lv2)
    -> allvars_sub sub.
Proof using. induction lv1 as [|v lv1 Hind]; introv Heq.
  allsimpl. invertsn Heq. introv Hin. inverts Hin.
  allsimpl. remember (sub_mk_renames lv1 lv2) as recv.
  destruct recv. apply Hind in Heqrecv.
  cases_if in Heq; inverts Heq; trivial.
  introv Hin. allsimpl. dorn Hin. inverts Hin. eexists; eauto.
  apply Heqrecv in Hin; trivial.
Qed.


Lemma sub_mk_renames2_allvars : forall lv1 lv2 lv sub lva,
  (lv, sub) = (sub_mk_renames2 lv1 lv2 lva)
   -> allvars_sub sub.
Proof using. induction lv1 as [|v lv1 Hind]; introv Heq.
  allsimpl. invertsn Heq. introv Hin. inverts Hin.
  allsimpl. remember (sub_mk_renames2 lv1 lv2 lva) as recv.
  destruct recv. apply Hind in Heqrecv.
  cases_if in Heq; inverts Heq; trivial.
  introv Hin. allsimpl. dorn Hin. inverts Hin. eexists; eauto.
  apply Heqrecv in Hin; trivial.
Qed.



 Lemma ssubst_aux_allvars_preserves_size : forall nt sub,
    allvars_sub sub
   -> size (ssubst_aux nt sub) = size nt.
Proof using. nterm_ind1 nt as [v | o lbt Hind] Case; introv Hall.
  Case "vterm". simpl.
    cases (sub_find sub v ) as Hsf; try reflexivity.
    apply sub_find_allvars in Hsf; trivial. exrepnd. subst; auto.
  Case "oterm". simpl. f_equal. f_equal.
    rewrite map_map. apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]. unfold compose. simpl.
    repnd. eapply Hind; eauto. apply sub_filter_sat;sp.
Qed.


Theorem allvars_combine: forall lvo lvn,
    allvars_sub (var_ren lvo lvn).
Proof using. introv Hin. apply in_combine in Hin. repnd.
  apply in_map_iff in Hin. exrepnd. unfold isvarc. rewrite Hin1. auto.
Qed.

Lemma ssubst_aux_allvars_preserves_size2 : forall (nt:NTerm) lvo lvn,
   size (ssubst_aux nt (var_ren lvo lvn)) = size nt.
Proof using.
  intros. apply ssubst_aux_allvars_preserves_size.
  apply allvars_combine.
Qed.

Theorem not_isvarc_ot: forall op lbt,
  (isvarc (oterm op lbt)) <=> False.
Proof using.
  split; try (sp; fail ); (** done for univ := prop*) (introv Hc; exrepnud Hc; inverts Hc0 ).
Qed.

Theorem isvarc_ssubst_iff: forall sub nt,
  allvars_sub sub
  -> (isvarc (ssubst nt sub) <=> isvarc nt).
Proof using. destruct nt; introv Hal.
  simpl. unfold ssubst. simpl. cases (sub_find sub n) as Hc.
  apply sub_find_allvars in Hc; auto. exrepnd. subst.
  split ;eexists; eauto.  apply t_iff_refl.
  rewrite ssubst_ssubst_aux_hide. unfold ssubsthide. cases_if;simpl;
  allrw not_isvarc_ot; apply t_iff_refl.
Qed.

Theorem isvarc_ssubst_vterm: forall sub v,
  allvars_sub sub
  -> (isvarc (ssubst (vterm v) sub)).
Proof using. intros.
  apply isvarc_ssubst_iff; auto.
  eexists; eauto.
Qed.


Theorem isvarc_ssubst_implies2: forall v nt sub,
  allvars_sub sub
  -> vterm v = (ssubst nt sub)
  -> isvarc nt.
Proof using. intros ? ? ? ? Heq. 
 assert (isvarc (ssubst nt sub)) as Hisv by (unfold isvarc; rewrite <- Heq; auto).
 eapply isvarc_ssubst_iff; eauto. 
Qed.

Theorem isvarc_ssubst_ot: forall v lbt sub o,
  allvars_sub sub 
     -> oterm o lbt = ssubst (vterm v) sub
     -> False.
Proof using. introv Hall Heq. 
    assert (isvarc (vterm v)) as Hc by (eexists; eauto).
    apply (isvarc_ssubst_iff sub) in Hc; trivial.
    rw <- Heq in Hc. rw not_isvarc_ot in Hc; sp.
Qed.


Notation assert_sub_vars := (@assert_sub_vars NVar).

Lemma covered_app_weak_l :
  forall (t:NTerm) vs1 vs2,
    covered t vs1
    -> covered t (vs1 ++ vs2).
Proof using.
  unfold covered; intros.
  allrw @assert_sub_vars; sp.
  apply_in_hyp p.
  allrw in_app_iff; sp.
Qed.

Lemma covered_app_weak_r :
  forall (t:NTerm) vs1 vs2,
    covered t vs2
    -> covered t (vs1 ++ vs2).
Proof using.
  unfold covered; intros.
  allrw assert_sub_vars; sp.
  apply_in_hyp p.
  allrw in_app_iff; sp.
Qed.

Lemma sub_find_some_implies_memvar_true :
  forall (sub:@Substitution Opid) v t,
    sub_find sub v = Some t
    -> memvar v (dom_sub sub) = true.
Proof using.
  sp.
  apply sub_find_some in H.
  rewrite fold_assert.
  rw assert_memvar.
  apply in_dom_sub in H; auto.
Qed.

Lemma sub_find_none_implies_memvar_false :
  forall (sub: @Substitution Opid) v,
    sub_find sub v = None
    -> memvar v (dom_sub sub) = false.
Proof using.
  sp.
  apply sub_find_none2 in H.
  rw not_of_assert.
  rw assert_memvar; auto.
Qed.

Fixpoint sub_keep_first (sub : @Substitution Opid) (vars : list NVar) : Substitution :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then (v, t) :: sub_keep_first xs (remove_nvar vars v)
      else sub_keep_first xs vars
  end.

Lemma sub_keep_first_nil_r :
  forall sub,
    sub_keep_first sub [] = [].
Proof using.
  induction sub; simpl; sp.
Qed.
Local Opaque varInterface.beq_var.

Lemma sub_keep_first_singleton_r_some :
  forall sub v t,
    sub_find sub v = Some t
    -> sub_keep_first sub [v] = [(v,t)].
Proof with (autorewrite with SquiggleEq) using.
  induction sub; simpl; sp.
  rewrite remove_nvar_cons.
  rewrite remove_nvar_nil.
  repeat rewrite decide_decideP.
  destruct (decideP (v=a0)); subst; autorewrite with SquiggleEq.
  allrw <- beq_var_refl.
  inversion H; subst. rewrite sub_keep_first_nil_r. refl.
  
  rw not_eq_beq_var_false in H; auto.
Qed.

Lemma sub_keep_first_singleton_r_none :
  forall sub v,
    sub_find sub v = None
    -> sub_keep_first sub [v] = [].
Proof using.
  induction sub; simpl; sp.
  rewrite remove_nvar_cons.
  rewrite remove_nvar_nil.
  repeat rewrite decide_decideP.
  destruct (decideP (a0=v)); subst; autorewrite with SquiggleEq.
  allrw <- beq_var_refl; sp.
  rewrite not_eq_beq_var_false; auto.
  rw not_eq_beq_var_false in H; auto.
  cases_if; auto.
  revert H0. cases_if; intros; try congruence; try tauto.
Qed.

Lemma sub_filter_sub_keep_first_weak_in :
  forall sub vs1 vs2 v,
    LIn v vs1
    -> sub_filter (sub_keep_first sub vs2) vs1
       = sub_filter (sub_keep_first sub (remove_nvar vs2 v)) vs1.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 (remove_nvar vs2 v)); symmetry in Heqb; destruct b;
  remember (memvar a0 vs2); symmetry in Heqb0; destruct b; simpl;
  remember (memvar a0 vs1); symmetry in Heqb1; destruct b; simpl; sp;
  allrw @fold_assert;
  allrw @not_of_assert;
  allrw @assert_memvar;
  allrw @in_remove_nvar; sp.

  - rewrite remove_nvar_comm; auto.

  - rewrite remove_nvar_comm.
    symmetry.
    rewrite <- IHsub; sp.

  - destruct (eq_var_dec a0 v); subst; sp.
    provefalse; apply Heqb; sp.

  - destruct (eq_var_dec a0 v); subst; sp.
    provefalse; apply Heqb; sp.
Qed.

Lemma sub_keep_first_sub_filter :
  forall sub vs1 vs2,
    sub_keep_first (sub_filter sub vs1) vs2
    = sub_filter (sub_keep_first sub vs2) vs1.
Proof using.
  induction sub; simpl; sp.
  remember (memvar a0 vs1); symmetry in Heqb; destruct b;
  remember (memvar a0 vs2); symmetry in Heqb0; destruct b; sp; simpl; allrw; sp.

  rw <- sub_filter_sub_keep_first_weak_in; sp.
  allrw fold_assert; allrw assert_memvar; sp.
Qed.

Lemma in_sub_keep_first :
  forall sub v vs t,
    LIn (v,t) (sub_keep_first sub vs)
    <=> (sub_find sub v = Some t # LIn v vs).
Proof using.
  induction sub; simpl; sp.
  split; sp.

  destruct (eq_var_dec a0 v); subst;
  allrw <- beq_var_refl;
  allrw not_eq_beq_var_false; auto;
  try (remember (memvar v vs); symmetry in Heqb; destruct b);
  try (remember (memvar a0 vs); symmetry in Heqb; destruct b);
  allsimpl; rw IHsub; allrw in_remove_nvars; allsimpl; allrw not_over_or;
  split; sp; cpx.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; auto.

  match goal with
  [H: Some _ = Some _ |- _ ] => inverts H
  end; subst; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; sp.

  match goal with
  [H: Some _ = Some _ |- _ ] => inverts H
  end; subst; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; sp.

(*
  right; sp.
  right; sp.
*)
Qed.

Lemma eqsetv_free_vars_disjoint_aux :
  forall t : NTerm,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> eq_set (free_vars (ssubst_aux t sub))
              (remove_nvars (dom_sub sub) (free_vars t)
               ++ sub_free_vars (sub_keep_first sub (free_vars t))).
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl;
    rewrite remove_nvars_cons_r.
    + applydup sub_find_some_implies_memvar_true in Heqo.
      rewrite Heqo0.
      rewrite remove_nvars_nil_r; simpl.
      applydup sub_keep_first_singleton_r_some in Heqo.
      rewrite Heqo1; simpl.
      rewrite app_nil_r; auto.

    + applydup sub_find_none_implies_memvar_false in Heqo.
      rewrite Heqo0.
      rewrite remove_nvars_nil_r.
      applydup sub_keep_first_singleton_r_none in Heqo.
      rewrite Heqo1; simpl; sp.

  - Case "oterm".
    rewrite remove_nvars_flat_map.
    rewrite flat_map_map; unfold compose.

    rewrite eqsetv_prop; sp.
    sp_iff SCase; intro.

    + SCase "->".

      allrw in_app_iff.
      allrw lin_flat_map; exrepd.
      destruct x0; allsimpl.

      allrw in_remove_nvars; sp.

      generalize (H n l H1 (sub_filter sub l)) as Hg; sp.
      dest_imp Hg hyp.
      intros ? ? Hin.
      apply in_sub_filter in Hin; sp.
      apply H0 in Hin0.
      rw disjoint_flat_map_r in Hin0.
      apply Hin0 in H1; allsimpl.
      rw disjoint_app_r in H1; sp.

      rewrite eqsetv_prop in Hg.
      rw Hg in H3.
      allrw in_app_iff; sp.
      rw <- @dom_sub_sub_filter in H3.
      allrw in_remove_nvars; sp.

      left.
      exists (bterm l n); simpl; sp.
      allrw in_remove_nvars; sp.

      allrw @in_sub_free_vars_iff; sp.
      rewrite sub_keep_first_sub_filter in H4.
      allrw @in_sub_filter; sp.
      allrw in_sub_keep_first; sp.
      right.
      exists x0 t; sp.
      allrw in_sub_keep_first; sp.
      rw lin_flat_map.
      exists (bterm l n); simpl; sp.
      rw in_remove_nvars; sp.

    + SCase "<-".

      allrw in_app_iff; sp; allrw lin_flat_map; exrepd;
      allrw in_remove_nvars; repd; allsimpl.

      destruct x0; allsimpl.
      allrw in_remove_nvars; sp.

      exists (bterm l n); simpl; sp.
      rw in_remove_nvars; sp.
      generalize (H n l H1 (sub_filter sub l)) as Hg; sp.
      dest_imp Hg hyp; sp.
      allrw @in_sub_filter; sp.
      apply H0 in H6.
      allrw disjoint_flat_map_r.
      apply H6 in H1; allsimpl.
      allrw disjoint_app_r; sp.

      rewrite eqsetv_prop in Hg.
      rw Hg.
      rw in_app_iff.
      rw in_remove_nvars.
      rewrite <- dom_sub_sub_filter.
      rw in_remove_nvars.
      left; sp.


      allrw @in_sub_free_vars_iff; exrepd.
      allrw in_sub_keep_first; sp.
      allrw lin_flat_map; sp.
      exists x1; sp.
      destruct x1; allsimpl.
      allrw in_remove_nvars; sp.

      generalize (H n l H4 (sub_filter sub l)) as Hg; sp.
      dest_imp Hg hyp; sp.
      allrw @in_sub_filter; sp.
      apply H0 in H7.
      allrw disjoint_flat_map_r.
      apply H7 in H4; allsimpl.
      allrw disjoint_app_r; sp.

      rewrite eqsetv_prop in Hg.
      rw Hg.
      rw in_app_iff.
      rw @in_sub_free_vars_iff; right.
      exists x0 t; sp.
      rw in_sub_keep_first; sp.
      rw sub_find_sub_filter_some; sp.
      applydup @sub_find_some in H3.
      apply H0 in H7.
      allrw disjoint_flat_map_r.
      apply H7 in H4; allsimpl.
      allrw disjoint_app_r; sp.
      unfold disjoint in *.
      apply H8 in H2; sp.
Qed.






Theorem lmap_lapply_eq_implies: forall lv1 lvi1 lvo1 lv2 lvi2 lvo2,
         lvmap_lapply (combine lvi1 lvo1) lv1 
      = lvmap_lapply (combine lvi2 lvo2) lv2
              -> disjoint (lvo1++ lvo2) (lv1 ++ lv2)
              -> length lvi1=length lvo1
              -> length lvi2=length lvo2
              -> remove_nvars lvi1 lv1 = remove_nvars lvi2 lv2.
Proof using.
   unfold lvmap_lapply. induction lv1 as [| v1 lv1 Hind]; introv Heq Hdis; auto.
   - simpl in Heq. symmetry in Heq. apply map_eq_nil in Heq. subst. 
      repeat( rewrite remove_nvars_nil_r). refl.
   - destruct lv2 as [| v2 lv2]; [ inverts Heq; fail | allsimpl].
     repeat(rewrite remove_nvars_cons_r). 
     repeat (rewrite memvar_dmemvar).
     apply disjoint_cons_r in Hdis. 
     rw disjoint_app_r in Hdis. 
     rw disjoint_cons_r in Hdis. 
     inverts Heq as Heq1 Heq2. unfold lmap_apply in Heq1.
       intros Hl1 Hl2. 
     destruct (lmap_find deq_nvar (combine lvi1 lvo1) v1)
          as [s1 | Hin1];
     [  destruct s1 as [b1 Hin1]; apply in_combine in Hin1 
        | rewrite combine_split in Hin1; auto; simpl];
     destruct (lmap_find deq_nvar (combine lvi2 lvo2) v2)
          as [s2 | Hin2]; repnd;
     try( destruct s2 as [? Hin2]; 
          apply in_combine in Hin2); 
     try (rewrite combine_split in Hin2; auto);
     repnd; allsimpl; subst.
     
     + (repeat cases_if; try contradiction). eapply Hind; eauto. 
        apply disjoint_app_r. split; trivial.
     + subst. provefalse. apply Hdis0. apply in_app_iff. sp.
     + subst. provefalse. apply Hdis. apply in_app_iff; sp.
     + subst. (repeat cases_if; try contradiction). f_equal.
        eapply Hind; eauto. 
        apply disjoint_app_r. split; trivial.
Qed.

Notation sub_range_sat := (@sub_range_sat NVar).
(**ssubst_wf_iff proved in alpgaeq.v*)
Theorem ssubst_aux_wf_iff: 
  forall sub, 
  sub_range_sat sub nt_wf
  -> forall nt, (nt_wf nt <=> nt_wf (ssubst_aux nt sub)).
Proof using.
 introv sr. sp_iff Case; introv hyp.
 - apply ssubst_aux_preserves_wf; auto. 
 - apply ssubst_aux_nt_wf in hyp; auto. 
Qed.

Theorem ssubst_aux_allvars_wf_iff: 
  forall sub, 
  allvars_sub sub
  -> forall nt, (nt_wf nt <=> nt_wf (ssubst_aux nt sub)).
Proof using.
 introv sr. apply ssubst_aux_wf_iff.
 introv Hlin. apply sr in Hlin.
  unfold isvarc in *. destruct t; auto; tauto.
Qed.


Lemma sub_app_sat_iff :  forall P (sub1 sub2: @Substitution Opid),
  (sub_range_sat  sub1 P
    # sub_range_sat  sub2 P)
  <=> sub_range_sat (sub1 ++ sub2) P.
Proof using. sp_iff Case.
  - introv sat  Hin. repnd. apply in_app_iff in Hin.
    dorn Hin; [ apply sat0 in Hin | apply sat in Hin]; trivial.
  - introv  sat. unfold  sub_range_sat in *. split; intros; eapply sat;
    apply in_app_iff; eauto.
Qed.

Lemma isvarc_fst_unique  : forall (t:NTerm ) (p1 p2: isvarc t),
  proj1_sig (isvarcImplies _ p1)=proj1_sig (isvarcImplies _ p2).
Proof using. intros. destruct t; simpl in *; [reflexivity| tauto].
Qed.

Notation get_sub_dom_varsd := get_sub_dom_vars.

Lemma get_sub_dom_vars_eq_d :
  forall sub (pall : allvars_sub sub),
    get_sub_dom_vars sub pall = get_sub_dom_varsd sub pall.
Proof using.
  reflexivity.
Qed.

Lemma get_sub_dom_vars_cons :
  forall a b sub (pall : allvars_sub ((a,b)::sub)),
    get_sub_dom_vars ((a,b) :: sub) pall
    = proj1_sig (isvarcImplies _ (pall a b (or_introl eq_refl)))
             :: get_sub_dom_vars sub (fun v t i => pall v t (or_intror i)).
Proof using.
  introv. fold (([(a, b)] ++ sub)) in *.
  generalize (pall _ _ (or_introl eq_refl)). intro hisv.
  destruct b; simpl in *;[reflexivity| contradiction].
Qed.

Theorem get_sub_dom_vars_spec :
  forall sub (Hall: allvars_sub sub),
    sub = combine (fst (split sub)) (map vterm (get_sub_dom_vars sub Hall)).
Proof using.
  introv.
  induction sub; introv; try (complete auto).
  destruct a as [v t].
  rw split_cons; rw simpl_fst.
  rw get_sub_dom_vars_cons.
  rw map_cons; rw combine_cons.
  generalize (Hall _ _ (or_introl eq_refl)). intro isvar.
  unfold isvarc in isvar. 
  destruct t;[| contradiction].
   simpl; subst.
  apply cons_eq.
  generalize (IHsub (fun v t i => Hall v t (or_intror i))); sp.
Qed.

(*
Theorem get_sub_dom_vars_spec :
  forall sub (Hall: allvars_sub sub),
    sub = combine (fst (split sub)) (map vterm (get_sub_dom_vars sub Hall)).
Proof using.
  induction sub as [| (v,t) sub Hind]; auto. intros ?. simpl.
  destruct (split sub) as [lv lnt]. simpl. f_equal. 
  - f_equal.
    (** wierd! if I dont specify implicit args,
    it guesses wrong ones and causes failure *)
    remember (Hall v t
           (@inl
              (@eq (prod NVar NTerm) (@pair NVar NTerm v t)
                 (@pair NVar NTerm v t))
              (@LIn (prod NVar NTerm) (@pair NVar NTerm v t) sub)
              (@eq_refl (prod NVar NTerm) (@pair NVar NTerm v t))))
     as Hisvar.
     destruct Hisvar. subst. simpl. reflexivity.
  - allsimpl. fold ([(v, t)] ++ sub) in Hall.
    pose proof (tiff_snd (sub_app_sat_iff _ _ _) Hall). repnd.
    assert (allvars_sub sub) as Hsub by auto.
    pose proof (Hind Hsub ) as Hw.
    allsimpl.
    symmetry in Hw.
    (** need to rewrite just the LHS. *)
    apply ( @ transport _ _ _
         (fun sub1 : Substitution =>
         sub1 =
         combine lv
           (map vterm
              (gmap sub
                 (fun (a0 : NVar # NTerm) (Hin : LIn a0 sub) =>
                  projT1
                    (Hall (fst a0) (snd a0)
                       ((let (n, n0) as p
                             return
                               ((v, t) = p[+]LIn p sub ->
                                (v, t) = (fst p, snd p)[+]LIn (fst p, snd p) sub) :=
                             a0 in
                         fun p : (v, t) = (n, n0)[+]LIn (n, n0) sub => p) (inr Hin)))))))
           Hw ).
      unfold get_sub_dom_vars.  repeat (f_equal).
      repeat (apply functional_extensionality_dep; intros).
      apply isvarc_fst_unique.
Qed.
*)


Lemma get_sub_dom_vars_length sub Hall : length (get_sub_dom_varsd sub Hall) = length sub.
Proof using.
  induction sub; simpl in *;[reflexivity|].
  f_equal. eauto. 
Qed.

Theorem get_sub_dom_vars_eta:  forall sub
  (Hall: allvars_sub sub),
  {lvi,lvo: list NVar $ (sub = var_ren lvi lvo) # length lvi =length lvo}.
Proof using.
  intros. exists (fst (split sub)).
  exists (get_sub_dom_vars sub Hall).
  split. apply get_sub_dom_vars_spec.
  rewrite split_length_l.
  symmetry. apply get_sub_dom_vars_length. 
Defined.


Theorem get_sub_dom_vars_ren:  forall lvi lvo
  (Hall: allvars_sub (var_ren lvi lvo)),
  length lvi=length lvo
  -> get_sub_dom_vars (var_ren lvi lvo) Hall = lvo.
Proof using.
  introv H. 
  pose proof (get_sub_dom_vars_spec (var_ren lvi lvo) Hall) as HH.
  unfold var_ren in HH. 
  rewrite combine_split in HH; 
    [ | rewrite map_length; trivial].
  allsimpl. apply combine_eq in HH;
  try (rewrite @map_length; auto).
  repnd. eapply @map_eq_lift_vterm; eauto.
  rewrite  get_sub_dom_vars_length.
  rewrite combine_length.
  rewrite map_length.
  rewrite H. rewrite Min.min_idempotent; refl.
Qed.


Lemma allvars_sub_filter : forall lvi lvo lv, allvars_sub (sub_filter (var_ren lvi lvo) lv).
  intros. apply sub_filter_allvars.
  apply allvars_combine.
Defined.

Lemma allvars_sub_filter_cons : forall lvi lvo lv vi vo,
   allvars_sub ((vi,vterm vo) :: (sub_filter (var_ren lvi lvo) lv)).
Proof using.
  introv Hin. dorn Hin. inverts Hin; eexists; eauto.
  apply allvars_sub_filter in Hin; auto.
Defined.


Lemma sub_find_sub_filter_eta : forall (lv : list NVar)
 (v : NVar) (t : NTerm) (sub : @Substitution Opid),
  !(LIn v lv)
  -> sub_find 
    (sub_filter sub lv) v
     = sub_find sub v.
Proof using.
  intros.
  cases (sub_find (sub_filter sub lv) v) as Hl.
  - apply sub_find_sub_filter_some in Hl; repnd; auto.
  - apply sub_find_sub_filter_none in Hl. dorn Hl; sp.
Qed.

Notation sub_filter := (@sub_filter NVar).

Theorem no_repeats_sub_filter:
  forall lvi lvo lvi0 lvo0 lv, 
  @var_ren _ Opid lvi0 lvo0 = sub_filter (var_ren lvi lvo) lv
  -> length lvi0 =length lvo0
  -> no_repeats lvo
  -> no_repeats lvo0.
Proof using.
  induction lvi as [|vi lvi Hind]; introv Heq Heql Hnr.
  unfold var_ren in Heq. simpl in Heq.
  destruct lvi0; destruct lvo0; try (inverts Heql);
   try (inverts Heq).
   - constructor.
   - destruct lvo.
     + unfold var_ren in Heq.
       simpl in Heq. 
       destruct lvi0; 
       destruct lvo0; try (inverts Heql);
       try (inverts Heq). constructor.
     + simpl in Heq. rewrite memvar_dmemvar in Heq.
        inverts Hnr as Hnin Hnr.
        destruct (dmemvar vi lv).
        eapply Hind; eauto.
       destruct lvi0; 
       destruct lvo0; try (invertsn Heql);
       try (invertsn Heq). constructor; auto.
       Focus 2. eapply Hind; eauto.
       intro Hc. eapply lin_lift_vterm in Hc.
       apply combine_in_right with (l1:=lvi0) in Hc.
       exrepnd. rewrite Heq in Hc0. apply in_sub_filter in Hc0.
       repnd. apply in_combine in Hc1. repnd. sp.
       apply lin_lift_vterm in Hc1. sp.
       rewrite map_length. omega.
Qed.

Lemma lin_combine_injective: forall {A B C D :Type} 
  (fa: A->C) (fb: B->D) (pa: injective_fun fa)
  (pb: injective_fun fb) (a:A) (b:B) (la: list A) (lb: list B),
  LIn (a, b) (combine la lb)
  <=> LIn (fa a,fb b) (combine (map fa la) (map fb lb)).
Proof using.
  induction la; intros; sp.
  simpl. destruct lb; sp.
  simpl. rw <- IHla. split; intro Hp; dorn Hp; cpx.
  apply pa in H. apply pb in H0. subst.
  sp.  
Qed.

Lemma combine_of_map_snd {A B C :Type} (f: B->C) (la:list A) lb :
  combine la (map f lb) = map (fun x => (fst x, f (snd x))) (combine la lb).
Proof.
  revert lb.
  induction la as [| a la Hind]; intros;[|destruct lb as [|b lb]]; simpl; auto.
  f_equal.
  eauto.
Qed.

Lemma lmap_find_injection:
  forall {A B C: Type} (deqa : Deq A) 
  (f: B->C)
  (a:A) (la: list A)  (lb:list B) ,
  option_map f (proj_as_option (lmap_find deqa (combine la lb) a))
    = proj_as_option (lmap_find deqa (combine la (map f lb)) a).
Proof using.
  induction la as [|va la Hind]; intros; auto. 
  allsimpl. destruct lb as [| b lb ]; auto.
  simpl. destruct (decideP (va=a)) as [eq | neq]; subst; sp.
  cases (lmap_find deqa (combine la (map f lb)) a); sp; simpl.
  apply (apply_eq proj_as_option) in H. allsimpl.
  rewrite <- Hind in H.
  destruct (lmap_find deqa (combine la lb) a) as [ ex | nex];
   allsimpl; sp.
  destruct (lmap_find deqa (combine la lb) a) as [ex | nex];
   allsimpl; sp.
  allsimpl.  provefalse.
  apply n. rewrite fst_split_as_map.
  apply in_map_iff. exists (a,f b0).
  split;[| refl].
  rewrite combine_of_map_snd.
  apply in_map_iff.
  eexists. eauto.
Qed.

Print lmap_find_injection.

Lemma lmap_apply_var: forall (lvi lvo : list NVar) v,
 (fun t=> @ssubst_aux _ _ Opid t (var_ren lvi lvo)) (vterm v)
  = vterm (lmap_apply deq_nvar (combine lvi lvo) v).
Proof using.
 intros. simpl. unfold ssubst. simpl. rewrite sub_lmap_find.
  unfold lmap_apply.
  unfold var_ren. rewrite <- (@lmap_find_injection NVar).
  cases(lmap_find deq_nvar (combine lvi lvo) v); exrepnd; simpl; auto.
Qed.

Lemma lmap_apply_var2: forall (lvi lvo : list NVar) v,
 (fun t=> @ssubst _ _ _ _ _ Opid t (var_ren lvi lvo)) (vterm v)
  = vterm (lmap_apply deq_nvar (combine lvi lvo) v).
Proof using.
 intros. simpl. unfold ssubst. simpl. rewrite sub_lmap_find.
  unfold lmap_apply.
  unfold var_ren. rewrite <- (@lmap_find_injection NVar).
  cases(lmap_find deq_nvar (combine lvi lvo) v); exrepnd; simpl; auto.
Qed.
  
Lemma lmap_lapply_var_map: forall (lvi lvo lv : list NVar),
 map (fun t:NTerm=> ssubst_aux t (var_ren lvi lvo)) (map (@vterm NVar Opid) lv)
  = map (@vterm NVar Opid) (lmap_lapply deq_nvar (combine lvi lvo) lv).
Proof using.
  induction lv as [|v lv Hind];auto.
  simpl. rewrite Hind. f_equal.
  rewrite <- lmap_apply_var; refl.
Qed.

(*
Theorem freevars_ssubst_aux_allvars:
   forall (t : NTerm) sub
     (p : allvars_sub sub),
      no_repeats (get_sub_dom_vars sub p)
       -> disjoint (get_sub_dom_vars sub p) (all_vars t)
       -> map vterm (free_vars (ssubst_aux t sub)) 
          = map (fun t=> ssubst_aux t sub) (map vterm (free_vars t)).
Proof using hdeq.
  clear varclass.
  clear VarClass.
  clear gts.
  nterm_ind1 t as [v | o lbt Hind] Case; 
  introv Hnr Hdis.
  - Case "vterm".  
    simpl. 
    unfold lmap_apply.
    cases (sub_find sub v) as Hsf; auto.
    exrepnd. apply sub_find_some in Hsf.
      pose proof (p _ _ Hsf) as X; exrepnud X. 
      subst. destruct n;[| contradiction]. refl.
  - Case "oterm".
    induction lbt as [|bt lbt IHlbt]; auto.
    allsimpl. repeat(rewrite map_app).
    rewrite IHlbt;
    [ | intros; eapply Hind; eauto; fail
           | (allrw disjoint_app_r); repnd;auto; fail].
    clear IHlbt.
     f_equal.
    destruct bt as [lv nt].
    simpl.
    remember ((sub_filter sub lv)) as sfio.
    pose proof (get_sub_dom_vars_eta sub p).
    exrepnd. subst.
     duplicate Hdis.
     unfold all_vars in Hdis. simpl in Hdis. 
     repeat(rw disjoint_app_r in Hdis).
    pose proof (allvars_sub_filter lvi lvo lv) as Halv.
  rewrite map_removevars.
    erewrite Hind with (p:=Halv)  ; eauto. clear Hind.
    unfold lvmap_lapply. 
    remember (free_vars nt) as fnt.
    pose proof (@transport _ _ _ (fun vs => subsetv fnt vs) 
                           Heqfnt (subsetv_refl fnt)) as Hsub.
    allsimpl.
     clear Heqfnt. repnd.
    induction fnt as [| vnt fnt Hfntind];
       [repeat(rewrite diff_nil || 
         rewrite remove_nvars_nil_r); refl;fail
         | simpl].
     apply subset_cons_l in Hsub; repnd.
     rewrite diff_cons_r.
     rewrite Hfntind; auto. clear Hfntind.
     rewrite memberb_din. 
     cases_if_sum Hmemd.
     + f_equal. rewrite remove_nvars_cons_r.
        rewrite memvar_dmemvar.
        cases_if_sum Hmemdin;auto.
        rewrite sub_lmap_find  in Hmemd.
        provefalse.
        apply disjoint_sym in Hdis3. 
        destruct (lmap_find deq_nvar (sub_filter (var_ren lvi lvo) lv)
           vnt) as [ex | ?]; exrepnd; allsimpl;
        [ | rewrite <- lin_lift_vterm in Hmemd; sp].
        subst. apply in_sub_filter in ex0; repnd.
        rewrite get_sub_dom_vars_ren in Hdis3; auto.
        clear Hdis Hdis1 Hdis2 Hdis4 Hdis0 Halv.
        apply in_combine in ex1. repnd.
        apply in_map_iff in ex1. exrepnd.
        subst. apply lin_lift_vterm in Hmemd.
        apply Hdis3 in Hmemd; sp.

     + rewrite remove_nvars_cons_r.
         rewrite memvar_dmemvar.
         cases_if_sum Hmemdin; auto.
         * provefalse. 
           rewrite sub_lmap_find  in Hmemd.
           destruct (lmap_find deq_nvar 
            (sub_filter (var_ren lvi lvo) lv) vnt) 
              as [ex | ?]; exrepnd; allsimpl.
           subst. apply in_sub_filter in ex0; repnd.
           apply in_combine in ex1. repnd. sp.
           rewrite <- lin_lift_vterm in Hmemd; sp.
         * simpl. f_equal.
           rewrite sub_find_sub_filter_eta; auto.
     + clear Hfntind. rewrite get_sub_dom_vars_ren; auto.
       rewrite get_sub_dom_vars_ren in Hdis4; auto.
       rewrite remove_nvars_cons_r in Hdis4. 
       revert Hdis4. cases_if; auto.
       rw disjoint_cons_r; sp.
     + remember ((sub_filter (var_ren lvi lvo) lv)) as Hsb.
        pose proof  (get_sub_dom_vars_eta Hsb Halv) as ex. exrepnd.
        revert Halv. rewrite ex0.
        intro. rewrite ex0 in HeqHsb.
        rewrite get_sub_dom_vars_ren; auto.
        rewrite get_sub_dom_vars_ren in Hnr; auto.
        apply no_repeats_sub_filter in HeqHsb; trivial.
     + remember ((sub_filter (var_ren lvi lvo) lv)) as Hsb.
        pose proof  (get_sub_dom_vars_eta Hsb Halv) as ex. exrepnd.
        revert Halv. rewrite ex0.
        intro. rewrite ex0 in HeqHsb.
        rewrite get_sub_dom_vars_ren; auto.
        rewrite get_sub_dom_vars_ren in Hdis2; auto.
        rewrite get_sub_dom_vars_ren in Hdis4; auto.
        rewrite get_sub_dom_vars_ren in Hdis3; auto.
        clear Hdis Hdis1  Hdis0 .
        assert (disjoint lvo (all_vars nt)) as Hvo.
          * apply disjoint_app_r. split; auto.
            introv Hin Hc. applydup Hdis4 in Hin.
            apply Hin0. apply in_remove_nvars. split; auto.
          * introv Hin Hc. eapply lin_lift_vterm in Hin.
            apply combine_in_right with (l1:=lvi0) in Hin.
            exrepnd. unfold var_ren in HeqHsb.
            rewrite HeqHsb in Hin0.
            apply in_sub_filter in Hin0. repnd.
            apply in_combine in Hin1. repnd.
            apply lin_lift_vterm in Hin1.
            apply Hvo in Hin1. sp.
            rewrite map_length. omega.
Qed.
*)

Lemma ssubst_vterm : forall v (sub : @Substitution Opid), 
  ssubst (vterm v) sub = ssubst_aux (vterm v) sub.
Proof using.
  intros.
  change_to_ssubst_aux4.
Qed.

Theorem freevars_ssubst_allvars9:
   forall (t : NTerm) (lvi lvo: list NVar),
      no_repeats lvo
       -> disjoint lvo (all_vars t)
       -> free_vars (ssubst_aux t (var_ren lvi lvo)) 
          = lvmap_lapply (combine lvi lvo) (free_vars t).
Proof using.
  clear varclass varcl freshv VarClass.
  nterm_ind1 t as [v | o lbt Hind] Case;
  introv Hnr Hdis.
  - Case "vterm".
    simpl. 
    unfold lmap_apply.
    rewrite sub_lmap_find.
    unfold var_ren.
    rewrite <- lmap_find_injection.
    destruct (lmap_find deq_nvar (combine lvi lvo) v); trivial.
    destruct s. refl.
  - Case "oterm".
    induction lbt as [|bt lbt IHlbt]; auto.
    allsimpl. repeat(rewrite map_app).
    rwsimpl Hdis.
    rewrite IHlbt;
    [ | intros; eapply Hind; eauto; fail| rwsimplC; disjoint_reasoningv].
    clear IHlbt.
    unfold lvmap_lapply in *.
    rewrite map_app.
    f_equal.
    destruct bt as [lv nt].
    simpl.
    pose proof (allvars_sub_filter lvi lvo lv) as Halv.
    pose proof (get_sub_dom_vars_eta _ Halv) as Heta.
    exrepnd.
    rewrite Heta0.
    erewrite Hind; eauto. clear Hind.
    unfold lvmap_lapply. 
    remember (free_vars nt) as fnt.
    pose proof (@transport _ _ _ (fun vs => subsetv fnt vs) 
                           Heqfnt (subsetv_refl fnt)) as Hsub.
    allsimpl.
     clear Heqfnt. repnd.
    induction fnt as [| vnt fnt Hfntind];
       [repeat(rewrite diff_nil || 
         rewrite remove_nvars_nil_r); refl;fail
         | simpl].
     apply subset_cons_l in Hsub; repnd.
     rewrite diff_cons_r.
     setoid_rewrite Hfntind; auto.
     setoid_rewrite Hfntind; auto. clear Hfntind.
     rewrite memberb_din. 
     cases_if_sum Hmemd.
     + f_equal. rewrite remove_nvars_cons_r.
        rewrite memvar_dmemvar.
        cases_if_sum Hmemdin;auto.
        provefalse. rewrite @lin_lift_vterm in Hmemd.
        rewrite <- lmap_apply_var in Hmemd.
        rewrite <- Heta0 in Hmemd.
        simpl in Hmemd.
        cases (sub_find (@sub_filter _ Opid (var_ren lvi lvo) lv)
           vnt) as Hs; exrepnd; allsimpl;
        [ |rewrite <- lin_lift_vterm in Hmemd; sp].
        subst. apply sub_find_some in Hs.
        apply in_sub_filter in Hs; repnd.
        apply in_combine in Hs0. repnd.
        apply in_map_iff in Hs0. exrepnd.
        subst. apply lin_lift_vterm in Hmemd.
        rwsimpl Hdis.
        disjoint_reasoningv.
        apply Hdis1 in Hmemd; auto.

     + rewrite remove_nvars_cons_r.
         rewrite memvar_dmemvar.
         cases_if_sum Hmemdin; auto.
         * provefalse.
           rewrite (@lin_lift_vterm NVar Opid) in Hmemd.
           rewrite <- lmap_apply_var in Hmemd.
           rewrite <- Heta0 in Hmemd.
           simpl in Hmemd.
           cases (sub_find (@sub_filter _ Opid (var_ren lvi lvo) lv) vnt) as Hs;
            [|rewrite <- lin_lift_vterm in Hmemd; sp; fail].
           subst. apply sub_find_some in Hs. apply in_sub_filter in Hs; repnd;
           apply in_combine in Hs0. repnd. sp.

         * simpl. f_equal. 
           apply (@vterm_inj _ Opid).
           do 2 rewrite <- lmap_apply_var.
           simpl. rewrite <- Heta0.
           rewrite sub_find_sub_filter_eta; auto.

     +  eauto using no_repeats_sub_filter.
     + rwsimpl Hdis. repeat (disjoint_reasoning).
       introv Hin Hc. eapply lin_lift_vterm in Hin.
       apply combine_in_right with (l1:=lvi0) in Hin;[| spcls; omega].
       exrepnd. unfold var_ren in Heta0.
       rewrite <- Heta0 in Hin0.
       apply in_sub_filter in Hin0. repnd.
       apply in_combine in Hin1. repnd.
       apply lin_lift_vterm in Hin1.
       apply Hdis0 in Hin1. sp.
Qed.


Theorem freevars_ssubst_allvars2:
   forall (t : NTerm) (lvi lvo: list NVar),
      length lvi= length lvo
      -> no_repeats lvo
       -> disjoint lvo (all_vars t)
       -> free_vars (ssubst t (var_ren lvi lvo) ) 
          = lvmap_lapply (combine lvi lvo) (free_vars t).
Proof using.
  clear gts.
  introv Hleq Hnr Hdis.
  rewrite ssubst_ssubst_aux_hide.
  unfold ssubsthide. cases_ifn Hd.
  Focus 2. allunfold (@var_ren NVar). spcls. spcls.
  provefalse. apply Hd. disjoint_reasoningv.
  apply freevars_ssubst_allvars9; trivial.
Qed.

(* Print Assumptions freevars_ssubst_allvars. *)


Lemma ssubst_aux_trivial5 :
  (forall t (sub : @Substitution Opid),
    disjoint (free_vars t) (dom_sub sub)
    -> ssubst_aux t sub = t)*
  (forall bt (sub : @Substitution Opid),
    disjoint (dom_sub sub) (free_vars_bterm bt)
    -> ssubst_bterm_aux bt sub = bt).
Proof using.
  apply NTerm_BTerm_ind.
  - intros n sub Hdis. simpl in *.
    disjoint_reasoningv.
    apply sub_find_none_if in Hdis.
    rewrite Hdis. refl.

  - intros ? ? Hind  ? Hdis. simpl in *. f_equal.
    rewrite <- map_id.
    apply eq_maps. intros bt Hin.
    apply Hind; auto. apply disjoint_sym in Hdis.
    eapply disjoint_flat_map_r; eauto.
  - intros ? ?  Hind ? Hdis. simpl.
    f_equal. simpl in *.
    apply Hind .
    rewrite <- dom_sub_sub_filter.
    apply disjoint_remove_nvars_l.
    disjoint_reasoning.
Qed.

Definition ssubst_aux_trivial_disj := fst ssubst_aux_trivial5.
Definition ssubst_bterm_aux_trivial_disj := snd ssubst_aux_trivial5.


(* TODO : delete because [ssubst_aux_trivial_disj] is stronger and easier to use *)
Lemma ssubst_aux_trivial3 :
  forall t (sub : @Substitution Opid),
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t) 
          # ! LIn v (free_vars t))
    -> ssubst_aux t sub = t.
Proof using.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    allunfold @isprogram; allunfold @closed; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply_in_hyp p; sp.
    apply not_over_or in p; sp.

  - Case "oterm". f_equal.
    induction lbt; simpl; auto.
    rw IHlbt; sp.
    + destruct a; simpl. f_equal.
      * f_equal. f_equal. eapply H; try(left); eauto.
        introv Hin. apply in_sub_filter in Hin. repnd.
        rename H0 into Hdis. apply Hdis in Hin0. repnd.
        rw disjoint_app_r in Hin1.
        rw disjoint_app_r in Hin1.
        repnd. split; auto.
        intro Hc. apply Hin0.
        apply in_app_iff.
        left. apply in_remove_nvars; sp.
    + rewrite H with (lv := lv); sp.
    + apply_in_hyp p; sp. allsimpl. 
        rw disjoint_app_r in p0. sp.
    + apply_in_hyp p; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
Qed.


Lemma ssubst_trivial3 :
  forall t (sub : @Substitution Opid),
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t) 
          # ! LIn v (free_vars t))
    -> ssubst t sub = t.
Proof using.
  introv HH. assert (disjoint_bv_sub t sub).
  introv Hin. apply HH in Hin. sp.
  change_to_ssubst_aux4.
  apply ssubst_aux_trivial3; try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.

Section TempTemp.

Notation ssubst := (@ssubst NVar _ _ _ _ Opid).

Lemma ssubst_trivial4 :
  forall t sub, disjoint (dom_sub sub) (free_vars t) 
    -> (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> ssubst t sub = t.
Proof using.
  introv Hdis Hfr.
  apply ssubst_trivial3.
  introv Hin.
  applydup_clear Hfr in Hin.
  sp. apply disjoint_sym in Hdis.
  apply Hdis in H.
  apply in_dom_sub in Hin. sp.
Qed.

Notation ssubst_aux := (@ssubst_aux NVar _ Opid).
Lemma ssubst_aux_trivial4 :
  forall t sub, disjoint (dom_sub sub) (free_vars t) 
    -> (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> ssubst_aux t sub = t.
Proof using.
  introv Hdis Hfr.
  apply ssubst_aux_trivial3.
  introv Hin.
  applydup_clear Hfr in Hin.
  sp. apply disjoint_sym in Hdis.
  apply Hdis in H.
  apply in_dom_sub in Hin. sp.
Qed.

Notation sub_filter := (@sub_filter _ Opid).

Lemma sub_filter_disjoint1:
  forall sub lf,
  disjoint (dom_sub sub) lf
  -> sub_filter sub lf
      = sub.
Proof using.
  induction sub as [|(v,t) sub Hind]; introv K; auto.
  simpl. allsimpl. apply disjoint_cons_l in K.
  rewrite memvar_dmemvar.
  cases_if; [clear H | ];sp.
  f_equal. auto.
Qed.



Lemma sub_filter_disjoint:
  forall lvi lvo lvf,
  length lvi = length lvo
  -> disjoint lvi lvf
  -> sub_filter (var_ren lvi lvo) lvf
      = var_ren lvi lvo.
Proof using.
  intros. apply sub_filter_disjoint1.
  unfold var_ren. rewrite dom_sub_combine. auto.
  rewrite map_length; auto; try omega.
Qed.

Notation var_ren := (@var_ren NVar Opid).


Lemma in_var_ren: forall lvi lvo u t,
  LIn (u, t) (var_ren lvi lvo)
  -> (LIn u lvi) # {v:NVar $ (t = vterm v) # (LIn v lvo)}.
Proof using.
  introv Hl.
  apply in_combine in Hl.
  repnd. apply in_map_iff in Hl.
  exrepnd.
  split; cpx.
  eexists; eauto.
Defined.

Notation vterm := (@vterm NVar Opid).

Lemma in_combine_vars_vterm: forall lvi lvo (u v: NVar) ,
  LIn (u,v) (combine lvi lvo) -> LIn (u, vterm v) (var_ren lvi lvo).
Proof using.
  introv X.   assert (injective_fun (fun x:NVar => x))  as Hi by (introv;auto).
  pose proof (tiff_fst (lin_combine_injective (fun x : NVar => x) vterm
    Hi vterm_inj _ _ _ _) X) as XX. rewrite map_id in XX.
    auto.
Qed.



Theorem disjoint_sub_filter_vars_l : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = var_ren lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint lvi ld 
   -> disjoint lvis ld.
Proof using.
  introv Hsf Hlen Hle1n Hdis. introv Hin.
  apply combine_in_left with (l2:=lvos) in Hin; auto.
  exrepnd. apply in_combine_vars_vterm in Hin0. rewrite <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply Hdis in Hin2. sp.
Qed.

Theorem disjoint_sub_filter_vars_r : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = var_ren lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint lvo ld 
   -> disjoint lvos ld.
Proof using.
  introv Hsf Hlen Hle1n Hdis. introv Hin.
  apply combine_in_right with (l1:=lvis) in Hin; auto.
  exrepnd. apply in_combine_vars_vterm in Hin0. rewrite <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply in_map_iff in  Hin1. exrepnd. inverts Hin3.
  apply Hdis in Hin1. sp.
  omega.
Qed.

Theorem disjoint_sub_filter_l : forall lvi lnt lvis lnts ld lv,
   sub_filter (combine lvi lnt) lv = combine lvis lnts
   -> length lvi =length lnt
   -> length lvis =length lnts
   -> disjoint lvi ld 
   -> disjoint lvis ld.
Proof using.
  introv Hsf Hlen Hle1n Hdis. introv Hin Hc.
  apply combine_in_left with (l2:=lnts) in Hin ; auto.
  exrepnd.
  rw <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply Hdis in Hin2. sp.
Qed.

Theorem disjoint_sub_filter_vars : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = var_ren lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint (lvi++lvo) ld 
   -> disjoint (lvis++lvos) ld.
Proof using.
  introv Hsf Hlen Hle1n Hdis. apply disjoint_app_l in Hdis. repnd.
  duplicate Hsf.
  apply disjoint_sub_filter_vars_l with (ld:=ld) in Hsf; auto.
  apply disjoint_sub_filter_vars_r with (ld:=ld) in Hsf0; auto.
  apply disjoint_app_l; auto.
Qed.

Notation dom_sub := (@dom_sub NVar Opid).

Lemma sub_find_first: forall sub v t,
  sub_find sub v= Some t
  -> {n: nat & (n < length sub) # nth n sub (v,t) =(v,t) # 
      not_in_prefix (dom_sub sub) v n}.
Proof using.
  introns K. rewrite (sub_lmap_find_first) in K.
  destruct (lmap_find_first deq_nvar sub v) as [s1s|n1n];
  exrepnd;  allsimpl; unfold  dom_sub in *; inverts K.
    exists n; sp.
Qed.

Notation sub_find := (@sub_find NVar _ Opid).


Lemma sub_find_some2_first:
  forall lv lnt1 lnt2 v t1 t2,
    length lv = length lnt1
    -> length lv = length lnt2
    -> sub_find (combine lv lnt1) v = Some t1
    -> sub_find (combine lv lnt2) v = Some t2
    -> {n:nat & n< length lv #
           nth n lv v= v # not_in_prefix lv v n
           # nth n lnt1 t1= t1 # nth n lnt2 t2= t2}.
Proof using.
  introv H1len H2len H1s H2s.
  apply sub_find_first in H1s.
  apply sub_find_first in H2s.
  exrepnd.
  rewrite_once combine_length.
  rewrite_once combine_length.
  rewrite_once dom_sub_combine; cpx.
  rewrite_once dom_sub_combine; cpx.
  rewrite_once combine_nth; cpx.
  rewrite_once combine_nth; cpx.
  rewrite_once min_eq; cpx.
  rewrite_once min_eq; cpx.
  assert (is_first_index lv v n) as H1isf by
   (unfolds_base;split;(try split);cpx; try(congruence)).
  assert (is_first_index lv v n0) as H2isf by
   (unfolds_base;split;(try split);cpx; try(congruence)).
  assert (n=n0) by (eapply is_first_index_unique; eauto).
  subst. rename n0 into n. GC.
  repeat (dpair_eq).
  exists n; dands; cpx; try congruence.
  rewrite H1s2l; auto.
  rewrite H1s2l; auto.
Qed.

Lemma sub_find_some_none_contra: forall lv lnt1 lnt2 v t1,
  length lv = length lnt1
  -> length lv = length lnt2
  -> sub_find (combine lv lnt1) v = Some t1
  -> sub_find (combine lv lnt2) v = None
  -> False.
Proof using.
  introv H1l H2n Hsfs Hsfn.
  apply sub_find_some in Hsfs. apply in_combine in Hsfs. repnd.
  apply sub_find_none2 in Hsfn. rewrite_once dom_sub_combine; sp.
Qed.





Lemma disjoint_free_vars_ssubst:
  forall (nt : NTerm) (sub : Substitution) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)
  -> disjoint (free_vars nt ++ (flat_map free_vars (range sub))) lvdr
  -> disjoint (free_vars (ssubst nt sub)) lvdr.
Proof using.
  introv H1dis H2dis.
  introv Hin Hc.
  apply free_vars_ssubst in Hin;
    [|unfold disjoint_bv_sub;rw disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- disjoint_sub_as_flat_map in H2dis.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.


Lemma disjoint_free_vars_ssubst_aux:
  forall (nt : NTerm) (sub : Substitution) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)
  -> disjoint (free_vars nt ++ (flat_map free_vars (range sub))) lvdr
  -> disjoint (free_vars (ssubst_aux nt sub)) lvdr.
Proof using.
  introv H1dis H2dis.
  introv Hin Hc.
  apply free_vars_ssubst_aux in Hin;
    [|unfold disjoint_bv_sub;rw disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- disjoint_sub_as_flat_map in H2dis.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.

Lemma boundvars_ssubst_aux_nb vv :
  (forall nt sub,
  LIn vv (bound_vars (ssubst_aux nt sub))
  -> LIn vv (bound_vars nt)[+]
      {v' : NVar $
      {t : NTerm $ sub_find sub v' =Some t # LIn v' (free_vars nt) # LIn vv (bound_vars t)}})
  *
  (forall bt sub,
  LIn vv (bound_vars_bterm (ssubst_bterm_aux bt sub))
  -> LIn vv (bound_vars_bterm bt)[+]
      {v' : NVar $
      {t : NTerm $ sub_find sub v' =Some t # LIn v' (free_vars_bterm bt) # LIn vv (bound_vars t)}})
  .
Proof using.
  apply NTerm_BTerm_ind.
  - simpl. intros v ? Hin. right. 
    dsub_find sn; cpx;[].
    exists v sns. split; auto.

  - simpl. intros _ ? Hind ? Hin.
    rewrite flat_map_map in Hin. 
    rw lin_flat_map in Hin. 
    destruct Hin as [bt Hin]. unfold compose in Hin.
    repnd.
    eapply Hind in Hin; eauto.
    repeat rewrite in_flat_map.
    setoid_rewrite in_flat_map. 
    dorn Hin;[left|exrepnd;right]; eexists; try eexists; try split; eauto.
  - simpl. intros ? ? Hind ? Hin. rewrite in_app_iff in *.
    dorn Hin;[ auto |].
    apply Hind in Hin; cpx.
    dorn Hin;[ auto | right].
    exrepnd. rw sub_find_sub_filter_some in Hin0.
    repnd. eexists; eauto. eexists; dands; eauto.
    apply in_remove_nvars. split; auto.
Qed.

    
Lemma boundvars_ssubst_aux :
  forall nt sub v,
  LIn v (bound_vars (ssubst_aux nt sub))
  -> LIn v (bound_vars nt)[+]
      {v' : NVar $
      {t : NTerm $ sub_find sub v' =Some t # LIn v' (free_vars nt) # LIn v (bound_vars t)}}.
Proof using.
  intros.
  apply boundvars_ssubst_aux_nb. auto.
Qed.

Definition boundvars_ssubst_bterm_aux :=
(fun vv => snd (boundvars_ssubst_aux_nb vv)).


Lemma boundvars_ssubst_aux_subset:
  forall nt sub,
  subset (bound_vars (ssubst_aux nt sub)) ((bound_vars nt) ++ flat_map bound_vars (range sub)).
Proof using.
  intros ? ? ? Hin.
  apply boundvars_ssubst_aux in Hin.
  apply in_app_iff. eauto.
  rewrite in_flat_map.
  dorn Hin;[left;tauto| right].
  exrepnd. apply sub_find_some, in_sub_eta in Hin0.
  repnd.
  eexists; split; eauto.
Qed.

Notation bound_vars := (@bound_vars NVar _ Opid).

Lemma boundvars_ssubst_bterm_aux_subset:
  forall bt sub,
  subset (bound_vars_bterm (ssubst_bterm_aux bt sub)) 
         ((bound_vars_bterm bt) ++ flat_map bound_vars (range sub)).
Proof using.
  intros ? ? ? Hin.
  apply boundvars_ssubst_bterm_aux in Hin.
  apply in_app_iff. eauto.
  rewrite in_flat_map.
  dorn Hin;[left;tauto| right].
  exrepnd. apply sub_find_some, in_sub_eta in Hin0.
  repnd.
  eexists; split; eauto.
Qed.

Lemma boundvars_ssubst:
  forall nt sub v,
  disjoint_bv_sub nt sub  
  -> LIn v (bound_vars (ssubst nt sub))
  -> LIn v (bound_vars nt)[+]
      {v' : NVar $
      {t : NTerm $ sub_find sub v' =Some t # LIn v' (free_vars nt) # LIn v (bound_vars t)}}.
Proof using.
  introv Hd. change_to_ssubst_aux8. intros. 
  apply boundvars_ssubst_aux;try(sp;fail).
Qed.


Lemma boundvars_ssubst_aux_vars:
  forall nt lvi lvo,
  length lvi = length lvo
  -> bound_vars (ssubst_aux nt (var_ren lvi lvo))
     = bound_vars nt.
Proof using.
  clear hdeq.
  nterm_ind1s nt as [v | o lbt Hind] Case; introv Hl; auto.
  - Case "vterm". simpl. rewrite sub_lmap_find. 
    destruct (lmap_find deq_nvar (var_ren lvi lvo) v) as [s1s| n1n];auto; exrepnd.
    allsimpl. apply in_var_ren in s1s0. exrepnd. subst. auto.
  - Case "oterm". simpl. rewrite flat_map_map.
    apply eq_flat_maps. intros bt Hin. destruct bt as [lv nt].
    unfold compose. simpl. 
    simpl. f_equal. pose proof (allvars_sub_filter lvi lvo lv) as X1X.
    apply get_sub_dom_vars_eta in X1X. exrepnd.
    rewrite X1X0. eapply Hind; eauto.
Qed.



Lemma boundvars_ssubst_vars:
  forall nt lvi lvo,
  length lvi = length lvo
  -> disjoint lvo (bound_vars nt)
  -> bound_vars (ssubst nt (var_ren lvi lvo))
     = bound_vars nt.
Proof using.
  intros. change_to_ssubst_aux4.
  apply boundvars_ssubst_aux_vars;try(sp;fail);
  try(rw disjoint_sub_as_flat_map;disjoint_reasoningv).
Qed.

Lemma boundvars_ssubst_vars2:
  forall nt sub,
  allvars_sub sub
  -> disjoint_bv_sub nt sub
  -> bound_vars (ssubst nt sub)
     = bound_vars nt.
Proof using.
  introv Ha Hd. change_to_ssubst_aux4.
  pose proof (get_sub_dom_vars_eta _ Ha) as XX.
  exrepnd. GC. revert Hd. intro Hd. allrw XX0.
  spcls.
  apply boundvars_ssubst_aux_vars;try(sp;fail).
Qed.

Lemma disjoint_bound_vars_ssubst:
  forall (nt : NTerm) (sub : Substitution) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)  
  -> disjoint (bound_vars nt ++ (flat_map bound_vars (range sub))) lvdr
  -> disjoint (bound_vars (ssubst nt sub)) lvdr.
Proof using.
  introv H1dis H2dis.
  introv Hin Hc.
  apply boundvars_ssubst in Hin;
    [|unfold disjoint_bv_sub;rw disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- disjoint_sub_as_flat_map in H2dis.
    apply sub_find_some in Hin0.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.
Lemma disjoint_bound_vars_ssubst_aux:
  forall (nt : NTerm) (sub : Substitution) lvdr,
  disjoint (bound_vars nt ++ (flat_map bound_vars (range sub))) lvdr
  -> disjoint (bound_vars (ssubst_aux nt sub)) lvdr.
Proof using.
  introv H2dis.
  introv Hin Hc.
  apply boundvars_ssubst_aux in Hin.
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- disjoint_sub_as_flat_map in H2dis.
    apply sub_find_some in Hin0.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.
  

(** 1 or less renaming subgoals. see ssubst_nest_swap2 for an example*)
Ltac almost_complete1 t :=
  ((t;fail) || (t;[])).

Ltac dis_almost_complete1 t :=
  try(almost_complete1 t);try (apply disjoint_sym; almost_complete1 t).

Hint Resolve prog_sub_implies_wf : slow.


Hint Resolve disjoint_sub_filter_r_flatmap2 : slow.
Hint Resolve disjoint_sym : slow.

Lemma disjoint_dom_sub_filt : forall sub lv, 
  disjoint (dom_sub (sub_filter sub lv)) lv.
Proof using. introv Hin Hinc.
  unfold dom_sub, ALDom in Hin.
  apply in_map_iff in Hin.
  exrepnd.
  allsimpl. subst.
  apply in_sub_filter in Hin1.
  repnd. sp.
Qed.

Lemma disjoint_dom_sub_filt2 : forall sub lv1 lvn,
  disjoint (dom_sub sub) lvn
  -> disjoint (dom_sub (sub_filter sub lv1)) lvn.
Proof using.
  introv Hdis Hin Hinc.
  unfold dom_sub, ALDom in Hin.
  apply in_map_iff in Hin.
  exrepnd.
  allsimpl. subst.
  apply in_sub_filter in Hin1.
  repnd. apply in_dom_sub in Hin0.
  disjoint_lin_contra.
Qed.

(** update it in substitution.v *)
Ltac disjoint_sub_filter :=
        let tac1:=(eapply disjoint_sub_filter_l;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_r_flatmap;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv;
 (
  let maintac := apply disjoint_sub_filter_r_flatmap2; disjoint_reasoningv in
  match goal with 
  |[ |- (disjoint (flat_map _ (range (sub_filter _ _ ))) _ )]
    =>  maintac
  |[ |- ( disjoint _ (flat_map _ (range (sub_filter _ _ ))))]
    => apply disjoint_sym; maintac
  | [ |- disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv ] 
      =>  apply disjoint_dom_sub_filt; fail
  | [ |- disjoint ?lv (dom_sub (sub_filter ?sub ?lv)) ] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt; fail
  | [ H : (disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv) |- _] 
      =>  clear H
  | [ H : ?lv (disjoint (dom_sub (sub_filter ?sub ?lv))) |- _] 
      =>  clear H
  | [ |- disjoint (dom_sub (sub_filter ?sub _)) _ ] 
      =>  apply disjoint_dom_sub_filt2; disjoint_reasoningv
  | [ |- disjoint _ (dom_sub (sub_filter ?sub _))] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt2; disjoint_reasoningv
    
  end
  ).

  Ltac disjoint_ssubst :=
  let maintacf := apply disjoint_free_vars_ssubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  let maintacb := apply disjoint_bound_vars_ssubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  match goal with 
  |[ |- disjoint (free_vars (ssubst_aux _ _ ))  _ ]
    => maintacf  
  |[ |- disjoint _ (free_vars (ssubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacf
  |[ |- disjoint (bound_vars (ssubst_aux _ _ ))  _ ]
    => maintacb  
  |[ |- disjoint _ (bound_vars (ssubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacb
  end.



Lemma ssubst_aux_nest_swap2: forall t (sub1 sub2:@Substitution Opid),
  let lvi1 := dom_sub sub1 in
  let lvi2 := dom_sub sub2 in
  let lnt1 := range sub1 in
  let lnt2 := range sub2 in
  disjoint lvi1 (flat_map free_vars lnt2) (**o/w capture will occur in RHS*)
  -> disjoint lvi2 (flat_map free_vars lnt1) (**o/w capture will occur in LHS*)
  -> disjoint lvi1 lvi2 (**o/w order will matter*)
  -> disjoint (flat_map bound_vars lnt1) (flat_map free_vars lnt2) (**o/w renaming will occur in LHS*)
  -> disjoint (flat_map bound_vars lnt2) (flat_map free_vars lnt1) (**o/w renaming will occur in RHS*)
  -> disjoint (bound_vars t) ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2)) (**o/w renaming will occur*)
  -> ssubst_aux(ssubst_aux t sub1) sub2 = ssubst_aux(ssubst_aux t sub2) sub1.
Proof using.
  nterm_ind1s t as [v| o lbt Hind] Case;
  introv H1dis H2dis H3dis H4dis H5dis Hdist; simpl;
  pose proof (sub_eta sub1) as Xsub1eta;
  pose proof (sub_eta sub2) as Xsub2eta;
  pose proof (sub_eta_length sub1) as Xlen1;
  pose proof (sub_eta_length sub2) as Xlen2;
  remember (dom_sub sub1) as lvi1;
  remember (dom_sub sub2) as lvi2;
  remember (range sub1) as lnt1;
  remember (range sub2) as lnt2.
  Case "vterm".

  - simpl. destructr (sub_find sub1 v) as  [s1|n1].
    + symmetry in HeqHdeq. applydup @sub_find_some in HeqHdeq.
      simpl. rw Xsub1eta in HeqHdeq0.
      apply in_combine in HeqHdeq0. repnd.
      assert (disjoint lvi1 lvi2) as XX by   disjoint_reasoningv.
      apply XX in HeqHdeq1.
      destructr (sub_find (combine lvi2 lnt2) v) as  [s2|n2];
      [ symmetry in HeqHdeq2; applydup @sub_find_some in HeqHdeq2;
        apply in_combine in HeqHdeq3; repnd; sp | ];[].
      simpl. rw Xsub2eta. rewrite <- HeqHdeq2. simpl. rw  HeqHdeq.
        rewrite ssubst_aux_trivial4; auto.
      * rewrite dom_sub_combine; sp. disjoint_reasoningv.
        GC. allsimpl. clear Hdist Hdist0.
        apply disjoint_sym in H2dis. rw disjoint_flat_map_l in H2dis.
        apply H2dis in HeqHdeq0. allsimpl. disjoint_reasoningv.
      * rw disjoint_sub_as_flat_map.
        try(rewrite dom_range_combine;try( congruence)).
        revert HeqHdeq0. clear HeqHdeq.
        revert s1. apply disjoint_flat_map_r.
        disjoint_reasoningv.
    + symmetry in HeqHdeq. rw Xsub2eta.
      destructr (sub_find (combine lvi2 lnt2) v) as  [s2|n2];simpl;
      [|rewrite HeqHdeq;rewrite <- HeqHdeq0; sp];[].
      simpl. rewrite <- HeqHdeq0.
      applysym @sub_find_some in HeqHdeq0.
      apply in_combine in HeqHdeq0. repnd.
      rewrite ssubst_aux_trivial4; auto.
      * rw <- Heqlvi1. revert HeqHdeq0. apply disjoint_flat_map_r.
        disjoint_reasoningv.
      * rw disjoint_sub_as_flat_map.
        rw <- Heqlnt1.
        revert HeqHdeq0. clear HeqHdeq.
        apply disjoint_flat_map_r.
        disjoint_reasoningv.
  - Case "oterm".
    simpl. f_equal. repeat(rewrite map_map). 
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    unfold compose.
    simpl.
    allsimpl. apply disjoint_sym in Hdist.
    eapply disjoint_lbt_bt2 in Hdist; eauto. repnd.
    apply disjoint_app_l in Hdist0. repnd.
    repeat (rewrite (bvar_renamings_subst_disjoint_bound_vars); [|
      apply disjoint_sub_as_flat_map;try (rewrite <-Heqlnt1);try (rewrite <-Heqlnt2); sp;
      disjoint_reasoning]).
    simpl.
    repeat (rewrite (bvar_renamings_subst_disjoint_bound_vars); [|
      apply disjoint_sub_as_flat_map;try (rewrite <-Heqlnt1);try (rewrite <-Heqlnt2); sp;
      disjoint_reasoningv]).
    simpl. f_equal. disjoint_reasoningv.
    erewrite Hind; eauto;[| | | | |];
    pose proof (sub_eta (sub_filter sub1 lv)) as Xsf1eta;
    pose proof (sub_eta (sub_filter sub2 lv)) as Xssf2eta;
    pose proof (sub_eta_length (sub_filter sub1 lv)) as X1len;
    pose proof (sub_eta_length (sub_filter sub2 lv)) as X2len;
    remember (dom_sub (sub_filter sub1 lv)) as lsvi1;
    remember (dom_sub (sub_filter sub2 lv)) as lsvi2;
    remember (range (sub_filter sub1 lv)) as lsnt1;
    remember (range (sub_filter sub2 lv)) as lsnt2;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;[| | | | |]; disjoint_reasoningv; disjoint_sub_filter.
Qed.

Lemma ssubst_nest_swap2: forall t (sub1 sub2 : @Substitution Opid),
  let lvi1 := dom_sub sub1 in
  let lvi2 := dom_sub sub2 in
  let lnt1 := range sub1 in
  let lnt2 := range sub2 in
  disjoint lvi1 (flat_map free_vars lnt2) (**o/w capture will occur in RHS*)
  -> disjoint lvi2 (flat_map free_vars lnt1) (**o/w capture will occur in LHS*)
  -> disjoint lvi1 lvi2 (**o/w order will matter*)
  -> disjoint (flat_map bound_vars lnt1) (flat_map free_vars lnt2) (**o/w renaming will occur in LHS*)
  -> disjoint (flat_map bound_vars lnt2) (flat_map free_vars lnt1) (**o/w renaming will occur in RHS*)
  -> disjoint (bound_vars t) ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2)) (**o/w renaming will occur*)
  -> ssubst(ssubst t sub1) sub2 = ssubst(ssubst t sub2) sub1.
Proof using.
  intros. change_to_ssubst_aux8.
  apply ssubst_aux_nest_swap2;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
  - rw <- ssubst_ssubst_aux;disjoint_reasoningv.
    apply disjoint_bound_vars_ssubst; disjoint_reasoningv.
  - rw <- ssubst_ssubst_aux;disjoint_reasoningv.
    apply disjoint_bound_vars_ssubst; disjoint_reasoningv.

Qed.




Lemma ssubst_nest_swap: forall t lvi1 lvo1 lvi2 lvo2,
  length lvi1=length lvo1
  -> length lvi2=length lvo2
  -> disjoint lvi1 lvi2 # disjoint lvi1 lvo2 # disjoint lvi2 lvo1
  -> disjoint (bound_vars t) (lvo1 ++ lvo2)
  -> let sub1:= var_ren lvi1 lvo1 in
       let sub2:= var_ren lvi2 lvo2 in
       ssubst(ssubst t sub1) sub2 = ssubst(ssubst t sub2) sub1.
Proof using.
  simpl.
  intros.
  unfold var_ren.
  apply ssubst_nest_swap2; spcls; disjoint_reasoningv.
Qed.

Lemma ssubst_aux_nest_swap: forall t lvi1 lvo1 lvi2 lvo2,
  length lvi1=length lvo1
  -> length lvi2=length lvo2
  -> disjoint lvi1 lvi2 # disjoint lvi1 lvo2 # disjoint lvi2 lvo1
  -> disjoint (bound_vars t) (lvo1 ++ lvo2)
  -> let sub1:= var_ren lvi1 lvo1 in
       let sub2:= var_ren lvi2 lvo2 in
       ssubst_aux(ssubst_aux t sub1) sub2 = ssubst_aux(ssubst_aux t sub2) sub1.
Proof using.
 simpl. intros. unfold var_ren. apply ssubst_aux_nest_swap2;spcls; disjoint_reasoningv.
Qed.



Lemma disjoint_bv_vars: forall t lvi lvo, 
  disjoint lvo (bound_vars t)
  -> disjoint_bv_sub t (var_ren lvi lvo).
Proof using.
  introv Hdis XX. apply in_var_ren in XX; exrepnd; subst.
  simpl. apply disjoint_cons_l. split;[sp|].
  apply Hdis; auto.
Qed.


Lemma wf_sub_vars : forall (lvi lvo : list NVar) ,wf_sub (var_ren lvi lvo).
Proof using.
  introv Hin. apply in_var_ren in Hin; exrepnd; subst.
  constructor.
Qed.

Definition filt_var_ren lvi lvo lv := sub_filter (var_ren lvi lvo) lv.


Lemma nth_var_ren_implies : forall lvi lvo v b vd bd n,
  nth n (var_ren lvi lvo) (vd, bd) = (v, b)
  -> length lvi = length lvo
  -> n < length lvi
  -> (nth n lvi v= v) 
      # {vsr : NVar $ (b= vterm vsr)
      # (nth n lvo vsr= vsr)}.
Proof using.
  introv X1X X2X X3X. unfold var_ren in X1X. 
  rewrite combine_nth in X1X;[| rewrite map_length]; auto.
  inversion X1X . pose proof (nth_in _ n ((map vterm lvo)) ) as XX. 
  rewrite map_length in XX. rewrite <- X2X in XX. lapply (XX bd); auto.
  intro Hin. apply in_map_iff in Hin. exrepnd.
  split; auto. 
  apply nth_indep; auto.
  exists a; auto. sp.
  assert (nth n (map vterm lvo) bd =nth n (map vterm lvo) (vterm a))  as XXX by
     (apply nth_indep; repeat(rewrite map_length); auto;congruence ).
  rewrite XXX in Hin0. rewrite map_nth in Hin0. inversion Hin0. rewrite H2. auto.
Qed.


Definition filt_combine lvi lnt lv := sub_filter (combine lvi lnt) lv.

Lemma ssubst_aux_nest_same_str :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map free_vars lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> ssubst_aux (ssubst_aux t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = ssubst_aux t (filt_combine lvi lnt lf).
Proof using.
  nterm_ind1s t as [v | o lbt Hind] Case;
  introv Hl1 Hl2 Hnr Hdisb Hdisf.
  Focus 2.
  Case "oterm". (**this part is easier!!*)
    allsimpl. f_equal. rewrite map_map. eapply eq_maps; eauto.
    intros bt Hinb. destruct bt as [lv nt].
    unfold compose.
    allsimpl. apply disjoint_app_r in Hdisb. repnd.
    rename Hdisb into Hdisl.
    rename Hdisb0 into Hdisb.
    eapply disjoint_lbt_bt2 in Hdisb; eauto. repnd.
    apply disjoint_app_l in Hdisb0. repnd.
    simpl. f_equal.
    unfold filt_var_ren. unfold filt_combine.
    repeat(rewrite <- sub_filter_app_r).
    eapply Hind; eauto;[disjoint_reasoningv|].
    rw disjoint_flat_map_r in Hdisf. apply Hdisf in Hinb.
    simpl in Hinb. rw <- @disjoint_remove_nvars_l in Hinb.
    apply remove_nvars_unchanged in Hdisb1.
    rewrite Hdisb1 in Hinb. trivial.


  Case "vterm".

  simpl. destructr (sub_find (filt_var_ren lvi lvio lf) v) as [s1st|n1n].
  - apply symmetry in HeqHdeq. rename HeqHdeq into s1s.
    apply sub_find_sub_filter_some in s1s. repnd.
    apply sub_find_first in s1s0. exrepnd.
    unfold var_ren in s1s1.
    rewrite dom_sub_combine in s1s1;
     [| rewrite map_length; congruence] .
    unfold var_ren in s1s0.
    rewrite length_combine_eq
    in s1s0;[| rewrite map_length]; auto. 
    apply nth_var_ren_implies in s1s2;auto. exrepnd. rename vsr into vio.
    simpl. rewrite s1s2. simpl.
    destructr (sub_find (filt_combine lvio lnt lf) vio) as [s2st|n2n].

    + apply symmetry in HeqHdeq. rename HeqHdeq into s2s.
      apply sub_find_sub_filter_some in s2s. repnd.
      apply sub_find_first in s2s0. exrepnd.
      unfold var_ren in s2s0. rewrite length_combine_eq
      in s2s0;spc.
      rw combine_nth in s2s2;spc. inverts s2s2 as s2s3 s2s4.
      simpl. rewrite <- Hl1 in s1s0.
     (** clear s2s1. it cannot rule out case when n>n0*) 
      pose proof (no_repeats_index_unique2
               _ _ _ _ _ _ Hnr s1s0 s2s0 s1s4 s2s3) as X99.
      destruct X99. GC.  clear s1s2. clear s1st.
      destructr (sub_find (filt_combine lvi lnt lf) v) as [s3st|n3n].
      * apply symmetry in HeqHdeq. rename HeqHdeq into s3s.
        apply sub_find_sub_filter_some in s3s. repnd.
        apply sub_find_first in s3s0. exrepnd.
        unfold var_ren in s3s0. rewrite length_combine_eq
        in s3s0;spc.
        rw combine_nth in s3s2;spc. inverts s3s2 as s3s3 s3s4.
        simpl.  rewrite  Hl1 in s1s0.
        fold dom_sub in *. 
        unfold var_ren in *. spcls. 
        assert (n0<n \/ n0=n \/ n<n0) as Htri by omega.
        (dorn Htri);[|(dorn Htri)];
          try (apply s1s1 in Htri); cpx;
          try (apply s3s1 in Htri); cpx.
        destruct Htri. GC. apply nth_select3 in s3s4;[| congruence].
        apply nth_select3 in s2s4; congruence.
      * rename HeqHdeq into n3n. symmetry in n3n. 
        apply sub_find_sub_filter_none in n3n. dorn n3n; [ |sp(**see s1s*)].
        apply sub_find_none2 in n3n.        
        clear s1s1. apply nth_in2 in s1s3;[| congruence]. unfold var_ren in *.
        simpl. spcls. sp.
    + rename HeqHdeq into n2n. symmetry in n2n.
      apply sub_find_sub_filter_none in n2n. dorn n2n.
      * apply sub_find_none2 in n2n. 
        apply nth_in2 in s1s4;[| congruence]. unfold var_ren in *.
        simpl. spcls. sp. 
      * apply nth_in2 in s1s4;[| congruence].
        assert (disjoint lvio lf) as X99 by disjoint_reasoningv.
        apply X99 in s1s4; sp.
  - apply disjoint_singleton_r in Hdisf. fold dom_sub in *.
    assert ((dom_sub (combine lvi lnt)) = lvi) as Xrw  by (spcls;sp).
    rename HeqHdeq into n1n. symmetry in n1n. 
    apply sub_find_sub_filter_none in n1n. 
    assert(sub_find (combine lvi lnt) v = None[+]LIn v lf) as X99.
     + dorn n1n;[left|right]; auto.
       apply sub_find_none2 in n1n. 
       unfold var_ren in n1n. rewrite dom_sub_combine in n1n
        ;[| rewrite map_length; congruence].
       rewrite <- Xrw in n1n. apply sub_find_none_iff in n1n. rewrite n1n.
       refl.
    + apply sub_find_sub_filter_none in X99. 
      unfold filt_combine. rewrite X99.
      assert ((dom_sub (combine lvio lnt)) = lvio) as X2rw by (spcls;sp).
      rewrite <- X2rw in Hdisf. apply sub_find_none_iff in Hdisf.
      simpl.
      assert(sub_find (combine lvio lnt) v = None[+]LIn v lf)
         as X98 by (left;sp).
      apply sub_find_sub_filter_none in X98.
      rewrite X98. refl.
Qed.

Lemma ssubst_nest_same_str :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map free_vars lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> ssubst (ssubst t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = ssubst t (filt_combine lvi lnt lf).
Proof using.
  intros. change_to_ssubst_aux8;
  try(apply ssubst_aux_nest_same_str;try(sp;fail));
  apply disjoint_sym;
    rw <- disjoint_sub_as_flat_map;
  try(apply sub_filter_sat).
  - rw disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw <- ssubst_ssubst_aux; disjoint_reasoningv.
    rw boundvars_ssubst_vars2; spcls; disjoint_reasoningv.
    + rw disjoint_sub_as_flat_map. spcls. sp.
    + apply allvars_sub_filter.
    + apply sub_filter_sat. rw disjoint_sub_as_flat_map.
      spcls. disjoint_reasoningv.
  - rw disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
Qed.

Lemma ssubst_nest_vars_same_str :
  forall t lvi lvio lvo lf,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> ssubst (ssubst t (filt_var_ren lvi lvio lf)) (filt_var_ren lvio lvo lf)
     = ssubst t (filt_var_ren lvi lvo lf).
Proof using.
    intros. apply ssubst_nest_same_str;spc; spcls;sp.
Qed.
  
Lemma ssubst_nest_same :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map free_vars lnt)) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> ssubst (ssubst t (var_ren lvi lvio)) (combine lvio lnt)
     = ssubst t (combine lvi lnt).
Proof using.
  intros.
  pose proof (sub_filter_nil_r (var_ren lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply ssubst_nest_same_str; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma ssubst_aux_nest_same :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map free_vars lnt)) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> ssubst_aux (ssubst_aux t (var_ren lvi lvio)) (combine lvio lnt)
     = ssubst_aux t (combine lvi lnt).
Proof using.
  intros.
  pose proof (sub_filter_nil_r (var_ren lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply ssubst_aux_nest_same_str; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma ssubst_nest_vars_same :
  forall t lvi lvio lvo,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> ssubst (ssubst t (var_ren lvi lvio)) (var_ren lvio lvo)
     = ssubst t (var_ren lvi lvo).
Proof using.
    intros. apply ssubst_nest_same;spc;spcls;sp.
Qed.

Lemma ssubst_aux_nest_vars_same :
  forall t lvi lvio lvo,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> ssubst_aux (ssubst_aux t (var_ren lvi lvio)) (var_ren lvio lvo)
     = ssubst_aux t (var_ren lvi lvo).
Proof using.
    intros. apply ssubst_aux_nest_same;spc;spcls;sp.
Qed.



Theorem free_vars_ssubst_aux2:
  forall nt sub,
     forall v,
         LIn v (free_vars (ssubst_aux nt sub))
         -> (LIn v (free_vars nt) # ! LIn v (dom_sub sub))
                [+] {v' : NVar
                     $ {t : NTerm
                     $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof using. nterm_ind1 nt as [vn | o lbt Hind] Case; introv Hin.
   Case "vterm". induction sub as [| (vs,ts) sub]. 
   - rw ssubst_aux_nil in Hin. left; split; auto; sp. 
   - destruct (eq_var_dec vn vs) as [? | Hneq];
      subst;simpl in Hin;
      ((rw <- beq_var_refl in Hin;auto) 
          || (rw not_eq_beq_var_false in Hin;auto)).
      + right. exists vs ts. sp; auto.
      + cases (sub_find sub vn) as Hf.
          * applydup @sub_find_some in Hf.
             right; exists vn n; split; auto. right;auto. simpl. split; auto.
          * left;split;auto. allsimpl;subst. introv Hc. dorn Hc; subst; sp.
            subst. apply sub_find_none2 in Hf. sp.
  - Case "oterm".
    simpl in Hin. rw lin_flat_map in Hin.
    destruct Hin as [bt' Hin]. repnd. apply in_map_iff in Hin0.
    destruct Hin0 as [bt Hin0]. repnd. subst. destruct bt as [lv nt].
    simpl in Hin.
    simpl in Hin. rw in_remove_nvars in Hin. repnd.
    apply Hind with (lv:=lv) in Hin0; auto.
    destruct Hin0 as [Hl | Hr].
    + left. simpl. repnd. split. 
       *  apply lin_flat_map. eexists; split; eauto. simpl.
          apply in_remove_nvars. split; auto.
       * introv Hc. apply Hl.
         rewrite <- dom_sub_sub_filter.
         apply in_remove_nvars. sp.
    + right. parallel vs Hr. parallel ts Hr. repnd. sp;auto.
      * rw @in_sub_filter in Hr0. repnd; auto.
      * simpl. apply lin_flat_map. eexists; split; eauto. simpl.
        apply in_remove_nvars. split; auto. rw @in_sub_filter in Hr0.
        repnd; auto.
Qed.

Theorem free_vars_ssubst2:
  forall nt sub,
    disjoint_bv_sub nt sub
    -> forall v,
         LIn v (free_vars (ssubst nt sub))
         -> (LIn v (free_vars nt) # ! LIn v (dom_sub sub))
                [+] {v' : NVar
                     $ {t : NTerm
                     $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof using.
  introns Hd. change_to_ssubst_aux4.
  apply free_vars_ssubst_aux2;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
  - rw <- ssubst_ssubst_aux;sp; disjoint_reasoning.
Qed.



Lemma ssubst_ssubst_aux2: forall t lvi lvo, 
  disjoint (bound_vars t) (lvo)
  -> length lvi = length lvo
  -> ssubst t (var_ren lvi lvo) = ssubst_aux t (var_ren lvi lvo).
Proof using.
  introv Hdis Hlen.
  rewrite ssubst_ssubst_aux_hide. unfold ssubsthide. rw flat_map_free_var_vars_range;sp.
  cases_if; sp.
Qed.


Ltac dlmap_find sn :=
match goal with
| [  |- context[lmap_find deq_nvar ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
| [  H:context[lmap_find deq_nvar ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
end.
  

Ltac dsub_find2 sn :=
match goal with
| [  |- context[sub_find ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  let H := get_last_hyp tt in
  let H' := fresh H "l" in
  (destruct sn as [sns |];
  symmetry in H;
  try (pose proof (sub_find_some _ _ _  H) as H');
  try (pose proof (sub_find_none2 _ _  H) as H'))
| [ H: context[sub_find ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  destruct sn as [sns |]
end.

Lemma prog_ssubst_aux_app : forall nt sub sub2,
  disjoint (free_vars (ssubst_aux nt sub)) (dom_sub sub2)
  -> disjoint_bv_sub nt sub
  -> prog_sub sub2
  -> ssubst_aux nt sub = ssubst_aux nt (sub++sub2).
Proof using.
  nterm_ind1 nt as [v | o lbt Hind] Case. introv.
  - simpl. dsub_find2 sv.
    symmetry in Heqsv. 
    + rw @sub_find_app. rw <- Heqsv;sp.
    + simpl. introv Hdis Hdbv Hprog. disjoint_reasoningv.
      dsub_find sa;sp. applysym @sub_find_some in 
      Heqsa.  apply in_dom_sub in Heqsa;sp.
      rewrite dom_sub_app in Heqsa.
      rw in_app_iff in Heqsa.
      cpx.
  - introv Hpr Hbv Hps. simpl. f_equal. apply eq_maps.
    intros bt Hin. destruct bt as [blv bnt].
    simpl. f_equal. rw @sub_filter_app.
    Hint Resolve sub_filter_sat.
    eapply Hind; unfold prog_sub, disjoint_bv_sub in *; eauto.
    + allsimpl. 
      apply lin_lift with (f:=fun t : BTerm => ssubst_bterm_aux t sub) in Hin.
    eapply disjoint_flat_map_l in Hpr; eauto;[].
      allsimpl. apply disjoint_remove_nvars_l in Hpr.
      rw @dom_sub_sub_filter in Hpr. sp.
    + apply sub_filter_sat. sp.
      eapply sub_range_sat_implies; eauto.
      introv Hdis. allsimpl.
      eapply disjoint_flat_map_r in Hdis; eauto.
      allsimpl. disjoint_reasoningv.
Qed.

Lemma range_app: forall (s1 s2 : @Substitution Opid), range (s1++s2) =
  (range s1) ++ (range s2).
Proof using.
  introv. unfold range. rw map_app.
  sp.
Qed.

Lemma sub_keep_first_sat :  forall P sub lv,
  sub_range_sat  sub P
  -> sub_range_sat (sub_keep_first sub lv) P.
Proof using. introv Hall hsub. apply in_sub_keep_first in hsub. repnd.
  apply sub_find_some in hsub0. apply Hall in hsub0; auto.
Qed.


Theorem sub_keep_first_nest:
  forall  sub vs1 vs2,
    (forall v, LIn v vs2 -> LIn v vs1 [+] ! LIn v (dom_sub sub))
    -> sub_keep_first (sub_keep_first sub vs1) vs2 =sub_keep_first sub vs2.
Proof using.
  induction sub as [| (hv,ht) sub Hind]; introv Hin; [reflexivity | allsimpl].
  simpl. allrw @memvar_dmemvar. 
  cases_ifd h1v; simpl; repeat (rw @memvar_dmemvar); cases_ifd h2v;
  repeat (rw @memvar_dmemvar); try(cases_ifd h3v);cpx.
  - f_equal. rw Hind;try(spc;fail).  introv H2in.
    allrw @in_remove_nvars. repnd. apply Hin in H2in0.
    dorn H2in0;[left;split|right];cpx.   
  - rw Hind;try(spc;fail).  introv H2in.
    allrw @in_remove_nvars. repnd. applydup Hin in H2in.
    dorn H2in0;[left;split|right];cpx;[].
    simpl. introv Hc; dorn Hc; subst; sp.
  - provefalse. apply Hin in h2vt. dorn h2vt;sp. 
  - rw Hind;try(spc;fail).  introv H2in.
    allrw in_remove_nvars. repnd. applydup Hin in H2in.
    dorn H2in0;[left|right];cpx.
Qed.


(** w/o the hypothesis, this does not hold for ssubst
    might occur only in RHS. if it happens in both,
    the new variables might be different as
    RHS has to avoid more variables.
    w/o hypothesis, we can prove alpha equality *)
Lemma ssubst_aux_trim :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> ssubst_aux t sub = ssubst_aux t (sub_keep_first sub (free_vars t)).
Proof using.
  nterm_ind1 t as [v| o lbt Hind] Case;  introv Hdis.
  - Case "vterm". simpl.
    dsub_find2 ds.
    + apply sub_keep_first_singleton_r_some in Heqds.
      rw Heqds. simpl. rw @beq_deq. cases_if; sp.
    + apply sub_keep_first_singleton_r_none in Heqds.
      rw Heqds; sp.

  - Case "oterm". simpl.  f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    simpl.
    f_equal.
    rw <- sub_keep_first_sub_filter.
    symmetry.
    rewrite Hind with (lv := lv); eauto;
    [ |
        apply sub_keep_first_sat;
        apply sub_filter_sat;
        disjoint_flat; sp;fail].

       assert( (sub_keep_first (sub_keep_first (sub_filter sub lv) 
        (flat_map free_vars_bterm lbt)) (free_vars nt)) =
           sub_keep_first (sub_filter sub lv) (free_vars nt)) as Hskeq. 
       + apply sub_keep_first_nest. introv Hinf. destruct (in_nvar_list_dec v lv). 
          * right. rw <- @dom_sub_sub_filter. intro HC. apply in_remove_nvars in HC. sp. 
          * left. apply lin_flat_map. eexists; split; eauto. 
                    simpl. apply in_remove_nvars; split; trivial.  
       + rw Hskeq. 
           symmetry. eapply Hind; eauto. 
           apply sub_filter_sat. disjoint_flat. disjoint_reasoning.
Qed.


Lemma in_sub_keep_first_app:
  forall lv1 lv2 sub v u,
  LIn (v,u) (sub_keep_first sub (lv1++lv2))
  -> LIn (v,u) (sub_keep_first sub lv1) [+]
     LIn (v,u) (sub_keep_first sub lv2). 
Proof using. introv Hin.
  apply in_sub_keep_first in Hin.
  repnd.
  apply in_app_iff in Hin. dorn Hin;[left|right];
  apply in_sub_keep_first;sp.
Qed.

Ltac ssubst_ssubst_aux_eq H :=
match goal with
| [ |- context[ssubst ?t ?sub]] =>
  assert (ssubst t sub = ssubst_aux t sub) as H;
  [change_to_ssubst_aux4; sp ;fail | rw H]
end.

Ltac ssubst_ssubst_aux_eq_hyp H Hyp :=
let T := type of Hyp in 
match T with
|  context[ssubst ?t ?sub] => 
  assert (ssubst t sub = ssubst_aux t sub) as H;
  [change_to_ssubst_aux4; sp  | rewrite H in Hyp ]
end.

Lemma disjoint_sym_eauto: forall (T : [univ]) (l1 l2 : list T),
       disjoint l1 l2 -> disjoint l2 l1.
Proof using.
  introv. apply disjoint_sym; auto.
Qed.

Fixpoint sub_range_rel  (R : bin_rel NTerm) (subl subr : Substitution) : [univ] :=
match (subl, subr) with 
| ([],[]) => True
| ((vl,tl) :: sl , (vr,tr) :: sr) => (vl=vr # R tl tr # sub_range_rel R sl sr)
| ( _ , _) => False
end.


Lemma sub_range_rel_app : forall R subl1 subl2 subr1 subr2,
  (sub_range_rel  R subl1 subl2 # sub_range_rel  R subr1 subr2)
  ->   sub_range_rel R (subl1 ++ subr1)  (subl2 ++ subr2).
Proof using.
  induction subl1 as [|(v1,t1) subl1 Hind]; introv Hsr;
  destruct subl2 as [|(v2,t2) subl2]; inverts Hsr; allsimpl;sp.
Qed.

  
Lemma sub_range_refl : forall R,
  refl_rel R -> refl_rel (sub_range_rel R).
Proof using.
  introv Hr. unfold refl_rel in Hr. unfold refl_rel.
  induction x as [|(v1,t1) subl1 Hind];  allsimpl;sp.
Qed.

Lemma sub_range_sat_nil : forall (P: NTerm -> Prop), sub_range_sat [] P.
Proof using.
  unfold sub_range_sat. introv HH.
  inverts HH.
Qed.

Hint Resolve disjoint_sym_eauto disjoint_flat_map_r : slow.


Lemma le_sub_range_rel : forall R1 R2, le_bin_rel R1 R2
  -> le_bin_rel (sub_range_rel R1) (sub_range_rel R2).
Proof using.
  introv Hl. unfold le_bin_rel; induction a as [| (va,ta) suba Hind];
  intros subb Hs1; destruct subb as [| (vb,tb) subb]; simpl; invertsn Hs1;
  auto;[]; repnud Hl; dands; auto.
Qed.


Lemma le_binrel_sub_un : forall R Rul Rur,
   le_bin_rel R (indep_bin_rel Rul Rur) 
   -> le_bin_rel (sub_range_rel R) 
    (indep_bin_rel (fun s => sub_range_sat s Rul) (fun s => sub_range_sat s Rur)).
Proof using.
  introv Hle.
   unfold le_bin_rel, indep_bin_rel; induction a as [| (va,ta) suba Hind];
  intros subb Hs1; destruct subb as [| (vb,tb) subb]; dands; dands; 
  introv Hin; try(invertsn Hin); repnud Hle; allsimpl;
  unfold indep_bin_rel in Hle;cpx; subst;
  try(apply Hle in r); repnd; auto;
  try (apply Hind in Hs1);
  try (apply Hind in H3);
  repnd; eauto;  unfold sub_range_sat in * ; eauto;
  apply Hle in H2; repnd; eauto.
Qed.


Lemma isprogram_ssubst3 :
  forall t : NTerm,
  forall sub : Substitution,
    isprogram t
    -> prog_sub sub
    -> isprogram (ssubst t sub).
Proof using.
  introv Hpr Hps. destruct Hpr.
  apply @isprogram_ssubst; eauto with slow; [].
  rewrite H.
  simpl. tauto.
Qed.

Lemma sub_filter_pair_dom : forall lvf R lvi lnta lntb,
  length lvi = length lnta
  ->  length lvi = length lntb
  -> bin_rel_nterm R lnta lntb
  ->  {lvi' : list NVar $ { lnta', lntb' : list NTerm $ sub_filter (combine lvi lnta) lvf = combine lvi' lnta'
                            # sub_filter (combine lvi lntb) lvf = combine lvi' lntb'
                            # length lvi' = length lnta'
                            # length lvi' = length lntb'
                            # bin_rel_nterm R lnta' lntb'
                                   (** pairwise relationships are preserved *)
                                                                                 } }.
Proof using.
  induction lvi as [| v lvi Hind]; introns Hl.
  - repeat apply ex_intro with (x:=nil). dands; spc. apply binrel_list_nil.
  - simpl. destruct lnta as [|ha lnta];invertsn Hl;
     destruct lntb as [| hb  lntb];invertsn Hl0;  allsimpl.
    rw @memvar_dmemvar. rw @memvar_dmemvar. 
    apply binrel_list_cons in Hl1. repnd. duplicate Hl0.
    cases_ifd Ha; eapply Hind with (lnta := lnta) in Hl0 ; eauto;[].
    exrepnd. exists (v::lvi') (ha :: lnta') (hb :: lntb').
    allsimpl. dands; spc; try (f_equal;spc).
    apply binrel_list_cons; sp.
Qed.

Lemma ssubst_bterm_trivial : forall bt sub,
  isprogram_bt bt
  -> prog_sub sub
  -> @ssubst_bterm_aux NVar _ Opid bt sub = bt.
Proof using.
  introv Hpr Hps.
  destruct bt as [lv nt].
  simpl. f_equal.
  rw @ssubst_aux_trivial. sp.
  introv Hin.
  apply in_sub_filter in Hin.
  repnd.
  apply Hps in Hin0.
  split; auto;[].
  repnud Hpr.
  invertsn Hpr0.
  rw @nil_remove_nvars_iff in Hpr0.
  spc.
Qed.


Ltac disjoint_flat3 := allunfold @disjoint_bv_sub; allunfold @sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn _ ?tl), H2 : (disjoint _ (flat_map _ ?tl))  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_r _ _ _ _ _)) H2) in H; hide_hyp H
|[ H: (LIn _ ?tl), H2 : (disjoint (flat_map _ ?tl) _)  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_l _ _ _ _ _)) H2) in H; hide_hyp H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.

Ltac fold_ssubst_ot :=
match goal with
[ |- context [ (oterm ?o (map (fun _ : BTerm => ssubst_bterm_aux _ ?sub) ?lbt))]]
  => let Hf := fresh "xxx" in
      let ts := eval simpl in (ssubst_aux (oterm o lbt) sub)  in
        assert (ts = ssubst_aux (oterm o lbt) sub) as Hf by refl;
        rewrite Hf; clear Hf
  end.

Ltac prove_sub_range_sat := 
  let Hin := fresh "Hin" in 
  introv Hin; simpl in Hin;
   repeat(dorn Hin;auto); try(inverts Hin); subst;auto.

Ltac ssubst_aux_ot_eq Hyp := let T := type of Hyp in
  let Hf := fresh Hyp "lseq" in
  match T with 
    context [ ssubst_aux (oterm ?o ?lbt) ?sub] =>
      let ts := eval simpl in (ssubst_aux (oterm o lbt) sub)  in
        assert (ts = ssubst_aux (oterm o lbt) sub) as Hf by refl 
  end.
Lemma ssubst_app_swap : forall t sub1 sub2,
  prog_sub sub1
  -> prog_sub sub2
  -> disjoint (dom_sub sub1) (dom_sub sub2)
  -> ssubst t (sub1++sub2) = ssubst t (sub2++sub1).
Proof using.
  introv H1p H2p Hdis.
  pose proof (sub_app_sat _ _ _ H1p H2p).
  pose proof (sub_app_sat _ _ _ H2p H1p).
  change_to_ssubst_aux4;[].
  pose proof (ssubst_aux_shift t sub1 sub2 []).
  simpl_vlist.
  eauto.
Qed.


Lemma ssubst_ssubst_aux_prog_sub : forall t sub,
  prog_sub sub
  -> ssubst t sub = ssubst_aux t sub.
Proof using.
  introv Hpr. change_to_ssubst_aux4. sp.
Qed.
Ltac fold_ssubst_subh Hyp := let T := type of Hyp in
match T with
  | [(?v1 ,ssubst ?t1 ?sub)] => fold (ssubst_sub [v1,t1] sub)
end.

Ltac fold_ssubst_sub :=
match goal with
| [ |- context [ [(?v1 ,ssubst ?t1 ?sub), (?v2 ,ssubst ?t2 ?sub)] ] ] => fold (ssubst_sub [(v1,t1),(v2,t2)] sub)
| [ |- context [ [(?v1 ,ssubst ?t1 ?sub)] ] ] => fold (ssubst_sub [(v1,t1)] sub)
end.

Lemma ssubst_bterm_aux_trim: forall lvf o lbt,
  disjoint  (free_vars (oterm o lbt)) lvf
  -> forall sub bt,
    disjoint_bv_sub (oterm o lbt) sub
    -> LIn bt lbt
    -> ssubst_bterm_aux bt sub = ssubst_bterm_aux bt (sub_filter sub lvf).
Proof using.
  introv Hdis Hbv Hin.
  destruct bt as [lv nt].
  simpl. f_equal.
  rw sub_filter_swap.
  rw <- @sub_filter_app_r.
  rw sub_filter_app_as_remove_nvars.
  rw @sub_filter_app_r.
  rewrite <- ssubst_aux_sub_filter2 with (l:= (remove_nvars lv lvf));sp.
  simpl in Hdis. clear Hbv. eapply disjoint_flat_map_l in Hdis;eauto.
    allsimpl. apply disjoint_remove_nvars_l in Hdis;sp.
Qed.
  

Lemma ssubst_bterm_aux_trivial : forall bt,
  @ssubst_bterm_aux NVar _ Opid bt [] = bt.
Proof using.
  introv. destruct bt.
  simpl. f_equal. 
  apply ssubst_aux_nil.
Qed.

Lemma closed_sub :
  forall (sub : @Substitution Opid),
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> flat_map free_vars (range sub) = [].
Proof using.
  induction sub as [| (v,t) sub]; allsimpl; introns Hh; sp. 
  generalize (Hh v t (or_introl eq_refl)); sp.
  unfold isprogram, closed in *. repnd. rewrite H0.
  rw IHsub; allsimpl;[sp|].
  intros vv tt Hin. generalize (Hh vv tt);  tauto.
Qed.

Lemma disjoint_sub_if_program :
  forall (sub : @Substitution Opid),
    (forall (v : NVar) (t : NTerm),
       LIn (v, t) sub -> isprogram t)
    -> forall t, disjoint (bound_vars t) (flat_map free_vars (range sub)).
Proof using.
  intros.
  generalize (closed_sub sub); sp.
  rw H0; sp.
Qed.

Lemma ssubst_ssubst_aux_prog :
  forall t sub,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> ssubst t sub = ssubst_aux t sub.
Proof using.
  intros.
  apply ssubst_ssubst_aux.
  apply disjoint_sub_if_program; sp.
Qed.


Lemma fold_subst :
  forall t v u, ssubst t [(v,u)] = subst t v u.
Proof using. auto. Qed.

Lemma simple_ssubst_cons :
  forall t v u sub,
    isprogram u
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> ssubst (subst t v u) sub = ssubst t ((v, u) :: sub).
Proof using.
  intros.
  unfold subst.
  rw simple_ssubst_app; simpl; sp; cpx.
Qed.


Lemma sub_range_sat_cons: forall h t (P : NTerm-> Prop),
  sub_range_sat (h::t) P  <=> (P (snd h) # sub_range_sat t P).
Proof using.
  intros. rw cons_as_app. rw <- sub_app_sat_iff.
  split; introv HH; repnd; dands; unfold sub_range_sat in *;
     allsimpl; eauto;[].
  introv Hin; in_reasoning. cpx. cpx.
Qed.




Ltac simpl_sub5 :=
(match goal with
| [ H : (prog_sub _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
| [ H : (forall _ _, LIn (_, _) _  -> isprogram _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
end).

Lemma ssubst_nest_progs_swap:
  forall (t : NTerm) (sub1 sub2 : Substitution),
  prog_sub sub1 ->
  prog_sub sub2 ->
  disjoint (dom_sub sub1) (dom_sub sub2) ->
  (ssubst (ssubst t sub1) sub2) = (ssubst (ssubst t sub2) sub1).
Proof using.
  introv H1p H2p Hdis.
  change_to_ssubst_aux8.
  apply ssubst_aux_nest_swap2; spcls; repeat(simpl_sub5); auto;
  rewrite (prog_sub_flatmap_range _ H1p); spcls; auto.
Qed.

Lemma ssubst_nest_progs_swap_single:
  forall (t st: NTerm) (sub : Substitution) (v: NVar),
  prog_sub sub ->
  isprogram st ->
  disjoint (dom_sub sub) [v] ->
  (ssubst (ssubst t sub) [(v,st)]) = (ssubst (ssubst t [(v,st)]) sub).
Proof using.
  intros. apply ssubst_nest_progs_swap; auto.
  prove_sub_range_sat.
Qed.


Lemma simple_ssubst_cons2 :
  forall t v u sub,
    prog_sub ((v, u) :: sub)
    -> ssubst (subst t v u) sub = ssubst t ((v, u) :: sub).
Proof using.
  introv Hps.
  rw cons_as_app in Hps.
  apply sub_app_sat_if in Hps.
  repnd. unfold subst.
  rw simple_ssubst_app; simpl; auto.
Qed.

Lemma simple_ssubst_cons3 :
  forall t v u sub,
    prog_sub ((v, u) :: sub)
    -> (!LIn v (dom_sub sub))
    -> subst  (ssubst t sub) v u = ssubst t ((v, u) :: sub).
Proof using.
  introv Hps Hd.
  rw cons_as_app in Hps.
  apply sub_app_sat_if in Hps.
  repnd.
  rw ssubst_swap; auto;
    [ |repnud Hps0; eapply Hps0; left; eauto].
  rw snoc_as_append.
  rw <- simple_ssubst_app; simpl; auto.
Qed.


Lemma eqsetv_sub_keep_first :
  forall sub la lb,
    eq_set la lb
    -> (sub_keep_first sub la) = (sub_keep_first sub lb).
Proof using.
  induction sub as [| (v,t) sub Hind]; introv Heq;auto.
  simpl. duplicate Heq. rw (@eqsetv_prop NVar) in Heq.
  rw @memvar_dmemvar.
  rw @memvar_dmemvar.
  dtiffs2.
  cases_if; cases_if; try (provefalse; eauto;fail); erewrite Hind; eauto 2 with eqsetv.
Qed.

Lemma in_range_iff :
  forall (t : NTerm) (sub : Substitution),
    LIn t (range sub) <=> {v : NVar $ LIn (v, t) sub}.
Proof using.
  clear gts varclass varcl freshv deqnvar VarClass.
  induction sub; simpl; split; intro k; sp; allsimpl; subst; discover; sp; cpx;
     eauto.
  apply IHsub in H. sp. exists v; sp. firstorder.
Qed.

Lemma prog_sub_cons :
  forall sub v t,
    prog_sub ((v,t) :: sub) <=> (isprogram t # prog_sub sub).
Proof using.
  introv.
  unfold prog_sub, sub_range_sat; simpl; split; intro k; sp; cpx; discover; sp; cpx;
     eauto.
Qed.

Lemma simple_ssubst_snoc :
  forall t v u sub,
    isprogram u
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> subst (ssubst t sub) v u = ssubst t (snoc sub (v,u)).
Proof using.
  intros.
  unfold subst.
  rw simple_ssubst_app; simpl; sp; cpx.
  rw snoc_as_append; sp.
Qed.


Lemma allvars_ssubst_aux :
  forall nt sub v,
  LIn v (all_vars (ssubst_aux nt sub))
  -> LIn v (all_vars nt)[+]
      {v' : NVar $
      {t : NTerm $ LIn (v', t) sub # LIn v' (free_vars nt) # LIn v (all_vars t)}}.
Proof using varclass varcl gts freshv VarClass.
  intros ? ? ? Hin.
  apply in_app_or in Hin.
  dorn Hin.
- apply free_vars_ssubst_aux2 in Hin.
  unfold all_vars. rewrite in_app_iff.
  setoid_rewrite in_app_iff. 
  dorn Hin;[left | right]; exrepnd; firstorder.
- apply boundvars_ssubst_aux in Hin.
  unfold all_vars. rewrite in_app_iff.
  setoid_rewrite in_app_iff. 
  dorn Hin;[left | right]; exrepnd; try tauto.
  apply sub_find_some in Hin0. eexists; eexists; eauto.
Qed.

(*

Lemma ssubst_aux_app_sub_filter :
  forall s1 s2 t,
    prog_sub s1
    -> prog_sub s2
    -> ssubst t (s1 ++ s2)
       = ssubst t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof using.
  induction s1; simpl; introv ps1 ps2.
  rw sub_filter_nil_r; sp.
  destruct a as [v u]; allsimpl.
  allrw prog_sub_cons; repnd.
  repeat (rw <- simple_ssubst_cons);
    try (complete sp);
    try (complete (introv i; allrw in_app_iff; sp; allrw <- prog_sub_eq;
                   allrw in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
                   try (complete (apply ps1; rw in_range_iff; exists v0; sp));
                   try (complete (apply ps2; rw in_range_iff; exists v0; sp)))).

  rw IHs1; sp.

  generalize (ssubst_sub_filter (subst t v u) (s1 ++ sub_filter s2 (dom_sub s1)) [v]);
    intro eq1.
  dest_imp eq1 hyp.
  introv i; allrw in_app_iff; sp; allrw <- prog_sub_eq;
  allrw in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
  try (complete (apply ps1; rw in_range_iff; exists v0; sp));
  try (complete (apply ps2; rw in_range_iff; exists v0; sp)).
  dest_imp eq1 hyp.
  unfold subst. rw isprogram_ssubst2.
 Local Opaque remove_nvars.
   simpl.
  rewrite disjoint_remove_nvars_l; rewrite remove_nvars_eq; sp.
  introv k; sp; cpx.

  generalize (ssubst_sub_filter (subst t v u) (s1 ++ sub_filter s2 (v :: dom_sub s1)) [v]);
    intro eq2.
  dest_imp eq2 hyp; apply in_single_iff in k; inverts k.
  introv i; allrw in_app_iff; sp; allrw <- prog_sub_eq;
  allrw in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
  try (complete (apply ps1; rw in_range_iff; exists v0; sp));
  try (complete (apply ps2; rw in_range_iff; exists v0; sp)).
  dest_imp eq2 hyp.
  unfold subst; rw isprogram_ssubst2; simpl.
  rw disjoint_remove_nvars_l; rw remove_nvars_eq; sp.
  introv kl; sp; cpx.

  allrw sub_filter_app; simpl.
  allrw <- sub_filter_app_r.

  assert (sub_filter s2 (dom_sub s1 ++ [v]) = sub_filter s2 ((v :: dom_sub s1) ++ [v]))
         as eq; try (complete (rw eq; sp)).
  symmetry.
  rewrite sub_filter_app_as_remove_nvars; simpl.
  rw remove_nvars_cons_r; boolvar; try (complete (allrw not_over_or; sp)).
  rw remove_nvars_nil_r; rw app_nil_r.
  rw cons_as_app.
  allrw sub_filter_app_r.
  rewrite sub_filter_swap; sp.
  
  rewrite eq. simpl. sp.
Qed.
*)

Lemma prog_sub_sub_filter :
  forall s vs, prog_sub s -> prog_sub (sub_filter s vs).
Proof using.
  introv ps.
  unfold prog_sub,sub_range_sat in *.
  introv i.
  apply in_sub_filter in i; repnd; discover; sp.
  eauto.
Qed.

Lemma prog_sub_snoc :
  forall s v t,
    prog_sub (snoc s (v,t)) <=> (prog_sub s # isprogram t).
Proof using.
  clear  varclass varcl freshv deqnvar VarClass.
  introv.
  unfold prog_sub, sub_range_sat; split; intro k.

  dands.
  introv i.
  generalize (k v0 t0); intro j; allrw in_snoc; sp.
  generalize (k v t); intro j; allrw in_snoc; sp.

  repnd.
  introv i; allrw in_snoc; sp; cpx; discover; sp; firstorder.
Qed.



Lemma sub_find_some_app2 :
  forall v t (sub1 sub2 : @Substitution Opid),
    !LIn v (dom_sub sub1)
    -> sub_find sub2 v = Some t
    -> sub_find (sub1 ++ sub2) v = Some t.
Proof using.
  introv niv sf.
  rw @sub_find_app.
  rw <- @sub_find_none_iff in niv.
  rw @niv; sp.
Qed.

Lemma subset_free_vars_sub_aux_app2 :
  forall t sub1 sub2,
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> isprogram t)
    -> disjoint (free_vars t) (dom_sub sub1)
    -> ssubst_aux t (sub1 ++ sub2) = ssubst_aux t sub2.
Proof using.
  nterm_ind t Case; simpl; introv k d.

  - Case "vterm".
    allrw disjoint_singleton_l; sp.
    remember (sub_find sub2 n); destruct o; symmetry in Heqo.
    apply sub_find_some_app2 with (sub1 := sub1) in Heqo; auto.
    rw Heqo; auto.
    rw @sub_find_none_iff in Heqo.
    assert (!LIn n (dom_sub (sub1 ++ sub2))) as nin
      by (rewrite dom_sub_app; rw in_app_iff; intro; sp).
    rw <- @sub_find_none_iff in nin.
    rw nin; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.
    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (sp; apply X with (v := v); rw in_app_iff; sp).
    rw @sub_filter_app.

    rewrite H with (lv := l); sp.
    apply k with (v := v).
    allrw @in_app_iff.
    allrw @in_sub_filter; sp.
    allrw @disjoint_flat_map_l.
    apply_in_hyp p.
    allsimpl.
    rw @disjoint_remove_nvars_l in p.
    rw <- @dom_sub_sub_filter; auto.
Qed.

Lemma subset_free_vars_sub_app2 :
  forall t (sub1 sub2 : @Substitution Opid),
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> isprogram t)
    -> disjoint (free_vars t) (dom_sub sub1)
    -> ssubst t (sub1 ++ sub2) = ssubst t sub2.
Proof using.
  introv Hpr.
  applydup (@sub_app_sat_if NVar Opid  isprogram) in Hpr.
  repnd.
  change_to_ssubst_aux4.
  apply subset_free_vars_sub_aux_app2; sp.
Qed.





Require Import Morphisms.

Global Instance sub_filter_proper :
  Proper (eq ==> eq_set ==> eq) sub_filter.
Proof using.
  intros ? sub ? l1 l2 Heq.
  subst. revert Heq.
  clear. intros.
  induction sub; auto;[].
  simpl.
  destruct a. unfold memvar.
  rewrite Heq.
  rewrite IHsub.
  refl.
Qed.

Lemma map_ssubst_aux: forall (ws: list NTerm) sub,
disjoint (flat_map free_vars ws) (dom_sub sub)
-> map (fun x : NTerm => bterm [] (ssubst_aux x sub)) ws = map (bterm []) ws.
Proof using.
  intros ? ? Hf.
  apply eq_maps.
  intros ? Hin.
  f_equal.
  apply ssubst_aux_trivial_disj.
  rewrite disjoint_flat_map_l in Hf.
  auto.
Qed.

(* Move to substitution.v *)
Lemma ssubst_aux_sub_trivial_disj:
  forall (sub2 sub1 : Substitution), 
  disjoint (flat_map free_vars (range sub1)) (dom_sub sub2)
  -> subst_aux_sub sub1 sub2 = sub1.
Proof using.
  intros ?. induction sub1; auto.
  intros Hdis.
  simpl. destruct a as [v t].
  simpl in *.
  apply disjoint_app_l in Hdis. repnd.
  simpl. f_equal; eauto;[].
  f_equal.
  apply ssubst_aux_trivial_disj. assumption.
Qed.


End TempTemp.

Lemma getopid_ssubst_aux_var_ren : forall (a : NTerm) sub,
   allvars_sub sub
  -> getOpid (ssubst_aux a sub) = getOpid a.
Proof using varcl freshv.
  intros nt sub H.
  destruct nt; auto.
   apply isvarc_ssubst_vterm with (v:=n) in H.
    simpl in *. unfold isvarc in H. dsub_find sc; auto.
    destruct scs; auto. contradiction.
Qed.

End SubstGeneric2.

Lemma dom_sub_map_range {NVar} {gtsi} {gtso} : forall (f : @NTerm NVar gtsi -> @NTerm NVar gtso) sub,
   dom_sub (map_sub_range f sub) = dom_sub sub.
Proof using.
  induction sub; auto.
  simpl. f_equal. auto.
Qed.
Lemma map_sub_range_combine {NVar} {gtsi} {gtso} : forall (f : @NTerm NVar gtsi -> @NTerm NVar gtso) lv nt,
    map_sub_range f (combine lv nt) = combine lv (map f nt). 
Proof using.
  induction lv; auto. intros. simpl.
  destruct nt; auto. simpl.
  f_equal; auto.
Qed.

Lemma sub_filter_map_range_comm {gtsi gtso NVar} `{Deq NVar}:
  forall sub (f: (@terms.NTerm NVar gtsi) -> (@NTerm NVar gtso)) l,
    sub_filter (map_sub_range  f sub)  l
    = map_sub_range f (sub_filter sub l)  .
Proof using.
  induction sub; simpl; sp. simpl.
  rewrite IHsub. clear IHsub.
  destruct (memvar a0 l); auto.
Qed.

Lemma sub_find_some_map {NVar} `{Deq NVar} {gtsi gtso : Type}
 (f : @NTerm NVar gtsi -> @NTerm NVar gtso) v (sub : @Substitution NVar gtsi) (t: @NTerm NVar gtsi) :
 sub_find sub v = Some t
 -> sub_find (map_sub_range f sub) v = Some (f t).
Proof using.
  induction sub as [| (vs,ts) sub]; intros Heq;[inverts Heq|].
  simpl in *.  cases_if; auto.
  inverts Heq. auto.
Qed.

Lemma sub_find_none_map {NVar} `{Deq NVar} {gtsi gtso : Type}
(f : @NTerm NVar gtsi -> @NTerm NVar gtso) v (sub : @Substitution NVar gtsi) :
 sub_find sub v = None
 -> sub_find (map_sub_range f sub) v = None.
Proof using.
  induction sub as [| (vs,ts) sub]; intros Heq;[inverts Heq|].
  simpl in *; auto. simpl in *.  cases_if; auto.
  inverts Heq.
Qed.




(** the stuff below are duplicates of above *)

Hint Rewrite (fun gs => @ssubst_nil gs).

Hint Immediate prog_sub_csub2sub.
Hint Resolve subst_preserves_isprog : isprog.
Hint Rewrite (fun gs => @ssubst_sub_nil gs).
Hint Resolve prog_sub_implies_wf : slow.
Hint Resolve disjoint_sub_filter_r_flatmap2 : slow.
Hint Resolve disjoint_sym : slow.
    Hint Resolve sub_filter_sat.
Hint Resolve disjoint_sym_eauto disjoint_flat_map_r : slow.

Ltac disjoint_flat := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  repeat match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map free_vars (range ?sub)) 
      (flat_map bound_vars_bterm ?lbt))  |- _ ] => 
    pose proof (disjoint_lbt_bt2 _ _ _ _ H2 H); apply hide_hyp in H2
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map bound_vars_bterm ?lbt)
      (flat_map free_vars (range ?sub)))  |- _ ] => 
      pose proof (disjoint_lbt_bt2 _ _ _ _ (disjoint_sym_impl _ _ _ H2) H);
      apply hide_hyp in H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end ; allrw <- hide_hyp.

Ltac disjoint_flat_sf :=
repeat match goal with
| [|- disjoint (flat_map _ (range (sub_filter _ _))) _] =>
    apply disjoint_sub_filter_r_flatmap2
| [|- disjoint _ (flat_map _ (range (sub_filter _ _)))] =>
    apply disjoint_sym; apply disjoint_sub_filter_r_flatmap2
end.

Ltac disjoint_flat2 := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.


Ltac dsub_find sn :=
  match goal with
    | [  |- context[sub_find ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
    | [ H: context[sub_find ?s ?v] |- _ ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
  end.

(** 1 or less renaming subgoals. see ssubst_nest_swap2 for an example*)
Ltac almost_complete1 t :=
  ((t;fail) || (t;[])).

Ltac dis_almost_complete1 t :=
  try(almost_complete1 t);try (apply disjoint_sym; almost_complete1 t).



(** update it in substitution.v *)
Ltac disjoint_sub_filter :=
        let tac1:=(eapply disjoint_sub_filter_l;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_r_flatmap;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv;
 (
  let maintac := apply disjoint_sub_filter_r_flatmap2; disjoint_reasoningv in
  match goal with 
  |[ |- (disjoint (flat_map _ (range (sub_filter _ _ ))) _ )]
    =>  maintac
  |[ |- ( disjoint _ (flat_map _ (range (sub_filter _ _ ))))]
    => apply disjoint_sym; maintac
  | [ |- disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv ] 
      =>  apply disjoint_dom_sub_filt; fail
  | [ |- disjoint ?lv (dom_sub (sub_filter ?sub ?lv)) ] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt; fail
  | [ H : (disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv) |- _] 
      =>  clear H
  | [ H : ?lv (disjoint (dom_sub (sub_filter ?sub ?lv))) |- _] 
      =>  clear H
  | [ |- disjoint (dom_sub (sub_filter ?sub _)) _ ] 
      =>  apply disjoint_dom_sub_filt2; disjoint_reasoningv
  | [ |- disjoint _ (dom_sub (sub_filter ?sub _))] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt2; disjoint_reasoningv
    
  end
  ).

  Ltac disjoint_ssubst :=
  let maintacf := apply disjoint_free_vars_ssubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  let maintacb := apply disjoint_bound_vars_ssubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  match goal with 
  |[ |- disjoint (free_vars (ssubst_aux _ _ ))  _ ]
    => maintacf  
  |[ |- disjoint _ (free_vars (ssubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacf
  |[ |- disjoint (bound_vars (ssubst_aux _ _ ))  _ ]
    => maintacb  
  |[ |- disjoint _ (bound_vars (ssubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacb
  end.

Ltac dlmap_find sn :=
match goal with
| [  |- context[lmap_find deq_nvar ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
| [  H:context[lmap_find deq_nvar ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
end.
  

Ltac dsub_find2 sn :=
match goal with
| [  |- context[sub_find ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  let H := get_last_hyp tt in
  let H' := fresh H "l" in
  (destruct sn as [sns |];
  symmetry in H;
  try (pose proof (sub_find_some _ _ _  H) as H');
  try (pose proof (sub_find_none2 _ _  H) as H'))
| [ H: context[sub_find ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  destruct sn as [sns |]
end.


Ltac fold_applybt := let XX := fresh "XX" in 
match goal with
[ |- context [ssubst ?e [(?v1, ?t1)]]] => 
  assert (apply_bterm (bterm [v1] e) [t1] = ssubst e [(v1, t1)]) as XX by auto;
    rewrite <- XX; clear XX
end.

Ltac simpl_sub :=
(match goal with
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
end).

Tactic Notation  "spcl" := spc;simpl_list.
Tactic Notation  "spcls" := repeat(simpl_list);sp;repeat(simpl_sub).


Hint Rewrite (fun gs => @sub_filter_nil_r gs) : SquiggleEq.

Ltac change_to_ssubst_aux4 :=
  unfold ssubst;
  allunfold disjoint_bv_sub;
  (repeat match goal with
            | [ |- context [csub2sub ?sub] ] =>
              let name := fresh "ps_csub2sub" in
              pose proof (prog_sub_csub2sub sub) as name;
            fold (hide_csub2sub sub)
          end);
  allunfold hide_csub2sub;
  allunfold prog_sub;
  allunfold sub_range_sat;
  (repeat match goal with
            | [ H:(forall _ _, LIn (_, _) _ -> isprogram _) |- _ ] =>
              progress(rw (prog_sub_flatmap_range _ H))
            | [ H:(forall _ _, LIn (_, _) _ -> closed _) |- _ ] =>
              progress(rw (closed_sub_flatmap_range _ H))
            | [ H:( forall _ _, LIn (_, _) _
                                -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
              apply disjoint_sub_as_flat_map in H;apply disjoint_sym in H
          end);
  repeat(cases_if;clears_last; [|sp;disjoint_reasoningv;spcls;try(false_disjoint)]).


Ltac simpl_sub5 :=
(match goal with
| [ H : (prog_sub _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
| [ H : (forall _ _, LIn (_, _) _  -> isprogram _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
end).

Ltac ssubst_ssubst_aux_eq H :=
match goal with
| [ |- context[ssubst ?t ?sub]] =>
  assert (ssubst t sub = ssubst_aux t sub) as H;
  [change_to_ssubst_aux4; sp ;fail | rw H]
end.

Ltac disjoint_flat3 := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn _ ?tl), H2 : (disjoint _ (flat_map _ ?tl))  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_r _ _ _ _ _)) H2) in H; hide_hyp H
|[ H: (LIn _ ?tl), H2 : (disjoint (flat_map _ ?tl) _)  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_l _ _ _ _ _)) H2) in H; hide_hyp H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.

Ltac fold_ssubst_ot :=
match goal with
[ |- context [ (oterm ?o (map (fun _ : BTerm => ssubst_bterm_aux _ ?sub) ?lbt))]]
  => let Hf := fresh "xxx" in
      let ts := eval simpl in (ssubst_aux (oterm o lbt) sub)  in
        assert (ts = ssubst_aux (oterm o lbt) sub) as Hf by refl;
        rewrite Hf; clear Hf
  end.

Ltac prove_sub_range_sat := 
  let Hin := fresh "Hin" in 
  introv Hin; simpl in Hin;
   repeat(dorn Hin;auto); try(inverts Hin); subst;auto.

Ltac ssubst_aux_ot_eq Hyp := let T := type of Hyp in
  let Hf := fresh Hyp "lseq" in
  match T with 
    context [ ssubst_aux (oterm ?o ?lbt) ?sub] =>
      let ts := eval simpl in (ssubst_aux (oterm o lbt) sub)  in
        assert (ts = ssubst_aux (oterm o lbt) sub) as Hf by refl 
  end.
Ltac fold_ssubst_subh Hyp := let T := type of Hyp in
match T with
  | [(?v1 ,ssubst ?t1 ?sub)] => fold (ssubst_sub [v1,t1] sub)
end.

Ltac fold_ssubst_sub :=
match goal with
| [ |- context [ [(?v1 ,ssubst ?t1 ?sub), (?v2 ,ssubst ?t2 ?sub)] ] ] => fold (ssubst_sub [(v1,t1),(v2,t2)] sub)
| [ |- context [ [(?v1 ,ssubst ?t1 ?sub)] ] ] => fold (ssubst_sub [(v1,t1)] sub)
end.

Hint Rewrite (fun gts => @ssubst_nil gts): SquiggleEq.

Ltac change_to_ssubst_aux8 :=
  repeat rewrite ssubst_ssubst_aux_hide;
  unfold ssubsthide;
  allunfold disjoint_bv_sub;
  (repeat match goal with
            | [ |- context [csub2sub ?sub] ] =>
              let name := fresh "ps_csub2sub" in
              pose proof (prog_sub_csub2sub sub) as name;
            fold (hide_csub2sub sub)
          end);
  allunfold hide_csub2sub;
  allunfold prog_sub;
  allunfold sub_range_sat;
  (repeat match goal with
            | [ H:(forall _ _, LIn (_, _) _ -> isprogram _) |- _ ] =>
              progress(rw (prog_sub_flatmap_range _ H))
            | [ H:(forall _ _, LIn (_, _) _ -> closed _) |- _ ] =>
              progress(rw (closed_sub_flatmap_range _ H))
            | [ H:( forall _ _, LIn (_, _) _
                                -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
              apply disjoint_sub_as_flat_map in H;apply disjoint_sym in H
          end);
  repeat(cases_if;clears_last; [|sp;disjoint_reasoningv;spcls;try(false_disjoint)]).
  
Ltac ssubst_ssubst_aux_eq_hyp H Hyp :=
let T := type of Hyp in 
match T with
|  context[ssubst ?t ?sub] => 
  assert (ssubst t sub = ssubst_aux t sub) as H;
  [change_to_ssubst_aux8; sp  | rewrite H in Hyp ]
end.

Hint Rewrite @dom_sub_map_range : SquiggleEq.
Hint Rewrite @ssubst_aux_nil: SquiggleEq.
Hint Rewrite @dom_sub_map_range : SquiggleEq.

Hint Immediate @allvars_combine : SquiggleEq.

Hint Resolve @sub_filter_subset : subset.

Lemma sub_range_sat_range {n s}: forall P (sub: @Substitution n s),
  sub_range_sat sub P
  <-> (lforall P (range sub)).
Proof.
  unfold sub_range_sat, lforall.
  induction sub as [| ss sub Hind]; 
     simpl in*;[tauto|].
  destruct ss as [v t]. simpl in *.
  split;
  intros; repeat(in_reasoning); subst; simpl in *; subst; cpx.
- eapply H; eauto.
- unfold range in *. apply in_map_iff in H0. exrepnd.
  simpl in *. subst.
  eapply H. right. eauto.
- 
  eapply H. right. apply in_map_iff. eexists; split; eauto.
Qed.



            Ltac lcongruence :=
            unfold isprogram in *;
            unfold isprogram_bt in *;
            unfold closed in *;
            unfold closed_bt in *;
            pose proof @app_nil_r;
            pose proof @map_length;
            pose proof @rev_length;
            pose proof @rev_involutive;
            pose proof @remove_nvars_nil_r;
            pose proof @ssubst_aux_nil;
            pose proof @ssubst_nil;
            pose proof @remove_var_nil;
            pose proof @remove_nvars_eq;
            congruence.

Definition disjoint_bv_sub_bterm := 
fun {NVar} `{Deq NVar} {gtsi: Type} (nt: @BTerm NVar gtsi) (sub : Substitution) =>
sub_range_sat sub (fun t : @NTerm NVar gtsi
    => disjoint (free_vars t) (bound_vars_bterm nt)).

(* to see why the [disjoint_bv_sub] hyp is needed, go back to 
8680feb51db7ea9e5b69766d113ee1aeb7048502,
where I was not able to finish the proof without it. *)

Lemma ssubst_aux_app_simpl_nb  {NVar} `{Deq NVar} {gtsi: Type}:
(forall (t: @NTerm NVar gtsi) sub1 sub2,
  disjoint_bv_sub t sub1->
    ssubst_aux (ssubst_aux t sub1) sub2 = ssubst_aux t (subst_aux_sub sub1 sub2 ++ sub2))
*
(forall (t: @BTerm NVar gtsi) sub1 sub2,
  disjoint_bv_sub_bterm t sub1->
    ssubst_bterm_aux (ssubst_bterm_aux t sub1) sub2 
      = ssubst_bterm_aux t (subst_aux_sub sub1 sub2 ++ sub2)).
Proof using.
  apply NTerm_BTerm_ind.
- intros ? ? ?. simpl.
  rw @sub_find_app.
  dsub_find s1v; symmetry in Heqs1v; unfold subst_aux_sub.
  + apply sub_find_some_map 
      with (f:=(fun t : NTerm => ssubst_aux t sub2)) in Heqs1v.
    rewrite Heqs1v. refl.
  + apply sub_find_none_map 
        with (f:=(fun t : NTerm => ssubst_aux t sub2)) in Heqs1v.
    rw Heqs1v ; simpl; sp.
- intros ? ? Hind ? ? Hd. simpl. f_equal. 
  rw map_map. unfold compose. simpl.
  apply eq_maps. intros b Hin.
  apply Hind; auto. unfold disjoint_bv_sub, disjoint_bv_sub_bterm in *.
  simpl in *. clear Hind.
  intros ? ? Hins. apply Hd in Hins. destruct b.
  eapply disjoint_lbt_bt2 in Hins; eauto. simpl in *.
  disjoint_reasoningv.

- intros ? ? Hind ? ? Hd. simpl in *. f_equal.
  rw @sub_filter_app. unfold subst_aux_sub in *.
  unfold disjoint_bv_sub, disjoint_bv_sub_bterm in *.
  rewrite Hind.
  + repeat rewrite  sub_filter_map_range_comm. simpl.
    f_equal.
    f_equal.
    unfold map_sub_range.
    apply eq_maps. intros ? Hins.
    simpl. f_equal.
    apply ssubst_aux_sub_filter2. destruct x.
    apply in_sub_filter in Hins. apply proj1 in Hins.
    apply Hd in Hins. simpl in *. disjoint_reasoningv.
  + intros ? ? Hins.
    apply in_sub_filter in Hins. apply proj1 in Hins.
    apply Hd in Hins. simpl in Hins.
    disjoint_reasoningv.
Qed.


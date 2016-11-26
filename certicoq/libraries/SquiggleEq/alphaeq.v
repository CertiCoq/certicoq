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
Require Import substitution.

(* Move *)
Lemma and_weaken_l : forall (A B C : Prop),
 (A -> B)
 -> (A # C)
 -> (B # C).
Proof using.
  intros. tauto. 
Qed.

(* Move *)
Lemma forall_combine : forall (A : Type) (P Q R: A -> Prop),
 (forall a:A, P a -> Q a /\ R a)
 -> ((forall a:A, P a -> Q a)#(forall a:A, P a -> R a)).
Proof using.
  intros. firstorder.
Qed.

Generalizable Variable Opid.

Section AlphaGeneric.
Context {NVar VarClass} {deqnvar : Deq NVar} {varcl freshv} 
  {varclass: @VarType NVar VarClass deqnvar varcl freshv} 
 `{hdeq : Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).
Notation WTerm := (@WTerm NVar Opid).
Notation CTerm := (@CTerm NVar  Opid).
Notation Substitution := (@Substitution NVar Opid).
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing <  $<$ #<# *)
(** printing $  $\times$ #×# *)

(** Most of the operations and relations in functional languages
    are invariant under renaming of variables. Alpha equality
    helps us express this property. We define it as follows:
 *)
Inductive alpha_eq : NTerm -> NTerm -> [univ] :=
  | al_vterm : forall v,  alpha_eq (vterm v) (vterm v)
  | al_oterm : forall (op: Opid) (lbt1 lbt2 : list BTerm),
         length lbt1 = length lbt2
         -> (forall n, n < length lbt1
                      -> alpha_eq_bterm (selectbt lbt1 n)
                                        (selectbt lbt2 n))
        -> alpha_eq (oterm op lbt1) (oterm op lbt2)
with alpha_eq_bterm : BTerm -> BTerm -> [univ] :=
  | al_bterm :
      forall (lv1 lv2 lv: list  NVar) (nt1 nt2 : NTerm) ,
        disjoint lv (all_vars nt1 ++ all_vars nt2)
        -> length lv1 = length lv2
        -> length lv1 = length lv
        -> no_repeats lv
        -> alpha_eq (ssubst nt1 (var_ren lv1 lv))
                    (ssubst nt2 (var_ren lv2 lv))
        -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).

(** % \noindent \\* %
    The interesting case is in the definition of [alpha_eq_bterm].
    We list some useful properties about [ssubst] and [alpha_eq].
    Just like the above definitions, these proofs are independent
    of the operators of the language.
   *)

 (** ** Key Properties about Substitution and Alpha Equality *)

 
Definition alphaeqc t1 t2 := alpha_eq (get_cterm t1) (get_cterm t2).

Inductive alpha_eq3 (lva: list NVar): NTerm -> NTerm -> [univ] :=
  | al_vterm3 : forall v,  alpha_eq3 lva (vterm v) (vterm v)
  | al_oterm3 :
      forall op lbt1 lbt2,
         length lbt1 = length lbt2
         -> (forall n, n < length lbt1
                      -> alpha_eq_bterm3 lva (selectbt lbt1 n)
                                        (selectbt lbt2 n))
        -> alpha_eq3 lva (oterm op lbt1) (oterm op lbt2)
with alpha_eq_bterm3 (lva: list NVar) : BTerm -> BTerm -> [univ] :=
  | al_bterm3 :
      forall (lv1 lv2 lv: list  NVar) (nt1 nt2 : NTerm) ,
        disjoint lv (all_vars nt1 ++ all_vars nt2 ++ lva)
        -> length lv1 = length lv2
        -> length lv1 = length lv
        -> no_repeats lv
        -> alpha_eq3 lva (ssubst_aux nt1 (var_ren lv1 lv))
                    (ssubst_aux nt2 (var_ren lv2 lv))
        -> alpha_eq_bterm3 lva (bterm lv1 nt1) (bterm lv2 nt2).

(* Scheme alpha_eq_mut := Induction for alpha_eq Sort Type
  with alpha_eq_bterm_mut := Induction for alpha_eq_bterm Sort Type.
*)



 (* Definition alphaeq  (t1 t2 :NTerm) := alpha_eq t1 t2. *)
Definition alphaeqbt  (t1 t2 :BTerm) := alpha_eq_bterm  t1 t2.
    
Lemma alpha_eq3_refl:
  forall nt lva, alpha_eq3 lva nt nt.
Proof using.
  nterm_ind1s nt as [v | o lbt Hind] Case; [constructor ; fail | idtac].
   Case "oterm". 
    simpl.
    constructor; auto.
    intros m Hlt.
    remember (selectbt lbt m) as bt.
    destruct bt as [lv nt].
    apply selectbt_eq_in in Heqbt; trivial.
    simpl.
    pose proof (fresh_vars (length lv) (all_vars nt ++ lva)) 
         as Hfresh.
    exrepnd.
    rename lvn into newbtv.
    apply al_bterm3 with (lv:=newbtv); auto;
    [disjoint_reasoningv|].
    eapply Hind; eauto.
    rewrite ssubst_aux_allvars_preserves_size2; auto.
Qed.

Theorem alpha_eq_if3: forall nt1 nt2 lv,
  (alpha_eq3 lv nt1 nt2)
   -> (alpha_eq nt1 nt2).
Proof using.
  nterm_ind1s nt1 as [v1 | o1 lbt1 Hind] Case; introv Hal;
  inverts Hal as Ha1 Ha2; constructor; auto.
  introv Hlt. duplicate Hlt. apply Ha2 in Hlt.
  inverts Hlt as Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7.
  apply al_bterm with (lv:=lv0); auto.
  disjoint_reasoningv.
  change_to_ssubst_aux8.
  apply Hind with(lv0:=lv)(lv:=lv1)(nt:=nt1); auto.
  rewrite Hb6. apply selectbt_in; auto.
  rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine; fail.
Qed.


Lemma alpha_eq_refl:
  forall nt, alpha_eq nt nt.
Proof using.
  intros. apply alpha_eq_if3 with (lv:=nil).
  apply alpha_eq3_refl.
Qed.

Lemma alpha_eq_sym:
  forall nt1 nt2, alpha_eq nt1 nt2 -> alpha_eq nt2 nt1.
Proof using.
  nterm_ind1s nt1 as [v1| o lbt1 Hind] Case; introv Hal;
  inverts Hal as Hlen Hal; constructor; [auto | ].
  introv Hlt. rewrite <- Hlen in Hlt. applydup Hal in Hlt.
  pose proof (selectbt_in2 n lbt1 Hlt) as XX. exrepnd. destruct bt as [lv1 nt1].
  revert Hlt0. intros Hlt0. allrw XX0.
  destruct (selectbt lbt2 n) as [lv2 nt2].
  inverts Hlt0 as Ha1 Ha2 Ha3 Ha4 Ha5. apply al_bterm with (lv:=lv); spc.
  - disjoint_reasoningv.
  - eapply Hind; eauto.
    change_to_ssubst_aux8. rewrite ssubst_aux_allvars_preserves_size; [ omega |].
    apply allvars_combine.
Qed.

(** exact same proof as above*)
Lemma alpha_eq3_sym:
  forall nt1 nt2 lva, alpha_eq3 lva nt1 nt2 -> alpha_eq3 lva nt2 nt1.
Proof using.
  nterm_ind1s nt1 as [v1| o lbt1 Hind] Case; introv Hal;
  inverts Hal as Hlen Hal; constructor; [auto | ].
  introv Hlt. rewrite <- Hlen in Hlt. applydup Hal in Hlt.
  pose proof (selectbt_in2 n lbt1 Hlt) as XX. exrepnd. destruct bt as [lv1 nt1].
  revert Hlt0. intros Hlt0. allrw XX0.
  destruct (selectbt lbt2 n) as [lv2 nt2].
  inverts Hlt0 as Ha1 Ha2 Ha3 Ha4 Ha5. apply al_bterm3 with (lv:=lv); spc.
  - disjoint_reasoningv.
  - eapply Hind; eauto.
    rewrite ssubst_aux_allvars_preserves_size; [ omega |].
    apply allvars_combine.
Qed.



Definition strong_alphaeqbt (bt1 bt2 : BTerm) :=
match (bt1, bt2) with
| (bterm lv1 nt1, bterm lv2 nt2) => 
    (length lv1=length lv2) #
      forall lv, (** in the weak version, this was an existential *)
      length lv1 = length lv
      -> disjoint lv (all_vars nt1 ++ all_vars nt2)
      -> no_repeats lv
      -> alpha_eq (ssubst nt1 (combine lv1 (map vterm lv)))
            (ssubst nt2 (combine lv2 (map vterm lv)))
end.
  

(* there is a stronger version of it later. But as of now,
    the proof of that indirectly depends on this weaker version *)
Lemma alpha3_ssubst_allvars_congr : forall nt1 nt2 lvi lvo lva,
  length lvi=length lvo
  -> alpha_eq3 (lvi++lvo++lva) nt1 nt2 
  -> disjoint (lvi++lvo) (bound_vars nt1 ++ bound_vars nt2) 
  -> alpha_eq3 lva (ssubst_aux nt1 (var_ren lvi lvo))
                     (ssubst_aux nt2 (var_ren lvi lvo)).
Proof using .
  clear hdeq.
  nterm_ind1s nt1 as [v1 | o1 lbt1 Hind] Case; introv Hllll Hal Hdis; inverts Hal as Hlen Hal.
  - Case "vterm"; apply alpha_eq3_refl.
  - Case "oterm". constructor;
    repeat(rewrite map_length); auto.
    introv Hlt. rewrite selectbt_map; auto.
    duplicate Hlt. rewrite Hlen in Hlt0.
    rewrite selectbt_map; auto.
    fold @ssubst_bterm_aux.
    applydup Hal in Hlt.
    clear Hal.
    pose proof (selectbt_in2 n lbt1 Hlt) as [bt99 pp].
    exrepnd. destruct bt99 as [blv1 bnt1].
    rewrite pp. rewrite pp in Hlt1.
    pose proof (selectbt_in2 n lbt2 Hlt0) as [bt99 p2p].
    exrepnd. destruct bt99 as [blv2 bnt2].
    rewrite p2p. rewrite p2p in Hlt1.
    inverts Hlt1 as Ha1 Ha2 Ha3 Ha4 Ha5.
    allsimpl. duplicate Hdis as Hdiso.
    apply disjoint_app_r in Hdis. repnd.
    eapply disjoint_lbt_bt2 in Hdis0; eauto. repnd.
    eapply disjoint_lbt_bt2 in Hdis; eauto. repnd.

    allsimpl.
    rename Ha5 into XX.
    try (rw fold_var_ren in XX).
    try (rw fold_var_ren in XX).
    rewrite sub_filter_disjoint;auto;
      [|apply disjoint_app_l in Hdis1; sp; fail].
    rewrite sub_filter_disjoint;auto;
      [|apply disjoint_app_l in Hdis2; sp; fail].
    apply al_bterm3 with (lv:=lv); auto.
    + introv Hin Hc. apply Ha1 in Hin.
      apply_clear Hin.
      repeat(rw in_app_iff).
      repeat(rw in_app_iff in Hc).
SearchAbout @map @combine @prod.
      rewrite boundvars_ssubst_aux_vars in Hc;auto.
      rewrite boundvars_ssubst_aux_vars in Hc;auto.
      repeat(dorn Hc); auto; [|];
      apply free_vars_ssubst_aux in Hc;try(apply wf_sub_vars);try(apply disjoint_bv_vars;disjoint_reasoningv);
         [|];
      dorn Hc; exrepnd; auto;[|];
      apply in_var_ren in Hc0; exrepnd; subst; allsimpl; dorn Hc1; subst; sp.
    + apply Hind with(lv:=blv1) (lvi:=lvi) (nt:=bnt1) in XX; eauto.
      Focus 2. rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine; fail.  
        Focus 2.
          introv Hin Hc.
          rewrite boundvars_ssubst_aux_vars in Hc; auto.
          rewrite boundvars_ssubst_aux_vars in Hc; auto;
           [|congruence].
          apply in_app_iff in Hc; auto.
          dorn Hc; [apply Hdis0 in Hin|apply Hdis in Hin];sp; fail.

       rewrite ssubst_aux_nest_swap; try congruence;  disjoint_reasoningv. 
       apply alpha_eq3_sym. (** because o/w rw undo the above *)
       simpl. rewrite ssubst_aux_nest_swap; try congruence; dands; disjoint_reasoningv. 
       apply alpha_eq3_sym; trivial.
Qed.

Theorem alpha_eq3_if: forall nt1 nt2,
    (alpha_eq nt1 nt2) -> forall lv, (alpha_eq3 lv nt1 nt2).
Proof using.
  nterm_ind1s nt1 as [v1 | o1 lbt1 Hind] Case; introv Hyp;
  destruct nt2 as [v2 | o2 lbt2]; 
  inverts Hyp as Hlen Hbt;
  constructor;auto;
  []; introv Hlt; applydup Hbt in Hlt; clear Hbt;
  destructr (selectbt lbt1 n) as [lv1 nnt1];
  destructr (selectbt lbt2 n) as [lv2 nnt2];
  inverts Hlt0 as Hb1 Hb2 Hb3 Hb4 Hb5.
    pose proof (fresh_vars (length lv1) 
    (all_vars nnt1 ++ all_vars nnt2 ++lv)) 
         as Hfresh.
    exrepnd.
    apply al_bterm3 with(lv:=lvn);auto.
    pose proof (selectbt_in   _ _ Hlt) as XX.
    rewrite <- HeqHdeq in XX.
    eapply Hind with(lv0:=(lv4++lvn++lv)) (nt:=nnt1) (lv:=lv1) in Hb5; auto.
    Focus 2. change_to_ssubst_aux8. 
    rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine; fail.
    try (rw fold_var_ren in Hb5).
    try (rw fold_var_ren in Hb5).
    try (rw fold_var_ren).
    try (rw fold_var_ren).
    apply alpha3_ssubst_allvars_congr in Hb5; try congruence.
    + revert Hb5. change_to_ssubst_aux8. intro Hb5.
      rewrite ssubst_aux_nest_vars_same in Hb5; auto;
      [ |congruence| disjoint_reasoningv | disjoint_reasoningv ].
      rewrite ssubst_aux_nest_vars_same in Hb5; auto;
      [ congruence | congruence | disjoint_reasoningv| disjoint_reasoningv].
    + rewrite boundvars_ssubst_vars; [|congruence|disjoint_reasoningv].
      rewrite boundvars_ssubst_vars;disjoint_reasoningv.
Qed.

Theorem alpha_eq3_change_avoidvars:
 forall lv lv' nt1 nt2, alpha_eq3 lv nt1 nt2
   ->  alpha_eq3 lv' nt1 nt2.
Proof using.
  introv Hal.
  apply alpha_eq_if3 in Hal.
  apply alpha_eq3_if; auto.
Qed.

Notation vterm := (@vterm NVar Opid).

Lemma alpha3_ssubst_aux_allvars_congr2 : forall nt1 nt2 lvi lvo lva,
  length lvi=length lvo
  -> alpha_eq3 (lvi++lvo++lva) nt1 nt2 
  -> disjoint (lvo) (bound_vars nt1 ++ bound_vars nt2) 
  -> alpha_eq3 lva (ssubst_aux nt1 (var_ren lvi lvo))
                     (ssubst_aux nt2 (var_ren lvi lvo)).
Proof using.
  nterm_ind1s nt1 as [v1 | o1 lbt1 Hind] Case; introv Hllll Hal Hdis;
    duplicate Hal; inverts Hal as Hlen Hal.
  - Case "vterm". apply alpha_eq3_refl.

  - Case "oterm". constructor;
    repeat(rewrite map_length); auto.
    introv Hlt. rewrite selectbt_map; auto.
    duplicate Hlt. rewrite Hlen in Hlt0.
    rewrite selectbt_map; auto.
    fold @ssubst_bterm_aux. clear Hal.
    pose proof (selectbt_in2 n lbt1 Hlt) as [bt99 pp].
    exrepnd. destruct bt99 as [blv1 bnt1].
    pose proof (selectbt_in2 n lbt2 Hlt0) as [bt99 p2p].
    exrepnd. destruct bt99 as [blv2 bnt2].
    apply alpha_eq3_change_avoidvars with (lv':= (lvi ++ lvo ++ lva ++ blv1 ++ blv2)) in Hal0.
    inverts Hal0 as H1len Hbal. GC.
    applydup Hbal in Hlt.
    rewrite pp. rewrite pp in Hlt1.
    rewrite p2p. rewrite p2p in Hlt1.
    clear Hbal.
    inverts Hlt1 as Ha1 Ha2 Ha3 Ha4 Ha5.
    allsimpl. duplicate Hdis as Hdiso.
    apply disjoint_app_r in Hdis. repnd.
    eapply disjoint_lbt_bt2 in Hdis0; eauto. repnd.
    eapply disjoint_lbt_bt2 in Hdis; eauto. repnd.

    repeat (rewrite (bvar_renamings_subst_disjoint_bound_vars); auto;[|
    apply disjoint_sub_as_flat_map;
    rewrite flat_map_free_var_vars_range;spc;sp;fail]).
    allsimpl.
    rename Ha5 into XX.
    simpl.  pose proof (@allvars_sub_filter _ _ Opid lvi lvo blv1) as X1.
    pose proof (get_sub_dom_vars_eta _ X1) as X1X. exrepnd.
    repeat(rewrite X1X0).
    simpl.  pose proof (@allvars_sub_filter _ _ Opid lvi lvo blv2) as X2.
    pose proof (get_sub_dom_vars_eta _ X2) as X2X. exrepnd.
    repeat(rewrite X2X0).
    apply al_bterm3 with (lv:=lv); auto.
    + disjoint_reasoningv.
      * apply disjoint_sym. apply disjoint_free_vars_ssubst_aux;sp;
        rewrite flat_map_free_var_vars_range;spc;spc;disjoint_reasoningv.

        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.

        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.


      * apply disjoint_sym. apply disjoint_bound_vars_ssubst_aux;sp;
        try(rewrite flat_map_free_var_vars_range;spc);
        try(rewrite flat_map_bound_var_vars_range;spc;spc);simpl;
        simpl_vlist;
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.

      * apply disjoint_sym. apply disjoint_free_vars_ssubst_aux;sp;
        rewrite flat_map_free_var_vars_range;spc;disjoint_reasoningv.

        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.

        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.

      * apply disjoint_sym. apply disjoint_bound_vars_ssubst_aux;sp;
        try(rewrite flat_map_free_var_vars_range;spc);
        try(rewrite flat_map_bound_var_vars_range;spc);simpl;
        simpl_vlist;
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.

   +  apply Hind with(lv:=blv1) (lvi:=lvi) (nt:=bnt1) in XX; eauto.

        Focus 2. rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine; fail.
        Focus 2.
          introv Hin Hc.
          rewrite boundvars_ssubst_aux_vars in Hc; auto.
          rewrite boundvars_ssubst_aux_vars in Hc; auto;
           [|congruence].
          apply in_app_iff in Hc; auto.
          dorn Hc; [apply Hdis0 in Hin|apply Hdis in Hin];sp; fail.

      rewrite ssubst_aux_nest_swap; try congruence;[|disjoint_reasoningv| disjoint_reasoningv].
      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 2.
        apply disjoint_sym. introv Hin Hinc.
        apply combine_in_left with (l2:= map vterm lvo0)  in Hinc;
          [| rewrite map_length;sp];[].
        exrepnd. try (rewrite fold_var_ren in Hinc0).
        rewrite <- X1X0 in Hinc0.
        apply in_sub_filter in Hinc0.
        sp;fail.
        
      apply alpha_eq3_sym.
      rewrite ssubst_aux_nest_swap; try congruence;[|disjoint_reasoningv| disjoint_reasoningv].

      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 3.
        let tac1:=(eapply disjoint_sub_filter_vars_r;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_vars_l;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv.
      Focus 2.
        apply disjoint_sym. introv Hin Hinc.
        apply combine_in_left with (l2:= map vterm lvo1)  in Hinc;
          [| rewrite map_length;sp];[].
        exrepnd. try (rewrite fold_var_ren in Hinc0).
        rewrite <- X2X0 in Hinc0.
        apply in_sub_filter in Hinc0.
        sp;fail.
        sp.
rw <- X1X0.
rw <- X2X0.

     rewrite ssubst_aux_sub_filter2.
    Focus 2.
      intros v Hin Hinc.
      apply free_vars_ssubst_aux2 in Hin.
      dorn Hin. 
      repnd. unfold var_ren in Hin.
      rewrite dom_sub_combine in Hin;[| rw map_length;sp]. sp.

      exrepnd. apply in_var_ren in Hin0. exrepnd. subst. allsimpl.
      dorn Hin1;sp;subst. rename Ha1 into Hcdis.
      assert(disjoint lv blv2) as XXX by disjoint_reasoningv.
      apply XXX in Hin4. sp.


     rewrite ssubst_aux_sub_filter2.
    Focus 2. 
      intros v Hin Hinc.
      apply free_vars_ssubst_aux2 in Hin.
      dorn Hin. 
      repnd. unfold var_ren in Hin.
      rewrite dom_sub_combine in Hin;[| rw map_length;sp]. sp.

      exrepnd. apply in_var_ren in Hin0. exrepnd. subst. allsimpl.
      dorn Hin1;sp;subst. rename Ha1 into Hcdis.
      assert(disjoint lv blv1) as XXX by disjoint_reasoningv.
      apply XXX in Hin4. sp.

  apply alpha_eq3_sym.
eapply alpha_eq3_change_avoidvars; eauto.
Qed.



Theorem alpha3bt_change_var: forall nt1 nt2 lv1 lv2 lv lva,
  alpha_eq_bterm3 lva (bterm lv1 nt1) (bterm lv2 nt2)
  -> length lv1 = length lv
  -> disjoint lv (all_vars nt1 ++ all_vars nt2)
  -> no_repeats lv
  -> alpha_eq3 lva (ssubst_aux nt1 (var_ren lv1 lv))
        (ssubst_aux nt2 (var_ren lv2 lv)).
Proof using.
  introv Hal Hlen Hdis Hnr.
  inverts Hal as Ha1 Ha2 Ha3 Ha4 Ha5.
  apply (alpha_eq3_change_avoidvars _ (lv4++lv++lva)) in Ha5.
  apply alpha3_ssubst_aux_allvars_congr2 in Ha5;[| congruence | ].
  Focus 2. rewrite boundvars_ssubst_aux_vars; [|congruence].
      rewrite boundvars_ssubst_aux_vars;disjoint_reasoningv.
  rewrite ssubst_aux_nest_vars_same in Ha5;auto;
    [| congruence| disjoint_reasoningv| disjoint_reasoningv].
  rewrite ssubst_aux_nest_vars_same in Ha5;auto;
    [ congruence | congruence | disjoint_reasoningv| disjoint_reasoningv]. 
Qed.



Lemma alpha_eq_trans:
  forall nt1 nt2 nt3, alpha_eq nt1 nt2 -> alpha_eq nt2 nt3 -> alpha_eq nt1 nt3.
Proof using.
  nterm_ind1s nt1 as [v1 | o1 lbt1 Hind] Case;
  introv Hal1 Hal2; apply alpha_eq3_if with (lv:=[]) in Hal1;
  apply alpha_eq3_if with (lv:=[]) in Hal2;
  apply alpha_eq_if3 with (lv:=[]);
  inverts Hal1 as Hlen1 Hal1; inverts Hal2 as Hlen2 Hal2; constructor
  ;try(congruence).
  Case "oterm".
  - introv Hlt0. duplicate Hlt0. duplicate Hlt0. apply Hal1 in Hlt0.
    rewrite Hlen1 in Hlt1. apply Hal2 in Hlt1.
    pose proof (selectbt_in _ _ Hlt2).
    destruct (selectbt lbt1 n) as [lv1 nt1].
    destruct (selectbt lbt2 n) as [lv2 nt2].
    destruct (selectbt lbt3 n) as [lv3 nt3].
    duplicate Hlt0 as Hl1t.
    duplicate Hlt1 as Hl2t.    
    inverts Hlt0 as Ha1 Ha2 Ha3 Ha4 Ha5.
    inverts Hlt1 as Hb1 Hb2 Hb3 Hb4 Hb5.
    pose proof (fresh_vars (length lv1) 
         (all_vars nt1 ++ all_vars nt2 ++ all_vars nt3)) as Hfresh.
    exrepnd.
    clear Hb5 Ha4 Ha5 Hb1 Hb4 Ha3 Hb3 Hb1.
    apply alpha3bt_change_var with (lv:=lvn) in Hl1t; 
      eauto;[|disjoint_reasoningv].
    apply alpha3bt_change_var with (lv:=lvn) in Hl2t; 
      eauto; [| congruence | disjoint_reasoningv].
    apply al_bterm3 with (lv:=lvn);auto;
    try congruence;[disjoint_reasoningv| ].
    apply alpha_eq_if3 with (lv:=[]) in Hl1t.
    apply alpha_eq_if3 with (lv:=[]) in Hl2t.
    apply alpha_eq3_if with (lv:=[]).
    eapply Hind with(lv:=lv1) (nt:=nt1); eauto.
    rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine.
Qed.

Lemma alphaeqbt_numbvars : forall a b,
  alpha_eq_bterm a b  -> num_bvars a = num_bvars b.
Proof using. intros ? ? Hal. invertsn Hal; auto.
Qed.

Theorem alphaeqbt_refl: forall b, alpha_eq_bterm b b.
Proof using. intros. destruct b.
  pose proof (fresh_vars (length l) (all_vars n)) as Hfresh.
  exrepnd. apply al_bterm with (lv:=lvn); auto.
  apply disjoint_app_r; auto.
  apply alpha_eq_refl.
Qed.


Definition alphaeqbtw (t1 t2: BTerm) := (bt_wf t1) # (bt_wf t2) 
                                             # alphaeqbt t1 t2.

Theorem alphaeqbtw_refl: forall b, bt_wf b -> alphaeqbtw b b.
Proof using. intros. destruct b. split; auto; split; auto.
    apply alphaeqbt_refl. 
Qed.



Theorem alpha_eq_ot_numvars: forall o lbt1 lbt2,
  alpha_eq (oterm o lbt1) (oterm o lbt2)
  -> map num_bvars lbt1 = map num_bvars lbt2.
Proof using. 
  introv Hal. duplicate Hal. inverts Hal as Hlen Hal.
  apply eq_maps_bt; auto. introv Hlt. 
  pose proof (Hal _ Hlt) as Halb. inverts Halb.
  auto.
Qed.


Theorem alphaeq3_preserves_wf: 
  forall t1 t2, alpha_eq3 [] t1 t2 -> (nt_wf t2 <=> nt_wf t1).
Proof using. 
  intros ?. nterm_ind1s t1 as [v | o lbt1 Hind] Case; intros t2  Hal. 
  Case "vterm". inverts Hal as .  split; constructor. 
  Case "oterm". duplicate Hal. inverts Hal as Hmap Hal. 
    apply alpha_eq_if3 in Hal0. apply alpha_eq_ot_numvars in Hal0.
    allrw ntot_wf_iff. 
    rewrite Hmap. rewrite Hal0.
    apply and_tiff_compat_l; auto. 
    apply iff_push_down_forallT. intros n. 
    apply iff_push_down_impliesT. 
    remember (selectbt lbt2 n) as bt2.
    remember (selectbt lbt1 n) as bt1.
    destruct bt2 as [lv2 nt2]. 
    destruct bt1 as [lv1 nt1].  
    intros Hlt. rewrite <- Hmap in Hlt.  
    repeat(rw bt_wf_iff). 
    applydup_clear Hal in Hlt. 
    rewrite <- Heqbt1 in Hlt0. rewrite <- Heqbt2 in Hlt0. 
    inverts Hlt0 as Hi1 Hi2 Hi3 Hi4 Hi5.
    
    assert(LIn (bterm lv1 nt1) lbt1) as Hinb 
      by (rewrite Heqbt1; apply selectbt_in; auto).
    eapply Hind  with (lv:=lv1) in Hi5; eauto.
     - rw <- (ssubst_aux_allvars_wf_iff _ (allvars_combine lv2 lv) )  in Hi5. 
       rw <- (ssubst_aux_allvars_wf_iff _ (allvars_combine lv1 lv) )  in Hi5.
       trivial.
        repeat rewrite bt_wf_iff. trivial.
     - rewrite ssubst_aux_allvars_preserves_size2; auto. 
Qed.

Lemma alphaeq_preserves_wf: 
  forall t1 t2, alpha_eq t1 t2 -> (nt_wf t2 <=> nt_wf t1).
Proof using.
  introv Hal.
  apply alpha_eq3_if with (lv:=[]) in Hal.
  apply alphaeq3_preserves_wf;sp.
Qed.
(**     % \noindent \\* %
The following lemma is the property we promised to prove while definining [ssubst].
*)

Lemma change_bvars_alpha_spec_aux: forall lv,
  (forall nt, 
  let nt' := change_bvars_alpha lv nt in
  disjoint lv (bound_vars nt') #alpha_eq nt nt')
  * (forall bt,
  let bt' := change_bvars_alphabt lv bt in
  disjoint lv (bound_vars_bterm bt') #alpha_eq_bterm bt bt').
Proof using.
  intros. apply NTerm_BTerm_ind;
    [intro v; cpx| |].
  - intros ? ? Hind.
   simpl. split.
    + rewrite disjoint_flat_map_r.
      intros ? Hin.
      apply in_map_iff in Hin.
      exrepnd. subst.
      apply Hind. auto.
    + 
      constructor; try (rw map_length; auto);[].
      introv Hlt. rw @selectbt_map; auto.
      pose proof (selectbt_in2 n lbt Hlt) as XX; exrepnd.
      destruct bt as [blv bnt]. rewrite XX0.
      apply Hind. auto.

- intros blv bnt Hnt. split.
   +  introv Hin Hinc. rename t into vv.
      allsimpl. subst.
      simpl in *.
       addFreshVarsSpec2 vn pp.
      exrepnd. allsimpl.
      duplicate Hin.
      repnd.
      apply Hnt0 in Hin0.
      setoid_rewrite boundvars_ssubst_aux_vars in Hinc; sp.
      apply disjoint_sym  in pp1.
      apply disjoint_app_l in pp1. repnd. apply pp2 in Hin.
      apply in_app_iff in Hinc.
      simpl in *.  
      dorn Hinc; sp.
  

  +  allsimpl. subst.
     simpl. addFreshVarsSpec2 vn pp.
      destruct (fresh_vars (length blv) (lv ++ vn ++ (all_vars bnt) 
        ++ all_vars
     (change_bvars_alpha lv bnt))) as [lvn pal].
    exrepnd. allsimpl.
    disjoint_reasoningv.
     apply al_bterm with (lv:=lvn); sp.
    unfold all_vars. rw @boundvars_ssubst_aux_vars;sp;
    try(disjoint_reasoningv).
    introv Hin Hinc.
    applydup pal5 in Hin.
    apply free_vars_ssubst_aux in Hinc;
    [ |apply disjoint_bv_vars; sp].
    dorn Hinc; exrepnd; sp. apply in_var_ren in Hinc0. exrepnd.
    subst.
    allsimpl.
    dorn Hinc1; sp.
    subst.
    apply pal3 in Hin. sp.
    rewrite <- ssubst_ssubst_aux; 
    spcls; disjoint_reasoningv. rewrite ssubst_nest_vars_same; sp;
    try congruence; try disjoint_reasoningv.
    apply alpha_eq_if3 with (lv:=nil).
    change_to_ssubst_aux8.
    apply alpha3_ssubst_aux_allvars_congr2;sp.
    Focus 2. disjoint_reasoningv.
    apply alpha_eq3_if.
    eauto.
Qed.

Definition change_bvars_alpha_spec: forall (nt : NTerm) (lv : list NVar),
       disjoint lv (bound_vars (change_bvars_alpha lv nt)) # alpha_eq nt (change_bvars_alpha lv nt)
 := fun nt lv => (fst (change_bvars_alpha_spec_aux lv)) nt.

Definition change_bvars_alphabt_spec 
: forall (lv : list NVar) (bt : BTerm),
       disjoint lv (bound_vars_bterm (change_bvars_alphabt lv bt)) # alpha_eq_bterm bt (change_bvars_alphabt lv bt)
:= fun lv => snd (change_bvars_alpha_spec_aux lv).



Lemma change_bvars_alpha_spec_varclass: forall lv vc,
  (forall (nt:NTerm), varsOfClass (bound_vars nt) vc 
      -> varsOfClass (bound_vars (change_bvars_alpha lv nt)) vc)
  * 
  (forall (bt:BTerm), varsOfClass (bound_vars_bterm bt) vc 
      -> varsOfClass (bound_vars_bterm (change_bvars_alphabt lv bt)) vc).
Proof using varclass.
  intros. apply NTerm_BTerm_ind;
    [intro v; simpl; unfold preservesVarclass; tauto| |].
  - intros ? ? Hind. simpl.
    rewrite flat_map_map.
    apply lforall_flatmap.
    exact Hind.
- intros blv bnt Hnt.
  simpl. repeat rewrite varsOfClassApp.
  introv Hin. repnd.
  split;[apply freshReplacementsSameClass; assumption|].
  eapply lforall_subset;[apply boundvars_ssubst_aux_subset|].
  rewrite flat_map_bound_var_vars_range;
      [| autorewrite with SquiggleEq; setoid_rewrite freshVarsLen; refl].
  autorewrite with list.
  unfold varsOfClass in *.
  eauto.
Qed.

(*
Lemma change_bvars_alpha_spec_varclass: forall lv vc,
  (forall nt, varsOfClass (bound_vars nt) vc 
      -> varsOfClass (bound_vars (change_bvars_alpha lv nt)) vc)
*)

Ltac add_changebvar_spec cb Hn:=
match goal with 
| [ |- context[change_bvars_alpha ?lv ?nt] ] => pose proof (change_bvars_alpha_spec nt lv) as Hn;
    remember (change_bvars_alpha  lv nt) as cb; simpl in Hn
| [ |- context[change_bvars_alphabt ?lv ?nt] ] => pose proof (change_bvars_alphabt_spec lv nt) as Hn;
    remember (change_bvars_alphabt  lv nt) as cb; simpl in Hn
end.


Theorem alphaeqbt_preserves_wf: 
  forall bt1 bt2, alpha_eq_bterm bt1 bt2 -> (bt_wf bt2 <=> bt_wf bt1).
Proof using. 
  introv Hal. inverts Hal as Hi1 Hi2 Hi3 Hi4 Hal. repeat(rw bt_wf_iff).
  apply alphaeq_preserves_wf in Hal.
  revert Hal. change_to_ssubst_aux8. intro Hal.
  rw <- (ssubst_aux_allvars_wf_iff _ (allvars_combine lv2 lv) )  in Hal. 
  rw <- (ssubst_aux_allvars_wf_iff _ (allvars_combine lv1 lv) )  in Hal.
  repeat rewrite bt_wf_iff.
  trivial.
Qed. 


Lemma alpha_eq3_preserves_size: forall nt1 nt2,
  alpha_eq3 [] nt1 nt2 -> size nt1 = size nt2.
Proof using.
  nterm_ind1s nt1 as [v1| o lbt1 Hind] Case; introv Hal;
  inverts Hal as Hlen Hal;sp.
  simpl. f_equal. f_equal. eapply eq_maps_bt; try (congruence).
  introv Hlt. pose proof (selectbt_in2 _ _ Hlt) as XX.
  exrepnd. destruct bt as [lv1 nt1].
  apply_clear Hal in Hlt. revert Hlt. rw XX0. introv Hlt.
  destruct (selectbt lbt2 n) as [lv2 nt2].
  simpl. invertsna Hlt  Hbal.
  eapply Hind in Hbal3; eauto;
  repeat rewrite @ssubst_aux_allvars_preserves_size2 in *; sp.
Qed.

Lemma alpha_eq_preserves_size: forall nt1 nt2,
  alpha_eq nt1 nt2 -> size nt1 = size nt2.
Proof using.
  intros. apply alpha_eq3_preserves_size.
  apply alpha_eq3_if. sp.
Qed.



Definition selectnt (bts: list NTerm) (n:nat) : NTerm :=
  nth n bts (vterm nvarx).



Definition alpha_eq_list (lnt1 lnt2 : list NTerm) := 
  bin_rel_nterm alpha_eq lnt1 lnt2.
  



Lemma alpha_eq3_bterm_lenbvars: forall lv1 lv2 nt1 nt2 lva,
  alpha_eq_bterm3 lva (bterm lv1 nt1) (bterm lv2 nt2)
  -> length lv1=length lv2.
Proof using.
  introv Hal. inverts Hal; sp.
Qed.


Hint Immediate alpha_eq_refl.

Hint Immediate alphaeqbt_refl.

Hint Resolve alpha3bt_change_var alpha_eq_if3 : slow.

Lemma alphaeq_bterm3_if: forall bt1 bt2,
  alpha_eq_bterm bt1 bt2
  -> forall lva, alpha_eq_bterm3 lva bt1 bt2.
Proof using.
  introv Hal. intro. invertsna Hal Hal.
  apply alpha_eq3_if with  (lv:=lva) in Hal3.
  assert (alpha_eq_bterm3 [] (bterm lv1 nt1) (bterm lv2 nt2)) as XX.
  - eapply al_bterm3 with (lv:=lv); simpl_vlist; eauto.
    rewrite <- ssubst_ssubst_aux; spcls; disjoint_reasoningv.
    rewrite <- ssubst_ssubst_aux; spcls; disjoint_reasoningv.
     eapply alpha_eq3_change_avoidvars; eauto.
  - pose proof (fresh_vars (length lv1) (all_vars nt1 ++ all_vars nt2 ++lva)) as Hfr.
    exrepnd. apply alpha3bt_change_var with (lv:=lvn) in XX;sp; try congruence;
    [| disjoint_reasoningv];[].
    econstructor; eauto.
    eapply alpha_eq3_change_avoidvars; eauto.
Qed.

Theorem alphabt_change_var_aux: forall nt1 nt2 lv1 lv2 lv,
  alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2)
  -> length lv1 = length lv
  -> disjoint lv (all_vars nt1 ++ all_vars nt2)
  -> no_repeats lv
  -> (alpha_eq (ssubst_aux nt1 (var_ren lv1 lv))
        (ssubst_aux nt2 (var_ren lv2 lv)) # length lv1 = length lv2).
Proof using.
  introns HX.
  unfold ssubst.
  duplicate HX as Hl.
  inverts Hl.
  apply alphaeq_bterm3_if with (lva:=[]) in HX.

     (*eauto*)
      split; spc;
      eapply alpha_eq_if3;
      eapply alpha3bt_change_var;eauto.

Qed.

Theorem alphabt_change_var: forall nt1 nt2 lv1 lv2 lv,
  alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2)
  -> length lv1 = length lv
  -> disjoint lv (all_vars nt1 ++ all_vars nt2)
  -> no_repeats lv
  -> (alpha_eq (ssubst nt1 (var_ren lv1 lv))
        (ssubst nt2 (var_ren lv2 lv)) # length lv1 = length lv2).
Proof using.
  introns HX.
  duplicate HX as Hl.
  inverts Hl.
  change_to_ssubst_aux8.
  apply alphaeq_bterm3_if with (lva:=[]) in HX.

     (*eauto*)

      split; spc;
      eapply alpha_eq_if3;
      eapply alpha3bt_change_var;eauto.
Qed.

Hint Resolve alpha_eq_sym alpha_eq_trans : slow.

Lemma alpha_eq_bterm_trans: forall bt1 bt2 bt3,
  alpha_eq_bterm bt1 bt2
  -> alpha_eq_bterm bt2 bt3
  -> alpha_eq_bterm bt1 bt3.
Proof using. introv H1b H2b.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  destruct bt3 as [lv3 nt3].
  pose proof (fresh_vars (length lv1) (all_vars nt1++all_vars nt2++all_vars nt3)).
  exrepnd.
  apply alphabt_change_var with (lv:=lvn) in H1b; eauto; disjoint_reasoningv.
  apply alphabt_change_var with (lv:=lvn) in H2b; eauto; disjoint_reasoningv;spc.
  apply al_bterm with (lv:=lvn); spc; disjoint_reasoningv.
  eauto with slow. 
Qed.


Lemma alpha_eq_bterm_sym :
  forall bt1 bt2, alpha_eq_bterm bt1 bt2 -> alpha_eq_bterm bt2 bt1.
Proof using.
  introv Hb.
  inverts Hb.
  apply al_bterm with (lv:=lv);sp; eauto with slow; [].
  disjoint_reasoningv.
Qed.

(* Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: slow. *)

(** all this to avoid duplicating these complicating proofs for nterm and bterm *)
Definition ssubst_alpha3_congr_aux t1 t2 lvi lnt1 lnt2 :=
  alpha_eq3 [] t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars t2)
  -> bin_rel_nterm (alpha_eq3 []) lnt1 lnt2
  -> alpha_eq3 [] (ssubst_aux t1 (combine lvi lnt1)) (ssubst_aux t2 (combine lvi lnt2)).

Definition ssubst_alphabt3_congr_aux bt1 bt2 lvi lnt1 lnt2 :=
  alpha_eq_bterm3 [] bt1 bt2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars_bterm bt1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars_bterm bt2)
  -> bin_rel_nterm (alpha_eq3 []) lnt1 lnt2
  -> alpha_eq_bterm3 [] (ssubst_bterm_aux bt1 (combine lvi lnt1)) 
                    (ssubst_bterm_aux bt2 (combine lvi lnt2)).

Hint Unfold ssubst_alphabt3_congr_aux.
Hint Unfold ssubst_alpha3_congr_aux.

(** induction step for nterm proof ... after nterm proof, it can be used 
  trivially to get the proof for bterm case without much effort *)
Theorem ssubst_alphabt3_congr_auxp : forall bnt1 blv1,
  (forall t1' t2 lvi lnt1 lnt2, (size t1' <= size bnt1) 
               -> ssubst_alpha3_congr_aux t1' t2 lvi lnt1 lnt2)
  -> forall bt2 lvi lnt1 lnt2, ssubst_alphabt3_congr_aux (bterm blv1 bnt1) 
                                                  bt2 lvi lnt1 lnt2.
Proof using. introv Hind Hlt1 H1len H2len H1dis H2dis Hall.  
    destruct bt2 as [blv2 bnt2].
    applydup alpha_eq3_bterm_lenbvars in Hlt1 as Hblen.
    pose proof (fresh_vars (length blv1)
     (all_vars bnt1 ++ all_vars bnt2 ++ flat_map free_vars lnt1 ++ flat_map free_vars lnt2
        ++ flat_map bound_vars lnt1 ++ flat_map bound_vars lnt2 ++ lvi ++ blv1 ++ blv2))
      as Hfresh. exrepnd.
    apply alpha3bt_change_var with (lv:=lvn) in Hlt1;sp;[| disjoint_reasoningv;fail].
    allsimpl.

    repeat( rewrite (bvar_renamings_subst_disjoint_bound_vars); [|
      apply disjoint_sub_as_flat_map; rewrite dom_range_combine;sp;
      disjoint_reasoningv]).
   allsimpl.
    rename Hlt1 into XX.
    pose proof (sub_eta (sub_filter (combine lvi lnt1) blv1)) as Xsf1eta;
    pose proof (sub_eta (sub_filter (combine lvi lnt2) blv2)) as Xsf2eta;
    pose proof (sub_eta_length (sub_filter (combine lvi lnt1) blv1)) as X1len;
    pose proof (sub_eta_length (sub_filter (combine lvi lnt2) blv2)) as X2len;
    remember (dom_sub (sub_filter (combine lvi lnt1) blv1)) as lsvi1;
    remember (dom_sub (sub_filter (combine lvi lnt2) blv2)) as lsvi2;
    remember (range (sub_filter (combine lvi lnt1) blv1)) as lsnt1;
    remember (range (sub_filter (combine lvi lnt2) blv2)) as lsnt2.
    rewrite Xsf1eta.
    rewrite Xsf2eta.
    unfold ssubst_alpha3_congr_aux in Hind.
    simpl in Hind. 
    apply al_bterm3 with (lv:=lvn); auto.
    + disjoint_reasoningv;apply disjoint_sym;
      try(apply disjoint_free_vars_ssubst_aux);
      try(apply disjoint_bound_vars_ssubst_aux); spcls; disjoint_reasoningv;
      disjoint_sub_filter.

    + eapply Hind with (lvi:=lvi)  (lnt1:=lnt1) (lnt2:=lnt2) in XX; eauto.
      Focus 2. rewrite ssubst_aux_allvars_preserves_size; [ omega |]. apply allvars_combine; fail.
      Focus 2. rewrite boundvars_ssubst_aux_vars;spc; disjoint_reasoningv;fail.
      Focus 2. rewrite boundvars_ssubst_aux_vars;spc; disjoint_reasoningv;fail.
      (** domains of subsitutions in the conclusion are different because 
        they were filtered by different sets. we need to swap the ssubst
        order to show that the filtering can be undone w.r.t syntactic equality*)
        
      unfold var_ren.
      (** swapping below requires the domains to be disjoint *)
      rewrite ssubst_aux_nest_swap2; spcls; simpl; 
      disjoint_reasoningv;try(disjoint_sub_filter; fail).

      Focus 2. rw Heqlsvi1.
        rewrite <- dom_sub_sub_filter.
        spcls. apply disjoint_remove_nvars.

      apply alpha_eq3_sym.
      rewrite ssubst_aux_nest_swap2; spcls; simpl; 
      disjoint_reasoningv;try(disjoint_sub_filter; fail).
      
      Focus 2. rewrite Heqlsvi2.
        rewrite <- dom_sub_sub_filter.
        spcls. apply disjoint_remove_nvars.


      rewrite <- Xsf2eta. rewrite ssubst_aux_sub_filter2.
      rewrite <- Xsf1eta. rewrite ssubst_aux_sub_filter2.
      apply alpha_eq3_sym. unfold var_ren in XX;sp.

      * introv Hin. apply free_vars_ssubst_aux2 in Hin. 
      
          simpl_sub.
          dorn Hin;exrepnd; auto;[].
          apply in_var_ren in Hin0. exrepnd.
          subst. allsimpl. dorn Hin1;subst;try(sp;fail);[].
          apply Hfresh10;sp.

      * introv Hin. apply free_vars_ssubst_aux2 in Hin. 
      
          simpl_sub.
          dorn Hin;exrepnd; auto;[].
          apply in_var_ren in Hin0. exrepnd.
          subst. allsimpl. dorn Hin1;subst;try(sp;fail);[].
          apply Hfresh2;sp.

Qed.


  

Theorem ssubst_alpha3_congr_auxp: forall t1 t2 lvi lnt1 lnt2,
  alpha_eq3 [] t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars t2)
  -> bin_rel_nterm (alpha_eq3 [] ) lnt1 lnt2
  -> alpha_eq3 [] (ssubst_aux t1 (combine lvi lnt1)) (ssubst_aux t2 (combine lvi lnt2)).
Proof using.
  nterm_ind1s t1 as [v1 | o1 lbt1 Hind] Case; introv Hal H1len H2len H1dis H2dis Hall; inverts Hal as Hlen Hal.
  - Case "vterm". simpl.
    destructrn (sub_find (combine lvi lnt1) v1) as [s1s|n1n] H1sn;
    destructrn (sub_find (combine lvi lnt2) v1) as [s2s|n2n] H2sn; allsimpl;sp.
    + symmetry in HeqH2sn. symmetry in HeqH1sn.
      eapply sub_find_some2_first in HeqH1sn; eauto. exrepnd.
      repnud Hall.
      repnud Hall.
      assert(n < length lnt1) as Hlt by congruence.
      pose proof (Hall _ Hlt).
      rewrite nth_indep with (d' := vterm nvarx ) in HeqH1sn0; try(congruence).
      rewrite nth_indep with (d' := vterm nvarx ) in HeqH1sn4; try(congruence). 
    + provefalse. symmetry in  HeqH1sn. eapply sub_find_some_none_contra in HeqH1sn ; eauto.
    + provefalse. symmetry in  HeqH2sn. 
      eapply sub_find_some_none_contra with(lnt4:=lnt1) in HeqH2sn; eauto.

  - Case "oterm". simpl. constructor;
    repeat(rewrite map_length); auto.
    introv Hlt. rewrite selectbt_map; auto.
    duplicate Hlt. rewrite Hlen in Hlt0.
    rewrite selectbt_map; auto.
    fold (@ssubst_bterm_aux NVar _).
    applydup Hal in Hlt.
    clear Hal.
    pose proof (selectbt_in2 n lbt1 Hlt) as [bt99 pp].
    exrepnd. destruct bt99 as [blv1 bnt1].
    rewrite pp. rewrite pp in Hlt1.
    pose proof (selectbt_in2 n lbt2 Hlt0) as [bt99 p2p].
    exrepnd. destruct bt99 as [blv2 bnt2].
    rewrite p2p. rewrite p2p in Hlt1.
    simpl in H1dis, H2dis.
    eapply disjoint_lbt_bt2 in H1dis; eauto. repnd.
    eapply disjoint_lbt_bt2 in H2dis; eauto. repnd.
    apply ssubst_alphabt3_congr_auxp; allsimpl; spc; disjoint_reasoningv;[].
    introv. intros. eapply Hind with (nt:=bnt1); eauto.
Qed.

    

(**
Theorem ssubst_alpha3_congr_aux2: forall t1 t2 lvi lnt1 lnt2,
  alpha_eq3 [] t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars t2)
  -> bin_rel_nterm (alpha_eq3 []) lnt1 lnt2
  -> alpha_eq3 [] (ssubst t1 (combine lvi lnt1)) (ssubst t2 (combine lvi lnt2)).
Proof using.
  intros. change_to_ssubst_aux4.
  apply ssubst_alpha3_congr_auxp;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.
*)
Lemma bin_rel_list_le: forall {T} (R1 R2: bin_rel T) (def:T),
  (le_bin_rel R1 R2) -> le_bin_rel (binrel_list def R1) (binrel_list def R2).
Proof using.
  introv HR. intros la lb Hb1. repnud Hb1. split; sp.
Qed.

Lemma alpha3_le: forall lv, le_bin_rel alpha_eq (alpha_eq3 lv).
Proof using.
  introv. unfold le_bin_rel. intros. apply alpha_eq3_if;sp.
Qed.


Theorem ssubst_aux_alpha_congr: forall t1 t2 lvi lnt1 lnt2,
  alpha_eq t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars t2)
  -> bin_rel_nterm alpha_eq lnt1 lnt2
  -> alpha_eq (ssubst_aux t1 (combine lvi lnt1)) (ssubst_aux t2 (combine lvi lnt2)).
Proof using.
  intros. apply alpha_eq_if3 with (lv:=[]). apply ssubst_alpha3_congr_auxp;sp.
  apply alpha_eq3_if;sp. eapply bin_rel_list_le; eauto.
  apply alpha3_le.
Qed.





Lemma alphaeq_bterm_if3: forall bt1 bt2 lva,
  alpha_eq_bterm3 lva bt1 bt2
  -> alpha_eq_bterm bt1 bt2.
Proof using.
  introv Hal.  invertsna Hal Hal.
  apply al_bterm with (lv:=lv);spc; disjoint_reasoningv;[].
  change_to_ssubst_aux8.
  eauto with slow.
Qed.

Lemma ssubst_aux_alphabt_congr : forall bt1 bt2 lvi lnt1 lnt2,
  alpha_eq_bterm bt1 bt2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars_bterm bt1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars_bterm bt2)
  -> bin_rel_nterm (alpha_eq) lnt1 lnt2
  -> alpha_eq_bterm (ssubst_bterm_aux bt1 (combine lvi lnt1)) 
                    (ssubst_bterm_aux bt2 (combine lvi lnt2)).
Proof using.
  introns HH. apply alphaeq_bterm_if3 with (lva:=[]).
  apply alphaeq_bterm3_if with (lva:=[]) in HH.
  pose proof ssubst_alphabt3_congr_auxp as XX.
  unfold ssubst_alphabt3_congr_aux in XX.
  destruct bt1 as [lv1 nt1].
  eapply (bin_rel_list_le _ _ _  (alpha3_le [])) in HH4; eauto.
  apply XX; spc;[].
  introv. intros. apply ssubst_alpha3_congr_auxp;sp.
Qed.

Ltac dfresh_vars :=
match goal with
[|- context[ fresh_vars ?n ?lv]] =>
  let Hfr := fresh "Hfr" in 
  let lvn := fresh "lvn" in 
    destruct (fresh_vars n lv) as [lvn Hfr]
end.

Lemma alphaeqbt_nilv: forall nt1 bt2,
  alpha_eq_bterm (bterm [] nt1) bt2 
  -> {nt2 : NTerm $ bt2 = (bterm [] nt2) # alpha_eq nt1 nt2}.
Proof using.
  introv Hal.
  invertsna Hal Hal.
  unfold var_ren in Hal3.
  destruct lv2; inverts Hal0.
  allsimpl.
  repeat(rewrite ssubst_nil in Hal3).
  eexists; split; eauto.
Qed.

Lemma alphaeqbt_nilv2: forall nt1 nt2,
  alpha_eq_bterm (bterm [] nt1) (bterm [] nt2)
  <=> alpha_eq nt1 nt2.
Proof using.
  sp_iff Case.
  - Case "->". introv Halb.
    apply alphaeqbt_nilv in Halb.
    exrepnd.
    invertsn Halb1; trivial.
  - Case "<-". introv Halb.
    eapply al_bterm; eauto;
        [constructor | unfold var_ren; simpl; 
        repeat (rewrite ssubst_nil); trivial]; fail.
Qed.

Lemma ssubst_alphabt_congr : forall (bt1 bt2 : BTerm) (sub : Substitution),
  alpha_eq_bterm bt1 bt2
  -> disjoint (bound_vars_bterm bt1 ++ bound_vars_bterm bt2)
         (flat_map free_vars (range sub))
  -> alpha_eq_bterm (ssubst_bterm_aux bt1 sub) (ssubst_bterm_aux bt2 sub).
Proof using.
  intros. rewrite (sub_eta sub).
  apply ssubst_aux_alphabt_congr; spc; eauto with slow; disjoint_reasoningv;
  repeat setoid_rewrite map_length; auto.
  apply bin_rel_list_refl.
  unfold refl_rel. eauto with slow.
Qed.

Lemma btchange_alpha_ssubst_aux: forall lv nt lvn,
  length lv = length lvn 
  -> no_repeats lvn
  -> disjoint (all_vars nt) lvn
  -> alpha_eq_bterm (bterm lv nt) (bterm lvn (ssubst_aux nt (var_ren lv lvn))).
Proof using.
  introv Hlen Hdis Hnr.
  pose proof (fresh_vars (length lvn) (all_vars nt ++lvn)).
  exrepnd.
  rename lvn0 into lvnn.
  exists lvnn;auto; try congruence; disjoint_reasoningv; repeat(disjoint_ssubst);spcls; disjoint_reasoningv;[].
  setoid_rewrite ssubst_ssubst_aux at 2; [| simpl; 
      rewrite boundvars_ssubst_aux_vars; spcls ;disjoint_reasoningv].
  unfold var_ren at 3.
  rewrite ssubst_aux_nest_same; auto; spcls; auto; disjoint_reasoningv.
  setoid_rewrite ssubst_ssubst_aux; [| simpl; spcls; disjoint_reasoningv].
  apply alpha_eq_refl.  
Qed.

Lemma alpha_eq_bterm_congr : forall lv nt nt',
  alpha_eq nt nt'
  -> alpha_eq_bterm (bterm lv nt) (bterm lv nt').
Proof using.
  introv Hal.
  pose proof (fresh_vars (length lv) (all_vars nt ++ all_vars nt')) as Hfr.
  exrepnd.
  apply al_bterm with (lv:= lvn); spc; disjoint_reasoningv.
  change_to_ssubst_aux8.
  apply ssubst_aux_alpha_congr; auto; spcls; auto.
  apply bin_rel_list_refl.
  exact alpha_eq_refl.
Qed.

(** this characterization makes ssubst look like the old lsubst, and
  hence makes it posssible to 
  easily revive proofs which used to work for lsubst *)
Lemma ssubst_ssubst_aux_alpha_nb: forall sub,
  ((forall t,
  let ta := change_bvars_alpha (flat_map free_vars (range sub)) t in
  alpha_eq (ssubst t sub) (ssubst_aux ta sub))
  *
  (forall bt,
  let bta := change_bvars_alphabt (flat_map free_vars (range sub)) bt in
  alpha_eq_bterm (ssubst_bterm bt sub) (ssubst_bterm_aux bta sub))).
Proof using.
  simpl. intros. apply NTerm_BTerm_ind.
- simpl. intros. apply alpha_eq_refl.
- intros ? ? Hind. simpl. constructor; repeat rewrite map_length;
    [refl|].
  intros. rewrite map_map.
  repeat (rewrite selectbt_map;[|assumption]).
  unfold compose. apply Hind.
  apply selectbt_in. assumption.
- intros ? ? Hind. destruct lv as [| v lv].
  + simpl. unfold freshReplacements in *. simpl. addFreshVarsSpec2 lvn hfr. repnd. dlist_len_name lvn lv.
    simpl. unfold var_ren. simpl.
    autorewrite with SquiggleEq.
    apply alphaeqbt_nilv2.
    assumption.
  + unfold ssubst_bterm. remember (v :: lv) as lvv.
    subst lvv. generalize (v :: lv). intro lvv.
    Local Opaque ssubst_bterm_aux.
     simpl.
    addFreshVarsSpec2 lvn Hfr. repnd.
    cases_ifn Hd;[| apply alphaeqbt_refl].
    unfold all_vars in Hfr1.
    add_changebvar_spec ss Hdd. simpl.
    apply ssubst_alphabt_congr;[| simpl; 
      rewrite boundvars_ssubst_aux_vars; disjoint_reasoningv].
    disjoint_reasoningv.
    clear dependent sub.
    apply alpha_eq_bterm_congr with (lv:=lvv )in Hdd.
    eapply alpha_eq_bterm_trans;[apply Hdd|].
    apply btchange_alpha_ssubst_aux; auto.
    disjoint_reasoningv.
    Local Transparent ssubst_bterm_aux.
    
Qed.

(*
Print Assumptions ssubst_ssubst_aux_alpha_nb.
Section Variables:
gts : GenericTermSig
*)

Definition ssubst_ssubst_aux_alpha := fun s => fst (ssubst_ssubst_aux_alpha_nb s).
Definition ssubst_ssubst_bterm_aux_alpha := fun s => snd (ssubst_ssubst_aux_alpha_nb s).

Global Instance equivAlphaEq : Equivalence alpha_eq.
Proof using.
  constructor; eauto with core slow.
Qed.

Global Instance alphaGetOpid : Proper (alpha_eq ==> eq) getOpid.
Proof.
  intros ? ? Hal.
  inverts Hal; refl.
Qed.

Global Instance equivAlphaEqBterm : Equivalence alpha_eq_bterm.
Proof using.
  constructor; eauto with core slow.
- intros ? ?. apply alpha_eq_bterm_sym.
- intros ? ?. apply alpha_eq_bterm_trans.
Qed.

Require Import Morphisms.

Global Instance properAlphaSize : Proper (alpha_eq ==> eq) size.
Proof using.
 exact alpha_eq_preserves_size.
Qed.

Global Instance properAlphaAlphaBt : Proper (eq ==> alpha_eq ==> alpha_eq_bterm) bterm.
Proof using.
  intros ? ? ? ? ? ?.
  subst. apply alpha_eq_bterm_congr.
  assumption.
Qed.

Lemma ssubst_allvars_preserves_size : forall (nt : NTerm) sub,
    allvars_sub sub
   -> size (ssubst nt sub) = size nt.
Proof using varclass.

  introv Hav. rewrite ssubst_ssubst_aux_alpha.
  add_changebvar_spec nt' Hs.
  rewrite ssubst_aux_allvars_preserves_size; auto.
  repnd. rewrite Hs. refl.
Qed.

Lemma ssubst_allvars_preserves_size2 : forall (nt : NTerm) lvo lvn,
   size (ssubst nt (var_ren lvo lvn)) = size nt.
Proof using varclass.
  intros. apply ssubst_allvars_preserves_size.
  apply allvars_combine.
Qed.

Theorem alphaeq_preserves_free_vars: 
  forall t1 t2, alpha_eq  t1 t2 ->
     (free_vars t1) = (free_vars t2). 
Proof using.
nterm_ind1s t1 as [v1 | o lbt1 Hind] Case; introv Hal. 
  Case "vterm". inverts Hal as . reflexivity. 
  Case "oterm". inverts Hal as Hmap Hal. 
    simpl. repeat(rewrite flat_map_as_appl_map). f_equal. 
    apply eq_maps_bt; trivial. 
    introv Hlt.
    pose proof (Hal _ Hlt) as Haln. clear Hal.
    remember (selectbt lbt1 n) as bt1.
    remember (selectbt lbt2 n) as bt2.
    destruct bt1 as [lv1 nt1].
    destruct bt2 as [lv2 nt2].
    allsimpl. inverts Haln as Hi1 Hi2 Hi3 Hi4 Haln.
    apply selectbt_eq_in in Heqbt1; trivial.
    eapply Hind in Haln; eauto;
      [ | rewrite ssubst_allvars_preserves_size2; auto; fail].
     apply disjoint_app_r in Hi1. repnd.
     assert (length lv2 = length lv) by (rewrite <- Hi2; trivial).
    rewrite freevars_ssubst_allvars2 in Haln; auto.
    rewrite freevars_ssubst_allvars2 in Haln; auto.
    apply lmap_lapply_eq_implies in Haln; auto.
   unfold all_vars in *. rewrite disjoint_app_r in *. repnd.
   split; allrw disjoint_app_l; sp.
Qed.

Global Instance properAlphaFvars : Proper (alpha_eq ==> eq) free_vars.
  exact alphaeq_preserves_free_vars.
Qed.

     
Theorem alphaeq_preserves_closed: 
  forall t1 t2, alpha_eq  t1 t2 ->
     ((closed t1) <=> (closed t2)). 
Proof using.
  introv Hal. unfold closed.
  rewrite (alphaeq_preserves_free_vars _ _ Hal).
    apply t_iff_refl.
Qed.

Global Instance properAlphaClosed : Proper (alpha_eq ==> iff) closed.
  exact alphaeq_preserves_closed.
Qed.

Global Instance properAlphaNtwf : Proper (alpha_eq ==> iff) nt_wf.
  intros ? ? ?.
  apply alphaeq_preserves_wf; eauto with relations.
Qed.

Theorem alphaeq_preserves_program: 
  forall t1 t2, alpha_eq  t1 t2 ->
     ((isprogram t1) <=> (isprogram t2)). 
Proof using.
  introv Hal. unfold isprogram. rewrite Hal. tauto.
Qed.


Global Instance properAlphaProgram : Proper (alpha_eq ==> iff) isprogram.
  exact alphaeq_preserves_program.
Qed.


Lemma id_le_alpha: le_bin_rel (fun x y : NTerm => (x = y)) (alpha_eq).
Proof using.
  introv Heq. allsimpl. subst. eauto with slow.
Qed.

Hint Resolve sub_eta_length : slow.



Lemma alphaeqbt_1v: forall v1 nt1 bt2,
  alpha_eq_bterm (bterm [v1] nt1) bt2
  -> {v2, vn : NVar $
         {nt2: NTerm $ bt2 = bterm [v2] nt2
          # disjoint [vn] (all_vars nt1 ++ all_vars nt2)
          # alpha_eq (ssubst nt1 (var_ren [v1] [vn]))
                    (ssubst nt2 (var_ren [v2] [vn])) } }.
Proof using.
  introv Halb. invertsna Halb Halb.
  destruct lv as [| vn lv ]; invertsn Halb1.
  destruct lv; inverts Halb1.
  clear Halb2.
  destruct lv2 as [| v2 lv2 ]; invertsn Halb0.
  destruct lv2; inverts Halb0.
  repnd. 
  eexists; eauto.
Qed.

Lemma alphaeqbt_2v: forall b1v1 b1v2 nt1 bt2,
  alpha_eq_bterm (bterm [b1v1,b1v2] nt1) bt2
  -> {b2v1 ,b2v2, vn1, vn2 : NVar $
         {nt2: NTerm $ bt2 = bterm [b2v1, b2v2] nt2
          # no_repeats [vn1,vn2]
          # disjoint [vn1,vn2] (all_vars nt1 ++ all_vars nt2)
          # alpha_eq (ssubst nt1 (var_ren [b1v1, b1v2] [vn1, vn2]))
                    (ssubst nt2 (var_ren [b2v1, b2v2] [vn1, vn2])) } }.
Proof using.
  introv Halb. invertsna Halb Halb.
  destruct lv as [| vn1 lv ]; invertsn Halb1.
  destruct lv as [| vn2 lv ]; invertsn Halb1.
  destruct lv; inverts Halb1.
  destruct lv2 as [| bt2v1 lv2 ]; invertsn Halb0.
  destruct lv2 as [| bt2v2 lv2 ]; invertsn Halb0.
  destruct lv2; inverts Halb0.
  repeat(eexists; eauto).
Qed.





Ltac alphahypsd :=
  match goal with 
  | [H: 1 = length _ |- _ ] => symmetry in H; apply length1 in H; exrepnd; subst
  | [H: 2 = length _ |- _ ] => symmetry in H; apply length2 in H; exrepnd; subst
  | [H: 0 = length _ |- _ ] => symmetry in H; apply length0 in H; subst
  | [H: _ = S (length _) |- _ ] =>  inverts H as H
  | [H: (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _)  |- _ ] => 
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps); clear H
  | [H: alpha_eq_bterm (bterm [] _) (bterm [] _) |- _] => apply alphaeqbt_nilv2 in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_] _) _ |- _] => apply alphaeqbt_1v in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_,_] _) _ |- _] => apply alphaeqbt_2v in H; exrepnd; subst
  end.

Ltac alphahypdfv H :=
match type of H with
| (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _) => 
  (let XXX:= fresh H "0bt" in
  assert (0<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps);
  try (let XXX:= fresh H "1bt" in
  assert (1<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps);
  try (let XXX:= fresh H "2bt" in
  assert (2<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps); try (fail_if_not_number m; clear H)
end.

Ltac get_lt_rhs H :=
match type of H with
| _ < ?m => constr:m
end.

Ltac get_alphabt_hyp HH :=
let m:= get_lt_rhs HH in 
match goal with 
| [ H : (forall _ : nat, _ < m -> _) |- _ ] => constr:H
end.

Ltac prove_alpha_eq :=
match goal with 
| [ |- alpha_eq ?t ?t] => apply alpha_eq_refl
| [  |- alpha_eq (oterm ?o _) (oterm ?o _)] =>
      let Hlt := fresh "XXHlt" in
      let n := fresh "XXn" in
      constructor; [simpl; congruence| ];[]; unfold selectbt;
      simpl; intros n Hlt;
      ( let Hyp := (get_alphabt_hyp Hlt)  in 
        unfold selectbt in Hlt;
        repeat(destruct n; simpl;[apply alphaeqbt_nilv2; auto|];[]);auto;
        apply Hyp in Hlt; allsimpl; auto
      )
end. 

Ltac prove_alpha_eq2 :=
match goal with 
| [  |- alpha_eq (oterm ?o _) (oterm ?o _)] =>
      let Hlt := fresh "XXHlt" in
      let n := fresh "XXn" in
      constructor; [simpl; congruence| ];[]; unfold selectbt;
      simpl; intros n Hlt;
        repeat(destruct n;simpl;[apply alphaeqbt_nilv2; auto|];[]);auto;
      try ( let Hyp := (get_alphabt_hyp Hlt)  in 
        unfold selectbt in Hlt;
        apply Hyp in Hlt; allsimpl; auto
      ); cpx
end. 





Lemma change_bvars_alpha_wspec:
  forall lv nt, {ntcv : NTerm & disjoint lv (bound_vars ntcv) #alpha_eq nt ntcv}.
Proof using.
  introv. exists (change_bvars_alpha lv nt).
  apply change_bvars_alpha_spec.
Qed.



 

Definition listAlpha (t:NTerm):Type :=
  list {t':NTerm & alpha_eq t t'}.

Definition listAlphaRefl (t:NTerm): (listAlpha t) :=
  [existT _ t (alpha_eq_refl t)].

Definition listAlphaCons (t t2:NTerm) (p:alpha_eq t t2) (tl:listAlpha t)
    : (listAlpha t) :=
  (existT _ t2 p)::tl.



Ltac get_sndal list h :=
let list' := eval unfold listAlphaRefl in list in
let list'' := eval unfold listAlphaCons in list' in
match list'' with 
| [] => constr:(0)
| ((existT _ h ?p)::_) => constr:(p)
| (_::?t) => get_sndal t h
end.



Ltac alpha_equiv_aux list target :=
match goal with
| [ H : alpha_eq ?t1 target |- _ ] =>
    let p1 := (get_sndal list t1) in
      constr:(alpha_eq_trans _ _ _ p1 H)
| [ H : alpha_eq target ?t1 |- _ ] =>
    let p1 := get_sndal list t1 in
      constr:(alpha_eq_trans _ _ _ p1 (alpha_eq_sym _ _ H))
| [ H : alpha_eq ?t1 ?t2 |- _ ] =>
 (
  let SS:= get_sndal list t2 in
  match SS with
  | 0 => 
    let p1 := get_sndal list t1 in
    let nlist:= constr:(listAlphaCons _ t2 (alpha_eq_trans _ _ _ p1 H) list) in
       alpha_equiv_aux nlist target
  | _ => 
    let SSS:= get_sndal list t1 in
      match SSS with
      | 0 => 
        let p1 := get_sndal list t2 in
        let nlist:= constr:(listAlphaCons _
            t1 (alpha_eq_trans _ _ _ p1 (alpha_eq_sym _ _ H)) list) in
           alpha_equiv_aux nlist target
      | _ => constr:(cons 0 "asdf")
      end
  end)

end.

Ltac alpha_equiv :=
match goal with
| [ |- alpha_eq ?t1 ?t1 ] => apply alpha_eq_refl
| [ |- alpha_eq ?t1 ?t2 ] => 
  let prf:= (alpha_equiv_aux (listAlphaRefl t1) t2) in
  exact prf
end.

(** % \noindent \\* %
    In the following theorem, 
    the binary relation [(bin_rel_nterm alpha_eq)] on [list NTerm]
    asserts that the lists have equal length and 
    the members are respectively alpha equal.

*)
Theorem ssubst_alpha_congr: forall t1 t2 lvi lnt1 lnt2,
  alpha_eq t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> bin_rel_nterm alpha_eq lnt1 lnt2
  -> alpha_eq (ssubst t1 (combine lvi lnt1)) (ssubst t2 (combine lvi lnt2)).
Proof using.
  introv Hal H1l H2l  Hbr.
  do 2 rewrite ssubst_ssubst_aux_alpha.
  add_changebvar_spec c1b H1s; repnd. add_changebvar_spec c2b H2s; repnd.
  apply ssubst_aux_alpha_congr; spc;spcls; disjoint_reasoningv.
    alpha_equiv.
Qed.

Corollary ssubst_alpha_congr2: forall t1 t2 sub,
  alpha_eq t1 t2
  -> alpha_eq (ssubst t1 sub) (ssubst t2 sub).
Proof using.
  intros. 
  pose proof (split_combine sub) as XX.
  pose proof (split_length_eq sub) as XL. repnd.
  destruct (split sub) as [lv lnt]. allrw <- XX. GC.
  apply ssubst_alpha_congr;sp.
  apply bin_rel_list_refl.
  exact alpha_eq_refl.
Qed.

Ltac get_alpha_lhs H :=
match type of H with
| alpha_eq  ?m _ => constr:m
end.

Lemma symmetricSubRangeRel (R:NTerm -> NTerm -> Prop) : 
  Symmetric R -> Symmetric (@sub_range_rel NVar Opid R).
Proof using.
  intro Hsm. intro a.
  induction a; intros b Hs;destruct b; try inverts Hs; sp.
  simpl in Hs. repnd. subst.
  constructor; eauto.
Qed.

Lemma transisitiveSubRangeRel (R:NTerm -> NTerm -> Prop) : 
   Transitive R -> Transitive (@sub_range_rel NVar Opid R).
Proof using.
  intro Hsm. intro a.
  induction a; intros b c H1s H2s ;destruct b; destruct c; try inverts Hs; cpx.
  simpl in *. repnd. subst.
  constructor; eauto.
Qed.

Global Instance equivAlphaEqSub : Equivalence (sub_range_rel alpha_eq).
Proof using.
  constructor.
  - apply sub_range_refl. eauto with slow. exact alpha_eq_refl.
  - apply @symmetricSubRangeRel. eauto with slow.
  - apply transisitiveSubRangeRel. eauto with slow.
Qed.

Lemma sub_range_rel_as_list : forall R subl subr, sub_range_rel R subl subr
  -> {lv : list NVar $ { lntl,lntr : list NTerm $ length lv = length lntl 
        # length lv = length lntr 
        # subl = combine lv lntl
        # subr = combine lv lntr 
        # bin_rel_nterm R lntl lntr
            }}.
Proof using.
  induction subl as [ |(vl,tl) subl Hind]; introv Hsr; allsimpl;
  destruct subr as [ |(vr,tr) subr]; try invertsn Hsr.
  - repeat (apply ex_intro with ( x:=nil)); dands; spc. apply binrel_list_nil.
  - repnd. apply Hind in Hsr. exrepnd.
    exists (vr::lv) (tl::lntl) (tr::lntr).
    allsimpl. dands; f_equal; spc.
    apply binrel_list_cons; spc.
Qed.

Lemma sub_rel_alpha_prop : forall subl subr,
  sub_range_rel alpha_eq subl subr
  -> forall t, alpha_eq (ssubst t subl) (ssubst t subr).
Proof using.
  introv Hs. intro t.
  apply sub_range_rel_as_list in Hs.
  exrepnd.
  rw Hs4.
  rw Hs3.
  apply ssubst_alpha_congr; spc.
Qed.

Global Instance properAlphaLSubst : 
  Proper (alpha_eq ==> (sub_range_rel alpha_eq) ==> alpha_eq) ssubst.
Proof using.
  intros ? ? Heq s1 s2 Hs.
  unfold subst.
  apply sub_rel_alpha_prop with (t:= x) in Hs.
  apply ssubst_alpha_congr2  with (sub:=s2)  in Heq.
  eauto with slow.
Qed.


Lemma sub_range_rel_sub_find: forall R s1 s2 (v:NVar) (t1: NTerm),
sub_range_rel R s1 s2
-> sub_find s1 v = Some t1
-> exists t2, sub_find s2 v = Some t2 /\ R t1 t2.
Proof using.
  intros ? ? ? ? ?.
  revert s2.
  induction s1; intros ? Hr Hf; destruct s2; simpl in *; cpx.
  destruct p. destruct a. simpl in *.
  repnd. subst. destruct (beq_var n v); eauto.
  inverts Hf. eexists; eauto.
Qed.

Lemma sub_range_rel_sub_none: forall R (s1 s2 : Substitution) (v:NVar),
sub_range_rel R s1 s2
-> sub_find s1 v = None
-> sub_find s2 v = None.
Proof using.
  intros ? ? ? ?.
  revert s2.
  induction s1; intros ? Hr Hf; destruct s2; simpl in *; cpx.
  destruct p. destruct a. simpl in *.
  repnd. subst. destruct (beq_var n v); eauto.
  inverts Hf. (* same as above proof *)
Qed.


Lemma sub_range_rel_sub_filter: forall R (s1 s2 : Substitution) (lv: list NVar),
sub_range_rel R s1 s2
-> sub_range_rel R (sub_filter s1 lv) (sub_filter s2 lv).
Proof using.
  intros ? ? ? ?.
  revert s2.
  induction s1; intros ? Hf; destruct s2; simpl in *; cpx.
  destruct p. destruct a. simpl in *.
  repnd. subst. destruct (memvar n lv); eauto.
  eexists; eauto.
Qed.

Lemma alpha_eq_map_bt {T}: forall o (f g : T -> BTerm) lbt,
  (forall b, In b lbt -> alpha_eq_bterm (f b) (g b))
  -> alpha_eq (oterm o (map f lbt)) (oterm o (map g lbt)).
Proof using.
  intros ? ? ? ? Hbt.
  constructor;repeat rewrite map_length in *; [refl |].
  intros ? Hin. pose proof Hin as Hinb.
  apply nth_error_Some in Hin.
  remember (nth_error lbt n) as nn.
  unfold selectbt.
  destruct nn as [b|]; cpx;[]. clear Hin.
  do 2 rewrite map_nth2 with (d:=b) by assumption.
  apply nth_select1 with (def:=b) in Hinb.
  setoid_rewrite <- Heqnn in Hinb.
  symmetry in Heqnn. apply nth_error_In in Heqnn.
  apply Hbt in Heqnn. clear Hbt. invertsn Hinb.
  do 2 rewrite <- Hinb. assumption.
Qed.

Lemma subst_aux_alpha_sub:
(forall (t : NTerm) (s2 s1 : Substitution),
sub_range_rel alpha_eq s1 s2 
  -> alpha_eq (ssubst_aux t s1) (ssubst_aux t s2))
*
(forall (t : BTerm) (s2 s1 : Substitution),
sub_range_rel alpha_eq s1 s2 
  -> alpha_eq_bterm (ssubst_bterm_aux t s1) (ssubst_bterm_aux t s2)).
Proof using.
  apply NTerm_BTerm_ind.
- intros v ? ? Hs. 
  simpl. dsub_find ss; symmetry in Heqss.
  + eapply sub_range_rel_sub_find in Heqss; eauto.
    exrepnd. rewrite Heqss1. assumption.
  + eapply sub_range_rel_sub_none in Heqss; eauto.
    rewrite Heqss. refl.
- intros ? ? Hind ? ? ?. simpl.
  apply alpha_eq_map_bt. eauto.
- intros ? ? Hind ? ? Hs. simpl.
  apply alpha_eq_bterm_congr.
  apply Hind. apply sub_range_rel_sub_filter.
  assumption.
Qed.


Global Instance properAlphaLSubstAux : 
  Proper (eq ==> (sub_range_rel alpha_eq) ==> alpha_eq) ssubst_aux.
Proof using.
  intros ? ? ? ? ?. subst.
  apply (fst subst_aux_alpha_sub).
Qed.

Global Instance properAlphaLSubstAuxBterm : 
  Proper (eq ==> (sub_range_rel alpha_eq) ==> alpha_eq_bterm) ssubst_bterm_aux.
Proof using.
  intros ? ? ? ? ?. subst.
  apply (snd subst_aux_alpha_sub).
Qed.


Ltac alpharw H := let X99:= fresh "Xalrw" in
let lhs := get_alpha_lhs H in
match goal with 
| [ |- alpha_eq (ssubst (ssubst lhs ?sub1) ?sub2) ?rhs] => 
    pose proof  (ssubst_alpha_congr2 _ _ sub2 (ssubst_alpha_congr2 _ _ sub1 H)) as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- alpha_eq (ssubst lhs ?sub) ?rhs] => pose proof  (ssubst_alpha_congr2 _ _ sub H) as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- alpha_eq lhs ?rhs ] => pose proof H as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- context [ free_vars lhs ] ] => 
    pose proof (alphaeq_preserves_free_vars _ _ H) as X99;
    rewrite X99; clear X99
| [ |- context [ free_vars (ssubst lhs ?sub) ] ] => 
    pose proof (alphaeq_preserves_free_vars _ _ ((ssubst_alpha_congr2 _ _ sub H))) as X99;
    rewrite X99; clear X99
| [ |- context[isprogram lhs] ] => 
  rw (alphaeq_preserves_program _ _ H)
end.


Ltac alpharws H :=
    repeat (alpharw H || (apply alpha_eq_sym; alpharw H; apply alpha_eq_sym)).

Ltac alpharw_rev H :=
  let H' :=  constr:(alpha_eq_sym _ _ H) in
  alpharws H'.

Ltac alpharwh H Hyp:=
let lhs := get_alpha_lhs H in
match goal with 
[ Hyp: alpha_eq (ssubst lhs ?sub) ?rhs |- _] => pose proof  (ssubst_alpha_congr2 _ _ sub H) as X99;
    apply alpha_eq_sym in X99;apply alpha_eq_trans with (nt3:=rhs)  in X99;sp;[];
    clear Hyp; rename X99 into Hyp
| [ Hyp: context [ free_vars lhs ] |- _ ] => 
    pose proof (alphaeq_preserves_free_vars _ _ H) as X99;
    rewrite X99 in Hyp; clear X99
| [ Hyp:context [ free_vars (ssubst lhs ?sub) ] |- _ ] => 
    pose proof (alphaeq_preserves_free_vars _ _ ((ssubst_alpha_congr2 _ _ sub H))) as X99;
    rewrite X99 in Hyp; clear X99
end.

Ltac alpharwhs H Hyp:=
   repeat  (alpharwh H Hyp|| (apply alpha_eq_sym in Hyp; alpharwh H Hyp;apply alpha_eq_sym in Hyp)).



Theorem apply_bterm_alpha_congr: forall bt1 bt2 lnt1 lnt2,
  alpha_eq_bterm bt1 bt2
  -> bin_rel_nterm alpha_eq lnt1 lnt2 (*enforces that the lengths are equal*)
  -> length lnt1 = num_bvars bt1 (*only required for simplicity*)
  -> alpha_eq (apply_bterm bt1 lnt1) (apply_bterm bt2 lnt2).
Proof using.
  introv Hal Hbr Hl. unfold apply_bterm.
  destruct bt1 as [lv1 nt1]. destruct bt2 as [lv2 nt2];allsimpl.
  invertsna Hal Hal. 
  remember (change_bvars_alpha (lv++(flat_map free_vars lnt1)) nt1) as X99.
  revert HeqX99. add_changebvar_spec nt1' Hnt1'. intro H99. clear dependent X99.
  repnd. clear Heqnt1'.
  remember (change_bvars_alpha (lv++(flat_map free_vars lnt2)) nt2) as X99.
  revert HeqX99. add_changebvar_spec nt2' Hnt2'. intro H99. clear dependent X99.
  repnd. clear Heqnt2'.
  unfold num_bvars in Hl. allsimpl. duplicate Hbr.
  destruct Hbr as [Hll X99]. clear X99. 
  alpharws Hnt1'. alpharws Hnt2'.
  alpharwh Hnt1' Hal3.
  alpharwhs Hnt2' Hal3.
  eapply ssubst_alpha_congr with (lvi:=lv) in Hal3; eauto.
  Focus 2. spc;fail. Focus 2. spc;fail.
  
  rewrite ssubst_nest_same in Hal3; spc; spcls;disjoint_reasoningv.
  - rewrite ssubst_nest_same in Hal3; spc; spcls;disjoint_reasoningv.
    alpharw_rev  Hnt2'. trivial.
  - alpharw_rev  Hnt1'. trivial.
Qed.


Theorem apply_bterm_alpha_congr2: forall bt1 bt2 lnt,
  alpha_eq_bterm bt1 bt2
  -> length lnt = num_bvars bt1 (*only required for simplicity*)
  -> alpha_eq (apply_bterm bt1 lnt) (apply_bterm bt2 lnt).
Proof using.
  intros.
  apply apply_bterm_alpha_congr; auto.
  apply bin_rel_list_refl.
  exact alpha_eq_refl.
Qed.

Lemma ssubst_nt_wf :
  forall t sub,
    nt_wf (ssubst t sub)
    -> nt_wf t.
Proof using varclass.
  introv. rewrite ssubst_ssubst_aux_alpha.
  add_changebvar_spec t' Hs. repnd. rw <- (alphaeq_preserves_wf _ _ Hs).
  apply ssubst_aux_nt_wf.
Qed.


Lemma ssubst_wf_iff: 
  forall sub, 
  wf_sub sub
  -> forall nt, (nt_wf nt <=> nt_wf (ssubst nt sub)).
Proof using varclass.
 introv sr. intro. rewrite ssubst_ssubst_aux_alpha.
 add_changebvar_spec nt' Hs.
 rw <- (ssubst_aux_wf_iff _ sr).
 repnd. rewrite Hs. refl.
Qed.


Theorem ssubst_wf_if_eauto: 
  forall sub, 
  wf_sub sub
  -> forall nt, (nt_wf nt -> nt_wf (ssubst nt sub)).
Proof using varclass.
   apply ssubst_wf_iff.
Qed.

Hint Resolve ssubst_wf_if_eauto : slow.
Hint Immediate wf_sub_vars.
Hint Resolve  ssubst_wf_iff: slow.

Theorem ssubst_wf_iff_vars: 
  forall lvi lvo nt, (nt_wf nt <=> nt_wf (ssubst nt (var_ren lvi lvo))).
Proof using varclass. intros. eauto with slow.
Qed.

Theorem ssubst_wf_if_vars_eauto: 
  forall lvi lvo nt, (nt_wf nt -> nt_wf (ssubst nt (var_ren lvi lvo))).
Proof using varclass. apply ssubst_wf_iff_vars; sp.
Qed.


Hint Resolve ssubst_wf_if_vars_eauto: slow.
Lemma ssubst_preserves_wf_term :
  forall sub t,
    wf_sub sub
    -> wf_term t
    -> wf_term (ssubst t sub).
Proof using varclass.
  introv ws wt.
  generalize (ssubst_wf_iff sub ws t); intro i.
  repeat (rewrite nt_wf_eq in i).
  rewrite <- i; sp.
Qed.

Lemma ssubst_wf_term :
  forall sub t,
    wf_term (ssubst t sub)
    -> wf_term t.
Proof using varclass.
  introv wf; allrw <- (@nt_wf_eq NVar Opid).
  apply ssubst_nt_wf in wf; sp.
Qed.

(** takes H which is of the form alpha_eq t1 t2
    and adds to context some properties about t2 
    see add_changebvar_spec2 for a usecase *)
Ltac alpha_hyps H :=
let lhs := get_alpha_lhs H in
(repeat match goal with 
| [ HH: isprogram lhs |- _ ] =>
      (let Hd := fresh "H_alpha_hypsp" in 
        pose proof ((tiff_fst (alphaeq_preserves_program _ _ H) HH)) as Hd;
       apply hide_hyp in HH)
| [ HH: closed lhs |- _ ] =>
      (let Hd := fresh "H_alpha_hypsc" in 
        pose proof ((tiff_fst (alphaeq_preserves_closed _ _ H) HH)) as Hd;
        apply hide_hyp in HH)
| [ HH: nt_wf lhs |- _ ] =>
      (let Hd := fresh "H_alpha_hypsw" in 
        pose proof ((tiff_snd (alphaeq_preserves_wf _ _ H) HH)) as Hd;
        apply hide_hyp in HH)
end ); allrw <- hide_hyp.


Ltac add_changebvar_spec2 cb Hn:=
match goal with 
| [ |- context[change_bvars_alpha ?lv ?nt] ] => pose proof (change_bvars_alpha_spec nt lv) as Hn;
    remember (change_bvars_alpha  lv nt) as cb; simpl in Hn; (
    let Hl := fresh Hn "l" in
    let Hr := fresh Hn "r" in
    try (destruct Hn as [Hl Hr];
     alpha_hyps Hr))
end.

Lemma ssubst_sub_wf:
  forall sub1 sub2,
    wf_sub sub1
    -> wf_sub sub2
    -> wf_sub (ssubst_sub sub1 sub2).

Proof using varclass.
  induction sub1 as [|(v,t) sub Hind]; introv H1wf H2wf; allsimpl;sp;[].
  rw cons_as_app. apply sub_app_sat;rw cons_as_app in H1wf; apply sub_app_sat_if in H1wf;sp.
  - unfold sub_range_sat in *. introv Hin. apply in_single in Hin. inverts Hin.
    apply ssubst_wf_iff;sp. pose proof (H1wf0 _ _ (or_introl _ (eq_refl _))). sp.
  - apply Hind;sp.
Qed.

Ltac alpha_refl_tac :=
match goal with
[ |- alpha_eq ?t1 ?t2 ] => let eq := fresh "Halrefleq" in 
  assert (t1=t2) as eq;[| rw eq; apply alpha_eq_refl;fail]
end.


Theorem free_vars_ssubst2:
  forall nt sub,
    forall v,
         LIn v (free_vars (ssubst nt sub))
         -> LIn v (free_vars nt)
                [+] {v' : NVar
                     $ {t : NTerm
                     $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof using varclass.
  introns XX. revert XX.
  rewrite ssubst_ssubst_aux_alpha.
  add_changebvar_spec2 nt' XX. alpharw XXr. 
  apply free_vars_ssubst_aux;try(sp;fail).
  try(setoid_rewrite disjoint_sub_as_flat_map;disjoint_reasoningv).  
Qed.

Lemma disjoint_free_vars_ssubst2:
  forall (nt : NTerm) (sub : Substitution) lvdr,
   disjoint (free_vars nt ++ (flat_map free_vars (range sub))) lvdr
  -> disjoint (free_vars (ssubst nt sub)) lvdr.
Proof using varclass.
  introv H2dis.
  introv Hin Hc.
  apply free_vars_ssubst2 in Hin.
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. setoid_rewrite <- disjoint_sub_as_flat_map in H2dis.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.

Lemma ssubst_sub_disjoint_bv2:
  forall sub1 sub2 (nt:NTerm),
    disjoint_bv_sub nt sub1
    -> disjoint_bv_sub nt sub2
    -> disjoint_bv_sub nt (ssubst_sub sub1 sub2).
Proof using varclass.
  induction sub1 as [|(v,t) sub Hind]; introv H1wf H2wf; allsimpl;sp;[].
  rw cons_as_app. apply sub_app_sat;rw cons_as_app in H1wf; apply sub_app_sat_if in H1wf;sp.
  - unfold sub_range_sat in *. introv Hin. apply in_single in Hin. inverts Hin.
    remember [(v,t)] as vt. 
    rewrite ssubst_ssubst_aux_alpha.
    add_changebvar_spec2 t' XX. disjoint_flat. allrw Heqvt. clear Heqvt.
    apply alpha_eq_sym in XXr.
    rewrite <- ssubst_ssubst_aux;[| spcls; disjoint_reasoningv];[].
    alpharw XXr.
    apply disjoint_free_vars_ssubst2; disjoint_flat;disjoint_reasoningv.
  - apply Hind;sp.
Qed.

Lemma combine_1var_sub:
  forall t sub1 sub2,
    allvars_sub sub1
    -> alpha_eq (ssubst (ssubst t sub1) sub2) (ssubst t (ssubst_sub sub1 sub2 ++ sub2)).
Proof using.
  (** change t to t' such that t' will never cause renaming.
      naive case split
    proof gives 8 non-trivial cases(2 for each ssubst) *)
  introv Hv.
  pose proof (get_sub_dom_vars_eta _ Hv) as Hs. exrepnd.
  rw Hs0. pose proof (change_bvars_alpha_spec t
       (lvo++(flat_map free_vars (range sub2)))) as Hfr.
  allsimpl. repnd. 
  remember (change_bvars_alpha (lvo ++ flat_map free_vars (range sub2)) t) as t'.
  alpharws Hfr.
  change_to_ssubst_aux8.
  - rename d into Hild. alpha_refl_tac.
    apply ssubst_aux_app; disjoint_flat; spcls; disjoint_reasoningv.
  - apply disjoint_sym. setoid_rewrite <- disjoint_sub_as_flat_map. 
    apply sub_app_sat;[| disjoint_flat; disjoint_reasoningv].
    apply ssubst_sub_disjoint_bv2;
    disjoint_flat; spcls; disjoint_reasoningv.
  - fold (@var_ren NVar Opid lvi lvo). 
    rewrite boundvars_ssubst_aux_vars;spc; spcls; disjoint_reasoningv.
Qed.

Lemma combine_1var_sub_wspec:
  forall sub1 sub2,
  allvars_sub sub1
  -> wf_sub sub2
  -> {sub3 : Substitution $ wf_sub sub3 # 
        forall t,alpha_eq (ssubst (ssubst t sub1) sub2) (ssubst t sub3)}.
Proof using.
  introv Hv Hw.
  pose proof (get_sub_dom_vars_eta _ Hv) as Hs. exrepnd.
  exists ((ssubst_sub sub1 sub2) ++ sub2). split.
  - apply sub_app_sat;sp. apply ssubst_sub_wf;sp;[]. 
    rw Hs0. apply wf_sub_vars.
  - intro nt. apply combine_1var_sub;sp.
Qed.

Lemma ssubst_trim_alpha:
forall t sub,
  alpha_eq (ssubst t sub) (ssubst t (sub_keep_first sub (free_vars t))).
Proof using.
  introv.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub)
    ++ flat_map free_vars (range (sub_keep_first sub (free_vars t)))) t) as Hfr.
  exrepnd. alpharw Hfr0. apply alpha_eq_sym. alpharw Hfr0.
  apply alpha_eq_sym.
  alpha_refl_tac.
  change_to_ssubst_aux8.
  alpharw Hfr0. apply ssubst_aux_trim.
  disjoint_flat. disjoint_reasoningv.
Qed.

Ltac ssubst_trim_alpha_tac :=
match goal with
[ |- context[ssubst ?t ?sub] ] => 
  alpharw (ssubst_trim_alpha t sub)
end.

(** The following lemma characterizes the free variables of the result of
    a substitution as a set. [eqsetv] is a binary relation on
    [list NVar] that asserts that the 2 lists are equal as sets.
    [sub_keep_first sub lv] filters the [Substitution] [sub] so as to keep only
    the first occurence of pairs whose domain is in [lv].

 *)
Lemma eqsetv_free_vars_disjoint :
  forall t : NTerm,
  forall sub : Substitution,
    eq_set (free_vars (ssubst t sub))
              (remove_nvars (dom_sub sub) (free_vars t)
               ++ sub_free_vars (sub_keep_first sub (free_vars t))).
Proof using varclass.
  introv. 
  pose proof (change_bvars_alpha_wspec 
      (flat_map free_vars (range sub)) t) as Hfr.
  exrepnd. alpharw Hfr0. alpharw Hfr0.
  change_to_ssubst_aux8.
  apply eqsetv_free_vars_disjoint_aux;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.

(*
Lemma prog_ssubst_app : forall nt sub sub2,
  prog_sub sub2
  -> disjoint (free_vars (ssubst nt sub)) (dom_sub sub2)
  -> ssubst nt sub = ssubst nt (sub++sub2).
Proof using.
  introv Hpr Hdis. 
  destruct nt. 
- do 2 rewrite ssubst_vterm. admit.
- simpl. f_equal. apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  simpl.
  rewrite ssubst_ssubst_aux_alpha at 2.
  intros
  rewrite ssubst_ssubst_aux_alpha.
  unfold ssubst at 1.
  simpl. cases_ifn ds.
  - change_to_ssubst_aux4. introv H1dis.
    + apply prog_ssubst_aux_app;sp; disjoint_flat;disjoint_reasoningv.
    + rw range_app. rw flat_map_app. change_to_ssubst_aux4.
      disjoint_reasoningv.
  - add_changebvar_spec2 nt' Hnt'. introv Hdis.
    repnd. unfold ssubst. rw range_app. rw flat_map_app.
    rw (prog_sub_flatmap_range _ Hpr). simpl_vlist.
    cases_ifn dsr; sp;[].
    rw <- Heqnt'.
    apply prog_ssubst_aux_app;sp; disjoint_flat;disjoint_reasoningv.
Qed.

Lemma prog_ssubst_app2 : forall nt sub sub2,
  isprogram (ssubst nt sub)
  -> prog_sub sub2
  -> ssubst nt sub = ssubst nt (sub++sub2).
Proof using.
  introv H1dis Hpr.
  apply prog_ssubst_app;sp.
  rw (proj1 H1dis). disjoint_reasoning.
Qed.
*)

Lemma ssubst_trim2_alpha1:
  forall a b sub,
  isprogram (ssubst a sub)
  -> isprogram (ssubst b sub)
  -> let sub':= (sub_keep_first sub (free_vars a ++ free_vars b)) in
     alpha_eq (ssubst a sub) (ssubst a sub')
     # alpha_eq (ssubst b sub) (ssubst b sub').
Proof using.
  introv H1pr H2pr. simpl.
  dands;try(apply alpha_eq_sym; ssubst_trim_alpha_tac;
    rewrite sub_keep_first_nest;[
    apply alpha_eq_sym; apply ssubst_trim_alpha; fail| introv; rw in_app_iff; cpx]).
Qed.

Lemma ssubst_trim2_alpha2:
  forall a b sub,
  wf_sub sub (* can be removed for a more complicated proof *)
  -> isprogram (ssubst a sub)
  -> isprogram (ssubst b sub)
  -> prog_sub (sub_keep_first sub (free_vars a ++ free_vars b)).
Proof using varclass.
  introv Hwfs Hapr Hbpr.
  inverts Hapr as Hacl X99. clear X99.
  inverts Hbpr as Hbcl X99. clear X99.
  unfold closed in *.
  pose proof (eqsetv_free_vars_disjoint a sub) as Xaeq.
  rw Hacl in Xaeq. apply eq_vars_nil in Xaeq.
  simpl_vlist.
  pose proof (eqsetv_free_vars_disjoint b sub) as Xbeq.
  rw Hbcl in Xbeq. apply eq_vars_nil in Xbeq.
  simpl_vlist.
  clear Xbeq0 Xaeq0 Hbcl Hacl.
  apply sub_keep_first_sat with (lv:= free_vars a ++ free_vars b) in Hwfs.
  introv Hin. applydup Hwfs in Hin. split;sp;[].
  clear Hwfs Hin0.
  apply in_sub_keep_first_app in Hin.
  unfold closed.
  remember (free_vars t) as ft.
  destruct ft as [| vt ft ];spcf.
  assert (LIn vt (free_vars t)) by (rw <- Heqft; cpx).
  clear Heqft.
  dorn Hin.
  - assert (LIn vt (sub_free_vars (sub_keep_first sub (free_vars a)))) as HX;
    [|rw Xaeq in HX;  cpx].
    apply in_sub_free_vars_iff. eexists; eauto.
  - assert (LIn vt (sub_free_vars (sub_keep_first sub (free_vars b)))) as HX;
    [|rw Xbeq in HX;  cpx].
    apply in_sub_free_vars_iff. eexists; eauto.
Qed.


Lemma ssubst_boundvars_varclass_nb: forall (vc : VarClass) (sub: Substitution),
 (varsOfClass (flat_map bound_vars (range sub)) vc)
 -> 
 (forall nt : NTerm, varsOfClass (bound_vars nt) vc -> varsOfClass (bound_vars (ssubst nt sub)) vc) *
 (forall bt : BTerm,
   varsOfClass (bound_vars_bterm bt) vc -> varsOfClass (bound_vars_bterm (ssubst_bterm bt sub)) vc).
Proof using varclass.
  simpl. intros ? ? Hvc. apply NTerm_BTerm_ind.
- intro. rewrite ssubst_vterm. intros Hv.
  eapply lforall_subset;
    [apply boundvars_ssubst_aux_subset|].
  simpl in *. exact Hvc.

- intros ? ? Hind.
  simpl. fold @ssubst_bterm.
  rewrite flat_map_map.
  apply lforall_flatmap.
  exact Hind.

- intros ? ? Hind. destruct lv as [| v lv];
    [simpl; fold @ssubst; assumption|].
  unfold ssubst_bterm. remember (v :: lv) as lvv.
  subst lvv. generalize (v :: lv). intro lvv.
  Local Opaque ssubst_bterm_aux change_bvars_alphabt.
  simpl.
  cases_ifn Hd; clear Hd; intros Hin;
    (eapply lforall_subset;[apply boundvars_ssubst_bterm_aux_subset|]);
    setoid_rewrite varsOfClassApp; simpl;
    repeat rewrite varsOfClassApp;
    repeat rewrite varsOfClassApp in Hin; [tauto|].
 
  split;[|assumption].
  apply change_bvars_alpha_spec_varclass.
  simpl.
  repeat rewrite varsOfClassApp.
  assumption.
  Local Transparent ssubst_bterm_aux change_bvars_alphabt.
Qed.

Lemma ssubst_allvars_varclass_nb: forall
 (vc : VarClass) (sub: Substitution) nt,
 (varsOfClass (all_vars nt ++ (flat_map all_vars (range sub))) vc)
 -> varsOfClass (all_vars (ssubst nt sub)) vc.
Proof using varclass.
  intros ? ? ?.
  unfold all_vars.
  repeat rewrite varsOfClassApp.
  unfold varsOfClass.
  rewrite flat_map_fapp.
  rewrite eqsetv_free_vars_disjoint.
  rewrite lforallApp.
  intros Hin.
  repnd.
  split;[|apply ssubst_boundvars_varclass_nb; assumption].
  apply lforallApp.
  split.
- eapply lforall_subset.
  apply subsetv_remove_nvars.
  apply subset_app_r.
  apply subset_refl.
  assumption.
- intros ? Hinn.
  apply Hin1.
  revert Hinn. clear.
  intros. apply in_sub_free_vars in Hinn.
  exrepnd.
  apply in_sub_keep_first in Hinn0.
  repnd.
  apply sub_find_some in Hinn2.
  setoid_rewrite flat_map_map.
  apply in_flat_map.
  eexists.
  split;[apply Hinn2|].
  unfold compose. simpl. assumption.
Qed.

Lemma change_bvars_alpha_wspec_ot:
  forall lv (o : Opid) (lbt : list BTerm) , 
    {lbtcv : (list BTerm) $ disjoint lv (bound_vars (oterm o lbtcv)) # alpha_eq (oterm o lbt) (oterm o lbtcv)}.
Proof using.
  introv. pose proof (change_bvars_alpha_wspec lv (oterm o lbt)) as Hcv.
  exrepnd. duplicate Hcv0. destruct ntcv; inverts Hcv0.
  exists l;sp.
Qed.

Lemma ssubst_sub_filter_alpha:
  forall (t : NTerm) (sub : Substitution) (l : list NVar),
  disjoint (free_vars t) l 
  -> alpha_eq (ssubst t (sub_filter sub l)) (ssubst t sub).
Proof using.
  introv Hdis.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub)) t) as Hft.
  exrepnd.
  alpharws Hft0.
  alpharwh Hft0 Hdis.
  alpha_refl_tac.
  apply ssubst_sub_filter2;sp;[];
  disjoint_flat;sp;fail.
Qed.

Ltac prove_alpha_eq3 :=
match goal with 
| [  |- alpha_eq (oterm ?o _) (oterm ?o _)] =>
      let Hlt := fresh "XXHlt" in
      let n := fresh "XXn" in
      constructor; [simpl; congruence| ];[]; unfold selectbt;
      simpl; intros n Hlt;
        repeat(destruct n;simpl;try(omega);try(apply alphaeqbt_nilv2;auto)); auto;
      try ( let Hyp := (get_alphabt_hyp Hlt)  in 
        unfold selectbt in Hlt;
        apply Hyp in Hlt; allsimpl; auto
      ); cpx
end. 

Ltac ssubst_ssubst_aux_eq_hyp H Hyp :=
let T := type of Hyp in 
match T with
|  context[ssubst ?t ?sub] => 
  assert (ssubst t sub = ssubst_aux t sub) as H;
  [change_to_ssubst_aux8; sp  | rewrite H in Hyp ]
end.
Lemma alpha_ssubst_congr_bterm_aux : forall (o:Opid) lva lvb nta ntb sub,
  alpha_eq_bterm (bterm lva nta) 
                 (bterm lvb ntb)
  -> disjoint (lva ++ lvb ++ bound_vars nta ++ bound_vars ntb ) (flat_map free_vars (range sub)) 
  -> alpha_eq_bterm (bterm lva (ssubst nta (sub_filter sub lva))) 
                    (bterm lvb (ssubst ntb (sub_filter sub lvb))).
Proof using.
  introv o Hbal Hdis.
  assert (alpha_eq (oterm o [(bterm lva nta)]) 
                  (oterm o [(bterm lvb ntb)])) as Hal by prove_alpha_eq3.

  apply ssubst_alpha_congr2 with (sub:=sub)  in Hal.
  pose proof (ssubst_sub_filter_alpha (oterm o [bterm lva nta]) sub lva) as Htra.
  pose proof (ssubst_sub_filter_alpha (oterm o [bterm lvb ntb]) sub lvb) as Htrb.
  Local Opaque ssubst.
  allsimpl.
  simpl_vlist.
  lapply Htra; clear Htra; [intro Htra|apply disjoint_remove_nvars];[].
  lapply Htrb; clear Htrb; [intro Htrb|apply disjoint_remove_nvars];[].
  apply alpha_eq_sym in Htra.
  apply alpha_eq_sym in Htrb.
  assert ( alpha_eq  (ssubst (oterm o [bterm lva nta]) sub)
         (ssubst (oterm o [bterm lvb ntb]) sub))  as Ha by (eauto with slow).
  ssubst_ssubst_aux_eq_hyp H3eq Ha;[
    simpl; simpl_vlist; disjoint_reasoningv |].
  ssubst_ssubst_aux_eq_hyp H4eq Ha;[
    simpl; simpl_vlist; disjoint_reasoningv |].
    
  simpl in Ha.
  invertsna Ha Hbal.
  allsimpl.
  assert (0< 1) as Hlt by omega.
  apply_clear Hbal1 in Hlt.
  unfold selectbt in Hlt. simpl in Hlt.
  change_to_ssubst_aux8;spc;[|];
  apply disjoint_sym; apply disjoint_sub_filter_r_flatmap2; disjoint_reasoningv.
  Local Transparent ssubst.
Qed.


Lemma alpha_eq_bterm_preserves_size: forall lv1 nt1 lv2 nt2,
  alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2) 
  -> size nt1 = size nt2.
Proof using.
  introv Hal. invertsna Hal Hal.
  apply alpha_eq_preserves_size in Hal3.
  rw ssubst_allvars_preserves_size2 in Hal3.
  rw ssubst_allvars_preserves_size2 in Hal3.
  sp.
Qed.

Lemma alpha_eq_bterm_preserves_size2: forall bt1 bt2,
  alpha_eq_bterm bt1 bt2 
  -> size (get_nt bt1) = size (get_nt bt2).
Proof using.
  introv Hal.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  simpl. eapply alpha_eq_bterm_preserves_size; eauto.
Qed.





Hint Resolve alpha_eq_bterm_preserves_size : slow.
Hint Resolve alpha_eq_preserves_size : slow.
Hint Resolve disjoint_free_vars_ssubst : slow.
Hint Resolve disjoint_sym : slow.
Lemma alpha_bterm_change: forall bt lv nt lvn,
  alpha_eq_bterm bt (bterm lv nt)
  -> disjoint (all_vars nt) lvn 
  (** bvars required by  disjoint_free_vars_ssubst 
      and fvars reqd by ssubst_nest_vars_same*)
  -> no_repeats lvn (** required by ssubst_nest_vars_same*)
  -> length lv = length lvn
  -> alpha_eq_bterm bt (bterm lvn (ssubst nt (var_ren lv lvn))).
Proof using.
  introv Hal Hdis Hnr Hlen.
  destruct bt as [lvl ntl]. allsimpl.
  apply alphaeq_bterm3_if with (lva:=lvn) in Hal.
  invertsna Hal Hbal.
  eapply al_bterm with (lv:=lv0);eauto;spc;[disjoint_reasoningv|].
  - apply disjoint_sym. apply disjoint_free_vars_ssubst; spcls; disjoint_reasoningv.
  - apply disjoint_sym. apply disjoint_bound_vars_ssubst; spcls; disjoint_reasoningv.
  - rewrite ssubst_nest_vars_same; spc; disjoint_reasoningv.
    apply alpha_eq_if3 in Hbal3. change_to_ssubst_aux8. sp.
Qed.

Lemma sub_filter_nil_combine : forall  (sub : Substitution) lv,
  sub_filter sub (lv++dom_sub sub) =[].
Proof using.
  induction sub as [|(v,u) sub Hind] ; introv ; auto;[].
  allsimpl. disjoint_reasoningv.
  rewrite memvar_dmemvar;
  cases_ifd Hd; cpx; allsimpl; disjoint_reasoningv; [| provefalse; apply Hdf].
  - rw cons_as_app. rw app_assoc. rw Hind; auto.
  - apply in_app_iff. right. cpx.
Qed.

Lemma sub_filter_nil_var_ren : forall lvi lvo,
  length lvi = length lvo
  -> sub_filter (@var_ren NVar Opid lvi lvo) lvi =[].
Proof using.
  introv Hlen. pose proof (sub_filter_nil_combine (var_ren lvi lvo) []) as XX.
  allsimpl. spcls.
  auto.
Qed.

Lemma alpha_eq_bterm_congr2 : forall lv lv' nt nt',
  alpha_eq nt nt'
  -> length lv = length lv'
  -> disjoint (lv ++ lv') (free_vars nt++ free_vars nt')
  -> alpha_eq_bterm (bterm lv nt) (bterm lv' nt').
Proof using.
  introv Hal Hlen Hdis.
  pose proof (fresh_vars (length lv) (all_vars nt ++ all_vars nt')) as Hfr.
  exrepnd.
  apply al_bterm with (lv:= lvn); spc; disjoint_reasoningv.
  dimp (ssubst_sub_filter_alpha nt (var_ren lv lvn) lv); disjoint_reasoningv.
  dimp (ssubst_sub_filter_alpha nt' (var_ren lv' lvn) lv'); disjoint_reasoningv.
  rw sub_filter_nil_var_ren in hyp; auto.
  rw sub_filter_nil_var_ren in hyp0; try congruence.
  rewrite ssubst_nil in hyp.
  rewrite ssubst_nil in hyp0.
  eauto with slow.
Qed.

  Hint Resolve ssubst_alpha_congr2 : slow.
  Hint Resolve alpha_eq_bterm_congr : slow.

Lemma alpha_bterm_pair_change : forall (bt1 bt2: BTerm) lv nt1 nt2 lva,
  alpha_eq_bterm bt1 (bterm lv nt1)
  -> alpha_eq_bterm bt2 (bterm lv nt2)
  -> {lvn :(list NVar) & { nt1n, nt2n : NTerm $ length lv =length lvn
                  # alpha_eq nt1 nt1n
                  # alpha_eq nt2 nt2n
                  # alpha_eq_bterm bt1 (bterm lvn (ssubst nt1n (var_ren lv lvn)))
                  # alpha_eq_bterm bt2 (bterm lvn (ssubst nt2n (var_ren lv lvn)))
                  # no_repeats lvn
                  #  disjoint lvn (all_vars nt1 ++ all_vars nt2 ++ lva ++ (bound_vars nt1n) ++ (bound_vars nt2n))
                  # disjoint (lvn ++ (bound_vars nt1n) ++ (bound_vars nt2n)) lva   } }.
Proof using. 
  introv H1b H2b.
  pose proof (change_bvars_alpha_wspec lva nt1) as H1fr.
  exrepnd.
  rename ntcv into nt1n.
  pose proof (change_bvars_alpha_wspec lva nt2) as H2fr.
  exrepnd.
  rename ntcv into nt2n.
  pose proof (fresh_vars (length lv) (all_vars nt1 ++ all_vars nt2 ++lva ++ (bound_vars nt1n) ++ (bound_vars nt2n))) as Hfr.
  exrepnd.
  exists lvn.
  exists nt1n.
  exists nt2n.
  spc;[| |disjoint_reasoningv;fail].
  - apply alpha_bterm_change with (lvn:=lvn) in H1b; spc; disjoint_reasoningv.
    rewrite H1b, H1fr0.
    refl.
  - apply alpha_bterm_change with (lvn:=lvn) in H2b; spc; disjoint_reasoningv.
    rewrite H2b, H2fr0. refl.
Qed.

Lemma alpha_bterm_pair_change2 : forall (bt1 bt2: BTerm) lv nt1 nt2 lvn,
  alpha_eq_bterm bt1 (bterm lv nt1)
  ->  alpha_eq_bterm bt2 (bterm lv nt2)
  -> length lv =length lvn
  -> no_repeats lvn
  ->  disjoint lvn (all_vars nt1 ++ all_vars nt2)
  -> { nt1n, nt2n : NTerm $
                  alpha_eq nt1 nt1n
                  # alpha_eq nt2 nt2n
                  # alpha_eq_bterm bt1 (bterm lvn (ssubst nt1n (var_ren lv lvn)))
                  # alpha_eq_bterm bt2 (bterm lvn (ssubst nt2n (var_ren lv lvn)))
                  #  disjoint lvn ((bound_vars nt1n) ++ (bound_vars nt2n))  }.
Proof using. 
  introv H1b H2b Hlen Hnr Hdis.
  pose proof (change_bvars_alpha_wspec lvn nt1) as H1fr.
  exrepnd.
  rename ntcv into nt1n.
  pose proof (change_bvars_alpha_wspec lvn nt2) as H2fr.
  exrepnd.
  rename ntcv into nt2n.
  exists nt1n.
  exists nt2n.
  spc; [| |disjoint_reasoningv].
  - apply alpha_bterm_change with (lvn:=lvn) in H1b; spc; disjoint_reasoningv.
    rewrite H1b, H1fr0. refl.

  - apply alpha_bterm_change with (lvn:=lvn) in H2b; spc; disjoint_reasoningv.
    rewrite H2b, H2fr0. refl.
Qed.

Lemma ssubst_trivial_alpha : forall nt lv ,
  alpha_eq (ssubst nt (var_ren lv lv)) nt.
Proof using.
  introv. pose proof (change_bvars_alpha_wspec lv nt) as Hfr.
  exrepnd.
  alpharws Hfr0.
  change_to_ssubst_aux8.
  unfold var_ren. rewrite combine_vars_map_sp. rewrite ssubst_aux_trivial_vars.
  apply alpha_eq_refl.
Qed.

Lemma alpha_eq_bterm_triv: forall lv nt1 nt2,
  alpha_eq_bterm (bterm lv nt1) (bterm lv nt2)
  -> alpha_eq nt1 nt2.
Proof using.
  introv Hbal.
  invertsna Hbal Hbal.
  pose proof (change_bvars_alpha_wspec  (lv++lv0) nt1) as H1sp. exrepnd.
  rename ntcv into nt1cv.
  pose proof (change_bvars_alpha_wspec  (lv++lv0) nt2) as H2sp. exrepnd.
  rename ntcv into nt2cv.
  alpharwhs H2sp0 Hbal3.
  alpharwh H1sp0 Hbal3.
  apply ssubst_alpha_congr2 with (sub := var_ren lv0 lv) in Hbal3.
  disjoint_reasoningv.
  alpharwh H2sp0  Hbal6.
  alpharwh H1sp0  Hbal6.

  rewrite ssubst_nest_vars_same in Hbal3; spc; disjoint_reasoningv.
  rewrite ssubst_nest_vars_same in Hbal3; spc; disjoint_reasoningv.
  pose proof (ssubst_trivial_alpha nt1cv lv) as H1p.
  pose proof (ssubst_trivial_alpha nt2cv lv) as H2p.

  assert (alpha_eq nt1cv nt2cv) by (eauto with slow).
  eauto with slow.
Qed.

Definition change_bvars_range (lva : list NVar) (sub: Substitution) : Substitution :=
  map (fun p : (NVar * NTerm) => (fst p, change_bvars_alpha lva (snd p))) sub.

Lemma refl_rel_alpha_eauto : refl_rel alpha_eq.
Proof using.
  unfold refl_rel. intros. apply alpha_eq_refl.
Qed.
  
Lemma change_bvars_range_spec : forall lva sub,
  let sub' := (change_bvars_range lva sub) in 
  sub_range_rel alpha_eq sub  sub' #
  disjoint (flat_map bound_vars (range sub')) lva.
Proof using.
  induction sub as [ |(v,t) sub Hind]; 
    [| pose proof (change_bvars_alpha_spec t lva )];
    allsimpl;sp; disjoint_reasoningv.
Qed.



Lemma sub_rel_alpha_prop2 : forall subl subr,
  sub_range_rel alpha_eq subl subr
  -> flat_map free_vars (range subl) =  flat_map free_vars (range subr) # dom_sub subl = dom_sub subr.
Proof using.
  induction subl as [ |(vl,tl) subl Hind]; introv Hsr; allsimpl;
  destruct subr as [ |(vr,tr) subr]; try invertsn Hsr; dands; spc;simpl; f_equal;
  apply Hind in Hsr; repnd; try congruence.
  apply alphaeq_preserves_free_vars; auto.
Qed.

Lemma change_bvars_range_wspec: forall  lva sub,
  {sub' : Substitution $ disjoint (flat_map bound_vars (range sub')) lva #
      forall t, alpha_eq (ssubst t sub) (ssubst t sub')}.
Proof using.
  introv. exists (change_bvars_range lva sub).
  pose proof (change_bvars_range_spec lva sub) as Hfr.
  allsimpl. repnd. dands;sp;[].
   eapply sub_rel_alpha_prop in Hfr0; eauto.
Qed.

Lemma change_bvars_range_wspec2: forall  lva sub,
  {sub' : Substitution $ disjoint (flat_map bound_vars (range sub')) lva #
      sub_range_rel alpha_eq sub sub'}.
Proof using.
  introv. exists (change_bvars_range lva sub).
  pose proof (change_bvars_range_spec lva sub) as Hfr.
  allsimpl. repnd. dands; sp.
Qed.

Lemma change_bvars_range_wspec3: forall  lva sub,
  {sub' : Substitution $ disjoint (flat_map bound_vars (range sub')) lva #
      flat_map free_vars (range sub) =  flat_map free_vars (range sub') # dom_sub sub = dom_sub sub'
      # (forall t, alpha_eq (ssubst t sub) (ssubst t sub'))}.
Proof using.
  introv. exists (change_bvars_range lva sub).
  pose proof (change_bvars_range_spec lva sub) as Hfr.
  allsimpl. repnd.
  applydup sub_rel_alpha_prop2 in Hfr0.
  pose proof (sub_rel_alpha_prop   _ _ Hfr0).
  dands; spc.
Qed.

  

Lemma sub_rel_ssubst_sub_alpha : forall subr subl subla,
  sub_range_rel alpha_eq subl subla
  -> sub_range_rel alpha_eq (ssubst_sub subl subr) (ssubst_sub subla subr).
Proof using.
  induction subl as [|(v,t) subl Hind]; introv Hsr;
  destruct subla as [|(va,ta) subla]; inverts Hsr; allsimpl;sp.
  eauto with slow.
Qed.


Hint Resolve sub_range_refl refl_rel_alpha_eauto : slow.

Hint Resolve sub_range_refl sub_range_rel_app sub_rel_ssubst_sub_alpha : slow.

(** 
    % \noindent \\* %
    In the following lemma, [ssubst_sub] is a function such that 
    [ssubst_sub sub1 sub2] performs the [Substitution] sub2 on each element
    of the range of [sub1].

*)

Lemma combine_sub_nest:
  forall t sub1 sub2,
    alpha_eq (ssubst (ssubst t sub1) sub2) 
             (ssubst t (ssubst_sub sub1 sub2 ++ sub2)).
Proof using.
  (* change t to t' such that t' will never cause renaming.
      naive case split
    proof gives 8 non-trivial cases(2 for each ssubst) *)
  
  introv.
  pose proof (change_bvars_range_wspec2 (flat_map free_vars (range sub2)) sub1) as Hfs.
  exrepnd. rename sub' into sub1b.
  duplicate Hfs0 as Hbc.  apply sub_rel_alpha_prop with (t:=t)  in Hbc.
  alpharw Hbc.
  assert (sub_range_rel alpha_eq (ssubst_sub sub1 sub2 ++ sub2) (ssubst_sub sub1b sub2 ++ sub2)) as XX.
    apply sub_range_rel_app. dands; eauto with slow. apply sub_range_refl; eauto with slow.
  
  apply sub_rel_alpha_prop with (t:=t)  in XX.
  alpharws XX.
  clear XX Hbc.
  remember ((flat_map free_vars (range sub1b))++(flat_map free_vars (range sub2))) as lva.
  pose proof (change_bvars_alpha_spec t lva) as Hfr.
  allsimpl. repnd. 
  remember (change_bvars_alpha lva t) as t'.
  alpharws Hfr. rewrite Heqlva in Hfr0.
  repeat rewrite ssubst_ssubst_aux; auto; disjoint_reasoningv.
  - alpha_refl_tac.
    apply ssubst_aux_app; disjoint_flat; spcls; disjoint_reasoningv.
  - apply disjoint_sym. setoid_rewrite <- disjoint_sub_as_flat_map. 
    apply sub_app_sat;[| disjoint_flat; disjoint_reasoningv].
    apply ssubst_sub_disjoint_bv2;
    disjoint_flat; spcls; disjoint_reasoningv.
  - disjoint_ssubst.
Qed.

Lemma combine_sub_nest_wspec:
  forall sub1 sub2,
  wf_sub sub1
  -> wf_sub sub2
  -> {sub3 : Substitution & wf_sub sub3 # 
        forall t,alpha_eq (ssubst (ssubst t sub1) sub2) (ssubst t sub3)}.
Proof using.
  introv H1w H2w.
  exists ((ssubst_sub sub1 sub2) ++ sub2). split.
  - apply sub_app_sat;sp. apply ssubst_sub_wf;sp. 
  - intro nt. apply combine_sub_nest;sp.
Qed.


Hint Resolve alpha_eq_preserves_size alpha_eq_bterm_preserves_size ssubst_allvars_preserves_size2: slow.

Ltac ntsize :=
  match goal with 
  [ |- context [size (ssubst ?t (var_ren _ _))]]
  => rewrite ssubst_allvars_preserves_size2
end.

Lemma ssubst_on_closed_term :
  forall t sub,
    isprogram t
    -> alpha_eq (ssubst t sub) t.
Proof using.
  introv isp.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub)) t); exrepnd.
  rewrite X0.
  change_to_ssubst_aux8.
  alpha_refl_tac.
  alpha_hyps X0.

  apply ssubst_aux_trivial4.
  unfold isprogram in *; repnd.
  allrw; spc.

  disjoint_flat; sp; disjoint_reasoningv.
Qed.

Lemma alphaeqbt_nilv3: forall lv nt1 nt2 ,
       alpha_eq_bterm (bterm [] nt1) (bterm lv nt2) -> ((lv = []) # alpha_eq nt1 nt2).
Proof using.
  introv Hal. apply alphaeqbt_nilv in Hal.
  exrepnd.
  inverts Hal1.
  split; eauto.
Qed.

Lemma alphaeqbt_preserves_fvars_aux: forall (bt1 bt2 : BTerm),
  alpha_eq_bterm bt1 bt2
  -> subset (free_vars_bterm bt1) (free_vars_bterm bt2).
Proof using.
  introv Hal. destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  simpl.   unfold subset.
  intros v Hin.
  invertsna Hal Hal.
  apply alphaeq_preserves_free_vars in Hal3.
  apply in_remove_nvars in Hin.
  repnd.
  assert (LIn v (free_vars (ssubst nt1 (var_ren lv1 lv)))) as XX.
  - pose proof (eqsetv_free_vars_disjoint nt1 (var_ren lv1 lv)) as XX.
    apply eqsetv_prop with (x:=v) in XX.
    apply XX. apply in_app_iff.
    left. unfold var_ren. rewrite dom_sub_combine; try( simpl_list;spc);[].
    apply in_remove_nvars;sp.
  - rewrite Hal3 in XX. apply substitution.free_vars_ssubst2 in XX;
      [| apply disjoint_bv_vars; disjoint_reasoningv;fail].
    dorn XX; exrepnd.
    + unfold var_ren in XX. rewrite dom_sub_combine in XX; try( simpl_list;spc);[].
      apply in_remove_nvars;sp.
    + apply in_var_ren in XX0. exrepnd. subst. allsimpl.
      dorn XX1; sp. subst. disjoint_reasoningv.
      disjoint_lin_contra.
Qed.

Lemma alphaeqbt_preserves_fvars: forall (bt1 bt2 : BTerm),
  alpha_eq_bterm bt1 bt2
  -> eq_set (free_vars_bterm bt1) (free_vars_bterm bt2).
Proof using.
  introv Hal.
  pose proof (alphaeqbt_preserves_fvars_aux _ _ Hal).
  apply alpha_eq_bterm_sym in Hal.
  pose proof (alphaeqbt_preserves_fvars_aux _ _ Hal).
  Hint Unfold subset.
  apply eqsetv_prop.
  split; eauto.
Qed.




Lemma free_vars_alpha_bterm : forall bt lv nt,
  alpha_eq_bterm bt (bterm lv nt)
  -> forall v, (LIn v (free_vars nt) 
        -> LIn v (free_vars_bterm bt) [+] LIn v lv).
Proof using.
  introv Hal Hin.
  apply alphaeqbt_preserves_fvars in Hal.
  allsimpl. destruct (in_nvar_list_dec v lv); spc;[].
  apply eqsetv_prop with (x:=v) in Hal.
  left. apply Hal.
  apply in_remove_nvars;sp.
Qed.



  
 
Hint Resolve alpha_eq_bterm_congr alpha_bterm_change 
alpha_bterm_change: slow.
Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: slow.

Lemma alpha_bterm_pair_change4 : forall (bt1 bt2: BTerm) lv nt1 nt2 lvn lva,
  alpha_eq_bterm bt1 (bterm lv nt1)
  ->  alpha_eq_bterm bt2 (bterm lv nt2)
  -> length lv =length lvn
  -> no_repeats lvn
  ->  disjoint lvn (free_vars_bterm bt1 ++ free_vars_bterm bt2)
  -> { nt1n, nt2n : NTerm $
                  alpha_eq nt1 nt1n
                  # alpha_eq nt2 nt2n
                  # alpha_eq_bterm bt1 (bterm lvn (ssubst nt1n (var_ren lv lvn)))
                  # alpha_eq_bterm bt2 (bterm lvn (ssubst nt2n (var_ren lv lvn)))
                  #  disjoint (lva ++ lvn) ((bound_vars nt1n) ++ (bound_vars nt2n))  }.
Proof using. 
  introv H1b H2b Hlen Hnr Hdis.
  pose proof (alpha_bterm_pair_change _ _ _ _ _ (lvn ++ lva) H1b H2b) as H1c.
  exrepnd.
  rename lvn0 into lvnp.
  dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn H1c4 H1c5); spcf.
  - exrepnd. 
    assert (alpha_eq_bterm bt2 (bterm lvn (ssubst (ssubst 
      nt2n (var_ren lv lvnp)) (var_ren lvnp lvn)))) as H1XX by eauto with slow.
    assert (alpha_eq_bterm bt1 (bterm lvn (ssubst (ssubst 
      nt1n (var_ren lv lvnp)) (var_ren lvnp lvn)))) as H2XX by eauto with slow.
    rewrite ssubst_nest_vars_same in H1XX; spc; try (disjoint_reasoningv; fail);
     [| alpharw (alpha_eq_sym _ _ H1c3); disjoint_reasoningv;fail].
    rewrite ssubst_nest_vars_same in H2XX; spc; try (disjoint_reasoningv; fail);
     [| alpharw (alpha_eq_sym _ _ H1c2); disjoint_reasoningv;fail].
    eexists . eexists. dands; eauto;[]. disjoint_reasoningv.
  - unfold all_vars. 
    repeat (rewrite boundvars_ssubst_vars;
    [ | disjoint_reasoningv | disjoint_reasoningv];[]).
    disjoint_reasoningv;[|].
    + introv Hin Hinc.
      apply substitution.free_vars_ssubst2 in Hinc;
        [| apply disjoint_bv_vars; disjoint_reasoningv;fail].
      dorn Hinc; exrepnd.
      * unfold var_ren in Hinc. rewrite dom_sub_combine in Hinc; try( simpl_list;spc);[].
        alpharwh (alpha_eq_sym _ _ H1c2)  Hinc0.
        eapply free_vars_alpha_bterm in Hinc0; eauto.
        dorn Hinc0; sp;[].
        disjoint_lin_contra.
      * apply in_var_ren in Hinc0. exrepnd. subst. allsimpl. dorn Hinc1;spc;[].
        subst. disjoint_lin_contra.
    + introv Hin Hinc.
      apply substitution.free_vars_ssubst2 in Hinc;
        [| apply disjoint_bv_vars; disjoint_reasoningv;fail].
      dorn Hinc; exrepnd.
      * unfold var_ren in Hinc. rewrite dom_sub_combine in Hinc;
           try( simpl_list;spc);[].
        alpharwh (alpha_eq_sym _ _ H1c3)  Hinc0.
        eapply free_vars_alpha_bterm in Hinc0; eauto.
        dorn Hinc0; sp;[].
        disjoint_lin_contra.
      * apply in_var_ren in Hinc0. exrepnd. subst. allsimpl. dorn Hinc1;spc;[].
        subst. disjoint_lin_contra.
Qed.

Ltac prove_bin_rel_nterm := 
  split;[sp|simpl];[];
  intros n Hlt; repeat (destruct n; try(omega));sp.
  (*-> disjoint (lvio++(flat_map free_vars lnt)) (bound_vars t)*)

Lemma ssubst_nest_same_alpha :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint lvio (free_vars t)
  -> alpha_eq (ssubst (ssubst t (var_ren lvi lvio)) (combine lvio lnt))
      (ssubst t (combine lvi lnt)).
Proof using.
  intros.
  pose proof (change_bvars_alpha_wspec (lvio++(flat_map free_vars lnt)) t) as Hf.
  exrepnd.
  alpharws Hf0.
  rewrite ssubst_nest_same;spc.
  alpharws (alpha_eq_sym _ _ Hf0). sp.
Qed.

Ltac prove_alpha_eq4 := unfold_all_mk; let Hlt := fresh "Hltalc" in
match goal with
| [ |- alpha_eq ?t ?t] => apply alpha_eq_refl
| [ |- alpha_eq (oterm ?o _) (oterm ?o _)] => constructor;simpl;[repeat(simpl_list);spc
                                                  | unfold selectbt;simpl]
| [ |- alpha_eq ?t1 ?t2] => auto ; fail
| [ |- forall _, _ < _ -> alpha_eq_bterm _ _ ] => introv Hlt;repeat(simpl_list);repeat(dlt Hlt)
| [ |- alpha_eq_bterm ?t ?t ] => apply alphaeqbt_refl
| [ |- alpha_eq_bterm (bterm [] _) (bterm [] _) ] => apply alphaeqbt_nilv2 
end.

Ltac alphahypsd2 := simpl;
  match goal with 
  | [H: S _ = length ?l |- _ ] => let ls := fresh l "s" in 
        destruct l as [| ls l]; simpl in H; inverts H as H
  | [H: length ?l = S _ |- _ ] => symmetry in H
  | [H: alpha_eq (oterm ?o _) _ |- _] => let H1:= fresh H "len" in
              let H2:= fresh H "bts" in
              inverts H as H1 H2; simpl in H1; simpl in H2     
  | [H: (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _)  |- _ ] => 
    
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX;  simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX;  simpl in XXX;
      unfold selectbt in XXX; simphyps); hide_hyp H
  | [H: alpha_eq_bterm (bterm [] _) (bterm [] _) |- _] => apply alphaeqbt_nilv2 in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_] _) _ |- _] => apply alphaeqbt_1v in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_,_] _) _ |- _] => apply alphaeqbt_2v in H; exrepnd; subst
  end.
Lemma ssubst_over_alpha_bt1 : forall o btnt rlbt sub,
  disjoint (flat_map bound_vars_bterm rlbt) (flat_map free_vars (range sub))
  -> alpha_eq (oterm o ((bterm [] (ssubst btnt sub)):: (map (fun t => ssubst_bterm_aux t sub) rlbt)))
              (ssubst (oterm o ((bterm [] btnt):: rlbt)) sub).
Proof using.
  introv Hdis.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub))
     (oterm o (bterm [] btnt :: rlbt))) as Hfr.
  exrepnd.
  alpharws Hfr0.
  remember (ssubst btnt sub) as ls.
  change_to_ssubst_aux8.
  subst. clear d.
  repeat (alphahypsd2); show_hyps.
  repeat(prove_alpha_eq4).
  - simpl. rewrite sub_filter_nil_r.
    rewrite <- ssubst_ssubst_aux;[| disjoint_reasoningv].
    eauto with slow.
  - dimp (Hfr0bts (S n));[omega|]. unfold selectbt in hyp. simpl in hyp.
    revert hyp. repeat(fold_selectbt). introv Hlt.
    repeat(rewrite selectbt_map);spc;[].
    dimp (selectbt_in n rlbt).
    dimp (selectbt_in n lbt2); spc;[].
    apply ssubst_alphabt_congr;sp;[].
    disjoint_reasoningv; repeat(disjoint_flat3);
      show_hyps; disjoint_reasoningv.
Qed.

Lemma ssubst_over_alpha_bt2 : forall o bt1 bt2nt rlbt sub,
  disjoint (flat_map bound_vars_bterm rlbt) (flat_map free_vars (range sub))
  -> disjoint (bound_vars_bterm bt1) (flat_map free_vars (range sub))
  -> alpha_eq (oterm o ((ssubst_bterm_aux bt1 sub)::(bterm [] (ssubst bt2nt sub))
                  :: (map (fun t => ssubst_bterm_aux t sub) rlbt)))
              (ssubst (oterm o (bt1:: (bterm [] bt2nt):: rlbt)) sub).
Proof using.
  introv Hdis H2dis.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub))
     (oterm o (bt1:: bterm [] bt2nt :: rlbt))) as Hfr.
  exrepnd.
  alpharws Hfr0.
  remember (ssubst bt2nt sub) as ls.
  change_to_ssubst_aux8.
  subst. clear d.
  repeat (alphahypsd2); show_hyps.
  repeat(prove_alpha_eq4).
  - simpl. apply ssubst_alphabt_congr;cpx; disjoint_reasoningv.
  - simpl. rewrite sub_filter_nil_r.
    rewrite <- ssubst_ssubst_aux;[| disjoint_reasoningv].
    eauto with slow.
  - dimp (Hfr0bts (S (S n)));[omega|]. unfold selectbt in hyp. simpl in hyp.
    revert hyp. repeat(fold_selectbt). introv Hlt.
    repeat(rewrite selectbt_map);spc;[].
    dimp (selectbt_in n rlbt).
    dimp (selectbt_in n lbt2); spc;[].
    apply ssubst_alphabt_congr;sp;[];
    disjoint_reasoningv; repeat(disjoint_flat3);
      show_hyps; disjoint_reasoningv.
Qed.
Lemma eq_vars_progsub :
  forall (t : NTerm) (sub : Substitution),
  prog_sub sub
  -> eq_set (free_vars (ssubst t sub)) (remove_nvars (dom_sub sub) (free_vars t)).
Proof using varclass.
  introv Hpr.
  pose proof (eqsetv_free_vars_disjoint t sub) as XX.
  assert ( (sub_free_vars (sub_keep_first sub (free_vars t))) = [] ) as Hn;
  [ | rewrite Hn in XX; simpl_vlist; sp; fail].
  apply null_iff_nil.
  introv Hin.
  apply in_sub_free_vars_iff in Hin.
  exrepnd.
  apply in_sub_keep_first in Hin0.
  exrepnd.
  apply sub_find_some in Hin2.
  apply Hpr in Hin2.
  repnud Hin2.
  rewrite Hin3 in Hin1.
  sp.
Qed.

Lemma ssubst_program_implies : forall t sub,
  isprogram (ssubst t sub)
  -> subset (free_vars t) (dom_sub sub).
Proof using varclass.
  introv Hpr.
  repnud Hpr.
  pose proof (eqsetv_free_vars_disjoint t sub) as XX.
  rewrite Hpr0 in XX.
  apply eq_vars_nil in XX.
  apply app_eq_nil in XX.
  repnd.
  rewrite nil_remove_nvars_iff in XX0.
  auto.
Qed.

Lemma eq_vars_prog_sub_same_dom: forall ta tb suba subb,
  prog_sub suba
  -> prog_sub subb
  -> (dom_sub suba = dom_sub subb)
  -> eq_set (free_vars ta) (free_vars tb)
  -> eq_set (free_vars (ssubst ta suba)) (free_vars (ssubst tb subb)).
Proof using varclass.
  introv Hap Hbp Hds Heq.
  pose proof (eq_vars_progsub ta _ Hap).
  pose proof (eq_vars_progsub tb _ Hbp).
  match goal with
  [ H1: eq_set ?a ?la , H2 : eq_set ?v ?lb |- eq_set ?a ?b ] =>
  assert (eq_set la lb);
    [| eauto with eqsetv]
  end.
  rewrite Hds.
  apply eqsetv_remove_nvars; eauto with eqsetv.
Qed.

Lemma eq_vars_same_sub: forall (ta tb : NTerm) sub,
  eq_set (free_vars ta) (free_vars tb)
  -> eq_set (free_vars (ssubst ta sub)) (free_vars (ssubst tb sub)).
Proof using varclass.
  introv Heq.
  pose proof (eqsetv_free_vars_disjoint ta sub).
  pose proof (eqsetv_free_vars_disjoint tb sub).
  match goal with
  [ H1: eq_set ?a ?la , H2 : eq_set ?v ?lb |- eq_set ?a ?b ] =>
  assert (eq_set la lb);
    [| eauto with eqsetv]
  end.
  apply eqsetv_app; [eauto with eqsetv;fail |].
  match goal with
  [|- eq_set ?a ?b ] => assert (a=b) as XX;[| rewrite XX; eauto 1 with eqsetv; fail]
  end.
  f_equal.
  apply eqsetv_sub_keep_first; auto.
Qed.

Hint Resolve ssubst_nt_wf ssubst_wf_if_eauto : slow.

Lemma isprogram_ssubst_implies_ispbt : forall t sub, 
    isprogram (ssubst t sub)
    -> isprogram_bt (bterm (dom_sub sub) t).
Proof using varclass.
  introv Hpr.
  unfolds_base.
  duplicate Hpr.
  repnud Hpr0.
  split;[|constructor; eauto with slow].
  unfolds_base.
  simpl.
  apply ssubst_program_implies in Hpr.
  apply nil_remove_nvars_iff; auto.
Qed.

Hint Unfold wf_sub sub_range_sat : slow.

Hint Resolve ssubst_nt_wf: slow.
(* replace in cequiv.v *)

Lemma subst_change_prog : forall t ts td v,
  isprogram td
  -> isprogram (subst t v ts)
  -> isprogram (subst t v td).
Proof using varclass.
  introv  Hpd Hpl.
  applydup ssubst_program_implies in Hpl.
  unfold subst in *. apply isprogram_ssubst;sp. 
  - repnud Hpl. apply ssubst_nt_wf in Hpl;sp.
  -  in_reasoning. cpx.
Qed.


(* Lemma alpha_preserves_value : forall t1 t2,
  alpha_eq t1 t2
  -> isvalue t1
  -> isvalue t2.
Proof using.
  introns Hc.
  invertsn Hc0.
  duplicate Hc as Hcc. invertsn Hc. 
  constructor.
  apply alphaeq_preserves_program in Hcc.
  inverts Hcc. auto.
Qed. *)

(* Hint Resolve alpha_preserves_value : slow. *)

Lemma subst_aux_change_prog : forall t ts td v,
  isprogram ts
  -> isprogram td
  -> isprogram (subst_aux t v ts)
  -> isprogram (subst t v td).
Proof using varclass.
  introns XX. unfold subst_aux in *.
  rewrite <- ssubst_ssubst_aux_prog_sub in XX1 ;[| prove_sub_range_sat; fail].
  apply subst_change_prog with (ts:=ts); auto.
Qed.

Lemma progsub_ssubst_disjointfv_domsub :
  forall t sub,
  prog_sub sub
  -> disjoint (free_vars (ssubst t sub)) (dom_sub sub).
Proof using.
  introv Hprs.
  intros v Hin Hinc.
  rewrite isprogram_ssubst2 in Hin; auto;[].
  apply in_remove_nvars in Hin.
  repnd. sp.
Qed.

  
Lemma btchange_alpha_aux: forall lv nt lvn,
  length lv = length lvn 
  -> no_repeats lvn
  -> disjoint (all_vars nt) lvn
  -> alpha_eq_bterm (bterm lv nt) (bterm lvn (ssubst nt (var_ren lv lvn))).
Proof using.
  introv Hlen Hdis Hnr.
  pose proof (fresh_vars (length lvn) (all_vars nt ++lvn)).
  exrepnd.
  rename lvn0 into lvnn.
  change_to_ssubst_aux8. clear d.
  exists lvnn;auto; try congruence; disjoint_reasoningv; repeat(disjoint_ssubst);spcls; disjoint_reasoningv;[].
  rewrite <- ssubst_ssubst_aux;[| spcls; disjoint_reasoningv].
  apply alpha_eq_sym.
  apply ssubst_nest_same_alpha; spcls; auto;disjoint_reasoningv.
Qed.

Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: slow.
Lemma btchange_alpha: forall lv nt lvn,
  length lv = length lvn 
  -> no_repeats lvn
  -> disjoint (free_vars nt) lvn
  -> alpha_eq_bterm (bterm lv nt) (bterm lvn (ssubst nt (var_ren lv lvn))).
Proof using.
  introv Hlen Hdis Hnr.
  pose proof (change_bvars_alpha_wspec lvn nt) as Hfr.
  exrepnd.
  alpharwh Hfr0 Hnr.
  assert (alpha_eq_bterm (bterm lv nt) (bterm lvn (ssubst ntcv (var_ren lv lvn))));
  [| eauto with slow].
  apply alpha_eq_bterm_sym.
  assert (alpha_eq_bterm (bterm lv ntcv) (bterm lvn (ssubst ntcv (var_ren lv lvn))));
  [| eauto with slow].
  clear dependent nt.
  apply btchange_alpha_aux; auto; disjoint_reasoningv.
Qed.


Lemma prove_alpha_bterm2: forall lv1 lv2 nt1 nt2,
  length lv1 = length lv2
  -> no_repeats lv2
  -> disjoint (free_vars nt1) lv2
  -> alpha_eq (ssubst nt1 (var_ren lv1 lv2)) nt2
  -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).
Proof using.
  intros.
  rewrite btchange_alpha with (lvn:=lv2) by assumption.
  apply alpha_eq_bterm_congr. assumption.
Qed.


Lemma prove_alpha_bterm3: forall lv1 lv2 nt1 nt2,
  length lv1 = length lv2
  -> no_repeats lv2
  -> disjoint (all_vars nt1) lv2
  -> alpha_eq (ssubst_aux nt1 (var_ren lv1 lv2)) nt2
  -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).
Proof using.
  intros. disjoint_reasoningv.
  rewrite btchange_alpha with (lvn:=lv2) by assumption.
  apply alpha_eq_bterm_congr.
  clear H3.
  change_to_ssubst_aux8.
  assumption.
Qed.

Lemma alpha_eq_bterm_single_change : forall e1 vx,
  subset (free_vars e1) [vx]
  -> forall vy, alpha_eq_bterm (bterm [vx] e1)
                (bterm [vy] (ssubst e1 (var_ren [vx] [vy]))).
Proof using.
  introv Hs. intros.
  destruct (decideP (vx=vy)); subst.
  - apply alpha_eq_bterm_congr. apply alpha_eq_sym. 
    apply ssubst_trivial_alpha.
  - apply btchange_alpha; auto;[apply NoDup_cons; cpx; fail|].
    eapply subset_disjoint; eauto.
    disjoint_reasoningv; cpx.
Qed.

Lemma alpha_eq_bterm_single_change3 : forall e vx vy,
  disjoint (remove_nvars [vx] (free_vars e)) [vy]
  -> alpha_eq_bterm (bterm [vx] e)
                (bterm [vy] (ssubst e (var_ren [vx] [vy]))).
Proof using.
  introv Hs. intros.
  destruct  (decideP (vx=vy)); subst.
  - apply alpha_eq_bterm_congr. apply alpha_eq_sym. 
    apply ssubst_trivial_alpha.
  - apply btchange_alpha; auto;[apply NoDup_cons; cpx; fail|].
    inauto. tauto.
Qed.

Local Opaque remove_nvars.
Lemma alpha_eq_bterm_single_change2 : forall e1 vx vy,
  isprogram_bt  (bterm [vx] e1)
  -> alpha_eq_bterm (bterm [vx] e1)
                (bterm [vy] (ssubst e1 (var_ren [vx] [vy]))).
Proof using.
  introv X. apply alpha_eq_bterm_single_change.
  repnud X.
  repnud X0.
  simpl in X0.
  introv Hin.
 
  rewrite nil_remove_nvars_iff in X0; auto.
Qed.


Lemma ssubst_nest_single : forall e vx vy t,
  subset (free_vars e) [vx]
  -> alpha_eq (ssubst e [(vx,t)])
                           (ssubst (ssubst e (var_ren [vx] [vy])) [(vy,t)]).
Proof using.
  introv Hs. intros.
  apply alpha_eq_bterm_single_change with (vy:=vy) in Hs.
  apply apply_bterm_alpha_congr2 with (lnt:=[t]) in Hs;
      unfold  num_bvars in *; auto.
Qed.


Lemma prog_sub_change : forall sub1 sub2 t,
  isprogram (ssubst t sub1)
  -> prog_sub sub1
  -> prog_sub sub2
  -> dom_sub sub1 =dom_sub sub2
  -> isprogram (ssubst t sub2).
Proof using hdeq varclass.
  introv Hp H1p H2p Hd.
  apply isprogram_ssubst_implies_ispbt in Hp.
  apply isprogram_bt_implies with (lnt := range sub2) in Hp;
  unfold num_bvars; simpl; auto;[ | |rewrite Hd; eauto with slow ].
  - unfold apply_bterm in Hp.
    simpl in Hp.
    rewrite Hd in Hp.
    rewrite <- sub_eta in Hp. auto.
  - introv Hin. apply in_range_t in Hin.
    exrepnd. apply H2p in Hin0.
    auto.
Qed.

(* Lemma subst_val : forall e vx no lbt,
  isvalue (subst_aux e vx (oterm (NCan no) lbt))
  -> {c : CanonicalOp $ {lbtc : list BTerm $ e = oterm (Can c) lbtc}}.
Proof using.
  unfold subst_aux. introv Hisv. destruct e as [v | oo llbt]; allsimpl;
  [revert Hisv; cases_if; simpl; introv Hisv; inverts Hisv |].
  destruct oo; inverts Hisv.
  eexists ; eauto.
Qed. *)

Lemma alpha_eq_bterm_lenbvars: forall lv1 lv2 nt1 nt2,
  alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2)
  -> length lv1=length lv2.
Proof using.
  introv Hal. inverts Hal; sp.
Qed.


Lemma alpha_eq_bterm_unify : forall a b,
  alpha_eq_bterm a b
  -> {lv : list NVar $ {nta, ntb : NTerm $ 
        alpha_eq_bterm a (bterm lv nta)
        # alpha_eq_bterm b (bterm lv ntb)}}.
Proof using.
  introv Hbal.
  destruct_bterms.
  applydup alpha_eq_bterm_lenbvars in Hbal.  
  pose proof (fresh_vars(length blv) (all_vars bnt ++ all_vars ant)) as Hfr.
  exrepnd. duplicate Hbal.
  apply alpha_bterm_change with (lvn:=lvn) in Hbal; auto; disjoint_reasoningv.
  apply alpha_eq_bterm_sym in  Hbal1.
  apply alpha_bterm_change with (lvn:=lvn) in Hbal1; auto; disjoint_reasoningv;
  spc.
  rep_eexists; dands; eauto.
Qed.


(* Lemma isvalue_change_subst_noncan :forall e vx no lbt t,
  isvalue (subst e vx (oterm (NCan no) lbt))
  -> isprogram t
  -> isvalue (subst e vx t).
Proof using.
  introv Hv Hp.
  pose proof (change_bvars_alpha_wspec (free_vars (oterm (NCan no) lbt)) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply ssubst_alpha_congr2 with (sub:= [(vx,t)])in Hfr0.
  apply (alpha_preserves_value _ _ Hfr0).
  apply ssubst_alpha_congr2 with (sub:= [(vx,(oterm (NCan no) lbt))])in Hal.
  apply (alpha_preserves_value _ _ Hal) in Hv.
  clear dependent e. duplicate Hv. inverts Hv0 as Hvv Hvvv.
  rewrite Hvvv in Hvv. apply subst_change_prog with (td:=t) in Hvv; auto.
  ssubst_ssubst_aux_eq_hyp  Hdd Hv; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  duplicate Hp. repnud Hp0.
  change_to_ssubst_aux8; [| simpl ;rewrite Hp1; disjoint_reasoningv;fail ].
  apply subst_val in Hv.
  exrepnd. subst.
  unfold subst in Hvv.
  ssubst_ssubst_aux_eq_hyp  Hff Hvv.
  allsimpl.
  auto.
Qed.
 *)
(* Lemma noncan_ssubst_aux : forall e vy t1 t2,
  isnoncan t1
  -> isnoncan (subst_aux e vy t1)
  -> isnoncan t2
  -> isnoncan (subst_aux e vy t2).
Proof using.
  unfold subst_aux. introv H1n Hisv H2n.
  destruct e as [v | oo llbt]; allsimpl;
  [revert Hisv; cases_if; simpl; introv Hisv; allsimpl; cpx  |].
  destruct oo; cpx.
Qed.
 *)
  
(* Lemma alpha_noncan : forall t1 t2,
  alpha_eq t1 t2
  -> isnoncan t1
  -> isnoncan t2.
Proof using.
  introns Hc.
  d_isnoncan Hc0.
  duplicate Hc as Hcc. invertsn Hc. 
  constructor.
Qed. *)
  
(* Lemma noncan_ssubst : forall e vx t1 t2,
  isnoncan t1
  -> isnoncan (subst e vx t1)
  -> isnoncan t2
  -> isnoncan (subst e vx t2).
Proof using.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply ssubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_noncan _ _ Hfr0).
  apply ssubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_noncan _ _ Hal) in H1snc.
  clear dependent e.
  ssubst_ssubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_ssubst_aux8; [| simpl; disjoint_reasoningv;fail ].
  eapply noncan_ssubst_aux with (t1:=t1); eauto.
Qed. *)

Lemma alpha_prog_eauto:
 forall t1 t2 : NTerm, alpha_eq t1 t2 -> (isprogram t1 -> isprogram t2).
Proof using.
  introv Hal Hp.
  apply alphaeq_preserves_program in Hal.
  apply Hal; auto.
Qed.

Hint Resolve alpha_prog_eauto : slow.

Lemma ssubst_nest_swap_alpha: forall t sub1 sub2,
  let lvi1 := dom_sub sub1 in
  let lvi2 := dom_sub sub2 in
  let lnt1 := range sub1 in
  let lnt2 := range sub2 in
  disjoint lvi1 (flat_map free_vars lnt2) (*o/w capture will occur in RHS*)
  -> disjoint lvi2 (flat_map free_vars lnt1) (*o/w capture will occur in LHS*)
  -> disjoint lvi1 lvi2 (*o/w order will matter*)
  -> alpha_eq (ssubst(ssubst t sub1) sub2)  (ssubst(ssubst t sub2) sub1).
Proof using.
  introv H2dis H1dis Hdom.
  pose proof (change_bvars_range_wspec3 (flat_map free_vars (range sub1)) sub2) as Hfs.
  exrepnd.
  rename sub' into sub2'.
  pose proof (Hfs0 t) as XX.
  alpharws XX. clear XX.
  pose proof (Hfs0 (ssubst t sub1)) as XX.
  alpharws XX. clear XX.
  rewrite Hfs3 in H1dis.
  rewrite Hfs3 in Hdom.
  rewrite Hfs2 in H2dis.
  clear dependent sub2.
  rename sub2' into sub2.
  pose proof (change_bvars_range_wspec3 (flat_map free_vars (range sub2)) sub1) as Hfss.
  exrepnd.
  rename sub' into sub1'.
  pose proof (Hfss0 t) as XX.
  alpharws XX. clear XX.
  pose proof (Hfss0 (ssubst t sub2)) as XX.
  alpharws XX. clear XX.
  rewrite Hfss3 in H2dis.
  rewrite Hfss3 in Hdom.
  rewrite Hfss2 in H1dis.
  rewrite Hfss2 in Hfs1.
  clear dependent sub1.
  rename sub1' into sub1.
  pose proof (change_bvars_alpha_wspec (flat_map free_vars (range sub1) ++ flat_map free_vars (range sub2)) t) as Hfr.
  exrepnd.
  alpharws Hfr0.
  clear dependent t.
  rename ntcv into t.
  change_to_ssubst_aux8; try(disjoint_ssubst).
  pose proof (ssubst_aux_nest_swap2 t sub1 sub2) as ZZ.
  simpl in ZZ.
  dimp ZZ; auto; disjoint_reasoningv.
  rewrite hyp.
  apply alpha_eq_refl.
Qed.









Lemma alpha_bterm_pair_change3 : forall (bt1 bt2: BTerm) lv nt1 nt2 lvn,
  alpha_eq_bterm bt1 (bterm lv nt1)
  ->  alpha_eq_bterm bt2 (bterm lv nt2)
  -> length lv =length lvn
  -> no_repeats lvn
  ->  disjoint lvn (free_vars_bterm bt1 ++ free_vars_bterm bt2)
  -> { nt1n, nt2n : NTerm $
                  alpha_eq nt1 nt1n
                  # alpha_eq nt2 nt2n
                  # alpha_eq_bterm bt1 (bterm lvn (ssubst nt1n (var_ren lv lvn)))
                  # alpha_eq_bterm bt2 (bterm lvn (ssubst nt2n (var_ren lv lvn)))
                  #  disjoint lvn ((bound_vars nt1n) ++ (bound_vars nt2n))  }.
Proof using. 
  intros. apply alpha_bterm_pair_change4 with (lva := nil);spc.
Qed.


Lemma alphaeqbt1v2 :forall v nt1 nt2 lv,
  alpha_eq_bterm (bterm [v] nt1) (bterm lv nt2)
   -> {v' : NVar $ lv = [v']}.
Proof using.
  introv Hal. duplicate Hal.
  inverts Hal.
  allsimpl.
  repeat(alphahypsd).
  eexists; eauto.
Qed.

(** replace simpl_sub with this *)
Ltac simpl_sub2 :=
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

Ltac simpl_sub4 :=
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

Lemma ssubst_nest3_1vars :  forall t lvi lvo sub subc,
  length lvi = length lvo
  -> disjoint (dom_sub subc) (lvi++lvo)
  -> prog_sub sub
  -> prog_sub subc
  -> alpha_eq  (ssubst (ssubst (ssubst t subc) (var_ren lvi lvo)) sub)
             (ssubst (ssubst (ssubst t (var_ren lvi lvo) ) (sub_filter sub (dom_sub subc)))  subc).
Proof using.
  introv Hlen Hdis Hps Hpr. 
  match goal with 
  [ |- alpha_eq (ssubst (ssubst (ssubst ?t ?subi) ?subo) _) _] => 
      pose proof (ssubst_nest_swap_alpha t subi subo) as ZZ 
  end.
  simpl in ZZ;spcls;
      dimp ZZ;repeat(simpl_sub4);(try match goal with [|- disjoint _ _] => disjoint_reasoningv end).
  clear ZZ. rewrite (@fold_var_ren NVar) in *.
  alpharw hyp. clear hyp.
  match goal with
  [ |- alpha_eq  (ssubst ?t sub) _ ] => 
      dimp (ssubst_sub_filter_alpha t sub (dom_sub subc));
      [apply  progsub_ssubst_disjointfv_domsub; auto|]
  end;[].
  apply alpha_eq_sym in hyp.
  alpharw hyp.
  match goal with
  [ |- alpha_eq  (ssubst (ssubst ?t ?subi) ?subo) _] => 
      pose proof (ssubst_nest_swap_alpha t subi subo) as ZZ; simpl in ZZ; spcls
  end.
  apply sub_filter_sat with (lv:=(dom_sub subc)) in Hps.
  fold (prog_sub (sub_filter sub (dom_sub subc))) in Hps.
  dimp ZZ; spcls; repeat(simpl_sub2);simpl;
  try(apply disjoint_sym; apply disjoint_dom_sub_filt);
  change_to_ssubst_aux4; disjoint_reasoningv.
Qed.

Lemma crary_5_9_aux :  forall t v lvi lvo sub tt,
  length lvi = length lvo
  -> disjoint [v] (lvi++lvo)
  -> prog_sub sub
  -> isprogram tt 
  -> alpha_eq  (ssubst (ssubst (ssubst t [(v, tt)]) (var_ren lvi lvo)) sub)
             (ssubst (ssubst (ssubst t (var_ren lvi lvo) ) (sub_filter sub [v]))  [(v, tt)]).
Proof using.
  intros.
  apply ssubst_nest3_1vars; auto.
  prove_sub_range_sat.
Qed.


(* !! MOVE  to list.v and add to disjoint_reasoning *)
Lemma disjoint_app_r_same : forall {T} (lvi lvo : list T ),
  disjoint lvi lvo
  -> disjoint lvi (lvo ++ lvo).
Proof using.
  introv Hd.
  apply disjoint_app_r; auto.
Qed.


Lemma alphaeqc_sym:
  forall t1 t2, alphaeqc t1 t2 -> alphaeqc t2 t1.
Proof using.
  introv a; destruct_cterms; allunfold alphaeqc; allsimpl.
  apply alpha_eq_sym; sp.
Qed.

Lemma alphaeqc_trans:
  forall t1 t2 t3, alphaeqc t1 t2 -> alphaeqc t2 t3 -> alphaeqc t1 t3.
Proof using.
  introv.
  unfold alphaeqc.
  destruct_cterms; simpl.
  intros a1 a2.
  apply alpha_eq_trans with (nt2 := x0); auto.
Qed.

Global Instance properAlphaNumbvars : Proper (alpha_eq_bterm ==> eq) num_bvars.
exact alphaeqbt_numbvars.
Qed.

Lemma ssubst_oterm : forall (lbt : list BTerm) (o : Opid) (sub: Substitution),
  {lbts : list BTerm | ssubst (oterm o lbt) sub = oterm o lbts
    /\ map num_bvars lbt = map num_bvars lbts}.
Proof using varclass.
  intros ? ? ?.
  simpl.
  eexists. split;[reflexivity|]. rewrite map_map.
  apply eq_maps. intros ? _. 
  unfold compose. simpl.
  rewrite ssubst_ssubst_bterm_aux_alpha.
  add_changebvar_spec ss ssd.
  rewrite num_bvars_bterm.
  repnd. rewrite ssd.
  refl.
Qed.

  
Lemma num_bvars_ssubst_bterm:
  forall  (bt : BTerm) (sub : Substitution),
  num_bvars (ssubst_bterm bt sub) = num_bvars bt.
Proof using varclass.
  intros. rewrite ssubst_ssubst_bterm_aux_alpha.
  rewrite num_bvars_bterm.
  apply alphaeqbt_numbvars.
  symmetry.
  apply change_bvars_alphabt_spec.
Qed.


Global Instance properAlphaSubst : 
  Proper (alpha_eq ==> eq ==>  alpha_eq ==> alpha_eq) subst.
Proof using.
  intros ? ? ? ? ? ? ? ? ?.
  apply properAlphaLSubst; cpx.
Qed.

(** substitution of substitutions *)
Global Instance properAlphaLSubstSub : 
  Proper ((sub_range_rel alpha_eq) ==> (eq (* can be generalized *)) ==> (sub_range_rel alpha_eq)) ssubst_sub.
Proof using.
  intros ? ? Heq s1 s2 Hs.
  subst. apply sub_rel_ssubst_sub_alpha. trivial.
Qed.


Lemma fold_apply_bterm : forall lv (nt : NTerm) lnt,
ssubst nt (combine lv lnt)
= 
apply_bterm (bterm lv nt) lnt.
Proof using.
intros. refl.
Qed.

(* easier to use than [al_bterm]:
1)  it picks the fresh variables ([lv]) for you.
        [lv] is aditionally disjoint from a list [lva] of your choice.
2)  lets you use ssubst_aux, so that you dont have to worry about alpha renaming while
    substitution.
*)
Lemma prove_alpha_bterm1 : 
forall (lva lv1 lv2  : list NVar) (nt1 nt2 : NTerm),
  (forall lv,
        disjoint lv (all_vars nt1 ++ all_vars nt2 ++ lva) ->
        length lv1 = length lv2 ->
        length lv1 = length lv ->
        no_repeats lv ->
        alpha_eq (ssubst nt1 (var_ren lv1 lv)) (ssubst nt2 (var_ren lv2 lv))) 
  -> length lv1 = length lv2
  -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).
Proof.
  intros ? ? ? ? ? Hal Hl.
  pose proof (fresh_vars (length lv1) (all_vars nt1 ++ all_vars nt2 ++ lva)) as Hfr.
  exrepnd.
  specialize (Hal lvn Hfr2 ltac:(congruence) ltac:(congruence) ltac:(assumption)).
  apply al_bterm with (lv:= lvn); spc; disjoint_reasoningv.
Qed.
(*  SearchPattern (alpha_eq_bterm (bterm _ _) (bterm _ _)). 
Print al_bterm
*)

(* easier to use than [al_bterm]:
1)  it picks the fresh variables ([lv]) for you.
        [lv] is aditionally disjoint from a list [lva] of your choice.
2)  lets you use ssubst_aux, so that you dont have to worry about alpha renaming while
    substitution. However, keep in mind that lemmas about [ssubst_aux], e.g. 
    about commuting nested substitutions,  have more
    obligations, e.g. about disjointness of bound variables.
    In that case, use [prove_alpha_bterm1] above
*)
Lemma prove_alpha_bterm : 
forall (lva lv1 lv2  : list NVar) (nt1 nt2 : NTerm),
  (forall lv,
        disjoint lv (all_vars nt1 ++ all_vars nt2 ++ lva) ->
        length lv1 = length lv2 ->
        length lv1 = length lv ->
        no_repeats lv ->
        alpha_eq (ssubst_aux nt1 (var_ren lv1 lv)) (ssubst_aux nt2 (var_ren lv2 lv))) 
  -> length lv1 = length lv2
  -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).
Proof.
  intros ? ? ? ? ? Hal Hl.
  apply (prove_alpha_bterm1 lva); auto.
  intros.
  change_to_ssubst_aux8.
  change_to_ssubst_aux8.
  eauto.
Qed.

(*
Ltac disjoint_reasoning :=
match goal with
| [  |- disjoint _ (_ ++ _) ] => apply disjoint_app_r;split
| [  |- disjoint (_ ++ _) _ ] => apply disjoint_app_l;split
| [  |- disjoint _ _ ] => (sp;fail  || apply disjoint_sym; sp;fail)
(** important to leave it the way it was .. so that repeat progress won't loop*)
| [ H: disjoint _ (_ ++ _) |- _ ] => apply disjoint_app_r in H;sp
| [ H: disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H;sp
| [ H: !(disjoint  _ []) |- _ ] => provefalse; apply H; apply disjoint_nil_r
| [ H: !(disjoint  [] _) |- _ ] => provefalse; apply H; apply disjoint_nil_l
| [ H: (disjoint  _ []) |- _ ] => clear H
| [ H: (disjoint  [] _) |- _ ] => clear H
end.
*)


Lemma ssubst_trivial_disjoint_dom:
  forall (t : NTerm) (sub : Substitution),
  disjoint (free_vars t) (dom_sub sub) 
  -> alpha_eq  (ssubst t sub) t.
Proof.
  introv H.
  erewrite <- ssubst_sub_filter_alpha;[| apply H].
  setoid_rewrite (sub_filter_nil_combine sub []).
  rewrite ssubst_nil.
  refl.
Qed.

Lemma ssubst_sub_trivial_disjoint_dom:
forall sub1 sub2 : Substitution,
disjoint (dom_sub sub1) (flat_map free_vars (range sub2)) ->
sub_range_rel alpha_eq (ssubst_sub sub2 sub1) sub2.
Proof.
  intros.
  induction sub2 as [| (v,tt) sub2 Hind ];[refl|].
  simpl in *. split; [refl|].
  split.
- rewrite ssubst_trivial_disjoint_dom; [refl| disjoint_reasoningv].
- apply Hind; disjoint_reasoningv.
Qed.

Lemma ssubst_nest_swap_as_app
     : forall (t : NTerm) (sub1 sub2 : Substitution),
       let lvi1 := dom_sub sub1 in
       let lvi2 := dom_sub sub2 in
       let lnt1 := range sub1 in
       let lnt2 := range sub2 in
       disjoint lvi1 (flat_map free_vars lnt2) ->
       disjoint lvi2 (flat_map free_vars lnt1) ->
       disjoint lvi1 lvi2 ->
       alpha_eq (ssubst (ssubst t sub1) sub2) (ssubst t (sub2++sub1)).
Proof.
  simpl. intros.
  rewrite ssubst_nest_swap_alpha; auto.
  rewrite combine_sub_nest.
  f_equiv.
  apply sub_range_rel_app.
  split;[| refl]. clear H1 H0.
  rewrite ssubst_sub_trivial_disjoint_dom; auto.
  refl.
Qed.

Lemma alpha_bterm_cons : forall (lv1 lv2  : list NVar) (nt1 nt2 : NTerm) v,
  disjoint [v] (lv1 ++ lv2)
  -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2)
  -> alpha_eq_bterm (bterm (v::lv1) nt1) (bterm (v::lv2) nt2).
Proof.
  intros ? ? ? ? ? Hdis Hal. 
  apply (prove_alpha_bterm1 ([v]++lv1++lv2)); simpl; [| inverts Hal; auto].
  intros ? Hd H1l H2l Hnr.
  dlist_len_name lv vv.
  inverts Hnr as Hnr Hin.
  apply alphabt_change_var with (lv:=lv)in Hal; auto;[| disjoint_reasoningv].
  unfold var_ren. simpl.
  repnd.
  pose proof (@properAlphaSubst _ _ Hal0 v v eq_refl (vterm vv) (vterm vv) ltac:(refl))
    as Hall. clear Hal.
  unfold subst in Hall.
  let t := repeat (progress disjoint_reasoning2) in
  rewrite ssubst_nest_swap_as_app in Hall; simpl; spcls;
    [| t |  t | t];[];
  rewrite ssubst_nest_swap_as_app in Hall; simpl; spcls;
    [t | t |  t ].
Qed.

(*
Lemma 
apply_bterm_alpha_congr_nested:
  forall lv1in lv2in lv1out lv2out nt1 nt2 o lnt1in lnt2in lnt1out lnt2out,
  alpha_eq_bterm (bterm lv1out (oterm o [bterm lv1in nt1]))
                 (bterm lv2out (oterm o [bterm lv2in nt2])) ->
  bin_rel_nterm alpha_eq lnt1in  lnt2in ->
  bin_rel_nterm alpha_eq lnt1out lnt2out ->
  length lnt1in  = length lv1in  ->
  length lnt1out = length lv1out
  -> alpha_eq (ssubst (ssubst nt1 (combine lv1in lnt1in)) (combine lv1out lnt1out))
              (ssubst (ssubst nt2 (combine lv2in lnt2in)) (combine lv2out lnt2out)).
Proof.
  intros.
  simpl in *. inverts H.
   SearchAbout (ssubst (ssubst _ _) _). 
   repeat alphahypsd2.
  apply apply_bterm_alpha_congr with (lnt1:= lnt1out) (lnt2:= lnt2out)  in H;
    unfold num_bvars; simpl; auto.
  unfold apply_bterm in H.
  simpl in H.
  SearchAbout ssubst oterm.  
  apply apply_bterm_alpha_congr with (lnt1:= lnt1out) (lnt2:= lnt2out)  in H.
  simpl in H.
   simpl ; auto.
  
  repeat rewrite fold_apply_bterm.
  apply apply_bterm_alpha_congr; simpl ; auto.
  econstructor. Focus 5.
  
  SearchAbout (alpha_eq_bterm (bterm _ _) (bterm _ _)). 
              
SearchAbout alpha_eq_bterm apply_bterm.
*)


Lemma alpha_eq_bterm_nil : forall o lnt t2,
alpha_eq (oterm o (map (bterm []) lnt)) t2
-> exists lnt2, t2 =  (oterm o (map (bterm []) lnt2))
  /\ bin_rel_nterm alpha_eq lnt lnt2.
Proof using.
  intros ? ? ? Hal.
  inverts Hal. rewrite map_length in *.
  rename H3 into Hbts.
  exists (map get_nt lbt2).
  rewrite map_map.
  rewrite <- (map_id lbt2) at 1.
  unfold compose.
  eapply and_weaken_l;
    [intros; f_equal; apply H|].
  unfold bin_rel_nterm, binrel_list.
  rewrite map_length. 
  rewrite <- and_assoc.
  eapply and_weaken_l;
    [intros; split; auto; apply H|].
  eapply and_weaken_l;
    [intros; apply eq_maps_bt; auto; apply H|].
  rewrite <- H1.
  apply forall_combine.
  intros n Hlt.
  
  specialize (Hbts n Hlt).
  unfold selectbt at 1 in Hbts.
  rewrite map_nth in Hbts.
  repeat alphahypsd.
  rewrite Hbts1.
  split;[refl|].
  change (vterm nvarx) with (get_nt (bterm [] (vterm nvarx))).
  rewrite map_nth.
  setoid_rewrite Hbts1.
  simpl. assumption.
Qed.

Local Notation fvars := free_vars.
Local Notation subst := ssubst.

Local Lemma alpharwtest : forall x y sub lv,
alpha_eq x y
-> disjoint (fvars (subst x sub)) lv
-> disjoint (fvars (subst y sub)) lv.
Proof.
  intros ? ? ? ? H1a Hs.
  rewrite <- H1a.
  assumption.
Qed.

End AlphaGeneric.

Ltac ntwfauto :=
unfold apply_bterm in *;
unfold subst in *;
(repeat match goal with
[ |- nt_wf (ssubst _ _)] => 
  let Hsub := fresh "Hsub" in
  apply ssubst_wf_iff;[intros ? ? Hsub; try in_reasoning; cpx|]
| [ H: nt_wf (ssubst _ _) |- _ ] => 
  let Hb := fresh H in
  pose proof H as Hb;
  apply ssubst_nt_wf in Hb
| [ H: nt_wf ?x |- _ ] => 
  let H1 := fresh "Hntwf" in
  let H2 := fresh "HntwfSig" in
    inverts H as H1 H2;[]; simpl in H1; dLin_hyp
| [ H: _ -> (nt_wf _) , H1:_ |- _ ] => apply H in H1; clear H
| [ H: forall (_:_),  _ -> (nt_wf _) , H1:_ |- _ ] => apply H in H1
| [ H: forall (_:_),  _ -> (bt_wf _) , H1:_ |- _ ] => apply H in H1
| [ H: bt_wf (bterm _ _) |- _ ] => apply bt_wf_iff in H
| [ |- nt_wf (vterm _)] => constructor
| [ |- bt_wf _] => constructor
| [ |- nt_wf _] => 
  let Hin := fresh "HntwfIn" in
    constructor; [try (intros ? Hin; simpl in Hin; in_reasoning; subst;  cpx)|]
end); cpx.

(* copied from the above section *)
Ltac alphahypsd2 := simpl;
  match goal with 
  | [H: S _ = length ?l |- _ ] => let ls := fresh l "s" in 
        destruct l as [| ls l]; simpl in H; inverts H as H
  | [H: length ?l = S _ |- _ ] => symmetry in H
  | [H: alpha_eq (oterm ?o _) _ |- _] => let H1:= fresh H "len" in
              let H2:= fresh H "bts" in
              inverts H as H1 H2; simpl in H1; simpl in H2     
  | [H: (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _)  |- _ ] => 
    
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX;  simpl in XXX;
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX;  simpl in XXX;
      unfold selectbt in XXX; simphyps); hide_hyp H
  | [H: alpha_eq_bterm (bterm [] _) (bterm [] _) |- _] => apply alphaeqbt_nilv2 in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_] _) _ |- _] => apply alphaeqbt_1v in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_,_] _) _ |- _] => apply alphaeqbt_2v in H; exrepnd; subst
  end.
  Ltac alphahypsd3 :=
  match goal with 
  | [H: 1 = length _ |- _ ] => symmetry in H; apply length1 in H; exrepnd; subst
  | [H: 2 = length _ |- _ ] => symmetry in H; apply length2 in H; exrepnd; subst
  | [H: 3 = length _ |- _ ] => symmetry in H; apply length3 in H; exrepnd; subst
  | [H: 0 = length _ |- _ ] => symmetry in H; apply length0 in H; subst
  | [H: _ = S (length _) |- _ ] =>  inverts H as H
  | [H: (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _)  |- _ ] => 
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps); hide_hyp H
  | [H: alpha_eq_bterm (bterm [] _) (bterm [] _) |- _] => apply alphaeqbt_nilv2 in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_] _) _ |- _] => apply alphaeqbt_1v in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_,_] _) _ |- _] => apply alphaeqbt_2v in H; exrepnd; subst
  end.

Ltac alphahypdfv H :=
match type of H with
| (forall _:nat, (_< ?m) -> alpha_eq_bterm _ _) => 
  (let XXX:= fresh H "0bt" in
  assert (0<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps);
  try (let XXX:= fresh H "1bt" in
  assert (1<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps);
  try (let XXX:= fresh H "2bt" in
  assert (2<m) as XXX by omega; apply H in XXX; 
  unfold selectbt in XXX; simphyps); try (fail_if_not_number m; clear H)
end.

Ltac prove_bin_rel_nterm := 
  split;[sp|simpl];[];
  intros n Hlt; repeat (destruct n; try(omega));sp.

Ltac prove_alpha_eq4 := unfold_all_mk; let Hlt := fresh "Hltalc" in
match goal with
| [ |- alpha_eq ?t ?t] => apply alpha_eq_refl
| [ |- alpha_eq (oterm ?o _) (oterm ?o _)] => constructor;simpl;[repeat(simpl_list);spc
                                                  | unfold selectbt;simpl]
| [ |- alpha_eq ?t1 ?t2] => auto ; fail
| [ |- forall _, _ < _ -> alpha_eq_bterm _ _ ] => introv Hlt;repeat(simpl_list);repeat(dlt Hlt)
| [ |- alpha_eq_bterm ?t ?t ] => apply alphaeqbt_refl
| [ |- alpha_eq_bterm (bterm [] _) (bterm [] _) ] => apply alphaeqbt_nilv2 
end.

Ltac add_changebvar_spec cb Hn:=
match goal with 
| [ |- context[change_bvars_alpha ?lv ?nt] ] => pose proof (change_bvars_alpha_spec nt lv) as Hn;
    remember (change_bvars_alpha  lv nt) as cb; simpl in Hn
| [ |- context[change_bvars_alphabt ?lv ?nt] ] => pose proof (change_bvars_alphabt_spec lv nt) as Hn;
    remember (change_bvars_alphabt  lv nt) as cb; simpl in Hn
end.

Ltac dfresh_vars :=
match goal with
[|- context[ fresh_vars ?n ?lv]] =>
  let Hfr := fresh "Hfr" in 
  let lvn := fresh "lvn" in 
    destruct (fresh_vars n lv) as [lvn Hfr]
end.

Ltac dnumvbars H btt :=
match type of H with
map num_bvars ?lbt = ?h::?t =>
let bt := fresh btt in 
let btlv := fresh bt "lv" in 
let btnt := fresh bt "nt" in 
let Hbt := fresh bt "H" in 
destruct lbt as [|bt lbt];[inverts H| inverts H as Hbt H];[];
destruct bt as [btlv btnt]; unfold num_bvars in Hbt; simpl in Hbt;
dlist_len_name btlv btlv;  try dnumvbars H btt

| map num_bvars ?lbt = [] => 
destruct lbt;[ clear H | inverts H]
end.

Ltac noRepDis2 :=
autorewrite with SquiggleEq;
(repeat match goal with
[H: no_repeats [] |- _] => clear H
|[H: ! (LIn _ _) |- _] => apply disjoint_singleton_l in H
|[|- ! (LIn _ _)] => apply disjoint_singleton_l
|[H: no_repeats (_::_) |- _] =>
  let Hnrd := fresh "Hnrd" in
  apply no_repeats_as_disjoint in H;
  destruct H as [Hnrd H]
end); disjoint_reasoningv; 
repeat rewrite in_single_iff in *; subst; try tauto.
(*
This section should be moved to SquiggleEq-parametricity.
(SquiggleEq should not depend on parametricity because 
the parametricity plugin may depend on it.)

Compiling this section needs a parametricity plugin.
Currently, the following one can be used.
https://github.com/aa755/paramcoq/tree/v86
*)
Declare ML Module "paramcoq".
Require Import Common.TermAbs.
Parametricity Recursive TermAbs.
Require Import SquiggleEq.bin_rels.
Require Import SquiggleEq.eq_rel.
Require Import SquiggleEq.universe.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varInterface.
Require Import SquiggleEq.export.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.
Definition t_iff (a b: Type) := (prod (a->b) (b->a)).


Class EqIfR {A:Type} (Ar : A -> A-> Type)  := eqIfR: forall (a1 a2:A), 
  t_iff (Ar a1 a2) (a1=a2).

Global Instance EqIfReq {A:Type}: EqIfR (@eq A).
Proof using.
  constructor; tauto.
Qed.

Inductive list_RP {A₁ A₂ : Type} (A_R : A₁ -> A₂ -> Prop) : list A₁ -> list A₂ -> Prop :=
    nil_R : list_RP A_R [] []
  | cons_R : forall (H : A₁) (H0 : A₂),
                    A_R H H0 ->
                    forall (H1 : list A₁) (H2 : list A₂),
                    list_RP  A_R H1 H2 -> list_RP A_R (H :: H1) (H0 :: H2).

Lemma list_RP_same (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Prop) : forall l1 l2,
  t_iff (list_R _ _ A_R l1 l2) (list_RP A_R l1 l2).
Proof using.
  induction l1; intros l2; split; intros Hyp; 
    destruct l2; try inverts Hyp; try constructor; try eauto;
    try (provefalse; inverts Hyp; fail); try apply IHl1; eauto;
    try inverts Hyp; auto.
Qed.

Lemma list_Rext (A₁ A₂ : Type) (A_R1 A_R2 : A₁ -> A₂ -> Prop) :
  (forall a1 a2, (A_R1 a1 a2) <-> (A_R2 a1 a2))
  -> forall l1 l2,
  (list_RP A_R1 l1 l2) <-> (list_RP A_R2 l1 l2).
Proof using.
  intros Hext. unfold t_iff in *.
  induction l1; intros l2; split; intros Hyp; 
    destruct l2; try inverts Hyp; try constructor; try eauto;
    try (provefalse; inverts Hyp; fail); try apply IHl1; eauto;
    try inverts Hyp; firstorder.
Qed.

(* SquiggleEq uses this style in the definition of alpha equality *)
Definition binrel_list
{A₁ A₂ : Type} (A_R : A₁ -> A₂ -> Type)
tls trs :=
prod
(length tls = length trs)
(forall n : nat, (n < length tls)%nat -> option_R _ _ A_R (select n tls) (select n trs)).

Definition list_R_binrel_list (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Prop) : forall l1 l2,
  t_iff (list_R _ _ A_R l1 l2) (binrel_list A_R l1 l2).
Proof using.
  unfold binrel_list, t_iff.
  induction l1; intros l2; split; intros Hyp; 
    destruct l2; try inverts Hyp; try constructor; try eauto;
    try (provefalse; inverts Hyp; fail); try apply IHl1; eauto;
    try inverts Hyp; simpl in *; intros; try firstorder; try omega.
- apply IHl1 in X3; cpx.
- destruct n; simpl; [constructor; auto |].
  apply IHl1; auto. omega.
- specialize (X O ltac:(omega)).
  inverts X. auto.
- specialize (X (S n) ltac:(omega)).
  simpl in X. assumption.
Qed.

Definition list_R_binrel_list_old (A : Type) (A_R : A -> A -> Prop) (def:A) : forall l1 l2,
  t_iff (list_R _ _ A_R l1 l2) (list.binrel_list def A_R l1 l2).
Proof using.
  unfold list.binrel_list, t_iff.
  induction l1; intros l2; split; intros Hyp; 
    destruct l2; try inverts Hyp; try constructor; try eauto;
    try (provefalse; inverts Hyp; fail); try apply IHl1; eauto;
    try inverts Hyp; simpl in *; intros; try firstorder; try omega.
- apply IHl1 in X3; cpx.
- destruct n; simpl; auto.
  apply IHl1; auto. omega.
- rename H0 into X. specialize (X O ltac:(omega)).
  inverts H. auto.
- rename H0 into X. specialize (X (S n) ltac:(omega)).
  simpl in X. assumption.
Qed.

Lemma list_R_map {A B:Type} (f:A->B) (B_R : B -> B -> Type ): forall la lb,
t_iff
(list_R _ _ (fun a b => B_R (f a) b) la lb)
  (list_R _ _ B_R (map f la) lb).
Proof using.
  induction la; destruct lb as [|b lb]; split; intros Hyp; inverts Hyp;
    simpl in *; try constructor; eauto; apply IHla; auto. 
Qed.

Lemma list_R_map_lforall {A B:Type} (f:A->B)  (A_P : A -> Prop) (B_R : B -> B -> Prop): forall la lb,
t_iff
(list_R _ _ (fun a b => A_P a /\ B_R (f a) b) la lb)%type
  ((lforall A_P la) * (list_R _ _ B_R (map f la) lb))%type.
Proof using.
  unfold lforall.
  induction la; destruct lb as [|b lb]; split; intros Hyp;  dands; repnd; inverts Hyp;
    simpl in *; try constructor; eauto; try apply IHla; auto; try tauto.
  intros ? Hin. dorn Hin; subst; repnd; auto.
  apply IHla in X3. firstorder.
Qed.


Global Instance nat_R_eq : EqIfR nat_R.
Proof.
  intros x.
  induction x; intros y; split; intros Hy; subst; try inversion Hy; auto.
- constructor.
- subst. apply IHx in H2. congruence.
- constructor. apply IHx. reflexivity.
Qed.

Global Instance prod_R_eq  {A B} (A_R : A->A->Type) (B_R : B -> B -> Type) :
  EqIfR A_R -> EqIfR B_R -> EqIfR (prod_R _ _ A_R _ _  B_R).
Proof.
  intros Ha Hb x y.  split; intros Hyp.
- inverts Hyp. f_equal; try apply Ha; try apply Hb; eauto.
- subst. destruct y. constructor; try apply Ha; try apply Hb; eauto.
Qed.

Global Instance option_R_eq  {A} (A_R : A->A->Type) :
  EqIfR A_R -> EqIfR (option_R _ _ A_R).
Proof.
  intros Ha x y.  split; intros Hyp.
- inverts Hyp; auto. f_equal; try apply Ha; eauto.
- subst. destruct y; constructor. try apply Ha; eauto.
Qed.

Global Instance list_R_eq  {A} (A_R : A->A->Type) :
  EqIfR A_R -> EqIfR (list_R _ _ A_R).
Proof.
  intros Ha x. induction x; intros y; split; intros Hyp; try invertsn Hyp; subst;
  try constructor; try f_equal; auto; try apply Ha; try apply IHx; auto.
Qed.

Parametricity Recursive GenericTermSig.
Definition eq_GenericTermSig_R   (Opid:Type) (gts : GenericTermSig Opid) :
  GenericTermSig_R Opid Opid eq gts gts.
Proof using.
  destruct gts.
  eapply GenericTermSig_R_Build_GenericTermSig_R.
  intros.
  apply eqIfR.
  f_equal; auto.
Defined.

Infix "<=>" := t_iff.

Section ParamRels.
(* this context list was copied from SquiggleEq.termsDB *)
Context {Name NVar VarClass Opid : Type} {deqv vcc fvv}
  `{vartyp: @VarType NVar VarClass deqv vcc fvv}
  `{deqo: Deq Opid} {gts : GenericTermSig Opid} (def:Name).

Definition TermAbs_R_NamedAlphaClosedWf Opid_R {Hoeq: @EqIfR Opid Opid_R}: 
TermAbs_R Opid Opid Opid_R
    (Named.TermAbsImpl NVar Opid)
    (Named.TermAbsImpl NVar Opid).
Proof using vartyp deqo def gts.
  (* could also have used the arity 1 version. but that would need many lemmas *)
  eapply TermAbs_R_Build_TermAbs_R with 
    (AbsTerm_R := fun t1 t2  => isprogram t1 /\ t1 = t2)
      (AbsBTerm_R := fun t1 t2  => isprogram_bt t1 /\ t1 = t2); [ | | | | | ].
- intros ? ? Hp. apply nat_R_eq.  repnd. subst. refl.
- intros t1 t Hp. repnd. subst. destruct t; try constructor.
  constructor;[ apply eqIfR; refl | ].
  apply  list_R_map_lforall. split.
  + apply isprogram_ot_iff in Hp0. repnd. assumption.
  + rewrite map_id. apply list_R_eq;[constructor; tauto | refl].
- intros b1 b Hpr. repnd. subst. destruct b as [lv ?].
  destruct lv; constructor.
  apply isprogram_bt_nobnd in Hpr0. auto.
- intros b1 b Hpr lt1 lt Hpt. repnd. subst.
  apply list_R_map_lforall in Hpt.
  rewrite map_id in Hpt.
  repnd.  apply list_R_eq in Hpt; [ | eauto with typeclass_instances].
  subst. unfold Named.applyBTermClosed. case_if as Hd; constructor.
  apply beq_nat_true in Hd.
  split;[| refl ].
  apply isprogram_bt_implies; auto.
- intros ? lt Hlt ? o Ho.
  apply eqIfR in Ho. subst.
  apply list_R_map_lforall in Hlt.
  rewrite map_id in Hlt. repnd.
  apply list_R_eq in Hlt; [ | eauto with typeclass_instances]. subst.
  constructor.
(* To preserve nt_wf, Named.mkBTermSafe must do a check that (map num_bvars lbt) is correct,
even when lbt are isprogram_bt *)
Abort.

Lemma alpha_eq_ot_list_R (o:Opid) (la: list (@BTerm NVar Opid)) lb:
  alpha_eq (terms.oterm o la) (terms.oterm o lb)
  <=> list_R _ _ alpha_eq_bterm la lb.
Proof using.
  split;
  intros Hal.
- apply list_RP_same.
  inverts Hal as Hlen Hlb. revert Hlen. revert Hlb. revert lb.
  induction la; intros; destruct lb;inverts Hlen; constructor; simpl in *.
  + specialize (Hlb O ltac:(omega)). exact Hlb.
  + apply IHla; auto. intros n ?. specialize (Hlb (S n) ltac:(omega)).
    assumption.
- apply list_R_binrel_list_old with (def:=(terms.bterm [] (terms.vterm nvarx)))
    in Hal. destruct Hal as [Hl Hlb].
  constructor; auto.
Qed.

Lemma alpha_eq_list (la lb: list (@NTerm NVar Opid)):
  bin_rel_nterm alpha_eq la lb
  <=> list_R _ _ alpha_eq la lb.
Proof using.
  split; intros H; eapply list_R_binrel_list_old; eauto.
Qed.

Require Import SquiggleEq.termsDB.
Section DBToNamed.

  Variable mkNVar: (N * Name) -> NVar.
  Variable getId: NVar -> N.
  Hypothesis getIdCorr: forall p n, getId (mkNVar (p,n)) = p.

  Definition Term_R := fun (d: @DTerm Name Opid) (n: @NTerm NVar Opid) =>
    fvars_below 0 d
    /\ alpha_eq (fromDB def mkNVar 0 FMapPositive.Empty d) n.


  Definition BTerm_R := fun (d: @DBTerm Name Opid) (n: @BTerm NVar Opid) =>
    fvars_below_bt 0 d
    /\ alpha_eq_bterm (fromDB_bt def mkNVar 0 FMapPositive.Empty d) n.

(* used many times in TermAbs_R_NamedDB *)
Lemma numBvars_R :
forall (H : DBTerm) (H0 : BTerm), BTerm_R H H0 -> (num_bvars H) = (terms.num_bvars H0).
Proof using.
  intros b ? Hal. apply proj2 in Hal.
  rewrite <- Hal. destruct b. simpl.
  unfold num_bvars.
  unfold terms.num_bvars.
  simpl. rewrite lengthMapCombineSeq. refl.
Qed.





Definition TermAbs_R_NamedDB Opid_R {Hoeq: @EqIfR Opid Opid_R}: 
TermAbs_R Opid Opid Opid_R
    (TermAbsDB Name Opid)
    (Named.TermAbsImpl NVar Opid).
Proof using vartyp mkNVar getIdCorr getId deqo def gts.
  eapply TermAbs_R_Build_TermAbs_R with 
    (AbsTerm_R := Term_R)
    (AbsBTerm_R := BTerm_R).
- intros ? ? ?. apply nat_R_eq. apply numBvars_R. assumption.
- intros d n Hal.  unfold Term_R in Hal. repnd.
  destruct d.
  + destruct n;[| provefalse; inverts Hal].
    simpl. constructor. 
  + destruct n;[provefalse; inverts Hal |].
    simpl in *. pose proof Hal as Halb.
    apply alphaGetOpid in Hal.
    simpl in Hal. inverts Hal.
    constructor.
    constructor;[apply eqIfR; refl|].
    apply alpha_eq_ot_list_R in Halb.
    unfold BTerm_R.
    apply list_RP_same.
    inverts Hal0.
    apply list_RP_same.
    apply (list_R_map_lforall). dands; auto.
- intros d b Hal. unfold BTerm_R in *. repnd.
  unfold safeGetNT.
  unfold Named.safeGetNT.
  pose proof Hal as Halb.
  apply properAlphaNumbvars in Hal.
  destruct d, b. unfold terms.num_bvars in *. simpl in *.
  rewrite lengthMapCombineSeq in Hal.
  destruct l, l0; inverts Hal; constructor.
  simpl in Halb. inverts Hal0.
  apply alphaeqbt_nilv2 in Halb. simpl in H1. split; assumption.
- intros d b Hal ld ln Hall.
  unfold applyBTermClosed, Named.applyBTermClosed.
  pose proof Hal as Halb.
  apply numBvars_R in Hal.
  rewrite <- Hal.
  pose proof Hall as Hallb.
  apply list_R_binrel_list in Hallb. apply fst in Hallb.
  rewrite Hallb. destruct d as [lnm dt].
  cases_if as Hc; simpl; constructor;[].
  apply DecidableClass.Decidable_eq_nat_obligation_1 in Hc.
  unfold num_bvars, NLength, terms.num_bvars in *. simpl in *.
  apply list_R_map_lforall in Hall. repnd.
  unfold BTerm_R in *. repnd. invertsn Halb0.
  rewrite N.add_0_r in Halb0. 
  split;
    [eapply fvars_below_subst_aux_list; eauto; unfold NLength in *; congruence |].
  rewrite fromDB_ssubst_eval2
    with (ln0:=lnm);unfold NLength in *; eauto;[| congruence].
  apply apply_bterm_alpha_congr with 
      (lnt1:= (map (fromDB def mkNVar 0 FMapPositive.Empty) ld))
      (lnt2 := ln) in Halb; unfold terms.num_bvars; simpl; autorewrite with list;
        [ |apply alpha_eq_list; assumption | congruence].
  rewrite <- Halb.
  unfold apply_bterm. simpl.
  assert (forall (x y : @NTerm NVar Opid) , x= y -> alpha_eq x y) 
    by (intros; subst; refl).
  apply H. f_equal;[congruence|].
  f_equal.
  match goal with
  [|- ?l=_] => remember l
  end.
  erewrite namesInsWierd1 with (def0:=def) (nf:=0) (names:=FMapPositive.Empty); eauto.
  subst. simpl.
  rewrite Hc,<- Hallb.
  rewrite map_map.
  apply eq_maps.
  intros.
  setoid_rewrite N.sub_0_r. refl.
- intros d b Hal ? ln Hall. subst.
  unfold mkBTermSafe.
  unfold Named.mkBTermSafe.
  constructor.
  apply list_R_map_lforall in Hal.
  split;[constructor; apply Hal|];[]. simpl.
  apply eqIfR in Hall. subst.
  apply alpha_eq_ot_list_R.
  tauto.
- unfold Term_R, BTerm_R. intros ? ? Hfb.
  simpl. repnd.
  rewrite Hfb. split;[constructor; simpl; assumption| refl].
Defined.

(*
Definition TermAbs_R_NamedDB2 :  
  TermAbs_R Opid Opid eq gts gts (eq_GenericTermSig_R Opid gts) 
    (TermAbsDB Name Opid)
    (Named.TermAbsImpl NVar Opid):=
TermAbs_R_NamedDB (eq_GenericTermSig_R Opid gts).
*)




End DBToNamed.

End ParamRels.



Require Import FunInd.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(** well-formedness of environs **)
Definition WFaEc: envClass Term -> Prop := AstCommon.WFaEc WFapp.
Definition WFaEnv: environ Term -> Prop := AstCommon.WFaEnv WFapp.

Lemma Lookup_pres_WFapp:
  forall p, WFaEnv p -> forall nm ec, Lookup nm p ec -> WFaEc ec.
Proof.
  apply AstCommon.Lookup_pres_WFapp.
Qed.

Lemma lookup_pres_WFapp:
    forall p, WFaEnv p -> forall nm ec, lookup nm p = Some ec -> WFaEc ec.
Proof.
  apply AstCommon.lookup_pres_WFapp.
Qed.

Lemma lookupDfn_pres_WFapp:
    forall p, WFaEnv p -> forall nm t, lookupDfn nm p = Ret t -> WFapp t.
Proof.
  apply lookupDfn_pres_WFapp.
Qed.

Definition ecTrm := ecTrm.
Definition ecTyp := ecTyp Term.
Hint Constructors AstCommon.fresh : core.
Hint Constructors AstCommon.Lookup : core.

(** correctness specification for programs (including local closure) **)
Inductive crctTerm: environ Term -> nat -> Term -> Prop :=
| ctRel: forall p n m, crctEnv p -> m < n -> crctTerm p n (TRel m)
| ctProof: forall p n, crctEnv p -> crctTerm p n TProof
| ctLam: forall p n nm bod,
    crctTerm p (S n) bod -> crctTerm p n (TLambda nm bod)
| ctLetIn: forall p n nm dfn bod,
    crctTerm p n dfn -> crctTerm p (S n) bod ->
    crctTerm p n (TLetIn nm dfn bod)
| ctApp: forall p n fn arg,
    crctTerm p n fn -> crctTerm p n arg -> crctTerm p n (TApp fn arg)
| ctConst: forall p n pd nm,
    crctEnv p -> LookupDfn nm p pd -> crctTerm p n (TConst nm)
| ctConstructor: forall p n ipkgNm inum cnum ipkg itp cstr npars nargs,
    crctEnv p -> 
    LookupTyp ipkgNm p npars ipkg ->
    getInd ipkg inum = Ret itp ->
    getCnstr itp cnum = Ret cstr ->
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum npars nargs)
| ctCase: forall p n ipkgNm  npars ipkg bn inum mch brs,
    LookupTyp ipkgNm p npars ipkg ->
    crctTerm p n mch -> crctBs p n brs ->
    crctTerm p n (TCase (mkInd ipkgNm inum, bn) mch brs)
| ctFix: forall p n ds m,
    crctDs p (n + dlength ds) ds -> m < dlength ds ->
    crctTerm p n (TFix ds m)
| ctProj: forall p n prj t, crctTerm p n t -> crctTerm p n (TProj prj t)
(* crctEnvs are closed in both ways *)
with crctEnv: environ Term -> Prop :=
     | ceNil: crctEnv nil
     | ceTrmCons: forall nm s p,
         crctEnv p -> fresh nm p -> crctTerm p 0 s -> crctEnv ((nm, ecTrm s)::p)
     | ceTypCons: forall nm m s p,
         crctEnv p -> fresh nm p -> crctEnv ((nm, ecTyp m s)::p)
with crctBs: environ Term -> nat -> Brs -> Prop :=
     | cbsNil: forall p n, crctEnv p -> crctBs p n bnil
     | cbsCons: forall p n m t ts,
         crctTerm p n t -> crctBs p n ts -> crctBs p n (bcons m t ts)
with crctDs: environ Term -> nat -> Defs -> Prop :=
     | cdsNil: forall p n, crctEnv p -> crctDs p n dnil
     | cdsCons: forall p n dnm bod ix ds,
         isLambda bod -> crctTerm p n bod -> crctDs p n ds ->
         crctDs p n (dcons dnm bod ix ds).
Hint Constructors crctTerm  crctBs crctDs crctEnv : core.
Scheme crct_ind' := Minimality for crctTerm Sort Prop
  with crctBs_ind' := Minimality for crctBs Sort Prop
  with crctDs_ind' := Minimality for crctDs Sort Prop
  with crctEnv_ind' := Minimality for crctEnv Sort Prop.
Combined Scheme crctCrctTsBsDsEnv_ind from
         crct_ind', crctBs_ind', crctDs_ind', crctEnv_ind'.

Inductive crctTerms: environ Term -> nat -> Terms -> Prop :=
| ctsNil: forall p n, crctEnv p -> crctTerms p n nil
| ctsCons: forall p n t ts,
    crctTerm p n t -> crctTerms p n ts -> crctTerms p n (cons t ts).

Lemma Crct_WFTrm:
  (forall p n t, crctTerm p n t -> WFTrm t n) /\
  (forall p n bs, crctBs p n bs -> WFTrmBs bs n) /\
  (forall p n (ds:Defs), crctDs p n ds -> WFTrmDs ds n) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; auto.
Qed.

Lemma Crct_CrctEnv:
  (forall p n t, crctTerm p n t -> crctEnv p) /\
  (forall p n bs, crctBs p n bs -> crctEnv p) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctEnv p) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; intuition.
Qed.

Lemma Crct_up:
  (forall p n t, crctTerm p n t -> crctTerm p (S n) t) /\
  (forall p n bs, crctBs p n bs -> crctBs p (S n) bs) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctDs p (S n) ds) /\
  (forall p, crctEnv p -> True). 
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; try (solve [constructor; assumption]).
  - apply ctRel; try assumption. lia.
  - eapply ctConst; eassumption.
  - eapply ctConstructor; eassumption.
  - eapply ctCase; eassumption.
Qed.

Lemma Crct_UP:
  forall n p t, crctTerm p n t -> forall m, n <= m -> crctTerm p m t.
Proof.
  intros n p t h. induction 1. assumption. apply Crct_up. assumption.
Qed.

Lemma Crct_Up:
  forall n p t, crctTerm p 0 t -> crctTerm p n t.
Proof.
  intros. eapply Crct_UP. eassumption. lia.
Qed.
Hint Resolve Crct_Up Crct_UP : core.
  
Lemma Crct_fresh_Pocc:
  (forall p n t, crctTerm p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n bs, crctBs p n bs ->
                  forall nm, fresh nm p -> ~ PoccBrs nm bs) /\
  (forall p n (ds:Defs), crctDs p n ds ->
                  forall nm, fresh nm p -> ~ PoccDefs nm ds) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; try intros j; auto.
  - inversion_Clear j.
  - inversion_Clear j.
  - inversion_Clear j. specialize (H0 _ H1); contradiction.
  - inversion_Clear j.
    + specialize (H0 _ H3); contradiction.
    + specialize (H2 _ H3); contradiction.
  - inversion_Clear j.
    + specialize (H0 _ H3). contradiction.
    + specialize (H2 _ H3); contradiction.
  - inversion_Clear j. unfold LookupDfn in H1.
    elim (Lookup_fresh_neq H1 H2). reflexivity.
  - inversion_Clear j.
    + unfold LookupTyp in H1. destruct H1.
      elim (Lookup_fresh_neq H1 H4). reflexivity.
  - inversion j. subst nm.
    + unfold LookupTyp in H. destruct H.
      elim (Lookup_fresh_neq H H4). reflexivity.
    + specialize (H1 _ H4); contradiction.
    + specialize (H3 _ H4); contradiction.
  - inversion_Clear j. specialize (H0 _ H2); contradiction.
  - inversion_Clear j. eelim H0; eassumption.
  - inversion j.              
  - inversion_Clear j.
    + specialize (H0 _ H3); contradiction.
    + specialize (H2 _ H3); contradiction.
  - inversion_Clear j.
  - inversion_Clear j.
    + specialize (H1 _ H4); contradiction.
    + specialize (H3 _ H4); contradiction.
Qed.

Lemma Crct_weaken:
  (forall p n t, crctTerm p n t -> 
                 forall nm s, fresh nm p -> crctTerm p 0 s ->
                              crctTerm ((nm,ecTrm s)::p) n t) /\
  (forall p n bs, crctBs p n bs -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctBs ((nm,ecTrm s)::p) n bs) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctDs ((nm,ecTrm s)::p) n ds) /\
  (forall p, crctEnv p ->
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctEnv ((nm,ecTrm s)::p)).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - destruct H1. split; try assumption.
    constructor; try eassumption.
    apply neq_sym. eapply Lookup_fresh_neq; eassumption.
  - destruct H. split; try eassumption.
    pose proof (Lookup_fresh_neq l H4) as k0. constructor.
    + auto.
    + exact l.
Qed.

Lemma Crct_weaken_Typ:
  (forall p n t, crctTerm p n t -> 
                 forall nm s m, fresh nm p ->
                              crctTerm ((nm,ecTyp m s)::p) n t) /\
  (forall p n ts, crctBs p n ts -> 
                  forall nm s m, fresh nm p ->
                               crctBs ((nm,ecTyp m s)::p) n ts) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s m, fresh nm p ->
                               crctDs ((nm,ecTyp m s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - unfold LookupTyp in *. destruct H1. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. apply (Lookup_fresh_neq H1). assumption.
  - destruct H. split; try eassumption.
    pose proof (Lookup_fresh_neq l H4) as k0. constructor.
    + auto.
    + exact l.
Qed.

Lemma Crct_strengthen:
  (forall pp n s, crctTerm pp n s -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrm nm s -> crctTerm p n s) /\
  (forall pp n ss, crctBs pp n ss -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccBrs nm ss -> crctBs p n ss) /\
  (forall pp n ds, crctDs pp n ds -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccDefs nm ds -> crctDs p n ds) /\
  (forall pp, crctEnv pp -> crctEnv (List.tl pp)).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; subst;
    try (econstructor; eapply H0; reflexivity; intros h; elim H2;
         econstructor; eassumption);
    try (econstructor; eassumption).
  - constructor. eapply H0. reflexivity. intros h. elim H2.
    constructor. assumption.
  - constructor. eapply H0. reflexivity.
    + intros h. elim H4. apply PoLetInDfn. assumption.
    + eapply H2. reflexivity. intros h. elim H4. eapply PoLetInBod.
      assumption.                                                   
  - constructor; try assumption. eapply H0. reflexivity.
    + intros h. elim H4. eapply PoAppL. assumption.
    + eapply H2. reflexivity. intros h. elim H4. apply PoAppA. assumption.
  - econstructor. exact H0. unfold LookupDfn in *.
    inversion_Clear H1.
    + elim H3. constructor.
    + eassumption.
  - econstructor; try eassumption; destruct H1.
    + unfold LookupTyp. intuition.
      eapply Lookup_strengthen. eassumption. reflexivity.
      inversion_Clear H1.
      * elim H5. constructor.
      * assumption.
  - econstructor; destruct H.
    + unfold LookupTyp. instantiate (1 := ipkg); intuition.
      destruct (kername_eq_dec nm ipkgNm).
      * subst. elim H5. constructor.
      * instantiate (1:= npars). eapply Lookup_strengthen.
        eassumption. reflexivity. auto.
    + eapply H1. reflexivity. intros h. elim H5. constructor. assumption.
    + eapply H3. reflexivity. intros h. elim H5. apply PoCaseR. assumption.
  - econstructor; try eassumption. eapply H0. reflexivity. intros h.
    elim H3. constructor. assumption.
  - econstructor; try eassumption. eapply H0. reflexivity. intros h.
    elim H2. constructor. assumption.
  - constructor.
    + eapply H0. reflexivity. intros h. elim H4. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H4. apply PoBtl. assumption.
  - constructor; try assumption.
    + eapply H1. reflexivity. intros h. elim H5. constructor. assumption.
    + eapply H3. reflexivity. intros h. elim H5. apply PoDtl. assumption.
  - cbn. eapply (proj1 Crct_CrctEnv). eassumption.
  - cbn. assumption.
Qed.


Lemma TWrong_not_Crct:
  forall p n s, ~ crctTerm p n (TWrong s).
Proof.
  induction p; intros; intros h.
  - inversion h.
  - eelim IHp. destruct a. eapply (proj1 Crct_strengthen _ _ _ h).
    + reflexivity.
    + intros j. inversion j.
Qed.
                                         
(** Crct inversions **)
Lemma Crct_invrt_Rel:
  forall p n m, crctTerm p n (TRel m) -> m < n.
Proof.
  intros. inversion_Clear H. assumption.
Qed.

Lemma Crct_LookupDfn_Crct:
  forall p, crctEnv p -> forall nm t, LookupDfn nm p t -> crctTerm p 0 t.
Proof.
  unfold LookupDfn. induction 1; intros.
  - inversion H.
  - inversion_Clear H2.
    + apply Crct_weaken; try assumption.
    + apply Crct_weaken; try assumption.
      eapply IHcrctEnv. eassumption.
  - inversion_Clear H1. apply (proj1 Crct_weaken_Typ); try assumption.
    eapply IHcrctEnv. eassumption.
Qed.    
      
Lemma Crct_invrt_Const:
  forall p n const, crctTerm p n const ->
  forall nm, const = TConst nm ->
       exists pd, (LookupDfn nm p pd /\ crctTerm p 0 pd).
Proof.
  induction 1; intros; try discriminate. myInjection H1. 
  pose proof (Crct_LookupDfn_Crct H H0). exists pd. intuition.
Qed.

Lemma Crct_invrt_Lam:
  forall p n nm bod, crctTerm p n (TLambda nm bod) -> crctTerm p (S n) bod.
Proof.
  intros. inversion_Clear H. assumption.
Qed.

Lemma Crct_invrt_LetIn:
  forall p n nm dfn bod, crctTerm p n (TLetIn nm dfn bod) ->
     crctTerm p n dfn /\ crctTerm p (S n) bod.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_App:
  forall p n fn arg,
    crctTerm p n (TApp fn arg) -> crctTerm p n fn /\ crctTerm p n arg.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Case:
  forall p n m s us,
    crctTerm p n (TCase m s us) -> crctTerm p n s /\ crctBs p n us.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Proof:
  forall p n, crctTerm p n TProof -> crctEnv p.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Fix:
  forall p n ds m, crctTerm p n (TFix ds m) ->
                   crctDs p (n + dlength ds) ds.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

(************
Lemma Crct_invrt_Construct:
  forall p n ipkgNm inum cnum npars nargs args,
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum npars nargs args) ->
    exists itypk,
      LookupTyp ipkgNm p npars itypk /\
      exists (ip:ityp), getInd itypk inum = Ret ip /\
                        exists (ctr:Cnstr), getCnstr ip cnum = Ret ctr.
Proof.
  intros. inversion_Clear H. 
  + exists ipkg. intuition. exists itp. intuition. exists cstr. intuition.
Qed.

Lemma CrctDs_invrt:
  forall n p dts, crctDs p n dts -> 
    forall m x, dnthBody m dts = Some x -> crctTerm p n x.
Proof.
  induction 1; intros.
  - cbn in H0. discriminate.
  - destruct m.
    + cbn in H2. myInjection H2. assumption.
    + eapply IHcrctDs. cbn in H2. eassumption.
Qed.


Lemma Instantiate_pres_Crct:
  forall tin, 
    (forall n bod ins,
       Instantiate tin n bod ins ->
       forall m p, n <= m -> crctTerm p (S m) bod -> crctTerm p m tin ->
                   crctTerm p m ins) /\
    (forall n bods inss,
       Instantiates tin n bods inss ->
       forall m p, n <= m -> crctTerms p (S m) bods -> crctTerm p m tin ->
                   crctTerms p m inss) /\
    (forall n bods inss,
       InstantiateBrs tin n bods inss ->
       forall m p, n <= m -> crctBs p (S m) bods -> crctTerm p m tin ->
                   crctBs p m inss) /\
    (forall n ds ids,
       InstantiateDefs tin n ds ids ->
       forall m p, n <= m -> crctDs p (S m) ds -> crctTerm p m tin ->
                   crctDs p m ids).
Proof.
  intros tin.
  apply InstTrmsBrsDefs_ind; intros; trivial;
  try (inversion_Clear H0; econstructor; eassumption);
  try (inversion_Clear H1; constructor; try assumption; apply H; assumption).
  - inversion_Clear H0. constructor. assumption. lia.
  - apply ctRel.
    + inversion H0. assumption.
    + inversion H0. lia.
  - inversion_Clear H1; constructor; try assumption; apply H; try assumption.
    lia. apply Crct_up. assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; assumption.                 
    + apply H0; try assumption. lia. apply (proj1 Crct_up). assumption.
  - inversion_Clear H2. constructor.
    + apply H; assumption.
    + apply H0; try assumption.
  - inversion_Clear H2. constructor.
    + eapply H; try eassumption.
    + eapply H0; try eassumption.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. econstructor; try lia.
    + eapply H; try lia.
      * rewrite <- k; assumption.
      * eapply Crct_UP. eassumption. lia.
  - inversion_Clear H2. constructor; intuition.
  - inversion_Clear H2. constructor; intuition.
  - inversion_Clear H2. constructor; intuition.
    eapply Instantiate_pres_isLambda; eassumption.
Qed.

Lemma instantiate_pres_Crct:
  forall p m bod, crctTerm p (S m) bod -> forall tin, crctTerm p m tin -> 
                  forall n, n <= m ->  crctTerm p m (instantiate tin n bod).
Proof.
  intros.
  apply (proj1 (Instantiate_pres_Crct tin) _ _ _
               (proj1 (instantiate_Instantiate tin) _ _));
    try assumption.
Qed.

Lemma whBetaStep_pres_Crct:
  forall p n bod, crctTerm p (S n) bod ->
                  forall a1, crctTerm p n a1 ->
                             crctTerm p n (whBetaStep bod a1).
Proof.
  intros. unfold whBetaStep. 
  apply instantiate_pres_Crct; try assumption.  lia.
Qed.
 *************)

Lemma fold_left_pres_Crct:
  forall p m (f:Term -> nat -> Term) (ns:list nat) (t:Term),
    (forall u, crctTerm p m u -> forall n, crctTerm p m (f u n)) ->
    crctTerm p m t -> crctTerm p m (fold_left f ns t).
Proof.
  intros p n f. induction ns; simpl; intros.
  - assumption.
  - apply IHns.
    + intros. apply H. assumption.
    + apply H. assumption.
Qed.

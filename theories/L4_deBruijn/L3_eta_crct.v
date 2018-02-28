(** Intermediate L3_eta language.

  Enforce eta-expanded branches in match, so that the following L3-L4 phase
  can strip them correctly. *)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
        Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz FunInd.
Require Export Common.Common.  (* shared namespace *)
Require Import L4.expression.
Require Import L3_to_L3_eta.
Require Import L3.term L3.program L3.compile L3.wcbvEval.

Set Implicit Arguments.
Open Scope nat_scope.

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
           crctTerm p n fn -> crctTerm p n arg ->
           crctTerm p n (TApp fn arg)
| ctConst: forall p n pd nm,
             crctEnv p -> LookupDfn nm p pd -> crctTerm p n (TConst nm)
| ctConstructor: forall p n ipkgNm inum cnum args ipkg itp cstr,
                   LookupTyp ipkgNm p 0 ipkg ->
                   getInd ipkg inum = Ret itp ->
                   getCnstr itp cnum = Ret cstr ->
                   CnstrArity cstr = tlength args ->
                   crctTerms p n args ->
                   crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum args)
| ctCase: forall p n i mch brs,
    crctTerm p n mch -> crctBs p n brs ->
    crctAnnot p i brs ->
    crctTerm p n (TCase i mch brs)
| ctFix: forall p n ds m,
           crctDs p (n + dlength ds) ds -> m < dlength ds ->
           crctTerm p n (TFix ds m)
(* crctEnvs are closed in both ways *)
with crctEnv: environ Term -> Prop :=
| ceNil: crctEnv nil
| ceTrmCons: forall nm s p,
    fresh nm p -> crctTerm p 0 s -> crctEnv ((nm,ecTrm s)::p)
| ceTypCons: forall nm m s p,
    crctEnv p -> fresh nm p -> crctEnv ((nm,AstCommon.ecTyp Term m s)::p)
with crctTerms: environ Term -> nat -> Terms -> Prop :=
| ctsNil: forall p n, crctEnv p -> crctTerms p n tnil
| ctsCons: forall p n t ts,
    crctTerm p n t -> crctTerms p n ts -> crctTerms p n (tcons t ts)
with crctBs: environ Term -> nat -> Brs -> Prop :=
| cbsNil: forall p n, crctEnv p -> crctBs p n bnil
| cbsCons: forall p n m t ts,
    crctTerm p n t -> crctBs p n ts ->
    (** Eta-expanded branches *)
    is_n_lambda m t = true ->
    crctBs p n (bcons m t ts)
with crctDs: environ Term -> nat -> Defs -> Prop :=
| cdsNil: forall p n nm bod ix,
    crctEnv p -> crctTerm p n bod -> isLambda bod ->
    crctDs p n (dcons nm bod ix dnil)
| cdsCons: forall p n nm bod ix ds,
    crctTerm p n bod -> isLambda bod -> crctDs p n ds ->
    crctDs p n (dcons nm bod ix ds).
Hint Constructors crctTerm crctTerms crctBs crctDs crctEnv.
Scheme crct_ind' := Minimality for crctTerm Sort Prop
  with crcts_ind' := Minimality for crctTerms Sort Prop
  with crctBs_ind' := Minimality for crctBs Sort Prop
  with crctDs_ind' := Minimality for crctDs Sort Prop
  with crctEnv_ind' := Minimality for crctEnv Sort Prop.
Combined Scheme crctCrctsCrctBsDsEnv_ind from
         crct_ind', crcts_ind', crctBs_ind', crctDs_ind', crctEnv_ind'.

Lemma crctDs_nonNil:
  forall p n ds, crctDs p n ds -> dlength ds > 0.
Proof.
  induction 1; cbn; intuition.
Qed.

Lemma Crct_WFTrm:
  (forall p n t, crctTerm p n t -> WFTrm t n) /\
  (forall p n ts, crctTerms p n ts -> WFTrms ts n) /\
  (forall p n bs, crctBs p n bs -> WFTrmBs bs n) /\
  (forall p n (ds:Defs), crctDs p n ds -> WFTrmDs ds n) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; auto.
Qed.
  
Lemma Crct_CrctEnv:
  (forall p n t, crctTerm p n t -> crctEnv p) /\
  (forall p n ts, crctTerms p n ts -> crctEnv p) /\
  (forall p n bs, crctBs p n bs -> crctEnv p) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctEnv p) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; intuition.
Qed.

Lemma Crct_up:
  (forall p n t, crctTerm p n t -> crctTerm p (S n) t) /\
  (forall p n ts, crctTerms p n ts -> crctTerms p (S n) ts) /\
  (forall p n bs, crctBs p n bs -> crctBs p (S n) bs) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctDs p (S n) ds) /\
  (forall p, crctEnv p -> True). 
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
    try (solve [constructor; assumption]).
  - apply ctRel; try assumption. omega.
  - eapply ctConst; eassumption.
  - eapply ctConstructor; try eassumption.
Qed.

Lemma CrctDs_Up:
  forall n p ds, crctDs p n ds -> forall m, n <= m -> crctDs p m ds.
Proof.
  intros n p ds h. induction 1. assumption.
  apply (proj1 (proj2 (proj2 (proj2 Crct_up)))). assumption.
Qed.

Lemma Crct_UP:
  forall n p t, crctTerm p n t -> forall m, n <= m -> crctTerm p m t.
Proof.
  intros n p t h. induction 1. assumption. apply Crct_up. assumption.
Qed.

Lemma Crct_Up:
  forall n p t, crctTerm p 0 t -> crctTerm p n t.
Proof.
  intros. eapply Crct_UP. eassumption. omega.
Qed.
Hint Resolve Crct_Up Crct_UP.

Lemma Crct_fresh_Pocc:
  (forall p n t, crctTerm p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n ts, crctTerms p n ts ->
                  forall nm, fresh nm p -> ~ PoccTrms nm ts) /\
  (forall p n bs, crctBs p n bs ->
                  forall nm, fresh nm p -> ~ PoccBrs nm bs) /\
  (forall p n (ds:Defs), crctDs p n ds ->
                         forall nm, fresh nm p -> ~ PoccDefs nm ds) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; auto; intros j; auto;
    inversion_Clear j;
  try (specialize (H2 _ H3); contradiction);
  try (specialize (H2 _ H5); contradiction);
  try (specialize (H5 _ H6); contradiction);
  try (specialize (H0 _ H3); contradiction);
  try (specialize (H0 _ H1); contradiction);
  try (specialize (H0 _ H6); contradiction);
  try (specialize (H0 _ H4); contradiction);
  try (specialize (H1 _ H4); contradiction);
  try (specialize (H1 _ H5); contradiction);
  try (specialize (H3 _ H4); contradiction);
  try (specialize (H3 _ H5); contradiction);
  try (specialize (H3 _ H6); contradiction);
  try (specialize (H4 _ H5); contradiction).
  - unfold LookupDfn in H1. elim (Lookup_fresh_neq H1 H2). reflexivity.
  - unfold LookupTyp in H. destruct H.
    elim (Lookup_fresh_neq H H5). reflexivity.
  - specialize (H2 _ H4). contradiction.
  - destruct H3 as (pack&ityp&Hlook&_).
    unfold LookupTyp in Hlook. destruct Hlook.
    elim (Lookup_fresh_neq H3 H4). reflexivity.
  - specialize (H0 _ H2). contradiction.
  - specialize (H2 _ H4). contradiction.
  - specialize (H2 _ H4). contradiction.
  - inversion H6. 
Qed.

Lemma Crct_weaken:
  (forall p n t, crctTerm p n t -> 
                 forall nm s, fresh nm p -> crctTerm p 0 s ->
                              crctTerm ((nm,ecTrm s)::p) n t) /\
  (forall p n ts, crctTerms p n ts -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctTerms ((nm,ecTrm s)::p) n ts) /\
  (forall p n bs, crctBs p n bs -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctBs ((nm,ecTrm s)::p) n bs) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctDs ((nm,ecTrm s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - destruct H. unfold LookupTyp. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. eapply Lookup_fresh_neq; eassumption.
  - red. red in H3. destruct i. destruct H3 as [pack [ityp0 [Hlook [Hget Hann]]]].
    exists pack. exists ityp0. intuition.
    destruct Hlook. split; auto. constructor; auto.
    apply neq_sym. eapply Lookup_fresh_neq; eassumption.
Qed.

Lemma Crct_weaken_Typ:
  (forall p n t, crctTerm p n t -> 
                 forall nm s m, fresh nm p ->
                              crctTerm ((nm,ecTyp Term m s)::p) n t) /\
  (forall p n ts, crctTerms p n ts -> 
                  forall nm s m, fresh nm p ->
                               crctTerms ((nm,ecTyp Term m s)::p) n ts) /\
  (forall p n ts, crctBs p n ts -> 
                  forall nm s m, fresh nm p ->
                               crctBs ((nm,ecTyp Term m s)::p) n ts) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s m, fresh nm p ->
                               crctDs ((nm,ecTyp Term m s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - unfold LookupTyp in *. destruct H. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. apply (Lookup_fresh_neq H). assumption.
  - red. red in H3. destruct i. destruct H3 as [pack [ityp0 [Hlook [Hget Hann]]]].
    exists pack. exists ityp0. intuition.
    destruct Hlook. split; auto. constructor; auto.
    apply neq_sym. eapply Lookup_fresh_neq; eassumption.
Qed.

Lemma Crct_strengthen:
  (forall pp n s, crctTerm pp n s -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrm nm s -> crctTerm p n s) /\
  (forall pp n ss, crctTerms pp n ss -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrms nm ss -> crctTerms p n ss) /\
  (forall pp n ss, crctBs pp n ss -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccBrs nm ss -> crctBs p n ss) /\
  (forall pp n ds, crctDs pp n ds -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccDefs nm ds -> crctDs p n ds) /\
  (forall (pp:environ Term), crctEnv pp -> crctEnv (List.tl pp)).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; subst;
    try (econstructor; eassumption);
    try (constructor; try eassumption; inversion_Clear H; assumption).
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
  - econstructor; try eassumption.
    + unfold LookupTyp in *. split; intuition.
      eapply Lookup_strengthen. eassumption. reflexivity.
      inversion_Clear H5.
      * elim H6. constructor.
      * assumption.
    + eapply H4. reflexivity. intros h. elim H6. apply PoCnstrA.
      assumption.
  - econstructor; try eassumption.
    + eapply H0. reflexivity. intros h. elim H5. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H5.
      apply PoCaseR. assumption.
    + destruct i. destruct H3 as (pack&ityp&Hlook&Hget&Hann).
      exists pack, ityp. split; auto.
      destruct Hlook as [Hlook Hnil]. split; auto.
      inversion Hlook; subst. elim H5. apply PoCaseAnn. assumption.
  - econstructor; try eassumption. eapply H0. reflexivity. intros h.
    elim H3. constructor. assumption.
  - constructor.
    + eapply H0. reflexivity. intros h. elim H4. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H4. apply PoTtl. assumption.
  - constructor; auto.
    + eapply H0. reflexivity. intros h. elim H5. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H5. apply PoBtl. assumption.
  - constructor; try assumption.
    + eapply H2. reflexivity. intros h. elim H5. constructor. assumption.
  - constructor; try assumption.
    + eapply H0. reflexivity. intros h. elim H5. constructor. assumption. 
    + eapply H3. reflexivity. intros h. elim H5. constructor.
      destruct (notPoccDefs H5). contradiction.
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

Lemma LookupDfn_pres_Crct:
  forall p, crctEnv p -> forall nm u, LookupDfn nm p u ->
                                      forall m, crctTerm p m u.
Proof.
  induction p; intros; unfold LookupDfn in *.
  - inversion H0.
  - inversion_Clear H0. inversion_Clear H.
    + apply (proj1 Crct_weaken); try assumption. apply Crct_Up. assumption.
    + inversion_Clear H. apply (proj1 Crct_weaken); try assumption.
      * eapply IHp. apply (proj1 Crct_CrctEnv p _ _ H5). eassumption.
      * apply (proj1 Crct_weaken_Typ); try assumption.
        eapply IHp; try eassumption.
Qed.
  
  
Lemma Crct_invrt_Rel:
  forall p n m, crctTerm p n (TRel m) -> m < n.
Proof.
  intros. inversion_Clear H. assumption.
Qed.

Lemma pre_Crct_LookupDfn_Crct:
  (forall p n t, crctTerm p n t ->
                 forall nm t, LookupDfn nm p t -> crctTerm p 0 t) /\
  (forall p n ts, crctTerms p n ts ->
                  forall nm t, LookupDfn nm p t -> crctTerm p 0 t) /\
  (forall p n bs, crctBs p n bs ->
                  forall nm t, LookupDfn nm p t -> crctTerm p 0 t) /\
  (forall p n (ds:Defs), crctDs p n ds ->
                         forall nm t, LookupDfn nm p t -> crctTerm p 0 t) /\
  (forall p, crctEnv p -> forall nm t, LookupDfn nm p t -> crctTerm p 0 t).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; unfold LookupDfn in *;
  try (eapply H0; eassumption); try (eapply H1; eassumption).
  - eapply H4; eassumption.          
  - inversion H.
  - inversion_Clear H2.
    + apply Crct_weaken; assumption.
    + apply Crct_weaken; try assumption. eapply H1. eassumption.
  - inversion_Clear H2.
    + apply Crct_weaken_Typ; try assumption. eapply H0. eassumption.
Qed.


Lemma Crct_invrt_:
  forall (ev:environ Term), crctEnv ev ->
  forall nm s p, ev = (nm, ecTrm s)::p -> crctTerm p 0 s.
Proof.
  induction 1; intros; subst;
    try (inversion_Clear H; assumption);
    try (eapply IHcrctTerm; reflexivity);
    try (eapply IHcrctTerm1; reflexivity).
  - myInjection H1. assumption.
  - discriminate.
Qed.

Lemma Crct_LookupDfn_Crct:
  forall p, crctEnv p -> forall nm t, LookupDfn nm p t -> crctTerm p 0 t.
Proof.
  intros. eapply pre_Crct_LookupDfn_Crct; eassumption.
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
  forall p n i s us,
    crctTerm p n (TCase i s us) -> crctTerm p n s /\ crctBs p n us /\ crctAnnot p i us.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Fix:
  forall p n ds m, crctTerm p n (TFix ds m) ->
                   crctDs p (n + dlength ds) ds.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Construct:
  forall p n ipkgNm inum cnum args,
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum args) ->
    crctTerms p n args /\
    exists itypk,
      LookupTyp ipkgNm p 0 itypk /\
      exists (ip:ityp), getInd itypk inum = Ret ip /\
                        exists (ctr:Cnstr), getCnstr ip cnum = Ret ctr /\
                                            CnstrArity ctr = tlength args.
Proof.
  intros. inversion_Clear H. intuition. exists ipkg. intuition.
  exists itp. intuition. exists cstr. intuition.
Qed.

Lemma pre_CrctDs_invrt:
  forall m dts x, dnth m dts = Some x ->
     forall p n, crctDs p n dts ->
                 crctTerm p n (dbody _ x).
Proof.
    intros m dts. functional induction (dnth m dts); intros.
  - discriminate.
  - myInjection H. cbn. inversion_Clear H0; try assumption.
  - specialize (IHo _ H). inversion_Clear H0.
    + discriminate.
    + eapply IHo. assumption.
Qed.

Lemma CrctDs_invrt:
  forall m dts x, dnthBody m dts = Some x ->
    forall p n, crctDs p n dts -> crctTerm p n x.
Proof.
  intros. functional induction (dnthBody m dts).
  - discriminate.
  - myInjection H. inversion_Clear H0; try assumption.
  - inversion_Clear H0.
    + inversion H.
    + intuition.
Qed.

Lemma CrctBs_invrt:
  forall n p dts, crctBs p n dts -> 
    forall m x ix, bnth m dts = Some (x, ix) -> crctTerm p n x /\ is_n_lambda ix x = true.
Proof.
  induction 1; intros.
  - inversion H0.
  - destruct m0.
    + cbn in H2. myInjection H2. split; assumption.
    + eapply IHcrctBs. cbn in H1. eassumption.
Qed.

Lemma Crcts_append:
  forall p n ts, crctTerms p n ts ->
  forall us, crctTerms p n us -> crctTerms p n (tappend ts us).
Proof.
  induction 1; intros us h; simpl.
  - assumption.
  - constructor; intuition.
Qed.

Lemma mkApp_pres_Crct:
  forall p n args, crctTerms p n args ->
                   forall fn, crctTerm p n fn ->
                              crctTerm p n (mkApp fn args).
Proof.
  induction 1; intros; cbn.
  - assumption.
  - apply IHcrctTerms. constructor; assumption.
Qed.

Lemma Instantiate_pres_is_n_lambda tin n t t' :
  Instantiate tin n t t' -> forall k, is_n_lambda k t = true -> is_n_lambda k t' = true.
Proof.
  induction 1; destruct k; simpl; intros; try discriminate || reflexivity.
  now apply IHInstantiate.
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
  apply InstInstsBrsDefs_ind; intros; trivial;
  try (inversion_Clear H0; econstructor; eassumption);
  try (inversion_Clear H1; constructor; try assumption; apply H; assumption).
  - inversion_Clear H0. constructor. assumption. omega.
  - apply ctRel.
    + inversion H0. assumption.
    + inversion H0. omega.
  - inversion_Clear H1. constructor; try assumption.
    apply H; try assumption. omega. apply (proj1 Crct_up). assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; assumption.
    + apply H0. omega. assumption. apply (proj1 Crct_up). assumption.
  - inversion_Clear H2. econstructor; try eassumption.
    + apply H; try eassumption.
    + apply H0; try eassumption.
  - inversion_Clear H1. econstructor; try eassumption.
    rewrite H11. erewrite Instantiates_pres_tlength; try eassumption.
    reflexivity.
    apply H; try eassumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; try eassumption.
    + apply H0; try eassumption.
    + destruct i as [ind k].
      destruct H11 as (pack&ityp&Hlook&Hget&Hann).
      exists pack, ityp; intuition auto.
      destruct ityp. simpl in *. clear H H0; revert Hann its i1; clear.
      induction 1; inversion_clear 1; constructor; auto.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. constructor; try omega. apply H. omega.
    + replace (S (m0 + dlength id)) with (S m0 + dlength d); try omega.
      assumption.
    + eapply Crct_UP. eassumption. omega.
  - inversion_Clear H2. apply ctsCons; intuition.
  - inversion_Clear H2. constructor; intuition.
    eapply Instantiate_pres_is_n_lambda; eassumption.
  - inversion_Clear H2.
    + inversion_Clear i0. apply cdsNil. assumption.
      * apply H; intuition.
      * eapply Instantiate_pres_isLambda; eassumption.
    + constructor.
      * apply H; intuition.
      * eapply Instantiate_pres_isLambda; eassumption.
      * apply H0; intuition.
Qed.

Lemma instantiate_pres_Crct:
  forall p m bod, crctTerm p (S m) bod -> forall tin, crctTerm p m tin -> 
                  forall n, n <= m -> crctTerm p m (instantiate tin n bod).
Proof.
  intros.
  refine (proj1 (Instantiate_pres_Crct tin) _ _ _ _ _ _ _ _ _);
    try eassumption.
  refine (proj1 (instantiate_Instantiate tin) _ _).
Qed.

Lemma whBetaStep_pres_Crct:
  forall p n bod, crctTerm p (S n) bod ->
                  forall a1, crctTerm p n a1 ->
                             crctTerm p n (whBetaStep bod a1).
Proof.
  intros. unfold whBetaStep. 
  apply instantiate_pres_Crct; try assumption. omega.
Qed.

Lemma bnth_pres_Crct:
  forall p n (brs:Brs), crctBs p n brs ->
    forall m x ix, bnth m brs = Some (x, ix) -> crctTerm p n x.
Proof.
  intros p n brs h m x ix.
  functional induction (bnth m brs); intros; auto.
  - discriminate.
  - myInjection H. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma whCaseStep_pres_Crct:
  forall p n ts, crctTerms p n ts -> forall brs, crctBs p n brs ->
  forall m s, whCaseStep m ts brs = Some s -> crctTerm p n s.
Proof.
  intros p n ts h1 brs h2 m s h3. unfold whCaseStep in h3.
  assert (j: bnth m brs = None \/ (exists t, bnth m brs = Some t)).
  { destruct (bnth m brs).
    + right. exists p0. reflexivity.
    + left. reflexivity. }
  destruct j.
  - rewrite H in h3. discriminate.
  - destruct H as [x jx]. rewrite jx in h3. destruct x as [y0 y1].
    myInjection h3. apply mkApp_pres_Crct; try assumption.
    eapply (bnth_pres_Crct h2). eassumption.
Qed.

Lemma fold_left_pres_Crct:
  forall (f:Term -> nat -> Term) (ns:list nat) p (a:nat),
    (forall u m, m >= a -> crctTerm p (S m) u ->
               forall n, In n ns -> crctTerm p m (f u n)) ->
    forall t, crctTerm p (a + List.length ns) t ->
              crctTerm p a (fold_left f ns t).
Proof.
  intros f. induction ns; cbn; intros.
  - replace (a + 0) with a in H0. assumption. omega.
  - apply IHns.
    + intros. apply H; try assumption. apply (or_intror H3).
    + replace (a0 + S (Datatypes.length ns))
        with (S (a0 + (Datatypes.length ns))) in H0.
      assert (j: a0 + Datatypes.length ns >= a0). omega.
      specialize (H t _ j H0).
      apply H. apply (or_introl eq_refl). omega.
Qed.

Lemma dnth_crctDs_crctTerm:
  forall m dts fs, dnth m dts = Some fs ->
                   forall p n, crctDs p n dts -> crctTerm p n (dbody _ fs).
Proof.
  intros m dts fs.
  functional induction (dnth m dts); intros; try discriminate.
  - inversion_Clear H0.
    + myInjection H. cbn. assumption.
    + myInjection H. cbn. assumption.
  - inversion_Clear H0.
    + discriminate.
    + apply IHo; try assumption.
Qed.


Lemma dnthBody_pres_Crct:
  forall m dts fs, dnthBody m dts = Some fs ->
                   forall p n, crctDs p n dts -> crctTerm p n fs.
Proof.
  intros m dts fs.
  functional induction (dnthBody m dts); intros; try discriminate.
  - myInjection H. inversion_Clear H0; try assumption.
  - inversion_Clear H0.
    + inversion H.
    + intuition.
Qed.

Lemma whFixStep_pres_Crct:
  forall (dts:Defs) p n,
    crctDs p (n + dlength dts) dts ->
    forall m s, whFixStep dts m = Some s -> crctTerm p n s.
Proof.
  unfold whFixStep. intros. case_eq (dnthBody m dts); intros.
  - assert (j: m < dlength dts).
    { eapply dnthBody_lt. eassumption. }
    rewrite H1 in H0. myInjection H0. apply fold_left_pres_Crct. 
    + intros. apply instantiate_pres_Crct; try omega. assumption.
      * pose proof (In_list_to_zero _ _ H3) as j0.
        constructor; try assumption.
        pose proof (dnthBody_pres_Crct _ H1 H) as k2.
        eapply CrctDs_Up. eassumption. omega.
    + rewrite list_to_zero_length.
      eapply dnthBody_pres_Crct. eassumption.
      eapply CrctDs_Up. eassumption. omega.
  - rewrite H1 in H0. discriminate.
Qed.

Lemma WcbvEval_pres_Crct:
  forall p,
    (forall t s, WcbvEval p t s ->
                 forall m, crctTerm p m t -> crctTerm p m s) /\
    (forall ts ss, WcbvEvals p ts ss ->
                   forall m, crctTerms p m ts -> crctTerms p m ss).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; cbn; intros;
    try (inversion_Clear H; intuition);
    try (inversion_Clear H0; intuition);
    try (inversion_Clear H1; intuition).
  - econstructor; try eassumption; intuition.
    rewrite H9. eapply WcbvEvals_pres_tlength; try eassumption.
  - erewrite (@LookupDfn_single_valued Term _ _ _ _ l H5) in H.
    eapply H. eapply LookupDfn_pres_Crct; try eassumption.
  - inversion_Clear H2. specialize (H _ H7). specialize (H0 _ H8).
    eapply H1. eapply whBetaStep_pres_Crct; try eassumption.
    inversion_clear H. assumption.
  - eapply H0. apply instantiate_pres_Crct; try eassumption; try omega.
    apply H. assumption.
  - specialize (H _ H6). inversion_Clear H. eapply H0.
    constructor; try assumption.
    apply fold_left_pres_Crct.
    + intros. apply instantiate_pres_Crct; try assumption; try omega.
      constructor. eapply CrctDs_Up. eassumption. omega.
      eapply In_list_to_zero. assumption.
    + apply (dnthBody_pres_Crct _ e). eapply CrctDs_Up. eassumption. 
      rewrite list_to_zero_length. omega.
  - apply H0. eapply whCaseStep_pres_Crct; try eassumption.
    specialize (H _ H7). inversion_Clear H. assumption.
Qed.

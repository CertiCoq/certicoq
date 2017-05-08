
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L1.term.
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
Hint Constructors AstCommon.fresh.
Hint Constructors AstCommon.Lookup.

(** correctness specification for programs (including local closure) **)
Inductive Crct: environ Term -> nat -> Term -> Prop :=
| CrctSrt: forall n srt, Crct nil n (TSort srt)
| CrctWkTrmTrm: forall n p t s nm,
    Crct p n t -> Crct p n s -> fresh nm p -> Crct ((nm,ecTrm s)::p) n t
| CrctWkTrmTyp: forall n p t s nm,
    Crct p n t -> fresh nm p -> forall m, Crct ((nm,ecTyp m s)::p) n t
| CrctRel: forall n m p, m < n -> Crct p n prop -> Crct p n (TRel m)
| CrctCast: forall n p t ty,
    Crct p n t -> Crct p n ty -> Crct p n (TCast t ty)
| CrctPrf: forall n p t, Crct p n t -> Crct p n (TProof t)
| CrctProd: forall n p nm ty bod,
    Crct p (S n) bod -> Crct p n ty -> Crct p n (TProd nm ty bod)
| CrctLam: forall n p nm ty bod,
    Crct p (S n) bod -> Crct p n ty -> Crct p n (TLambda nm ty bod)
| CrctLetIn: forall n p nm dfn ty bod,
    Crct p n dfn -> Crct p (S n) bod -> Crct p n ty -> 
    Crct p n (TLetIn nm dfn ty bod)
| CrctApp: forall n p fn a args,
    ~ (isApp fn) -> Crct p n fn -> Crct p n a -> Crcts p n args ->
    Crct p n (TApp fn a args)
| CrctConst: forall n p pd nm,
    Crct p n prop -> LookupDfn nm p pd -> Crct p n (TConst nm)
| CrctAx: forall n p, Crct p n prop -> Crct p n TAx
| CrctConstruct: forall n p ipkgNm inum cnum ipkg itp cstr m np na,
    Crct p n prop ->
    LookupTyp ipkgNm p m ipkg ->
    getInd ipkg inum = Ret itp ->
    getCnstr itp cnum = Ret cstr ->
    Crct p n (TConstruct (mkInd ipkgNm inum) cnum np na)
| CrctCase: forall nm tx cx pack n p ty mch brs,
    LookupTyp nm p tx pack ->
    Crct p n mch -> CrctDs p n brs -> Crct p n ty -> 
    Crct p n (TCase ((mkInd nm tx), cx) ty mch brs)
| CrctFix: forall n p ds m,
    Crct p n prop ->    (** convenient for IH *)
    (******
    (dnthBody m ds = Some t -> isLambda t) ->
    ******************)
    CrctDs p (n + dlength ds) ds -> Crct p n (TFix ds m)
| CrctInd: forall n p ind, Crct p n prop -> Crct p n (TInd ind)
with Crcts: environ Term -> nat -> Terms -> Prop :=
     | CrctsNil: forall n p, Crct p n prop -> Crcts p n tnil
     | CrctsCons: forall n p t ts,
         Crct p n t -> Crcts p n ts -> Crcts p n (tcons t ts)
with CrctDs: environ Term -> nat -> Defs -> Prop :=
     | CrctDsNil: forall n p, Crct p n prop -> CrctDs p n dnil
     | CrctDsCons: forall n p dn dty db dra ds,
         Crct p n dty -> Crct p n db -> CrctDs p n ds ->
         CrctDs p n (dcons dn dty db dra ds).
Hint Constructors Crct Crcts CrctDs.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with Crcts_ind' := Minimality for Crcts Sort Prop
  with CrctDs_ind' := Minimality for CrctDs Sort Prop.
Combined Scheme CrctCrctsCrctDs_ind from
         Crct_ind', Crcts_ind', CrctDs_ind'.


Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall p (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n).
Proof.
  apply CrctCrctsCrctDs_ind; intros; auto.
Qed.

Lemma Crct_WFApp:
  forall p n t, Crct p n t -> WFapp t.
  intros p n t h. eapply WFTrm_WFapp. eapply (proj1 Crct_WFTrm). eassumption.
Qed.

 
Lemma Crct_up:
  (forall p n t, Crct p n t -> Crct p (S n) t) /\
  (forall p n ts, Crcts p n ts -> Crcts p (S n) ts) /\
  (forall p (n:nat) (ds:Defs), CrctDs p n ds -> CrctDs p (S n) ds).
Proof.
  apply CrctCrctsCrctDs_ind; intros;
  try (econstructor; try omega; eassumption).
Qed.

Lemma Crct_Sort:
  forall p n t, Crct p n t -> forall srt, Crct p n (TSort srt).
  induction 1; intuition.  
Qed.


Lemma Crcts_tnil:
  forall p n t, Crct p n t -> Crcts p n tnil.
induction 1; apply CrctsNil; try assumption;
try (solve [eapply Crct_Sort; eassumption]).
- constructor.
- apply CrctWkTrmTrm; try assumption. eapply Crct_Sort; eassumption.
- apply CrctWkTrmTyp; try assumption. eapply Crct_Sort; eassumption.
Qed.

Lemma CrctDs_dnil:
  forall p n t, Crct p n t -> CrctDs p n dnil.
induction 1; apply CrctDsNil; try assumption;
try (solve [eapply Crct_Sort; eassumption]).
- constructor.
- apply CrctWkTrmTrm; try assumption. eapply Crct_Sort; eassumption.
- apply CrctWkTrmTyp; try assumption. eapply Crct_Sort; eassumption.
Qed.

(** Tail preserves correctness **)
Lemma CrctTrmTl:
  forall pp n t, Crct pp n t ->
             forall nm s p, pp = ((nm,ecTrm s)::p) -> Crct p n s.
induction 1; intros;
try (solve [eapply IHCrct2; eassumption]);
try (solve [eapply IHCrct; eassumption]);
try (solve [eapply IHCrct1; eassumption]);
try discriminate.
- injection H2; intros. subst. assumption.
Qed.


(******** different approach to correctness checking constructors  ***
Inductive Crct: environ -> nat -> envClass -> Prop :=
| CrctSrt: forall n, Crct nil n (ecTrm (TSort))
| CrctWk: forall n p t s nm, Crct p n t -> Crct p n s ->
           fresh nm p -> Crct ((nm,s)::p) n t
| CrctRel: forall n m p, m < n -> Crct p 0 (ecTrm prop) ->
                         Crct p n (ecTrm (TRel m))
| CrctCast: forall n p t ck ty,
              Crct p n (ecTrm t) -> Crct p n (ecTrm ty) ->
              Crct p n (ecTrm (TCast t ck ty))
| CrctProd: forall n p nm ty bod,
              Crct p (S n) (ecTrm bod) -> Crct p n (ecTrm ty) ->
              Crct p n (ecTrm (TProd nm ty bod))
| CrctLam: forall n p nm ty bod,
             Crct p (S n) (ecTrm bod) -> Crct p n (ecTrm ty) ->
             Crct p n (ecTrm (TLambda nm ty bod))
| CrctLetIn: forall n p nm dfn ty bod,
         Crct p n (ecTrm dfn) -> Crct p (S n) (ecTrm bod) ->
         Crct p n (ecTrm ty) -> 
         Crct p n (ecTrm (TLetIn nm dfn ty bod))
| CrctApp: forall n p fn a args,
             Crct p n (ecTrm fn) -> Crct p n (ecTrm a) -> Crcts p n args -> 
             Crct p n (ecTrm (TApp fn a args))
| CrctConst: forall n p pd nm,
               Crct p n (ecTrm prop) -> LookupDfn nm p pd ->
               Crct p n (ecTrm (TConst nm))
| CrctConstruct: forall n p i m1,
                   Crct p n (ecTrm prop) -> Crct p n (ecTrm (TConstruct i m1))
| CrctCase: forall n p m ty mch brs,
              Crct p n (ecTrm mch) -> Crcts p n brs -> Crct p n (ecTrm ty) -> 
              Crct p n (ecTrm (TCase m ty mch brs))
| CrctFix: forall n p ds m, CrctDs p (n + dlength ds) ds ->
                            Crct p n (ecTrm (TFix ds m))
with Crcts: environ -> nat -> Terms -> Prop :=
| CrctsNil: forall n p, Crct p n (ecTrm prop) -> Crcts p n tnil
| CrctsCons: forall n p t ts,
               Crct p n (ecTrm t) -> Crcts p n ts -> Crcts p n (tcons t ts)
with CrctDs: environ -> nat -> Defs -> Prop :=
| CrctDsNil: forall n p, Crct p n (ecTrm prop) -> CrctDs p n dnil
| CrctDsCons: forall n p dn dty db dra ds,
          Crct p n (ecTrm dty) -> Crct p n (ecTrm db) -> CrctDs p n ds ->
          CrctDs p n (dcons dn dty db dra ds)
with CrctTyp: environ -> nat -> itypPack -> Prop := 
| CrctTypStart: forall p n itp, Crct p n (ecTrm prop) -> CrctTyp p n itp.
Hint Constructors Crct Crcts CrctDs CrctTyp.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with Crcts_ind' := Minimality for Crcts Sort Prop
  with CrctDs_ind' := Minimality for CrctDs Sort Prop
  with CrctTyp_ind' := Minimality for CrctTyp Sort Prop.
Combined Scheme CrctCrctsCrctDsTyp_ind from
         Crct_ind', Crcts_ind', CrctDs_ind', CrctTyp_ind'.


Lemma Crct_WFTrm:
  (forall p n ec, Crct p n ec -> forall t, ec = ecTrm t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n) /\
  (forall (p:environ) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; auto;
Qed.
*****************)

Lemma Crct_fresh_Pocc:
  (forall p n t, Crct p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n ts, Crcts p n ts -> forall nm, fresh nm p -> ~ PoccTrms nm ts) /\
  (forall p n (ds:Defs), CrctDs p n ds -> forall nm, fresh nm p ->
                                                     ~ PoccDefs nm ds).
apply CrctCrctsCrctDs_ind; intros; intros j;
try (solve [inversion j]);
try (solve [inversion_clear j; elim (H0 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm0); trivial; elim (H2 nm0); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear H4; elim (H0 nm0); trivial]).
- elim (H0 nm0); trivial. inversion H2. assumption.
- inversion_clear j. elim (H0 nm0); assumption. elim (H2 nm0); assumption.
  elim (H4 nm0); assumption.
- inversion_clear j. elim (H1 nm); trivial. elim (H3 nm); trivial.
  induction args. inversion H7. elim (H5 nm); trivial.
- inversion_Clear j. eelim (fresh_Lookup_fails H2). eassumption.
- inversion_Clear j. eelim (fresh_Lookup_fails H4).
  destruct H1. eassumption.
- inversion_Clear j.
  + unfold LookupTyp in H. elim (fresh_Lookup_fails H6 (proj1 H)).
  + elim (H1 _ H6); intuition.
  + elim (H3 _ H6); trivial.
  + elim (H5 _ H6); trivial.
- inversion_clear j. elim (H0 nm); trivial. elim (H2 nm); trivial.
  elim (H4 nm); trivial.
Qed.

Lemma Crct_not_bad_Lookup:
  (forall p n s, Crct p n s ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ss, Crcts p n ss ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ds, CrctDs p n ds ->
                  forall nm, LookupDfn nm p (TConst nm) -> False).
Proof.
  apply CrctCrctsCrctDs_ind; intros; auto;
  try (solve [elim (H0 _ H3)]); try (solve [elim (H0 _ H5)]);
  try (solve [elim (H0 _ H1)]); try (solve [elim (H0 _ H2)]).
  - inversion H.
  - destruct (string_dec nm0 nm).
    + subst. inversion_Clear H4.
      * assert (j:= proj1 Crct_fresh_Pocc _ _ _ H1 _ H3).
        elim j. constructor. 
      * elim (H0 _ H11).
    + eelim (H0 _ (Lookup_strengthen H4 _ n0)).
  - elim (H0 nm0). unfold LookupDfn in H2. unfold LookupDfn.
    destruct (string_dec nm0 nm).
    + subst. inversion H2. assumption.
    + eapply (Lookup_strengthen H2). reflexivity. assumption.
  - elim (H1 _ H2).
  - elim (H1 _ H6).
  - elim (H0 _ H4).
  - elim (H5 _ H6).
    Grab Existential Variables.
    + reflexivity.
Qed.


Lemma  Crct_weaken:
  (forall p n t, Crct p n t -> 
    forall nm s, fresh nm p -> Crct p n s -> Crct ((nm,ecTrm s)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm s, fresh nm p -> Crct p n s -> Crcts ((nm,ecTrm s)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
                  forall nm s, fresh nm p -> Crct p n s -> CrctDs ((nm,ecTrm s)::p) n ds).
Proof.
  eapply CrctCrctsCrctDs_ind; intros; intuition.
  - apply CrctWkTrmTrm; try assumption. eapply CrctConst; eassumption.
  - eapply CrctConstruct; try eassumption.
    apply H0; try assumption. destruct H1. split.
    + apply Lookup_weaken; eassumption.
    + assumption.
  - apply CrctWkTrmTrm; try assumption. eapply CrctCase; eassumption.
Qed.

Lemma  Crct_Typ_weaken:
  (forall p n t, Crct p n t -> 
    forall nm itp, fresh nm p -> 
                   forall npars, Crct ((nm,ecTyp npars itp)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm itp, fresh nm p ->
                 forall npars, Crcts ((nm,ecTyp npars itp)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
    forall nm itp, fresh nm p ->
                   forall npars, CrctDs ((nm,ecTyp npars itp)::p) n ds).
Proof.
  eapply CrctCrctsCrctDs_ind; intros; auto.
  - apply CrctWkTrmTyp; try assumption. eapply CrctConst; try eassumption.
  - eapply CrctConstruct; try eassumption.
    apply H0; try assumption. destruct H1. split.
    + apply Lookup_weaken; eassumption.
    + assumption.
  - apply CrctWkTrmTyp; try assumption. eapply CrctCase; eassumption.
Qed.

Lemma Crct_strengthen:
  (forall pp n t, Crct pp n t -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrm nm t -> Crct p n t) /\
  (forall pp n ts, Crcts pp n ts -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrms nm ts -> Crcts p n ts) /\
  (forall pp n ds, CrctDs pp n ds -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccDefs nm ds -> CrctDs p n ds).
Proof.
  eapply CrctCrctsCrctDs_ind; intros; auto.
  - inversion H.
  - injection H4; intros. subst. assumption.
  - injection H2; intros. subst. assumption.
  - apply CrctRel; try assumption. eapply H1. eapply H2.
    intros h. inversion h.
  - apply CrctCast.
    + eapply H0. eassumption.
      intros h. elim H4. apply PoCastTm. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoCastTy. assumption.
  - apply CrctPrf; try assumption.
    + eapply H0.
      * eassumption.
      * intros h. elim H2. apply PoProof. assumption.
  - apply CrctProd.
    + eapply H0. eassumption.
      intros h. elim H4. apply PoProdBod. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoProdTy. assumption.
  - apply CrctLam.
    + eapply H0. eassumption.
      intros h. elim H4. apply PoLambdaBod. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoLambdaTy. assumption.
  - apply CrctLetIn.
    + eapply H0. eassumption.
      intros h. elim H6. apply PoLetInDfn. assumption.
    + eapply H2. eassumption.
      intros h. elim H6. apply PoLetInBod. assumption.
    + eapply H4. eassumption.
      intros h. elim H6. apply PoLetInTy. assumption.
  - apply CrctApp. assumption.
    + eapply H1. eassumption.
      intros h. elim H7. apply PoAppL. assumption.
    + eapply H3. eassumption.
      intros h. elim H7. apply PoAppA. assumption.
    + eapply H5. eassumption.
      intros h. elim H7. apply PoAppR. assumption.
  - eapply CrctConst. eapply H0. eapply H2.
    intros h. inversion h. rewrite H2 in H1.
    assert (j: nm0 <> nm).
    { apply notPocc_TConst. assumption. }
    inversion H1.
    + rewrite H6 in j. nreflexivity j.
    + eassumption.
  - eapply CrctAx. eapply H0; try eassumption. intros h. inversion h. 
  - eapply CrctConstruct; try eassumption.
    + eapply H0. eapply H4. intros h. inversion h.
    + rewrite H4 in H1.
      assert (j: nm <> ipkgNm).
      { eapply notPocc_TCnstr. eassumption. }
      destruct H1. subst. split; try assumption.
      inversion_Clear H1.
      * elim j. reflexivity.
      * eassumption.
  - eapply CrctCase.
    + subst p. assert (k:nm0 <> nm).
      { destruct (string_dec nm0 nm).
        - subst nm. elim H7. constructor.
        - assumption. }
      unfold LookupTyp in H. destruct H. inversion l. subst.
      elim k. reflexivity.
      unfold LookupTyp. split; eassumption.
    + eapply H1. eassumption.
      intros h. elim H7. apply PoCaseL. assumption.
    + eapply H3. eassumption.
      intros h. elim H7. apply PoCaseR. assumption.
    + eapply H5. eassumption.
      intros h. elim H7. apply PoCaseTy. assumption.
  - apply CrctFix.
    + eapply H0. eassumption. intros h. inversion h.
    + eapply H2. eassumption. intros h. elim H4. apply PoFix. assumption.
  - apply CrctInd. apply (H0 _ _ _ H1). inversion 1. 
  - apply CrctsNil. rewrite H1 in H. inversion H; assumption.
  - apply CrctsCons.
    + eapply H0. eassumption. intros h. elim H4. apply PoThd. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoTtl. assumption.
  - apply CrctDsNil. eapply H0. eassumption. intros h. inversion h.
  - apply CrctDsCons.
    + eapply H0. eassumption. intros h. elim H6. apply PoDhd_ty. assumption.
    + eapply H2. eassumption. intros h. elim H6. apply PoDhd_bod. assumption.
    + eapply H4. eassumption. intros h. elim H6. apply PoDtl. assumption.
Qed.

Lemma TWrong_not_Crct:
  forall p n s, ~ Crct p n (TWrong s).
Proof.
  induction p; intros; intros h.
  - inversion h.
  - eelim IHp. destruct a. eapply (proj1 Crct_strengthen _ _ _ h).
    + reflexivity.
    + intros j. inversion j.
Qed.

 (** Crct inversions **)
Lemma LookupDfn_pres_Crct:
  forall p n t, Crct p n t -> forall nm u, LookupDfn nm p u -> Crct p n u.
Proof.
assert (lem: (forall p n t, Crct p n t -> 
                            forall nm u, LookupDfn nm p u -> Crct p n u) /\
             (forall p n ts, Crcts p n ts -> True) /\
             (forall (p:environ Term) (n:nat) (ds:Defs),
                CrctDs p n ds -> True)).
  { apply CrctCrctsCrctDs_ind; intros; auto;
    try (solve [eapply H1; eassumption]);
    try (solve [eapply H2; eassumption]);
    try (solve [eapply H0; eassumption]).
    - inversion H.
     - apply CrctWkTrmTrm; try assumption. inversion H4; subst.
      + assumption.
      + eapply H0. apply H11.
     - apply CrctWkTrmTyp; try assumption. eapply H0.
       inversion H2. eassumption.
  }
  apply (proj1 lem).
Qed.

Lemma Crct_invrt_Rel:
  forall p n rel, Crct p n rel -> forall m, rel = TRel m ->
     m < n /\ Crct p n prop.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 m). intuition.
  - assert (j:= IHCrct m). specialize (IHCrct _ H1). intuition.
  - assert (j:= IHCrct m). injection H1. intuition.
Qed.

Lemma Crct_invrt_WkTrm:
  forall (ev:environ Term) n t, Crct ev n t ->
  forall nm s p, ev = (nm, ecTrm s)::p -> Crct p n s.
Proof.
  induction 1; intros; try discriminate;
  try (solve [eapply IHCrct2; eassumption]);
  try (solve [eapply IHCrct1; eassumption]);
  try (solve [eapply IHCrct; eassumption]).
  - injection H2; intros; subst. assumption.
Qed.

Lemma Crct_invrt_Const:
  forall p n const, Crct p n const ->
  forall nm, const = TConst nm ->
       (Crct p n prop /\ exists pd, LookupDfn nm p pd /\ Crct p n pd).
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ H2). intuition.
    destruct H4 as [x [h2 h3]]. exists x. split.
    + assert (j: nm0 <> nm).
      { destruct (string_dec nm0 nm). 
        - subst. elim (fresh_Lookup_fails H1 h2).
        - assumption. }
      apply (LMiss _ j). trivial.
    + apply CrctWkTrmTrm; trivial.
  - assert (j:= IHCrct _ H1). intuition.
    destruct H3 as [x [h2 h3]]. exists x. split.
    + assert (j: nm0 <> nm).
      { destruct (string_dec nm0 nm). 
        - subst. elim (fresh_Lookup_fails H0 h2).
        - assumption. }
      apply (LMiss _ j). trivial.
    + apply CrctWkTrmTyp; trivial.
  - injection H1. intros. subst. intuition. exists pd; intuition.
    eapply LookupDfn_pres_Crct; eassumption.
Qed.

Lemma Crct_invrt_Prod:
  forall p n prod, Crct p n prod ->
  forall nm ty bod, prod = TProd nm ty bod ->
     Crct p n ty /\ Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ H2). intuition.
    apply CrctWkTrmTrm; trivial.
    apply (proj1 (Crct_up)). assumption.
  - assert (j:= IHCrct _ _ _ H1). intuition.
  - injection H1. intros. subst. intuition.
Qed.

Lemma Crct_invrt_Lam:
  forall p n lam, Crct p n lam ->
  forall nm ty bod, lam = TLambda nm ty bod ->
     Crct p n ty /\ Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ H2). intuition.
    apply CrctWkTrmTrm; trivial.
    apply (proj1 (Crct_up)). assumption.
  - assert (j:= IHCrct _ _ _ H1). intuition.
  - injection H1. intros. subst. intuition.
Qed.

Lemma Crct_invrt_LetIn:
  forall p n letin, Crct p n letin ->
  forall nm dfn ty bod, letin = TLetIn nm dfn ty bod ->
     Crct p n dfn /\ Crct p n ty /\ Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ _ H2). intuition.
    apply CrctWkTrmTrm; trivial.
    apply (proj1 (Crct_up)). assumption.
  - assert (j:= IHCrct _ _ _ _ H1). intuition.
  - injection H2. intros. subst. intuition.
Qed.

Lemma Crct_invrt_App:
  forall p n app,
    Crct p n app -> forall fn arg args, app = (TApp fn arg args) ->
    Crct p n fn /\ Crct p n arg /\ Crcts p n args /\ ~(isApp fn).
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
  apply (proj2 Crct_weaken); auto.
- assert (j:= IHCrct _ _ _ H1); destruct j as [j0 [j1 [j2 j3]]]. intuition.
  inversion_clear j2. intuition. constructor.
  apply (proj1 Crct_Typ_weaken); assumption.
  apply (proj1 (proj2 Crct_Typ_weaken)); assumption.
- injection H3; intros; subst. auto.
Qed.

Lemma Crct_invrt_Case:
  forall p n case,
    Crct p n case ->
    forall us nm tx cx t s, case = TCase ((mkInd nm tx), cx) t s us ->
    (exists pack, LookupTyp nm p tx pack) /\ Crct p n t /\ Crct p n s /\ CrctDs p n us.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ _ _ _ H2). intuition.
    + destruct H3 as [x [j1x j2x]]. exists x. subst t.
      assert (k: nm0 <> nm).
      { destruct (string_dec nm0 nm); try assumption.
        - subst nm0. unfold LookupTyp in j1x.
          eapply Lookup_fresh_neq. eapply j1x. assumption. }
      unfold LookupTyp. split; try assumption.
      * eapply LMiss; assumption.
    + case_eq us; intros.
      * constructor. constructor; try assumption. eapply Crct_Sort. eassumption.
      * { subst us t. inversion_Clear H7. 
          destruct(IHCrct1 (dcons n0 t1 t2 n1 d) nm0 tx cx t0 s0 eq_refl) as
              [k0 [k1 [k2 k3]]].
          inversion_Clear k3. eapply Crct_weaken; try assumption.
          constructor; try assumption. }
  - assert (j:= IHCrct _ _ _ _ _ _ H1). intuition.
    + destruct H2 as [x [j1x j2x]]. exists x. subst t.
      assert (k: nm0 <> nm).
      { destruct (string_dec nm0 nm); try assumption.
        - subst nm0. unfold LookupTyp in j1x.
          eapply Lookup_fresh_neq. eapply j1x. assumption. }
      unfold LookupTyp. split; try assumption.
      * eapply LMiss; assumption.
    + case_eq us; intros.
      * constructor. constructor; try assumption. eapply Crct_Sort. eassumption.
      * { subst us t. inversion_Clear H6. 
          destruct(IHCrct (dcons n0 t1 t2 n1 d) nm0 tx cx t0 s0 eq_refl) as
              [k0 [k1 [k2 k3]]].
          inversion_Clear k3. eapply (proj2 (proj2 Crct_Typ_weaken)); try assumption.
          constructor; try assumption. }
  - myInjection H3. intuition. exists pack. assumption.
Qed.

Lemma Crct_invrt_Cast:
  forall p n cast,
    Crct p n cast -> forall t ty, cast = (TCast t ty) ->
    Crct p n t /\ Crct p n ty.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ H2). intuition.
- assert (j:= IHCrct _ _ H1). intuition.
- injection H1; intros; subst. auto.
Qed.

Lemma Crct_invrt_Proof:
  forall p n prf,
    Crct p n prf -> forall t, prf = TProof t -> Crct p n t.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ H2). intuition.
  - assert (j:= IHCrct _ H1). intuition.
  - myInjection H0. assumption.
Qed.

Lemma Crct_invrt_Fix:
  forall p n gix, Crct p n gix ->
  forall ds m, gix = (TFix ds m) -> CrctDs p (n + dlength ds) ds.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ H2). intuition.
  apply (proj2 Crct_weaken); auto.
  + generalize (dlength ds). induction n0.
    * rewrite <- plus_n_O. assumption.
    * rewrite <- plus_n_Sm. apply Crct_up. assumption.
- assert (j:= IHCrct _ _ H1). inversion_Clear j. intuition. constructor.
  + apply (proj1 Crct_Typ_weaken); assumption.
  + apply (proj1 Crct_Typ_weaken); assumption.
  + apply (proj2 (proj2 Crct_Typ_weaken)); assumption.
- injection H1; intros; subst. assumption.
Qed.

Lemma Crct_invrt_Construct:
  forall p n construct, Crct p n construct ->
  forall ipkgNm inum cnum npars nargs,
    construct = (TConstruct (mkInd ipkgNm inum) cnum npars nargs) ->
    Crct p n prop /\
    exists np itypk,
      LookupTyp ipkgNm p np itypk /\
      exists (ip:ityp), getInd itypk inum = Ret ip /\
      exists (ctr:Cnstr), getCnstr ip cnum = Ret ctr.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ _ _ H2). intuition.
  destruct H4 as [np [itypk [h1 h2]]]. exists np, itypk. intuition.
  destruct h1; split; try assumption.
  apply Lookup_weaken; trivial.
- assert (j:= IHCrct _ _ _ _ _ H1). intuition.
  destruct H3 as [np [itypk [h1 h2]]]. exists np, itypk. intuition.
  destruct h1; split; trivial. 
  apply Lookup_weaken; trivial.
- myInjection H3. intuition.
  exists m, ipkg. intuition.
  exists itp. intuition.
  exists cstr. assumption.
Qed.

Lemma Crct_invrt_any:
  forall p n t, Crct p n t -> Crct p n prop.
Proof.
  induction 1; try (solve[constructor; eassumption]); try assumption.
Qed.


Lemma Crct_App_fn_notApp:
  forall p n fn arg args, Crct p n (TApp fn arg args) -> ~(isApp fn).
intros p n fn arg args h1.
assert (j:= @Crct_invrt_App p n (TApp fn arg args) h1 fn arg args eq_refl).
intuition.
Qed.


Lemma Crcts_append:
  forall p n ts, Crcts p n ts ->
  forall us, Crcts p n us -> Crcts p n (tappend ts us).
Proof.
  induction 1; intros us h; simpl.
  - assumption.
  - apply CrctsCons; intuition.
Qed.

Lemma mkApp_pres_Crct:
  forall fn p n, Crct p n fn ->
  forall args, Crcts p n args -> Crct p n (mkApp fn args).
Proof.
  induction fn; simpl; intros p' nx h0 args h1;
  destruct args; intuition;
  try (solve [inversion_Clear h1; apply CrctApp; try assumption; not_isApp]).
  - destruct (Crct_invrt_App h0 eq_refl) as [j1 [j2 [j3 j4]]].
    rewrite tappend_tnil.
    apply CrctApp; try assumption.
  - destruct (Crct_invrt_App h0 eq_refl) as [j1 [j2 [j3 j4]]].
    apply CrctApp; try assumption. destruct t; simpl.
    + assumption.
    + inversion j3. apply CrctsCons; try assumption.
      apply Crcts_append; assumption.
Qed.

Lemma Instantiate_pres_Crct:
  forall tin, 
  (forall n bod ins, Instantiate tin n bod ins ->
  forall m p, n <= m -> Crct p (S m) bod -> Crct p m tin -> Crct p m ins) /\
  (forall n bods inss, Instantiates tin n bods inss ->
  forall m p, n <= m -> Crcts p (S m) bods -> Crct p m tin -> Crcts p m inss) /\
  (forall n ds ids, InstantiateDefs tin n ds ids ->
  forall m p, n <= m -> CrctDs p (S m) ds -> Crct p m tin -> CrctDs p m ids).
Proof.
  intros tin. apply InstInstsDefs_ind; intros.
  - assumption.
  - constructor. omega. eapply Crct_invrt_any. eassumption.
  - destruct (Crct_invrt_Rel H0 eq_refl). apply CrctRel.
    + omega.
    + eapply Crct_Sort. eassumption.
  - eapply Crct_Sort; eassumption.
  - specialize (H m p H0 (Crct_invrt_Proof H1 eq_refl) H2).
    constructor. assumption.
  - destruct (Crct_invrt_Cast H2 eq_refl). apply CrctCast.
    + apply H; trivial.
    + apply H0; trivial.
  - destruct (Crct_invrt_Prod H2 eq_refl). apply CrctProd.
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
    + apply H0; trivial.
  - destruct (Crct_invrt_Lam H2 eq_refl). apply CrctLam.
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
    + apply H0; trivial.
  - destruct (Crct_invrt_LetIn H3 eq_refl). apply CrctLetIn.
    + apply H; trivial.
    + apply H0; intuition. apply (proj1 Crct_up). assumption.
    + apply H1; intuition.
  - destruct (Crct_invrt_App H3 eq_refl) as [j1 [j2 [j3 j4]]]. 
    apply mkApp_pres_Crct.
    + apply H; trivial.
    + apply CrctsCons.
      * apply H0; trivial.
      * apply H1; trivial.
  - edestruct (Crct_invrt_Const H0).
    + reflexivity.
    + destruct H3 as [x [h1 h2]]. eapply (@CrctConst _ _ x); trivial.
      * eapply Crct_Sort. eassumption.
  - constructor. eapply Crct_Sort. eassumption.
  - apply CrctInd. eapply Crct_Sort. eassumption.
  - destruct ind. edestruct (Crct_invrt_Construct H0).
    + reflexivity.
    + destruct H3 as [npars [ip [h1 [it [h2 [ctr h3]]]]]].
      eapply CrctConstruct; try eassumption.
      * eapply Crct_Sort. eassumption.
  - destruct np, i2.
    destruct (Crct_invrt_Case H3 eq_refl) as [k0 [k1 [k2 k3]]].
    destruct k0 as [x0 jx]. eapply CrctCase. eassumption.
    + apply H; trivial.
    + apply H1; trivial.
    + apply H0; trivial.
  - assert (j:= Crct_invrt_Fix H1 eq_refl). apply CrctFix. 
    + eapply Crct_Sort. eassumption.
    + rewrite <- (InstantiateDefs_pres_dlength i). apply H. omega.
      * simpl in j. assumption.
      * simpl in j. generalize (dlength d). induction n0.
        rewrite <- plus_n_O. assumption.
        rewrite <- plus_n_Sm. apply (proj1 Crct_up). assumption.
  - eelim TWrong_not_Crct. eassumption.
  - apply CrctsNil. eapply Crct_Sort. eassumption.
  - inversion_Clear H2. apply CrctsCons.
    + apply H; trivial.
    + apply H0; trivial.
  - apply CrctDsNil. eapply Crct_Sort. eassumption.
  - inversion_Clear H3. apply CrctDsCons.
    + apply H; trivial.
    + apply H0; trivial.
    + apply H1; trivial.
Qed.

Lemma instantiate_pres_Crct:
  forall p m bod, Crct p (S m) bod ->
  forall n tin, n <= m -> Crct p m tin -> Crct p m (instantiate tin n bod).
Proof.
  intros. eapply (proj1 (Instantiate_pres_Crct tin)); try eassumption.
  - apply (proj1 (instantiate_Instantiate tin)). 
Qed.

Lemma whBetaStep_pres_Crct:
  forall p n bod, Crct p (S n) bod ->
  forall arg, Crct p n arg ->
  forall args, Crcts p n args -> Crct p n (whBetaStep bod arg args).
Proof.
  intros. unfold whBetaStep. apply mkApp_pres_Crct; trivial.
  + apply instantiate_pres_Crct; trivial. omega.
Qed.

Lemma tnth_pres_Crct:
  forall p n ts, Crcts p n ts ->
  forall m s, tnth m ts = Some s -> Crct p n s.
Proof.
  induction 1; induction m; intros.
  - simpl in H0. discriminate.
  - simpl in H0. discriminate.
  - simpl in H1. injection H1. intros. subst. assumption.
  - simpl in H1. eapply IHCrcts. eassumption.
Qed.

Lemma dnthBody_pres_Crct:
  forall p n (ds:Defs), CrctDs p n ds ->
    forall m x ix, (dnthBody m ds) = Some (x, ix) -> Crct p n x.
Proof.
  intros p n ds h m x ix.
  functional induction (dnthBody m ds); intros; auto.
  - discriminate.
  - myInjection H. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma tskipn_pres_Crct:
  forall m ts ss, tskipn m ts = Some ss -> forall p n, Crcts p n ts ->
  Crcts p n ss.
Proof.
induction m; induction ts; intros.
- simpl in H. injection H; intros; subst. assumption.
- simpl in H. injection H; intros; subst. assumption.
- simpl in H. discriminate.
- simpl in H. eapply IHm. eassumption. inversion H0. assumption.
Qed.

Lemma whCaseStep_pres_Crct:
  forall p n ts, Crcts p n ts -> forall brs, CrctDs p n brs ->
  forall m s, whCaseStep m ts brs = Some s -> Crct p n s.
Proof.
  intros p n ts h1 brs h2 m s h3. unfold whCaseStep in h3.
  assert (j: dnthBody m brs = None \/ (exists t, dnthBody m brs = Some t)).
  { destruct (dnthBody m brs).
    + right. exists p0. reflexivity.
    + left. reflexivity. }
  destruct j.
  - rewrite H in h3. discriminate.
  - destruct H as [x jx]. rewrite jx in h3. destruct x as [y0 y1].
    myInjection h3. apply mkApp_pres_Crct; try assumption.
    eapply (dnthBody_pres_Crct h2). eassumption.
Qed. 

Lemma fold_left_pres_Crct:
  forall p m (f:Term -> nat -> Term) (ns:list nat) (t:Term),
    (forall u, Crct p m u -> forall n, Crct p m (f u n)) ->
    Crct p m t -> Crct p m (fold_left f ns t).
Proof.
  intros p n f. induction ns; simpl; intros.
  - assumption.
  - apply IHns.
    + intros. apply H. assumption.
    + apply H. assumption.
Qed.

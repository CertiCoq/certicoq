(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L0_QuotedCoq" as L0.
Add LoadPath "../L1_MalechaQuoted" as L1.
(****)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L0.term.
Require Import L1.compile.
Require Import L1.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(** all items in an env are application-well-formed **)
Inductive WFaEc: envClass -> Prop :=
| wfaecTrm: forall (t:Term), WFapp t -> WFaEc (ecTrm t)
| wfaecTyp: forall n i, WFaEc (ecTyp Term n i)
| wfaecAx: WFaEc (ecAx Term).

Inductive WFaEnv: environ -> Prop :=
| wfaenil: WFaEnv nil
| wfaecons: forall ec, WFaEc ec -> forall p, WFaEnv p -> 
                   forall nm, WFaEnv ((nm, ec) :: p).
(***************
Definition WFaEc (ec: AstCommon.envClass term) : bool :=
  match ec with
    | ecTrm t => WF_term (termSize t) t
    | _ => true
  end.

Function WFaEnv (e: AstCommon.environ term) : bool :=
  match e with
    | (_, ec) :: p => WFaEc ec && WFaEnv p
    | _ => true
  end.
 **********************)




Definition ecTrm := ecTrm.
Definition ecTyp := ecTyp Term.
Definition ecAx := ecAx Term.
Definition envClass_dec := envClass_dec.
Definition fresh := fresh.
Hint Constructors AstCommon.fresh.

(** Lookup an entry in the environment **)
Definition Lookup := AstCommon.Lookup.
Hint Constructors AstCommon.Lookup.

Definition LookupDfn s p (t:Term) := Lookup s p (ecTrm t).
Definition LookupTyp s p n i := Lookup s p (ecTyp n i).
Definition LookupAx s p := Lookup s p ecAx.

(** equivalent functions **)
Definition lookup := @AstCommon.lookup Term.
Definition lookupDfn := @AstCommon.lookupDfn Term.


Lemma Lookup_pres_WFapp:
  forall p, WFaEnv p -> forall nm ec, Lookup nm p ec -> WFaEc ec.
Proof.
  induction 1; intros nn ed h; inversion_Clear h.
  - assumption.
  - eapply IHWFaEnv. eassumption.
Qed.
(*****************
Lemma Lookup_pres_WFapp:
  forall p, WFaEnv p = true ->
            forall nm ec, Lookup nm p ec -> WFaEc ec = true.
Proof.
  intros p. functional induction (WFaEnv p); intros.
  - inversion_Clear H0.
    + destruct (andb_true_true _ _ H). assumption.
    + refine (IHb _ _ _ H7). inversion_Clear H7.
      * destruct (andb_true_true _ _ H). assumption.
      * destruct (andb_true_true _ _ H). assumption.
  - inversion_Clear H0; contradiction.
Qed.
********************************)

(** Check that a named datatype and constructor exist in the environment **)
Definition CrctCnstr (ipkg:itypPack) (inum cnum:nat) : Prop :=
  if (nth_ok inum ipkg defaultItyp)
  then (if nth_ok cnum (itypCnstrs (nth inum ipkg defaultItyp)) defaultCnstr
        then True else False)
  else False.

(** correctness specification for programs (including local closure) **)
Inductive Crct: environ -> nat -> Term -> Prop :=
| CrctSrt: forall n srt, Crct nil n (TSort srt)
| CrctWkTrmTrm: forall n p t s nm, Crct p n t -> Crct p n s ->
           fresh nm p -> Crct ((nm,ecTrm s)::p) n t
| CrctWkTrmTyp: forall n p t s nm, Crct p n t -> CrctTyp p n s ->
           fresh nm p -> forall m, Crct ((nm,ecTyp m s)::p) n t
| CrctRel: forall n m p, m < n -> Crct p n prop -> Crct p n (TRel m)
| CrctCast: forall n p t ck ty, Crct p n t -> Crct p n ty ->
                                Crct p n (TCast t ck ty)
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
| CrctConstruct: forall n p ipkgNm npars itypk inum cnum,
                   Crct p n prop -> LookupTyp ipkgNm p npars itypk ->
                   CrctCnstr itypk inum cnum ->
                   Crct p n (TConstruct (mkInd ipkgNm inum) cnum)
| CrctCase: forall n p m ty mch brs,
              Crct p n mch -> Crcts p n brs -> Crct p n ty -> 
              Crct p n (TCase m ty mch brs)
| CrctFix: forall n p ds m,
             Crct p n prop ->    (** convenient for IH *)
             CrctDs p (n + dlength ds) ds -> Crct p n (TFix ds m)
| CrctInd: forall n p ind, Crct p n prop -> Crct p n (TInd ind)
with Crcts: environ -> nat -> Terms -> Prop :=
| CrctsNil: forall n p, Crct p n prop -> Crcts p n tnil
| CrctsCons: forall n p t ts,
               Crct p n t -> Crcts p n ts -> Crcts p n (tcons t ts)
with CrctDs: environ -> nat -> Defs -> Prop :=
| CrctDsNil: forall n p, Crct p n prop -> CrctDs p n dnil
| CrctDsCons: forall n p dn dty db dra ds,
          Crct p n dty -> Crct p n db -> CrctDs p n ds ->
          CrctDs p n (dcons dn dty db dra ds)
with CrctTyp: environ -> nat -> itypPack -> Prop := 
| CrctTypStart: forall n itp, CrctTyp nil n itp
| CrctTypWk1: forall n p t s nm, CrctTyp p n t -> Crct p n s ->
           fresh nm p -> CrctTyp ((nm,ecTrm s)::p) n t
| CrctTypWk2: forall n p t s nm, CrctTyp p n t -> CrctTyp p n s ->
           fresh nm p -> forall m, CrctTyp ((nm,ecTyp m s)::p) n t.
Hint Constructors Crct Crcts CrctDs CrctTyp.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with Crcts_ind' := Minimality for Crcts Sort Prop
  with CrctDs_ind' := Minimality for CrctDs Sort Prop
  with CrctTyp_ind' := Minimality for CrctTyp Sort Prop.
Combined Scheme CrctCrctsCrctDs_ind from
         Crct_ind', Crcts_ind', CrctDs_ind'.
Combined Scheme CrctCrctsCrctDsTyp_ind from
         Crct_ind', Crcts_ind', CrctDs_ind', CrctTyp_ind'.


Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n) /\
  (forall (p:environ) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; auto.
Qed.

Lemma Crct_WFApp:
  forall p n t, Crct p n t -> WFapp t.
  intros p n t h. eapply WFTrm_WFapp. eapply (proj1 Crct_WFTrm). eassumption.
Qed.

Lemma Crct_up:
  (forall p n t, Crct p n t -> Crct p (S n) t) /\
  (forall p n ts, Crcts p n ts -> Crcts p (S n) ts) /\
  (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> CrctDs p (S n) ds) /\
  (forall (p:environ) (n:nat) (itp:itypPack), CrctTyp p n itp ->
                                              CrctTyp p (S n) itp).
Proof.
  apply CrctCrctsCrctDsTyp_ind; intros;
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

Lemma CrctTypTl:
  forall pp n t, Crct pp n t ->
   forall nm npars tp p, pp = ((nm,ecTyp npars tp)::p) -> CrctTyp p n tp.
induction 1; intros; try discriminate;
try (solve [eapply IHCrct2; eassumption]);
try (solve [eapply IHCrct; eassumption]).
- injection H2; intros. subst. assumption.
- eapply IHCrct1. eassumption.
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
                                                     ~ PoccDefs nm ds) /\
  (forall (p:environ) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; try intros j; auto;
try (solve [inversion j]);
try (solve [inversion_clear j; elim (H0 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm0); trivial; elim (H2 nm0); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear H4; elim (H0 nm0); trivial]).
- inversion_clear j; elim (H0 nm0); trivial. elim (H2 nm0); trivial.
  elim (H4 nm0); trivial.
- inversion_clear j. elim (H1 nm); trivial. elim (H3 nm); trivial.
  induction args. inversion H7. elim (H5 nm); trivial.
- inversion j. subst. elim (@fresh_Lookup_fails _ _ _ (ecTrm pd) H2).
  assumption.
- inversion_Clear j. eelim (fresh_Lookup_fails H3). eassumption.
- inversion_Clear j. elim (H0 nm); trivial. elim (H2 nm); trivial.
  elim (H4 nm); trivial.
- inversion_clear j. elim (H0 nm); trivial. elim (H2 nm); trivial.
  elim (H4 nm); trivial.
Qed.

Lemma Crct_not_bad_Lookup:
  (forall p n s, Crct p n s ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ss, Crcts p n ss ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ds, CrctDs p n ds ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n itp, CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; auto;
try (solve [elim (H0 _ H3)]); try (solve [elim (H0 _ H5)]);
try (solve [elim (H0 _ H1)]); try (solve [elim (H0 _ H2)]).
- inversion H.
- destruct (string_dec nm0 nm).
  + subst. inversion_Clear H4.
    * assert (j:= proj1 Crct_fresh_Pocc _ _ _ H1 _ H3).
      elim j. constructor. 
    * elim (H0 _ H11).
  + eelim (H0 _ (Lookup_strengthen H4 _ n0)).
- elim (H0 nm0). unfold LookupDfn in H4. unfold LookupDfn.
  destruct (string_dec nm0 nm).
  + subst. inversion H4. assumption.
  + eapply (Lookup_strengthen H4). reflexivity. assumption.
- elim (H1 _ H2).
- elim (H1 _ H6).
Grab Existential Variables.
  + reflexivity.
Qed.


Lemma  Crct_weaken:
  (forall p n t, Crct p n t -> 
    forall nm s, fresh nm p -> Crct p n s -> Crct ((nm,ecTrm s)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm s, fresh nm p -> Crct p n s -> Crcts ((nm,ecTrm s)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
    forall nm s, fresh nm p -> Crct p n s -> CrctDs ((nm,ecTrm s)::p) n ds) /\
  (forall p n itp, CrctTyp p n itp -> 
    forall nm s, fresh nm p -> Crct p n s -> CrctTyp ((nm,ecTrm s)::p) n itp).
eapply CrctCrctsCrctDsTyp_ind; intros; intuition.
- apply CrctWkTrmTrm; try assumption. eapply CrctConst; try eassumption.
- eapply CrctConstruct; try eassumption.
  apply H0; try assumption. apply Lookup_weaken; eassumption.
Qed.

Lemma  Crct_Typ_weaken:
  (forall p n t, Crct p n t -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                   forall npars, Crct ((nm,ecTyp npars itp)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                 forall npars, Crcts ((nm,ecTyp npars itp)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                   forall npars, CrctDs ((nm,ecTyp npars itp)::p) n ds) /\
  (forall p n jtp, CrctTyp p n jtp -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                  forall npars,  CrctTyp ((nm,ecTyp npars itp)::p) n jtp).
Proof.
  eapply CrctCrctsCrctDsTyp_ind; intros; auto.
  - apply CrctWkTrmTyp; try assumption. eapply CrctConst; try eassumption.
  - eapply CrctConstruct; try eassumption.
    apply H0; try assumption. apply Lookup_weaken; eassumption.
Qed.

Lemma Crct_strengthen:
  (forall pp n t, Crct pp n t -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrm nm t -> Crct p n t) /\
  (forall pp n ts, Crcts pp n ts -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrms nm ts -> Crcts p n ts) /\
  (forall pp n ds, CrctDs pp n ds -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccDefs nm ds -> CrctDs p n ds) /\
  (forall p n itp, CrctTyp p n itp -> True).
eapply CrctCrctsCrctDsTyp_ind; intros; auto.
- inversion H.
- injection H4; intros. subst. assumption.
- injection H4; intros. subst. assumption.
- apply CrctRel; try assumption. eapply H1. eapply H2.
  intros h. inversion h.
- apply CrctCast.
  + eapply H0. eassumption.
    intros h. elim H4. apply PoCastTm. assumption.
  + eapply H2. eassumption.
    intros h. elim H4. apply PoCastTy. assumption.
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
- eapply CrctConstruct; try eassumption.
  + eapply H0. eapply H3. intros h. inversion h.
  + rewrite H3 in H1.
    assert (j: nm <> ipkgNm).
    { eapply notPocc_TCnstr. eassumption. }
    inversion H1.
    * rewrite H7 in j. nreflexivity j.
    * eassumption.
- apply CrctCase.
  + eapply H0. eassumption.
    intros h. elim H6. apply PoCaseL. assumption.
  + eapply H2. eassumption.
    intros h. elim H6. apply PoCaseR. assumption.
  + eapply H4. eassumption.
    intros h. elim H6. apply PoCaseTy. assumption.
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

(** Crct inversions **)
Lemma LookupDfn_pres_Crct:
  forall p n t, Crct p n t -> forall nm u, LookupDfn nm p u -> Crct p n u.
Proof.
assert (lem: (forall p n t, Crct p n t -> 
                            forall nm u, LookupDfn nm p u -> Crct p n u) /\
             (forall p n ts, Crcts p n ts -> True) /\
             (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> True) /\
             (forall (p:environ) (n:nat) (itp:itypPack),
                CrctTyp p n itp -> True)).
  { apply CrctCrctsCrctDsTyp_ind; intros; auto;
    try (solve [eapply H1; eassumption]);
    try (solve [eapply H2; eassumption]);
    try (solve [eapply H0; eassumption]).
    - inversion H.
     - apply CrctWkTrmTrm; try assumption. inversion H4; subst.
      + assumption.
      + eapply H0. apply H11.
    - apply CrctWkTrmTyp; try assumption. inversion H4; subst.
      eapply H0. eassumption.
  }
  apply (proj1 lem).
Qed.

Lemma Crct_invrt_Rel:
  forall p n rel, Crct p n rel -> forall m, rel = TRel m ->
     m < n /\ Crct p n prop.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 m). intuition.
  - assert (j:= IHCrct m). specialize (IHCrct _ H2). intuition.
  - assert (j:= IHCrct m). injection H1. intuition.
Qed.

Lemma Crct_invrt_WkTrm:
  forall (ev:environ) n t, Crct ev n t ->
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
  - assert (j:= IHCrct _ H2). intuition.
    destruct H4 as [x [h2 h3]]. exists x. split.
    + assert (j: nm0 <> nm).
      { destruct (string_dec nm0 nm). 
        - subst. elim (fresh_Lookup_fails H1 h2).
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
  - assert (j:= IHCrct _ _ _ H2). intuition.
    apply (CrctWkTrmTyp);trivial.
    apply (proj2 (proj2 (Crct_up))). assumption.    
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
  - assert (j:= IHCrct _ _ _ H2). intuition.
    apply (CrctWkTrmTyp);trivial.
    apply (proj2 (proj2 (Crct_up))). assumption.    
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
  - assert (j:= IHCrct _ _ _ _ H2). intuition.
    apply (CrctWkTrmTyp); trivial.
    apply (proj2 (proj2 Crct_up)). assumption.
  - injection H2. intros. subst. intuition.
Qed.

Lemma Crct_invrt_App:
  forall p n app,
    Crct p n app -> forall fn arg args, app = (TApp fn arg args) ->
    Crct p n fn /\ Crct p n arg /\ Crcts p n args /\ ~(isApp fn).
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
  apply (proj2 Crct_weaken); auto.
- assert (j:= IHCrct _ _ _ H2). intuition.
  apply (proj1 (proj2 Crct_Typ_weaken)); auto.
- injection H3; intros; subst. auto.
Qed.

Lemma Crct_invrt_Case:
  forall p n case,
    Crct p n case -> forall m t s us, case = (TCase m t s us) ->
    Crct p n t /\ Crct p n s /\ Crcts p n us.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ _ H2). intuition.
  apply (proj2 Crct_weaken); auto.
- assert (j:= IHCrct _ _ _ _ H2). intuition.
  apply (proj1 (proj2 Crct_Typ_weaken)); auto.
- injection H2; intros; subst. auto.
Qed.

Lemma Crct_invrt_Cast:
  forall p n cast,
    Crct p n cast -> forall t ck ty, cast = (TCast t ck ty) ->
    Crct p n t /\ Crct p n ty.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
- assert (j:= IHCrct _ _ _ H2). intuition.
- injection H1; intros; subst. auto.
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
- assert (j:= IHCrct _ _ H2). 
  apply (proj1 (proj2 (proj2 Crct_Typ_weaken))); auto.
  + generalize (dlength ds). induction n0.
    * rewrite <- plus_n_O. assumption.
    * rewrite <- plus_n_Sm. apply Crct_up. assumption.
- injection H1; intros; subst. assumption.
Qed.
  
Lemma Crct_invrt_Construct:
  forall p n construct, Crct p n construct ->
  forall ipkgNm inum cnum, construct = (TConstruct (mkInd ipkgNm inum) cnum) ->
    Crct p n prop /\
    exists npars itypk,
      LookupTyp ipkgNm p npars itypk /\ CrctCnstr itypk inum cnum.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
  destruct H4 as [npars [itypk [h1 h2]]]. exists npars, itypk. intuition.
  apply Lookup_weaken; trivial.
- assert (j:= IHCrct _ _ _ H2). intuition.
  destruct H4 as [npars [itypk [h1 h2]]]. exists npars, itypk. intuition.
  apply Lookup_weaken; trivial.
- injection H2; intros; subst. intuition.
  exists npars, itypk. intuition.
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
  - apply CrctInd. eapply Crct_Sort. eassumption.
  - destruct ind. edestruct (Crct_invrt_Construct H0).
    + reflexivity.
    + destruct H3 as [npars [x [h1 h2]]]. eapply CrctConstruct; try eassumption.
      * eapply Crct_Sort. eassumption.
  - destruct (Crct_invrt_Case H3 eq_refl) as [h1 [h2 h3]]. apply CrctCase.
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
  forall p n ts, Crcts p n ts -> forall brs, Crcts p n brs ->
  forall m s, whCaseStep m ts brs = Some s -> Crct p n s.
Proof.
  intros p n ts h1 brs h2 m s h3. unfold whCaseStep in h3.
  assert (j: tnth m brs = None \/ (exists t, tnth m brs = Some t)).
  { destruct (tnth m brs).
    + right. exists t. reflexivity.
    + left. reflexivity. }
  destruct j.
  - rewrite H in h3. discriminate.
  - destruct H. rewrite H in h3. injection h3; intros. rewrite <- H0.
    apply mkApp_pres_Crct; try assumption.
    apply (tnth_pres_Crct h2 _ H).
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

(***
Lemma whFixStep_pres_Crct:
  forall dts m args,
  forall p i, CrctDs p i dts -> Crcts p i args -> i >= dlength dts ->
              Crcts p i args -> Crct p i (whFixStep dts m args).
Proof.
  Admitted.
(***)
  intros dts m args p i h2 h3 h4.
  unfold whFixStep, pre_whFixStep.
(*  Check fold_left_pres_mkApp. *)
  induction dts.
  - simpl in *. inversion_Clear h2. inversion_Clear h4. assumption.
    assert (j: n + 0 = n). induction n; auto.
    rewrite j in *. constructor; try assumption. not_isApp.
  - simpl in h3. eapply IHdts. simpl in h1. simpl.

    rewrite 
    constructor.
  functional induction (fold_left
            (fun (bod : Term) (ndx : nat) => instantiate (TFix dts ndx) 0 bod)
            (list_to_zero (dlength dts)) (dnthBody m dts)).
  - rewrite <- h1. inversion_Clear h4.
    +
  - simpl in *. destruct args.
  - unfold whFixStep in h1. simpl in h1. discriminate.
  - simpl in h3. unfold whFixStep in h1. simpl in h1.
    injection h1; intros j. rewrite <- j. admit.
  - unfold whFixStep in h1. simpl in h1.

 destruct (dnthBody m dts).
***)


 (***
Goal
  forall dts m args n t s i,
    whFixStep dts m args = whFixStep (dcons n t s i dts) (S m) args.
unfold whFixStep. intros. simpl. induction dts; induction m.
-  reflexivity.
-  reflexivity.
- unfold dnthBody. apply f_equal. destruct (dnthBody 0 dts). 
  + admit.
  + simpl. Check fold_left.

Goal
  forall dts m args n t s i,
    whFixStep dts m args = whFixStep (dcons n t s i dts) (S m) args.
induction dts; induction m; intros.
- reflexivity.
- reflexivity.
- unfold whFixStep. unfold dnthBody. apply f_equal.
  Definition mkapp (args:Terms) (t:Term) := mkApp t args.
  change (mkapp args
     (fold_left
        (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n t t0 n0 dts) ndx) 0 bod)
        (list_to_zero (dlength (dcons n t t0 n0 dts))) t0)  =
   mkapp args
     (fold_left
        (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n1 t1 s i (dcons n t t0 n0 dts)) ndx) 0 bod)
        (list_to_zero (dlength (dcons n1 t1 s i (dcons n t t0 n0 dts)))) t0)).
  apply f_equal.
  unfold whFixStep in IHdts. admit.
- unfold whFixStep. unfold dnthBody.
 
Lemma whFixStep_pres_Crct:
  forall dts p i, CrctDs p i dts -> forall n, i = (n + dlength dts) ->
  forall args, Crcts p i args ->
  forall m s, whFixStep dts m args = Some s -> Crct p i s.
Proof.
  induction dts; intros p i h1 nx h2 args h3 m s h4.
  - unfold whFixStep in h4. simpl in h4. discriminate.
  - eapply IHdts. 
    + inversion h1. assumption.
    + rewrite h2. instantiate (1:= S nx). simpl. omega.
    + eassumption.
    + rewrite <- h4. instantiate (1:= S m).
unfold whFixStep; simpl; fold whFixStep.
destruct m. simpl.


      unfold whFixStep at 2. 
      change (whFixStep dts (S m) args =
   match dnthBody m (dcons n t t0 n0 dts) with
   | Some body =>
       let f :=
         fold_left
           (fun (bod : Term) (ndx : nat) =>
            instantiate (TFix (dcons n t t0 n0 dts) ndx) 0 bod)
           (cons (dlength dts)
                         (list_to_zero (dlength dts))) body in
       Some (mkApp f args)
   | None => None
   end). 
      unfold whFixStep.

    change (match dnthBody m (dcons n t t0 n0 dts) with
       | Some body =>
           Some
             (mkApp
                (fold_left
                   (fun (bod : Term) (ndx : nat) =>
                    instantiate (TFix (dcons n t t0 n0 dts) ndx) 0 bod)
                   (cons (dlength dts)
                         (list_to_zero (dlength dts))) body) args)
       | None => None
       end = Some s) in h4. simpl in h4.

unfold whFixStep in IHdts.


  induction 1; intros nx h1; inversion 1;
  destruct m; intros s h2; try discriminate.
  - unfold whFixStep in h2. simpl in h2. injection h2; intros.
    rewrite <- H7. 
    unfold whFixStep in IHCrctDs. rewrite .
admit.
  - unfold whFixStep in h.

  intros p n dts h1 args h2 m s h4. unfold whFixStep in h4.
  assert (j: dnthBody m dts = None \/ (exists t, dnthBody m dts = Some t)).
  { destruct (dnthBody m dts).
    + right. exists t. reflexivity.
    + left. reflexivity. }
  destruct j.
  - rewrite H in h4. discriminate.
  - destruct H. rewrite H in h4. injection h4; intros. rewrite <- H0.
    apply mkApp_pres_Crct; try assumption.
    + induction dts; simpl.
      * unfold dnthBody in H. discriminate.
      * { 
          - simpl. destruct m. simpl in H. injection H; intros. subst.

Qed. 
***)


(***********************
(** An alternative correctness specification for programs: [crct], below **)
Definition weaklyClosed (t:Term) (p:environ) : Prop :=
  forall nm, PoccTrm nm t -> lookupDfn nm p <> None.
Fixpoint weaklyCloseds (ts:Terms) p : Prop :=
  match ts with
    | tnil => True
    | tcons s ss => weaklyClosed s p /\ weaklyCloseds ss p
  end.
Fixpoint weaklyClosedd (ds:Defs) p : Prop :=
  match ds with
    | dnil => True
    | dcons nm ty tb m es =>
      weaklyClosed ty p /\ weaklyClosed tb p /\ weaklyClosedd es p
  end.

(****  ???????
Lemma Pocc_notWC:
  forall nm,
  (forall t, PoccTrm nm t -> ~ weaklyClosed t nil) /\
  (forall ts, PoccTrms nm ts -> ~ weaklyCloseds ts nil) /\
  (forall ds, PoccDefs nm ds -> ~ weaklyClosedd ds nil).
intros nm; apply poTrmTrmsDefs_ind; unfold not; intros;
           try (unfold weaklyClosed in H0; simpl in H0);
           try (unfold weaklyClosed in H1; simpl in H1); 
           try (apply H0; intros xnm h; apply (H1 xnm));
           try (solve [constructor; assumption]).
- apply PoCastTy. assumption.
- apply PoProdTy. assumption.
- apply PoLambdaTy. assumption.
- apply PoLetInBod; assumption.
- apply PoLetInTy; assumption.
- apply PoAppA. assumption.
- apply H0. elim (H1 nm); auto. apply PoAppR. assumption.
- elim (H0 nm); auto. constructor. assumption.
- elim (H1 nm); auto. apply PoCaseR. assumption.
- elim (H1 nm); auto. apply PoCaseTy. assumption.
- elim (H1 nm); auto. apply PoFix. assumption.
- destruct H1. apply H0. intros xnm h. unfold weaklyClosed in H1.
  apply (H1 nm). assumption.
- destruct H1. apply H0. assumption.
- destruct H1. apply H0. intros nm0 j. induction ds.
  elim H0.

  apply (H2 nm). assumption.
- intuition.
Qed.
**************)

Lemma weaklyClosed_TCast:
  forall t ty c p, weaklyClosed (TCast t c ty) p ->
                   weaklyClosed t p /\ weaklyClosed ty p.
unfold weaklyClosed. intros t ty c pb h1. split; intros nm h2.
- apply h1. apply PoCastTm. assumption.
- apply h1. apply PoCastTy. assumption.
Qed.

Lemma weaklyClosed_TCase:
  forall n ty mch brs p, weaklyClosed (TCase n ty mch brs) p ->
            weaklyClosed mch p /\ weaklyCloseds brs p /\ weaklyClosed ty p.
unfold weaklyClosed. intros n ty mch brs p h1. split; [|split].
- intros xnm h2. apply (h1 xnm). apply PoCaseL. assumption.
- induction brs; unfold weaklyCloseds. auto. split.
  + unfold weaklyClosed. intros xnm h2. apply (h1 xnm).
    apply PoCaseR. apply PoThd. assumption.
  + apply IHbrs. intros xnm h2. apply (h1 xnm). inversion_clear h2.
    apply PoCaseL. assumption.
    apply PoCaseR. apply PoTtl. assumption.
    apply PoCaseTy. assumption.
- intros xnm h2. apply (h1 xnm). apply PoCaseTy. assumption.
Qed.

Lemma Pocc_weakClsd_no_lookup:
  forall nm t, PoccTrm nm t ->
               forall p, weaklyClosed t p -> lookupDfn nm p <> None.
induction 1; intros p h1; unfold weaklyClosed in h1; apply h1;
try (solve [constructor; assumption]).
- apply PoCastTy. assumption.
- apply PoProdTy. assumption.
- apply PoLambdaTy. assumption.
- apply PoLetInBod. assumption.
- apply PoLetInTy. assumption.
- apply PoAppA. assumption.
- apply PoAppR. assumption.
- apply PoCaseR. assumption.
- apply PoCaseTy. assumption.
Qed.

Lemma weaklyClosed_weaken:
  forall s p, weaklyClosed s p -> 
              forall t nm, weaklyClosed s ((nm, ecConstr t) :: p).
unfold weaklyClosed. intros s p h1 t nmx nmy h2.
assert (j1:= h1 _ h2). destruct (string_dec nmy nmx).
- rewrite e. unfold lookupDfn, lookupDfn. rewrite string_eq_bool_rfl.
  intros j2. discriminate.
- rewrite (lookupDfn_neq _ _ n). assumption.
Qed.

Lemma weaklyClosed_lookupDfn:
  forall nm p, weaklyClosed (TConst nm) p <-> lookupDfn nm p <> None.
unfold weaklyClosed; split.
- intros h1. apply h1. apply PoConst. rewrite string_eq_bool_rfl. reflexivity.
- intros h1 nmx h2. destruct (string_dec nmx nm).
  + subst. assumption. 
  + inversion_clear h2. rewrite (string_eq_bool_neq n) in H. discriminate.
Qed.

Lemma lookup_wclsd:
  forall nm p t, LookupDfn nm p t -> weaklyClosed (TConst nm) p.
induction 1; intros nm h; unfold weaklyClosed.
- inversion_clear h. simpl. rewrite H. intuition. discriminate.
- destruct (string_dec nm s1).
  + rewrite e. simpl. rewrite string_eq_bool_rfl. destruct t.
    intuition. discriminate.
  + simpl. rewrite (string_eq_bool_neq n). destruct t.
    unfold weaklyClosed in IHLookupDfn. apply (IHLookupDfn _ h).
Qed.

Inductive envOk : environ -> Prop :=
| envOk_nil : envOk nil
| envOk_cons : forall nm t p,
      fresh nm p -> envOk p -> weaklyClosed t p ->
         envOk ((nm, ecConstr t) :: p).
Hint Constructors envOk.

Lemma envOk_nPocc_hd:
  forall nmtp, envOk nmtp ->
  forall nm t p, nmtp = ((nm, ecConstr t) :: p) -> ~ PoccTrm nm t.
induction 1; intros nmx tx px h.
- discriminate.
- injection h. intros. subst. unfold weaklyClosed in H1. intros j.
  elim (H1 _ j). apply (proj1 (fresh_lookup_fails _ _) H).
Qed.

Lemma envOk_tl:
  forall nmtp, envOk nmtp ->
  forall nm t p, nmtp = ((nm, ecConstr t) :: p) -> envOk p.
induction 1; intros nmx tx px h.
- inversion h.
- injection h; intros. subst. auto.
Qed.

Lemma LookupEvnOk_nPocc:
  forall nm p t, LookupDfn nm p t -> envOk p -> ~ PoccTrm nm t.
induction 1; intros; intros h.
- inversion_Clear H. unfold weaklyClosed in H5. elim (H5 s). auto.
  apply (proj1 (fresh_lookup_fails _ _)). auto.
- elim IHLookupDfn; auto. destruct t. eapply (@envOk_tl _ H1 s1 t).
  reflexivity.
Qed.

(******************  ????????????
Lemma Crct_weaklyClosed:
  (forall p n t, Crct p n t -> weaklyClosed t p) /\
  (forall p n ts, Crcts p n ts -> weaklyCloseds ts p) /\
  (forall p n ds, CrctDs p n ds -> weaklyClosedd ds p).
apply CrctCrctsCrctDs_ind; unfold weaklyClosed; intros;
try (solve [inversion H|inversion H0|simpl;auto]).
- destruct (string_dec nm0 nm); unfold lookupDfn.
  + subst. rewrite (string_eq_bool_rfl nm). intros j. discriminate.
  + rewrite (string_eq_bool_neq n0). apply H0. assumption.
- inversion_clear H2. 
- inversion_clear H3. apply H0. assumption. apply H2. assumption.
- inversion_clear H3. apply H0. assumption. apply H2. assumption.
- inversion_clear H3.
  + apply H0. assumption.
  + apply H2. assumption.
- inversion_clear H5.
  + apply H0. assumption.
  + apply H2. assumption.
  + apply H4. assumption.
- inversion_clear H5. 
  + apply H0. assumption.
  + apply H2. assumption.
  + induction args. inversion_clear H6.
    * inversion_clear H6. destruct H4. unfold weaklyClosed in H4.
      apply (H4 nm H5). destruct H4. inversion_clear H3.
      apply IHargs; assumption.
- inversion H2. rewrite (string_eq_bool_eq _ _ H4). intros h. 
  assert (j:= @lookupDfn_None_not_LookupDfn _ _ pd h). contradiction.
- inversion H1.
- inversion_clear H5.
  + apply H0. assumption.
  + induction brs; destruct H2; inversion_clear H6. 
    * unfold weaklyClosed in H2. apply H2. assumption.
    * inversion_clear H1. eapply IHbrs; assumption.
  + apply H4. assumption.
- inversion_clear H1.
  induction ds; inversion_clear H2; inversion_clear H;
  destruct H0; destruct H0.
  + unfold weaklyClosed in H. apply (H _ H1).
  + unfold weaklyClosed in H0. apply (H0 _ H1).
  + apply IHds; assumption.
Qed.

Lemma Crct_envOk:
  (forall p n t, Crct p n t -> envOk p) /\
  (forall p n ts, Crcts p n ts -> envOk p) /\
  (forall p n ds, CrctDs p n ds -> envOk p).
apply CrctCrctsCrctDs_ind; intros; auto.
- constructor; auto. destruct (Crct_weaklyClosed). apply (H4 _ _ _ H1).
Qed.


Definition crct (p:environ) (t:Term) : Prop := envOk p /\ weaklyClosed t p.
Fixpoint crcts (p:environ) (ts:Terms) : Prop :=
  match ts with
    | tnil => True
    | tcons s ss => crct p s /\ crcts p ss
  end.

Goal forall p n t, Crct p n t -> crct p t.
intros p n t h. destruct Crct_envOk. destruct Crct_weaklyClosed; split.
- apply (H _ _ _ h).
- apply (H1 _ _ _ h).
Qed.

Lemma ok_lookup_nPocc:
  forall stp, envOk stp -> forall s t p, stp = ((s, ecConstr t) :: p) ->
                ~ PoccTrm s t.
induction 1; intros ss tt pp h.
- discriminate.
- injection h. intros. subst. unfold weaklyClosed in H1. intros j.
  elim (H1 _ j). apply (proj1 (fresh_lookup_fails _ _) H).
Qed.

Lemma weaklyClosed_nil_crct: forall t, weaklyClosed t nil -> crct nil t.
split; auto. 
Qed.

Lemma envOk_lookup_crct:
  forall p, envOk p -> forall nm t, LookupDfn nm p t -> crct p (TConst nm).
induction 1; intros xnm tx h1; inversion h1; subst; split; try intuition; 
unfold weaklyClosed; intros nmy h3; inversion_clear h3; simpl.
- rewrite H2. intuition. discriminate.
- rewrite (string_eq_bool_eq _ _ H2). rewrite (string_eq_bool_neq H7). 
  rewrite (proj2 (lookupDfn_LookupDfn _ _ _) H8). intuition. discriminate.
Qed.

**********************************)
******************************************)

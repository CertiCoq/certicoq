(******)
(* Add LoadPath "../common" as Common. *)
(* Add LoadPath "../L1_MalechaQuoted" as L1. *)
(* Add LoadPath "../L1_5_box" as L1_5. *)
(* Add LoadPath "../L2_typeStripped" as L2. *)
(* Add LoadPath "../L3_flattenedApp" as L3. *)
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L3.term.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(** Check that a named datatype and constructor exist in the environment **)
Definition defaultCnstr := {| CnstrNm:=""; CnstrArity:= 0 |}.
Definition defaultItyp := {| itypNm:=""; itypCnstrs:=nil |}.
Definition CrctCnstr (ipkg:itypPack) (inum cnum:nat) (args:nat): Prop :=
  match
    (do ity <- getInd ipkg inum;
     do itp <- getCnstr ity cnum;
        ret (CnstrArity itp))
  with
  | Exc s => False
  | Ret n => n = args
  end.

Definition getIndArities pack n :=
  do ity <- getInd pack n;
     ret (List.map CnstrArity ity.(itypCnstrs)).

Fixpoint is_n_lambda (n : nat) (t : Term) :=
  match n with
  | 0%nat => true
  | S n => 
    match t with
    | TLambda _ t => is_n_lambda n t
    | _ => false
    end
  end.

Definition CrctBranches
           (e: environ Term) (arities: list nat) (brs: Terms) : Prop :=
  List.length arities = tlength brs /\
  forall i, match List.nth_error arities i, tnth i brs with
       | Some ar, Some t => is_n_lambda ar t = true
       | _, _ => False
       end.

Definition CrctAnnot
    (e: environ Term) (ann: inductive * nat * list nat) (brs: Terms) : Prop :=
  let '(ind, pars, args) := ann in
  let 'mkInd mind n := ind in
  match lookup mind e with
  | Some (ecTyp _ pars' pack) =>
    pars' = pars /\ getIndArities pack n = Ret args /\
    CrctBranches e args brs
  | _ => False
  end.

(** correctness specification for programs (including local closure) **)
Inductive Crct: (environ Term) -> nat -> Term -> Prop :=
| CrctSrt: forall n s, Crct nil n (TSort s)
| CrctWkTrmTrm: forall n p t s nm, Crct p n t -> Crct p n s ->
           fresh nm p -> Crct ((nm,ecTrm s)::p) n t
| CrctWkTrmTyp: forall n p t s nm, Crct p n t -> CrctTyp p n s ->
           fresh nm p -> forall m, Crct ((nm,ecTyp _ m s)::p) n t
| CrctRel: forall n m p, m < n -> Crct p n prop -> Crct p n (TRel m)
| CrctProd: forall n p nm bod,
            Crct p n prop -> Crct p (S n) bod -> Crct p n (TProd nm bod)
| CrctLam: forall n p nm bod,
            Crct p n prop -> Crct p (S n) bod -> Crct p n (TLambda nm bod)
| CrctLetIn: forall n p nm dfn bod,
         Crct p n dfn -> Crct p (S n) bod -> 
         Crct p n (TLetIn nm dfn bod)
| CrctApp: forall n p fn a,  ~ (isConstruct fn) ->
             Crct p n fn -> Crct p n a -> Crct p n (TApp fn a)
| CrctConst: forall n p pd nm,
               Crct p n prop -> LookupDfn nm p pd -> Crct p n (TConst nm)
| CrctConstruct: forall n p ipkgNm npars itypk inum cnum args,
                   Crct p n prop -> LookupTyp ipkgNm p npars itypk ->
                   CrctCnstr itypk inum cnum (tlength args) ->
                   Crcts p n args ->
                   Crct p n (TConstruct (mkInd ipkgNm inum) cnum args)
| CrctCase: forall n p m mch brs,
    CrctAnnot p m brs ->
              Crct p n mch -> Crcts p n brs ->
              Crct p n (TCase m mch brs)
| CrctFix: forall n p ds m,
             Crct p n prop ->    (** convenient for IH *)
             CrctDs p (n + dlength ds) ds -> Crct p n (TFix ds m)
| CrctInd: forall n p ind, Crct p n prop -> Crct p n (TInd ind)
with Crcts: environ Term -> nat -> Terms -> Prop :=
| CrctsNil: forall n p, Crct p n prop -> Crcts p n tnil
| CrctsCons: forall n p t ts,
               Crct p n t -> Crcts p n ts -> Crcts p n (tcons t ts)
with CrctDs: environ Term -> nat -> Defs -> Prop :=
| CrctDsNil: forall n p, Crct p n prop -> CrctDs p n dnil
| CrctDsCons: forall n p dn db dra ds,
          Crct p n db -> CrctDs p n ds -> CrctDs p n (dcons dn db dra ds)
with CrctTyp: environ Term -> nat -> itypPack -> Prop := 
| CrctTypStart: forall n itp, CrctTyp nil n itp
| CrctTypWk1: forall n p t s nm, CrctTyp p n t -> Crct p n s ->
           fresh nm p -> CrctTyp ((nm,ecTrm s)::p) n t
| CrctTypWk2: forall n p t s nm, CrctTyp p n t -> CrctTyp p n s ->
           fresh nm p -> forall m, CrctTyp ((nm,ecTyp _ m s)::p) n t.
Hint Constructors Crct Crcts CrctDs CrctTyp.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with Crcts_ind' := Minimality for Crcts Sort Prop
  with CrctDs_ind' := Minimality for CrctDs Sort Prop
  with CrctTyp_ind' := Minimality for CrctTyp Sort Prop.
Combined Scheme CrctCrctsCrctDsTyp_ind from
         Crct_ind', Crcts_ind', CrctDs_ind', CrctTyp_ind'.
Combined Scheme CrctCrctsCrctDs_ind from Crct_ind', Crcts_ind', CrctDs_ind'.
 
Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall (p:environ Term) (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n) /\
  (forall (p:environ Term) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
  apply CrctCrctsCrctDsTyp_ind; intros; try auto; try (solve [constructor]).
Qed.

Lemma Crct_up:
  (forall p n t, Crct p n t -> Crct p (S n) t) /\
  (forall p n ts, Crcts p n ts -> Crcts p (S n) ts) /\
  (forall (p:environ Term) (n:nat) (ds:Defs),
     CrctDs p n ds -> CrctDs p (S n) ds) /\
  (forall (p:environ Term) (n:nat) (itp:itypPack),
     CrctTyp p n itp -> CrctTyp p (S n) itp).
Proof.
  apply CrctCrctsCrctDsTyp_ind; intros;
  try (solve[econstructor; try eassumption; try omega]).
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
    forall nm npars tp p, pp = ((nm,ecTyp _ npars tp)::p) -> CrctTyp p n tp.
induction 1; intros; try discriminate;
try (solve [eapply IHCrct2; eassumption]);
try (solve [eapply IHCrct; eassumption]);
try (solve [eapply IHCrct1; eassumption]).
- injection H2; intros. subst. assumption.
Qed.

Lemma Crct_fresh_Pocc:
  (forall p n t, Crct p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n ts, Crcts p n ts -> forall nm, fresh nm p -> ~ PoccTrms nm ts) /\
  (forall p n (ds:Defs), CrctDs p n ds -> forall nm, fresh nm p ->
                                                     ~ PoccDefs nm ds) /\
  (forall (p:environ Term) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; try intros j; auto;
try (solve [inversion j]);
try (solve [inversion_clear j; elim (H0 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear j; elim (H0 nm0); trivial; elim (H2 nm0); trivial]);
try (solve [inversion_clear j; elim (H0 nm); trivial; elim (H2 nm); trivial]);
try (solve [inversion_clear H4; elim (H0 nm0); trivial]).
- inversion j; subst.
  + elim (H1 _ H4). assumption.
  + elim (H3 _ H4). assumption.
- inversion j. subst.
  elim (@fresh_Lookup_fails _ _ _ (ecTrm pd) H2). assumption.
- inversion_Clear j. destruct H1. 
  + eelim (fresh_Lookup_fails H5). eassumption.
  + eelim H4; eassumption.
- inversion j; subst.
  + red in H. apply fresh_lookup_None in H4. rewrite H4 in H. auto.
  + inversion_clear j; elim (H1 nm); trivial; elim (H3 nm); trivial.
  + inversion_clear j; elim (H1 nm); trivial; elim (H3 nm); trivial.
Qed.

Lemma Crct_not_bad_Lookup:
  (forall p n s, Crct p n s ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ss, Crcts p n ss ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ds, CrctDs p n ds ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall (p:environ Term) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctDsTyp_ind; intros; auto;
try (solve [elim (H0 _ H3)]); try (solve [elim (H0 _ H5)]);
try (solve [elim (H1 _ H2)]); try (solve [elim (H1 _ H3)]);
try (solve [elim (H0 _ H1)]); try (solve [elim (H0 _ H2)]).
- inversion H.
- destruct (string_dec nm0 nm).
  + subst. inversion_Clear H4.
    * assert (j:= proj1 Crct_fresh_Pocc _ _ _ H1 _ H3).
      elim j. constructor.
    * elim (H0 _ H11).
  + refine (H0 _ (Lookup_strengthen H4 eq_refl n0)).
- elim (H0 nm0). unfold LookupDfn in H4. unfold LookupDfn.
  destruct (string_dec nm0 nm).
  + subst. inversion H4. assumption.
  + refine (Lookup_strengthen H4 eq_refl _). assumption.
- elim (H1 _ H4).
- elim (H1 _ H4).
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
- destruct H1. eapply CrctConstruct; try eassumption.
  + apply H0; assumption. 
  + split; try apply Lookup_weaken; eassumption.
  + apply H4; assumption.
Qed.


Lemma  Crct_Typ_weaken:
  (forall p n t, Crct p n t -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                   forall npars, Crct ((nm,ecTyp _ npars itp)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                 forall npars, Crcts ((nm,ecTyp _ npars itp)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                   forall npars, CrctDs ((nm,ecTyp _ npars itp)::p) n ds) /\
  (forall p n jtp, CrctTyp p n jtp -> 
    forall nm itp, fresh nm p -> CrctTyp p n itp ->
                  forall npars,  CrctTyp ((nm,ecTyp _ npars itp)::p) n jtp).
Proof.
  eapply CrctCrctsCrctDsTyp_ind; intros; auto.
  - apply CrctWkTrmTyp; try assumption. eapply CrctConst; try eassumption.
  - destruct H1. eapply CrctConstruct; try eassumption.
    + apply H0; try assumption. 
    + split; try apply Lookup_weaken; eassumption.
    + apply H4; try assumption.
Qed.

Lemma Crct_strengthen:
  (forall pp n s, Crct pp n s -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrm nm s -> Crct p n s) /\
  (forall pp n ss, Crcts pp n ss -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrms nm ss -> Crcts p n ss) /\
  (forall pp n ds, CrctDs pp n ds -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccDefs nm ds -> CrctDs p n ds) /\
  (forall (pp:environ Term) (n:nat) (itp:itypPack), CrctTyp pp n itp -> True).
Proof.
  apply CrctCrctsCrctDsTyp_ind; intros; auto.
  - discriminate.
  - injection H4; intros. subst. assumption.
  - injection H4; intros. subst. assumption.
  - apply CrctRel; try assumption. eapply H1. eapply H2.
    intros h. inversion h.
  - apply CrctProd.
    + eapply H0. eassumption.
      intros h. inversion h.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoProdBod. assumption.
  - apply CrctLam.
    + eapply H0. eassumption.
      intros h. inversion h.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoLambdaBod. assumption.
  - apply CrctLetIn.
    + eapply H0. eassumption.
      intros h. elim H4. apply PoLetInDfn. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoLetInBod. assumption.
  - apply CrctApp; try assumption.
    + eapply H1. eassumption.
      intros h. elim H5. apply PoAppL. assumption.
    + eapply H3. eassumption.
      intros h. elim H5. apply PoAppA. assumption.
  - eapply CrctConst. eapply H0. eapply H2.
    intros h. inversion h. rewrite H2 in H1.
    assert (j: nm0 <> nm).
    { apply notPocc_TConst. assumption. }
    inversion H1.
    + rewrite H6 in j. nreflexivity j.
    + eassumption.
  - eapply CrctConstruct; try eassumption.
    + eapply H0. eapply H5. intros h. inversion h.
    + rewrite H5 in H1.
      assert (j: nm <> ipkgNm).
      { eapply notPocc_TCnstr. eassumption. }
      destruct H1. subst. split; try assumption.
      inversion_Clear H1.
      * elim j. reflexivity.
      * eassumption.
    + eapply H4; try eassumption.
      intros h. destruct H6. apply PoCnstrA. assumption.
  - apply CrctCase.
    + red. destruct m as [[[mind n0] pars] args].
      simpl in H. rewrite H4 in H. simpl in H.
      revert H; case_eq (string_eq_bool mind nm); auto.
      intros. elim H5. apply string_eq_bool_eq in H. subst mind.
      constructor.
    + eapply H1. eassumption.
      intros h. elim H5. apply PoCaseL. assumption.
    + eapply H3. eassumption.
      intros h. elim H5. apply PoCaseR. assumption.
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
    + eapply H0. eassumption. intros h. elim H4. apply PoDhd_bod. assumption.
    + eapply H2. eassumption. intros h. elim H4. apply PoDtl. assumption.
Qed.

(** Crct inversions **)
Lemma LookupDfn_pres_Crct:
  forall p n t, Crct p n t -> forall nm u, LookupDfn nm p u -> Crct p n u.
Proof.
assert (lem: (forall p n t, Crct p n t -> 
                            forall nm u, LookupDfn nm p u -> Crct p n u) /\
             (forall p n ts, Crcts p n ts -> True) /\
             (forall (p:environ Term) (n:nat) (ds:Defs),
                CrctDs p n ds -> True) /\
             (forall (p:environ Term) (n:nat) (itp:itypPack),
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
  forall nm bod, prod = TProd nm bod -> Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2).
    apply CrctWkTrmTrm; trivial.
    apply (proj1 Crct_up). assumption.
  - assert (j:= IHCrct _ _ H2).
    apply CrctWkTrmTyp; trivial.
    apply (proj2 (proj2 (Crct_up))). assumption.    
  - injection H1. intros. subst. assumption.
Qed.

Lemma Crct_invrt_Lam:
  forall p n lam, Crct p n lam ->
  forall nm bod, lam = TLambda nm bod -> Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2).
    apply CrctWkTrmTrm; trivial.
    apply (proj1 Crct_up). assumption.
  - assert (j:= IHCrct _ _ H2).
    apply CrctWkTrmTyp; trivial.
    apply (proj2 (proj2 (Crct_up))). assumption.    
  - injection H1. intros. subst. assumption.
Qed.

Lemma Crct_invrt_LetIn:
  forall p n letin, Crct p n letin ->
  forall nm dfn bod, letin = TLetIn nm dfn bod ->
     Crct p n dfn /\ Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ H2). intuition.
    apply CrctWkTrmTrm; trivial.
    apply (proj1 (Crct_up)). assumption.
  - assert (j:= IHCrct _ _ _ H2). intuition.
    apply (CrctWkTrmTyp); trivial.
    apply (proj2 (proj2 Crct_up)). assumption.
  - injection H1. intros. subst. intuition.
Qed.

Lemma Crct_invrt_App:
  forall p n app,
    Crct p n app -> forall fn arg, app = (TApp fn arg) ->
                                   Crct p n fn /\ Crct p n arg /\ ~ isConstruct fn.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2); intuition.
  - assert (j:= IHCrct _ _ H2). intuition.
  - myInjection H2. intuition.
Qed.

Lemma CrctAnnot_weaken nm (p : environ Term) m brs d :
  CrctAnnot p m brs -> fresh nm p ->
  CrctAnnot ((nm, d) :: p) m brs.
Proof.
  intros HC Hf.
  red.
  destruct m as [[[mind n0] pars] args]. simpl.
  simpl in HC.
  case_eq (string_eq_bool mind nm); auto.
  intros Heq%string_eq_bool_eq. subst mind.
  apply fresh_lookup_None in Hf. now rewrite Hf in HC.
Qed.

Lemma Crct_invrt_Case:
  forall p n case,
    Crct p n case -> forall m s us, case = (TCase m s us) ->
    CrctAnnot p m us /\ Crct p n s /\ Crcts p n us.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
  apply CrctAnnot_weaken; auto.
  apply (proj2 Crct_weaken); auto.
- assert (j:= IHCrct _ _ _ H2). intuition.
  apply CrctAnnot_weaken; auto.
  apply (proj1 (proj2 Crct_Typ_weaken)); auto.
- injection H2; intros; subst. auto.
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
  forall ipkgNm inum cnum args,
    construct = (TConstruct (mkInd ipkgNm inum) cnum args) ->
    Crct p n prop /\ Crcts p n args /\
    exists npars itypk,
      LookupTyp ipkgNm p npars itypk /\
      CrctCnstr itypk inum cnum (tlength args).
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ _ H2).
  intuition; destruct H6 as [npars [itypk [h1 h2]]].
  + apply (proj1 (proj2 Crct_weaken)); trivial.
  + destruct h1. exists npars, itypk. repeat split; try assumption.
    apply Lookup_weaken; trivial.
- assert (j:= IHCrct _ _ _ _ H2).
  intuition; destruct H6 as [npars [itypk [h1 h2]]].
  + apply (proj1 (proj2 Crct_Typ_weaken)); trivial.
  + exists npars, itypk. destruct h1. repeat split; try assumption.
    apply Lookup_weaken; trivial.
- injection H3; intros; subst. intuition.
  exists npars, itypk. intuition.
Qed.

Lemma Crcts_append:
  forall p n ts, Crcts p n ts ->
  forall us, Crcts p n us -> Crcts p n (tappend ts us).
Proof.
  induction 1; intros us h; simpl.
  - assumption.
  - apply CrctsCons; intuition.
Qed.

Lemma Instantiate_pres_is_n_lambda tin n t it k :
  Instantiate tin n t it ->
  is_n_lambda k t = true -> is_n_lambda k it = true.
Proof.
  intros H; revert k; induction H;
  simpl; intros; destruct k; 
  try (simpl in *; reflexivity || discriminate).
  simpl in H0. apply (IHInstantiate _ H0). 
Qed.

Lemma Instantiates_pres_is_n_lambda tin n ts its k :
  Instantiates tin n ts its ->
  forall i t, tnth i ts = Some t ->
         exists t', tnth i its = Some t' /\
               (is_n_lambda k t = true ->
                is_n_lambda k t' = true).
Proof.
  induction 1. simpl. intros. discriminate.
  intros.
  simpl in H1. destruct i.
  - injection H1. intros <-.
    exists it. intuition.
    eapply Instantiate_pres_is_n_lambda in H. apply H. apply H2.
  - destruct (IHInstantiates _ _ H1) as [t' [Hnth Hlam]].
    exists t'. intuition.
Qed.

Lemma Instantiates_pres_CrctAnnot tin n ts its p np :
  Instantiates tin n ts its ->
  CrctAnnot p np ts -> CrctAnnot p np its.
Proof.
  destruct np as [[[mind ind] pars] args]; intros i h1. simpl in *.
  destruct (lookup mind p); trivial. destruct e; trivial.
  destruct h1 as [h1 [h1' h1'']].
  intuition. red in h1'' |- *. intuition.
  now rewrite <- (Instantiates_pres_tlength i).
  specialize (H0 i1). destruct (nth_error args i1); trivial.
  revert H0; case_eq (tnth i1 ts). intros t Ht Hnt.
  destruct (Instantiates_pres_is_n_lambda n1 i _ Ht) as [t' [Hnt' Hnlam]].
  rewrite Hnt'. intuition. now intros _ Hf.
Qed.

(*****
Lemma Instantiate_pres_Crct:
  forall tin, 
  (forall n bod ins, Instantiate tin n bod ins ->
  forall m p, n <= m -> Crct p (S m) bod -> Crct p m tin -> Crct p m ins) /\
  (forall n bods inss, Instantiates tin n bods inss ->
  forall m p, n <= m -> Crcts p (S m) bods -> Crct p m tin -> Crcts p m inss) /\
  (forall n ds ids, InstantiateDefs tin n ds ids ->
  forall m p, n <= m -> CrctDs p (S m) ds -> Crct p m tin -> CrctDs p m ids).
Proof.
  intros tin. apply InstInstsDefs_ind; intros; trivial.
  - apply CrctRel.
    + omega.
    + eapply Crct_Sort. eassumption.
  - destruct (Crct_invrt_Rel H0 eq_refl). apply CrctRel.
    + omega.
    + eapply Crct_Sort. eassumption.
  - eapply Crct_Sort; eassumption.
  - apply CrctProd. eapply Crct_Sort; eassumption.
    assert (j:= Crct_invrt_Prod H1 eq_refl).
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
  -  apply CrctLam. eapply Crct_Sort; eassumption.
     assert (j:= Crct_invrt_Lam H1 eq_refl).
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
  - destruct (Crct_invrt_LetIn H2 eq_refl). apply CrctLetIn.
    + apply H; trivial.
    + apply H0; intuition. apply (proj1 Crct_up). assumption.
  - destruct (Crct_invrt_App H2 eq_refl) as [j1 [j2 j3]]. apply CrctApp.
    + assumption.
    + inversion H2.
    + apply H; trivial.
    + apply H0; trivial.
  - edestruct (Crct_invrt_Const H0).
    + reflexivity.
    + destruct H3 as [x [h1 h2]]. eapply (@CrctConst _ _ x); trivial.
      * eapply Crct_Sort. eassumption.
  - apply CrctInd. eapply Crct_Sort. eassumption.
  - destruct ind. edestruct (Crct_invrt_Construct H1).
    + reflexivity.
    + destruct H4 as [npars [x [h1 [h2 h3]]]].
      eapply CrctConstruct; try eassumption.
      * eapply Crct_Sort. eassumption.
      * rewrite <- (Instantiates_pres_tlength i). apply h3; trivial.
      * apply H; auto.
  - destruct (Crct_invrt_Case H2 eq_refl) as [h1 [h2 h3]]. apply CrctCase.
    + eapply Instantiates_pres_CrctAnnot; eauto.
    + apply H; trivial.
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
  - inversion_Clear H2. apply CrctDsCons.
    + apply H; trivial.
    + apply H0; trivial.
Qed.
 ****)

(***
Lemma Crct_App_inv:
  forall p n fn a1 args, Crct p n (TApp fn a1 args) ->
                         Crct p n fn /\ Crct p n a1 /\ Crcts p n args.
intros p n fn a1 args h. split; try split. inversion_Clear h.
- inversion H; subst.
induction 1. try (intros; discriminate); intros h; subst; split; try split;
try (inversion_Clear h; assumption).
- eapply CrctWkTrmTrm; try eassumption. intuition.
- eapply CrctWkTrmTrm; try eassumption. intuition.
- assert (j:Crct p n fn /\ Crct p n a1 /\ Crcts p n args).
  apply IHCrct1; reflexivity.
  destruct j. destruct H3.
  eapply (CrctsWk H4); assumption. 
Qed.

Lemma Crct_App_inv:
  forall p n fn a1 args t, Crct p n t -> t = (TApp fn a1 args) ->
                         Crct p n fn /\ Crct p n a1 /\ Crcts p n args.
intros p n fn a1 args t h j. 
induction h; try (intros; discriminate). intros h. subst; split; try split;
try (inversion_Clear h; assumption).
- eapply CrctWkTrmTrm; try eassumption. intuition.
- eapply CrctWkTrmTrm; try eassumption. intuition.
- assert (j:Crct p n fn /\ Crct p n a1 /\ Crcts p n args).
  apply IHCrct1; reflexivity.
  destruct j. destruct H3.
  eapply (CrctsWk H4); assumption. 
Qed.
***)

(*********
(** An alternative correctness specification for programs: [crct], below **)
Definition weaklyClosed (t:Term) (p:environ Term) : Prop :=
  forall nm, PoccTrm nm t -> lookupDfn nm p <> None.
Fixpoint weaklyCloseds (ts:Terms) p : Prop :=
  match ts with
    | tnil => True
    | tcons s ss => weaklyClosed s p /\ weaklyCloseds ss p
  end.
Fixpoint weaklyClosedd (ds:Defs) p : Prop :=
  match ds with
    | dnil => True
    | dcons nm tb m es => weaklyClosed tb p /\ weaklyClosedd es p
  end.

Lemma weaklyClosed_TCase:
  forall n mch brs p, weaklyClosed (TCase n mch brs) p ->
            weaklyClosed mch p /\ weaklyCloseds brs p.
unfold weaklyClosed. intros n mch brs p h1. split.
- intros xnm h2. apply (h1 xnm). apply PoCaseL. assumption.
- induction brs; unfold weaklyCloseds. auto. split.
  + unfold weaklyClosed. intros xnm h2. apply (h1 xnm).
    apply PoCaseR. apply PoThd. assumption.
  + apply IHbrs. intros xnm h2. apply (h1 xnm). inversion_clear h2.
    apply PoCaseL. assumption.
    apply PoCaseR. apply PoTtl. assumption.
Qed.

Lemma Pocc_weakClsd_no_lookup:
  forall nm t, PoccTrm nm t ->
               forall p, weaklyClosed t p -> lookupDfn nm p <> None.
induction 1; intros p h1; unfold weaklyClosed in h1; apply h1;
try (solve [constructor; assumption]).
- apply PoLetInBod. assumption.
- apply PoAppA. assumption.
- apply PoAppR. assumption.
- apply PoCaseR. assumption.
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

Inductive envOk : environ Term -> Prop :=
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

(*********************** ??????
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
- inversion_clear H1. apply H0. assumption.
- inversion_clear H1. apply H0. assumption.
- inversion_clear H3.
  + apply H0. assumption.
  + apply H2. assumption.
- inversion_clear H5. 
  + apply H0. assumption.
  + apply H2. assumption.
  + induction args. inversion_clear H6.
    * inversion_clear H6. destruct H4. unfold weaklyClosed in H4.
      apply (H4 nm H5). destruct H4. inversion_clear H3.
      apply IHargs; assumption.
- inversion H2. rewrite (string_eq_bool_eq _ _ H4). assumption.
- inversion H1.
- inversion_clear H3. 
  + apply (H0 nm). assumption.
  + induction brs; destruct H2; inversion_clear H4.
    * unfold weaklyClosed in H2. apply (H2 nm). assumption.
    * inversion_clear H1. eapply IHbrs; assumption.
- inversion_clear H1.
  induction ds; inversion_clear H2; inversion_clear H; destruct H0.
  + unfold weaklyClosed in H. eapply H. assumption.
  + apply IHds. simpl in H3. try assumption.
Qed.

Lemma Crct_envOk:
  (forall p n t, Crct p n t -> envOk p) /\
  (forall p n ts, Crcts p n ts -> envOk p) /\
  (forall p n ds, CrctDs p n ds -> envOk p).
apply CrctCrctsCrctDs_ind; intros; auto.
- constructor; auto. destruct (Crct_weaklyClosed). apply (H4 _ _ _ H1).
Qed.


Definition crct (p:environ Term) (t:Term) : Prop := envOk p /\ weaklyClosed t p.
Fixpoint crcts (p:environ Term) (ts:Terms) : Prop :=
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
***************)
***********************)

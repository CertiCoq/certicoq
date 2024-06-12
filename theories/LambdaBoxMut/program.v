
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.
Require Import Arith.
Require Import FunInd.
Require Import Common.Common.
Require Import LambdaBoxMut.term.
Require Import LambdaBoxMut.compile.
Require Import MetaCoq.Utils.bytestring.

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


(********
(** Check that a Term is Canonical (constructor in head)
*** and return the constructor number and its argument list:
*** used for a Case step, as the match argument must be canonical
*** before Case can be evaluated
**)
Inductive Canonical : Term -> nat -> Terms -> Prop :=
| canC: forall (i:inductive) (n:nat),
          Canonical (TConstruct i n) n tnil
| canA: forall (i:inductive) (n:nat) (t:Term) (ts:Terms),
          Canonical (TApp (TConstruct i n) t ts) n (tcons t ts).
#[global] Hint Constructors Canonical : core.


Lemma Canonical_dec:
  forall t n ts, Canonical t n ts \/ ~ Canonical t n ts.
induction t; intros; try (solve [right; intros h; inversion_Clear h]).
- destruct (isConstruct_dec t1). destruct H. elim H. intros.
  subst. destruct (eq_nat_dec x0 n). subst.

Definition canonical (t:Term) : option (nat * Terms) :=
  match t with
    | TConstruct _ n => Some (n, tnil)
    | TApp (TConstruct _ n) t ts => Some (n, (tcons t ts))
    | _ => None
  end.

Lemma Canonical_canonical:
  forall m t, WFTrm t m -> 
              forall n ts, Canonical t n ts <-> canonical t = Some (n, ts).
induction 1; intros xn xts; split; intros h;
try discriminate; try (inversion h); try reflexivity.
- destruct fn; try discriminate. injection H4. intros. subst. apply canA.
- apply canC.
Qed.
 ***)

(** pick inductive type out of a mutual package **)
Inductive crctInd: (environ Term) -> inductive -> ityp -> Prop :=
| ci: forall p ind itp pack,
    LookupTyp (inductive_mind ind) p 0 pack ->
    getInd pack (inductive_ind ind) = Ret itp ->
    crctInd p ind itp.
#[export] Hint Constructors crctInd : core.

(** pick a constructor of an inductive type **)
Inductive crctCnstr: (environ Term) -> inductive -> nat -> Terms -> Prop :=
| cc: forall p ind cnum args itp cstr,
    crctInd p ind itp ->
    getCnstr itp cnum = Ret cstr ->
    CnstrArity cstr = tlength args ->
    crctCnstr p ind cnum args.
#[export] Hint Constructors crctCnstr : core.

Inductive crctTerm: environ Term -> nat -> Term -> Prop :=
| ctRel: forall p n m, crctEnv p -> m < n -> crctTerm p n (TRel m)
| ctProof: forall p n, crctEnv p -> crctTerm p n TProof
| ctPrim : forall p n v, crctEnv p -> crctTerm p n (TPrim v)
| ctLam: forall p n nm bod,
    crctTerm p (S n) bod -> crctTerm p n (TLambda nm bod)
| ctLetIn: forall p n nm dfn bod,
    crctTerm p n dfn -> crctTerm p (S n) bod ->
    crctTerm p n (TLetIn nm dfn bod)
| ctApp: forall p n fn arg,
    crctTerm p n fn -> crctTerm p n arg -> crctTerm p n (TApp fn arg)
| ctConst: forall p n pd nm,
    crctEnv p -> LookupDfn nm p pd -> crctTerm p n (TConst nm)
| ctConstructor: forall p n ind cnum args,
    crctCnstr p ind cnum args ->
    crctTerms p n args ->
    crctTerm p n (TConstruct ind cnum args)
| ctCase: forall p n ind ityp mch brs,
    crctInd p ind ityp ->
    crctTerm p n mch -> crctBs p n brs ->
    crctTerm p n (TCase ind mch brs)
| ctFix: forall p n ds m,
    crctDs p (n + dlength ds) ds -> m < dlength ds ->
    crctTerm p n (TFix ds m)
(* crctEnvs are closed in both ways *)
with crctEnv: environ Term -> Prop :=
     | ceNil: crctEnv nil
     | ceTrmCons: forall nm s p,
         crctEnv p -> fresh nm p -> crctTerm p 0 s -> crctEnv ((nm, ecTrm s)::p)
     | ceTypCons: forall nm s p,
         crctEnv p -> fresh nm p -> crctEnv ((nm, ecTyp Term 0 s)::p)
with crctTerms: environ Term -> nat -> Terms -> Prop :=
     | ctsNil: forall p n, crctEnv p -> crctTerms p n tnil
     | ctsCons: forall p n t ts,
         crctTerm p n t -> crctTerms p n ts ->
         crctTerms p n (tcons t ts)
with crctBs: environ Term -> nat -> Brs -> Prop :=
     | cbsNil: forall p n, crctEnv p -> crctBs p n bnil
     | cbsCons: forall p n m t ts,
         crctTerm p (List.length m + n) t -> crctBs p n ts ->  crctBs p n (bcons m t ts)
with crctDs: environ Term -> nat -> Defs -> Prop :=
     | cdsNil: forall p n, crctEnv p -> crctDs p n dnil
     | cdsCons: forall p n nm bod ix ds,
         isLambda bod -> crctTerm p n bod -> crctDs p n ds ->
         crctDs p n (dcons nm bod ix ds).
#[export] Hint Constructors crctTerm crctTerms crctBs crctDs crctEnv : core.
Scheme crct_ind' := Minimality for crctTerm Sort Prop
  with crcts_ind' := Minimality for crctTerms Sort Prop
  with crctBs_ind' := Minimality for crctBs Sort Prop
  with crctDs_ind' := Minimality for crctDs Sort Prop
  with crctEnv_ind' := Minimality for crctEnv Sort Prop.
Combined Scheme crctCrctsCrctBsDsEnv_ind from
         crct_ind', crcts_ind', crctBs_ind', crctDs_ind', crctEnv_ind'.

Lemma Crct_WFTrm:
  (forall p n t, crctTerm p n t -> WFTrm t n) /\
  (forall p n ts, crctTerms p n ts -> WFTrms ts n) /\
  (forall p n bs, crctBs p n bs -> WFTrmBs bs n) /\
  (forall p n (ds:Defs), crctDs p n ds -> WFTrmDs ds n) /\
  (forall p, crctEnv p -> True).
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

Lemma Crct_WFApp:
  forall p n t, crctTerm p n t -> WFapp t.
  intros p n t h. eapply WFTrm_WFapp. eapply (proj1 Crct_WFTrm). eassumption.
Qed.

Lemma Crct_up:
  (forall p n t, crctTerm p n t -> crctTerm p (S n) t) /\
  (forall p n ts, crctTerms p n ts -> crctTerms p (S n) ts) /\
  (forall p n bs, crctBs p n bs -> crctBs p (S n) bs) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctDs p (S n) ds) /\
  (forall p, crctEnv p -> True). 
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; try (solve [constructor; assumption]).
  - apply ctRel; try assumption. lia.
  - eapply ctConst; eassumption.
  - eapply ctCase; eassumption.
  - eapply cbsCons; eauto. now rewrite Nat.add_succ_r.
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
#[global] Hint Resolve Crct_Up Crct_UP : core.
  
Lemma CrctDs_Up:
  forall n p ds, crctDs p n ds -> forall m, n <= m -> crctDs p m ds.
Proof.
  intros n p ds h. induction 1. assumption.
  apply (proj1 (proj2 (proj2 (proj2 Crct_up)))). assumption.
Qed.

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
  apply crctCrctsCrctBsDsEnv_ind; intros; try intros j; auto;
    inversion_Clear j.
  - eelim H0; eassumption.
  - eelim H0; eassumption.
  - eelim H2; eassumption.
  - eelim H0; eassumption.
  - eelim H2; eassumption.
  - unfold LookupDfn in H1. elim (Lookup_fresh_neq H1 H2). reflexivity.
  - inversion_Clear H. inversion_Clear H3. cbn in H. cbn in H6.
    unfold LookupTyp in H. destruct H.
    elim (Lookup_fresh_neq H H2). reflexivity.
  - inversion_Clear H. inversion_Clear H3. 
    unfold LookupTyp in H. destruct H. eelim H1; eassumption.
  - eelim H1; eassumption.
  - eelim H3; eassumption.
  - inversion_Clear H. inversion_Clear H5. unfold LookupTyp in H.
    cbn in H. elim (Lookup_fresh_neq H H4). reflexivity.
  - eelim H0; eassumption.
  - eelim H0; eassumption.
  - eelim H2; eassumption.
  - eelim H0; eassumption.
  - eelim H2; eassumption.
  - eelim H1; eassumption.
  - eelim H3; eassumption.
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
  (forall p, crctEnv p ->
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctEnv ((nm,ecTrm s)::p)).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition auto]);
  try (econstructor; intuition auto); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - inversion_Clear H. inversion_Clear H4.
    unfold LookupTyp in H. destruct H.
    econstructor; try eassumption.
    econstructor; try eassumption. unfold LookupTyp. intuition.
    destruct (Classes.eq_dec (inductive_mind ind) nm).
    + subst. eelim Lookup_fresh_neq; try eassumption. reflexivity.
    + apply LMiss; assumption.
  - inversion_Clear H. inversion_Clear H6.
    unfold LookupTyp in H.
    econstructor; try eassumption. econstructor; try eassumption.
    unfold LookupTyp. 
    case_eq (Classes.eq_dec (inductive_mind ind) nm); intros.
    + rewrite e in H. elim (Lookup_fresh_neq H H4). reflexivity.
    + apply LMiss; assumption.
Qed.

Lemma Crct_lift:
  (forall p n t, crctTerm p n t -> forall k, crctTerm p (S n) (lift k t)) /\
  (forall p n ts, crctTerms p n ts -> forall k, crctTerms p (S n) (lifts k ts)) /\
  (forall p n ts, crctBs p n ts -> forall k, crctBs p (S n) (liftBs k ts)) /\
  (forall p n ts, crctDs p n ts -> forall k, crctDs p (S n) (liftDs k ts)) /\
  (forall p, crctEnv p -> crctEnv p).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
  try (solve[cbn; repeat econstructor; intuition eauto]).
  (* 2-9:try (econstructor; intuition auto); try eassumption. *)
  - cbn. constructor; eauto. destruct (Nat.compare_spec m k); subst; try lia.
  - cbn. econstructor; eauto. inversion_Clear H. econstructor; eauto.
    now rewrite lifts_pres_tlength.
  - econstructor; eauto.
  - cbn. constructor; eauto. rewrite liftDs_pres_dlength. eauto.
    rewrite liftDs_pres_dlength; lia.
  - cbn. constructor; eauto. now rewrite Nat.add_succ_r.
  - cbn. constructor; eauto. destruct H as [na [body ->]]. now do 2 eexists.
Qed.

Lemma Crct_weaken_Typ:
  (forall p n t, crctTerm p n t -> 
                 forall nm s, fresh nm p ->
                              crctTerm ((nm,ecTyp Term 0 s)::p) n t) /\
  (forall p n ts, crctTerms p n ts -> 
                  forall nm s, fresh nm p ->
                               crctTerms ((nm,ecTyp Term 0 s)::p) n ts) /\
  (forall p n ts, crctBs p n ts -> 
                  forall nm s, fresh nm p ->
                               crctBs ((nm,ecTyp Term 0 s)::p) n ts) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s, fresh nm p ->
                               crctDs ((nm,ecTyp Term 0 s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition auto]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - inversion_Clear H. inversion_Clear H3.
    econstructor; try eassumption. econstructor; try eassumption.
    + unfold LookupTyp in *. destruct H. split; try eassumption.
      destruct (Classes.eq_dec (inductive_mind ind) nm).
      * subst. eelim Lookup_fresh_neq; try eassumption. reflexivity.
      * apply LMiss; assumption.
  - inversion_Clear H. inversion_Clear H5.
    unfold LookupTyp in H. econstructor; try eassumption.
    econstructor; try eassumption.
    unfold LookupTyp.
    destruct (Classes.eq_dec (inductive_mind ind) nm).
    + subst. eelim Lookup_fresh_neq; try eassumption. reflexivity.
    + apply LMiss; assumption.
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
  (forall pp, crctEnv pp -> crctEnv (List.tl pp)).
Proof.
  apply crctCrctsCrctBsDsEnv_ind; intros; subst;
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
  - econstructor; try eassumption.
    + inversion_Clear H. inversion_Clear H2.
      unfold LookupTyp in H. destruct H. econstructor; try eassumption.
      econstructor; try eassumption. unfold LookupTyp. split; intuition.
      destruct (Classes.eq_dec (inductive_mind ind) nm).
      * subst. elim H3. destruct ind. cbn. apply PoCnstri.
      * inversion_Clear H.
        -- elim n0. reflexivity.
        -- assumption.
    + eapply H1. reflexivity. intros j. elim H3.
      apply PoCnstrargs. assumption.
  - inversion_Clear H. inversion_Clear H4. unfold LookupTyp in H.
    case_eq (Classes.eq_dec (inductive_mind ind) nm); intros.
    + subst. inversion_Clear H.
      * elim H5. destruct ind. cbn. apply PoCaseAnn.
      * elim H13. reflexivity.
    + pose proof (Lookup_strengthen H eq_refl n0) as j.
      eapply ctCase.
      * econstructor; try eassumption.
        econstructor; try eassumption.
      * eapply H1. reflexivity.
        intros j0. elim H5. apply PoCaseL. assumption.
      * eapply H3. reflexivity.
        intros j0. elim H5. apply PoCaseR. assumption.
  - econstructor; try eassumption. eapply H0. reflexivity. intros h.
    elim H3. constructor. assumption.
  - constructor.
    + eapply H0. reflexivity. intros h. elim H4. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H4. apply PoTtl. assumption.
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

Lemma LookupDfn_pres_Crct:
  forall p, crctEnv p ->
            forall nm t, LookupDfn nm p t -> forall n, crctTerm p n t.
Proof.
  unfold LookupDfn. induction 1; intros.
  - inversion H.
  - inversion_Clear H2.
    + apply Crct_weaken; try assumption. eapply Crct_UP. eassumption. lia.
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
  pose proof (LookupDfn_pres_Crct H H0). exists pd. intuition.
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

Lemma Crct_invrt_Construct:
  forall p n ipkgNm inum cnum arty,
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum arty) ->
    exists npars itypk,
      LookupTyp ipkgNm p npars itypk /\
      exists (ip:ityp), getInd itypk inum = Ret ip /\
                        exists (ctr:Cnstr), getCnstr ip cnum = Ret ctr.
Proof.
  intros. inversion_Clear H. exists 0. inversion_Clear H4. inversion_Clear H.
  exists pack. intuition. exists itp. intuition. exists cstr. assumption.
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

Lemma Crcts_append:
  forall p n ts, crctTerms p n ts ->
  forall us, crctTerms p n us -> crctTerms p n (tappend ts us).
Proof.
  induction 1; intros us h; simpl.
  - assumption.
  - constructor; intuition.
Qed.

Lemma dnth_pres_Crct:
  forall m dts dfn, dnth m dts = Some dfn ->
                   forall p n, crctDs p n dts -> crctTerm p n (dbody dfn).
Proof.
  intros m dts dfn.
  functional induction (dnth m dts); intros; try discriminate.
  - myInjection H. inversion_Clear H0; try assumption.
  - inversion_Clear H0.
    + intuition.
Qed.

Lemma dnthBody_pres_Crct:
  forall m dts fs, dnthBody m dts = Some fs ->
                   forall p n, crctDs p n dts -> crctTerm p n fs.
Proof.
  intros m dts fs. unfold dnthBody.
  functional induction (dnth m dts); intros; try discriminate.
  - myInjection H. inversion_Clear H0; try assumption.
  - inversion_Clear H0. intuition.
Qed.

Lemma mkApp_pres_Crct:
  forall p n args,
    crctTerms p n args -> 
    forall fn, crctTerm p n fn -> forall x, mkApp fn args = Some x -> crctTerm p n x.
Proof.
  induction 1; intros.
  - destruct (isConstruct_dec fn).
    + dstrctn i. subst. cbn in H1. myInjection H1. assumption.
    + destruct fn; inversion_Clear H0; cbn in H1; try myInjection H1; auto.
      * eapply ctConst; eassumption.
      * eapply ctCase; eassumption.
  - assert (j:~ isConstruct fn).
    { intros h. dstrctn h. subst fn. cbn in H2. discriminate. }
    eapply (IHcrctTerms (TApp fn t)).
    + constructor; assumption.
    + rewrite mkApp_tcons in H2; assumption.
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
    + apply H0; assumption.
  - inversion_Clear H1. inversion_Clear H7. inversion_Clear H1.
    econstructor; try eassumption.
    + econstructor; try eassumption.
      * econstructor; try eassumption.
      *rewrite <- (Instantiates_pres_tlength i). assumption.
    + apply H; try eassumption.
  - inversion_Clear H2. inversion_Clear H9. inversion_Clear H2.
    econstructor.
    + econstructor; try eassumption. econstructor; try eassumption.
    + apply H; try assumption.
    + apply H0; try assumption.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. econstructor; try lia.
    + eapply H; try lia.
      * rewrite <- k; assumption.
      * eapply Crct_UP. eassumption. lia.
  - inversion_Clear H2. apply ctsCons; intuition.
  - inversion_Clear H2. constructor; intuition. eapply H. lia.
    now rewrite Nat.add_succ_r in H8. eapply Crct_UP; try eassumption. lia.
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

Lemma instantiatel_pres_Crct:
  forall p m bod tin, crctTerm p (tlength tin + m) bod -> crctTerms p m tin -> 
                  forall n, n <= m ->  crctTerm p m (instantiatel tin n bod).
Proof.
  intros.
  induction tin in bod, H, H0 |- *; cbn. eapply H.
  eapply IHtin. cbn in H.
  eapply instantiate_pres_Crct; auto. inv H0. eapply Crct_UP; try eassumption. lia. lia.
  now inv H0.
Qed.

Lemma whBetaStep_pres_Crct:
  forall p n bod,
    crctTerm p (S n) bod ->
    forall a1, crctTerm p n a1 -> crctTerm p n (whBetaStep bod a1).
Proof.
  intros. unfold whBetaStep. apply instantiate_pres_Crct; try assumption.
  lia.
Qed.

Lemma bnth_pres_Crct:
  forall p n (brs:Brs), crctBs p n brs ->
    forall m x ix, bnth m brs = Some (ix, x) -> crctTerm p (List.length ix + n) x.
Proof.
  intros p n brs h m ix x.
  functional induction (bnth m brs); intros; auto.
  - discriminate.
  - myInjection H. inversion h. subst. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma whCaseStep_pres_Crct:
  forall p n ts, crctTerms p n ts -> forall brs, crctBs p n brs ->
  forall m s, whCaseStep m ts brs = Some s -> crctTerm p n s.
Proof.
  intros p n ts h1 brs h2 m s h3. pose proof (whCaseStep_Some _ _ _ h3).
  dstrctn H.
  cbn in j. subst. unfold whCaseStep in h3.
  rewrite z in h3. revert h3. elim Nat.eqb_spec; cbn; try discriminate.
  intros.
  eapply bnth_pres_Crct in z; try eassumption. 
  rewrite p0 in z.
  eapply instantiatel_pres_Crct; auto. lia.
Qed.
  
Lemma canonicalP_pres_crctTerms:
  forall p m t, crctTerm p m t ->
                forall n args, canonicalP t = Some (n, args) ->
                               crctTerms p m args.
Proof.
  induction 1; intros; try (cbn in H1; discriminate).
  - cbn in H0. myInjection H0. constructor. intuition.
  - cbn in H0. discriminate.
  - inversion_Clear H0.
  - now inversion_Clear H1.
Qed.

Lemma tnth_pres_Crct:
  forall p m ts, crctTerms p m ts ->
                 forall n x, tnth n ts = Some x -> crctTerm p m x.
Proof.
  induction 1; intros. discriminate. destruct n0.
  - cbn in H1. myInjection H1. assumption.
  - cbn in H1. eapply IHcrctTerms. eassumption.
Qed.

Lemma fold_left_pres_Crct:
  forall (f:Term -> nat -> Term) (ns:list nat) p (a:nat),
    (forall u m, m >= a -> crctTerm p (S m) u ->
               forall n, In n ns -> crctTerm p m (f u n)) ->
    forall t, crctTerm p (a + List.length ns) t ->
              crctTerm p a (fold_left f ns t).
Proof.
  intros f. induction ns; cbn; intros.
  - replace (a + 0) with a in H0. assumption. lia.
  - apply IHns.
    + intros. apply H; try assumption. apply (or_intror H3).
    + replace (a0 + S (Datatypes.length ns))
        with (S (a0 + (Datatypes.length ns))) in H0.
      assert (j: a0 + Datatypes.length ns >= a0). lia.
      specialize (H t _ j H0).
      apply H. apply (or_introl eq_refl). lia.
Qed.

Lemma whFixStep_pres_Crct:
  forall (dts:Defs) p n,
    crctDs p (n + dlength dts) dts ->
    forall m s, whFixStep dts m = Some s -> crctTerm p n s.
Proof.
  unfold whFixStep. intros. case_eq (dnth m dts); intros.
  - assert (j: m < dlength dts).
    { eapply dnth_lt. eassumption. }
    rewrite H1 in H0. destruct d. myInjection H0. apply fold_left_pres_Crct.
    + intros. apply instantiate_pres_Crct; try lia. assumption.
      * pose proof (In_list_to_zero _ _ H3) as j0.
        constructor; try assumption.
        pose proof (dnth_pres_Crct _ H1 H) as k2.
        eapply CrctDs_Up. eassumption. lia.
    + rewrite list_to_zero_length.
      eapply (dnth_pres_Crct _ H1 H).
  - rewrite H1 in H0. discriminate.
Qed.

(***********
Lemma pre_whFixStep_pres_Crct:
  forall (dts:Defs) p n a m x,
    crctDs p (n + dlength dts) dts -> crctTerm p n a ->
    dnth m dts = Some x ->
    crctTerm p n (pre_whFixStep (dbody x) dts a).
Proof.
  intros. unfold pre_whFixStep.
  assert (c:= TApp (whFixStep_pres_Crct n H m _ a)). destruct x.
  unfold whFixStep in c. rewrite H1 in c. apply c. apply f_equal.

  destruct x.
  specialize (c _ eq_refl).
  constructor. apply c. apply H0.
Qed.
 ************)

(*****
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
***************)

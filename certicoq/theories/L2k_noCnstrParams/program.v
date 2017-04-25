
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import L2k.term.
Require Import L2k.compile.

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
Hint Constructors Canonical.


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

Inductive crctTerm: environ Term -> nat -> Term -> Prop :=
| ctRel: forall p n m, crctEnv p -> m < n -> crctTerm p n (TRel m)
| ctCast: forall p n t, crctEnv p -> crctTerm p n t ->
                        crctTerm p n (TCast t)
| ctProof: forall p n t, crctEnv p -> crctTerm p n t ->
                         crctTerm p n (TProof t)
| ctLam: forall p n nm bod,
           crctEnv p -> crctTerm p (S n) bod -> crctTerm p n (TLambda nm bod)
| ctLetIn: forall p n nm dfn bod,
             crctEnv p -> crctTerm p n dfn -> crctTerm p (S n) bod ->
             crctTerm p n (TLetIn nm dfn bod)
| ctApp: forall p n fn arg args,
           crctEnv p -> crctTerm p n fn -> ~ isApp fn -> crctTerm p n arg ->
           crctTerms p n args -> crctTerm p n (TApp fn arg args)
| ctConst: forall p n pd nm,
             crctEnv p -> LookupDfn nm p pd -> crctTerm p n (TConst nm)
| ctAx: forall p n, crctEnv p -> crctTerm p n TAx
| ctConstructor: forall p n ipkgNm inum cnum args ipkg itp cstr pars,
                   crctEnv p -> LookupTyp ipkgNm p pars ipkg ->
                   getInd ipkg inum = Ret itp ->
                   getCnstr itp cnum = Ret cstr ->
                   crctTerms p n args ->
                   crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum args)
| ctCase: forall p n m mch brs,
            crctEnv p -> crctTerm p n mch -> crctDs p n brs ->
            crctTerm p n (TCase m mch brs)
| ctFix: forall p n ds m,
           crctEnv p -> crctDs p (n + dlength ds) ds -> m < dlength ds ->
           crctTerm p n (TFix ds m)
(* crctEnvs are closed in both ways *)
with crctEnv: environ Term -> Prop :=
| ceNil: crctEnv nil
| ceTrmCons: forall nm s p,
               crctEnv p -> fresh nm p -> crctTerm p 0 s ->
               crctEnv ((nm,ecTrm s)::p)
| ceTypCons: forall nm m s p,
               crctEnv p -> fresh nm p ->
               crctEnv ((nm,AstCommon.ecTyp Term m s)::p)
with crctTerms: environ Term -> nat -> Terms -> Prop :=
| ctsNil: forall p n, crctEnv p -> crctTerms p n tnil
| ctsCons: forall p n t ts,
             crctEnv p -> crctTerm p n t -> crctTerms p n ts ->
             crctTerms p n (tcons t ts)
with crctDs: environ Term -> nat -> Defs -> Prop :=
| cdsNil: forall p n, crctEnv p -> crctDs p n dnil
| cdsCons: forall p n nm bod ix ds,
             crctEnv p -> crctTerm p n bod -> crctDs p n ds ->
             crctDs p n (dcons nm bod ix ds).
Hint Constructors crctTerm crctTerms crctDs crctEnv.
Scheme crct_ind' := Minimality for crctTerm Sort Prop
  with crcts_ind' := Minimality for crctTerms Sort Prop
  with crctDs_ind' := Minimality for crctDs Sort Prop
  with crctEnv_ind' := Minimality for crctEnv Sort Prop.
Combined Scheme crctCrctsCrctDsEnv_ind from
         crct_ind', crcts_ind', crctDs_ind', crctEnv_ind'.

Lemma Crct_WFTrm:
  (forall p n t, crctTerm p n t -> WFTrm t n) /\
  (forall p n ts, crctTerms p n ts -> WFTrms ts n) /\
  (forall p n (ds:Defs), crctDs p n ds -> WFTrmDs ds n) /\
  (forall p, crctEnv p -> True).
apply crctCrctsCrctDsEnv_ind; intros; auto.
Qed.

Lemma Crct_WFApp:
  forall p n t, crctTerm p n t -> WFapp t.
  intros p n t h. eapply WFTrm_WFapp. eapply (proj1 Crct_WFTrm). eassumption.
Qed.

Lemma Crct_up:
  (forall p n t, crctTerm p n t -> crctTerm p (S n) t) /\
  (forall p n ts, crctTerms p n ts -> crctTerms p (S n) ts) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctDs p (S n) ds) /\
  (forall p, crctEnv p -> True). 
Proof.
  apply crctCrctsCrctDsEnv_ind; intros; try (solve [constructor; assumption]).
  - apply ctRel; try assumption. omega.
  - eapply ctConst; eassumption.
  - eapply ctConstructor; eassumption.
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

Lemma Crcts_tnil:
  forall p n t, crctTerm p n t -> crctTerms p 0 tnil.
Proof.
  induction 1; apply ctsNil; try assumption;
  try (solve [eapply Crct_Sort; eassumption]).
Qed.

Lemma Crct_fresh_Pocc:
  (forall p n t, crctTerm p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n ts, crctTerms p n ts ->
                  forall nm, fresh nm p -> ~ PoccTrms nm ts) /\
  (forall p n (ds:Defs), crctDs p n ds ->
                         forall nm, fresh nm p -> ~ PoccDefs nm ds) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctsCrctDsEnv_ind; intros; try intros j; auto;
  inversion_Clear j;
  try (specialize (H2 _ H3); contradiction);
  try (specialize (H2 _ H5); contradiction);
  try (specialize (H4 _ H5); contradiction);
  try (specialize (H2 _ H8); contradiction);
  try (specialize (H2 _ H4); contradiction);
  try (specialize (H5 _ H8); contradiction);
  try (specialize (H7 _ H8); contradiction).
  - unfold LookupDfn in H1. elim (Lookup_fresh_neq H1 H2). reflexivity.
  - unfold LookupTyp in H1. destruct H1.
    elim (Lookup_fresh_neq H1 H6). reflexivity.
  - specialize (H5 _ H6). intuition.
Qed.    

Lemma Crct_weaken:
  (forall p n t, crctTerm p n t -> 
                 forall nm s, fresh nm p -> crctTerm p 0 s ->
                              crctTerm ((nm,ecTrm s)::p) n t) /\
  (forall p n ts, crctTerms p n ts -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctTerms ((nm,ecTrm s)::p) n ts) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctDs ((nm,ecTrm s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - destruct H1. unfold LookupTyp. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. apply (Lookup_fresh_neq l). assumption.
Qed.

Lemma Crct_weaken_Typ:
  (forall p n t, crctTerm p n t -> 
                 forall nm s m, fresh nm p ->
                              crctTerm ((nm,ecTyp Term m s)::p) n t) /\
  (forall p n ts, crctTerms p n ts -> 
                  forall nm s m, fresh nm p ->
                               crctTerms ((nm,ecTyp Term m s)::p) n ts) /\
  (forall p n ds, crctDs p n ds -> 
                  forall nm s m, fresh nm p ->
                               crctDs ((nm,ecTyp Term m s)::p) n ds) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctsCrctDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - destruct H1. unfold LookupTyp. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. apply (Lookup_fresh_neq l). assumption.
Qed.


Lemma Crct_strengthen:
  (forall pp n s, crctTerm pp n s -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrm nm s -> crctTerm p n s) /\
  (forall pp n ss, crctTerms pp n ss -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccTrms nm ss -> crctTerms p n ss) /\
  (forall pp n ds, crctDs pp n ds -> forall nm ec p, pp = (nm,ec)::p ->
                 ~ PoccDefs nm ds -> crctDs p n ds) /\
  (forall (pp:environ Term), crctEnv pp -> True).
Proof.
  apply crctCrctsCrctDsEnv_ind; intros; try (subst p);
  try (econstructor; eassumption);
  try (inversion_Clear H; constructor; try assumption;
       eapply H2; try reflexivity; try eassumption;
       intros h; elim H4; constructor; assumption).
  - inversion_Clear H; constructor; try assumption;
    try (eapply H2; try reflexivity; intros h; elim H6;
         constructor; assumption);
    try (eapply H4; try reflexivity; intros h; elim H6;
         constructor; assumption).
  - inversion_Clear H; constructor; try assumption;
    try (eapply H2; try reflexivity; intros h; elim H9;
         constructor; assumption);
    try (eapply H5; try reflexivity; intros h; elim H9;
         constructor; assumption);
    try (eapply H7; try reflexivity; intros h; elim H9;
         constructor; assumption).
  - unfold LookupDfn in *.
    destruct (string_dec nm nm0).
    + subst. elim H3. constructor.
    + inversion_Clear H; econstructor; try assumption; unfold LookupDfn;
      eapply Lookup_strengthen; try reflexivity; try eassumption.
  - unfold LookupTyp in *. destruct (string_dec ipkgNm nm).
    + subst. elim H7. constructor.
    + destruct H1. pose proof (Lookup_strengthen H1 eq_refl n0) as j.
      econstructor; try eassumption.
      * inversion_Clear H; assumption.
      * unfold LookupTyp. intuition. eassumption.
      * eapply H5. reflexivity. intros h. elim H7.
        apply PoCnstrargs. assumption.
  - inversion_Clear H; econstructor; try assumption;
    try (eapply H2; try reflexivity; intros h; elim H6;
         constructor; assumption);
    try (eapply H4; try reflexivity; intros h; elim H6;
         constructor; assumption).
  - inversion_Clear H; econstructor; try assumption;
    eapply H2; try reflexivity; intros h; elim H5;
         constructor; assumption.
  - inversion_Clear H; econstructor; try assumption;
    try (eapply H2; try reflexivity; intros h; elim H6;
         constructor; assumption);
    try (eapply H4; try reflexivity; intros h; elim H6;
         constructor; assumption).
  - inversion_Clear H; econstructor; try assumption;
    try (eapply H2; try reflexivity; intros h; elim H6;
         constructor; assumption);
    try (eapply H4; try reflexivity; intros h; elim H6;
         constructor; assumption).
Qed.

Lemma TWrong_not_Crct:
  forall p n, ~ crctTerm p n TWrong.
Proof.
  induction p; intros; intros h.
  - inversion h.
  - eelim IHp. destruct a. eapply (proj1 Crct_strengthen _ _ _ h).
    + reflexivity.
    + intros j. inversion j.
Qed.
                                         
(** Crct inversions **)
Lemma LookupDfn_pres_Crct:
  forall p n t, crctTerm p n t ->
                forall nm u, LookupDfn nm p u -> crctTerm p 0 u.
Proof.
  assert (lem:
            (forall p n t, crctTerm p n t -> 
                  forall nm u, LookupDfn nm p u -> crctTerm p 0 u) /\
            (forall p n ts, crctTerms p n ts -> True) /\
            (forall (p:environ Term) (n:nat) (ds:Defs),
               crctDs p n ds -> True) /\
            (forall (p:environ Term), crctEnv p ->
                         forall nm u, LookupDfn nm p u -> crctTerm p 0 u)).
  { apply crctCrctsCrctDsEnv_ind; intros; auto; unfold LookupDfn in *;
    try (eapply H0; eassumption); try (eapply H2; eassumption).
    - inversion H.
    - destruct (string_dec nm0 nm).
      + subst nm0. inversion_Clear H4.
        eapply Crct_weaken; try assumption. elim H10; reflexivity.
      + eapply Crct_weaken; try assumption. eapply H0.
        inversion_Clear H4.
        * elim n. reflexivity.
        * eassumption.
    - destruct (string_dec nm0 nm).
      + subst nm0. inversion_Clear H2. elim H8. reflexivity.
      + pose proof (Lookup_strengthen H2 eq_refl n) as j.
        specialize (H0 _ _ j). eapply Crct_weaken_Typ; try assumption.
  }
  apply (proj1 lem).
Qed.


Lemma Crct_invrt_Rel:
  forall p n m, crctTerm p n (TRel m) -> m < n.
Proof.
  intros. inversion_Clear H. assumption.
Qed.

Lemma Crct_invrt_WkTrm:
  forall (ev:environ Term) n t, crctTerm ev n t ->
  forall nm s p, ev = (nm, ecTrm s)::p -> crctTerm p 0 s.
Proof.
  induction 1; intros;
  subst p; inversion_Clear H; assumption.
Qed.

Lemma Crct_LookupDfn_Crct:
  forall p, crctEnv p -> forall nm t, LookupDfn nm p t -> crctTerm p 0 t.
Proof.
  unfold LookupDfn. induction 1; intros.
  - inversion H.
  - apply Crct_weaken; inversion_Clear H2; try assumption.
    eapply IHcrctEnv. eassumption.
  - eapply (Crct_weaken_Typ); try assumption. eapply IHcrctEnv.
    destruct (string_dec nm0 nm).
    + subst nm. inversion_Clear H1. elim H7. reflexivity.
    + eapply (Lookup_strengthen H1). reflexivity. assumption.
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
  forall p n fn arg args,
    crctTerm p n (TApp fn arg args) ->
    crctTerm p n fn /\ crctTerm p n arg /\ crctTerms p n args /\ ~(isApp fn).
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Case:
  forall p n m s us,
    crctTerm p n (TCase m s us) -> crctTerm p n s /\ crctDs p n us.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Cast:
  forall p n t, crctTerm p n (TCast t) -> crctTerm p n t.
Proof.
   intros. inversion_Clear H. intuition.
Qed.

Lemma Crct_invrt_Proof:
  forall p n t, crctTerm p n (TProof t) -> crctTerm p n t.
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
  intros. inversion_Clear H. exists pars, ipkg. intuition.
  exists itp. intuition. exists cstr. intuition.
Qed.

Lemma Crct_invrt_any:
  forall p n t, crctTerm p n t -> crctEnv p.
Proof.
  intros. inversion_Clear H; assumption.
Qed.

Lemma CrctDs_invrt:
  forall n p dts, crctDs p n dts -> 
    forall m x ix, dnthBody m dts = Some (x, ix) -> crctTerm p n x.
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

Lemma mkApp_pres_Crct:
  forall fn p n, crctTerm p n fn ->
  forall args, crctTerms p n args -> crctTerm p n (mkApp fn args).
Proof.
  induction fn; unfold mkApp; simpl; intros p' nx h0 args h1;
  destruct args; try assumption;
  try (solve [inversion_Clear h1; apply ctApp; try assumption; not_isApp]).
  - destruct (Crct_invrt_App h0) as [j1 [j2 [j3 j4]]].
    rewrite tappend_tnil. assumption.
  - destruct (Crct_invrt_App h0) as [j1 [j2 [j3 j4]]].
    apply ctApp; try assumption. destruct t; simpl.
    + inversion h1; assumption.
    + inversion h1. assumption.
    + apply Crcts_append; assumption.
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
    (forall n ds ids,
       InstantiateDefs tin n ds ids ->
       forall m p, n <= m -> crctDs p (S m) ds -> crctTerm p m tin ->
                   crctDs p m ids).
Proof.
  intros tin.
  apply InstInstsDefs_ind; intros; trivial;
  try (inversion_Clear H0; econstructor; eassumption);
  try (inversion_Clear H1; constructor; try assumption; apply H; assumption).
  - inversion_Clear H0. constructor. assumption. omega.
  - apply ctRel.
    + inversion H0. assumption.
    + inversion H0. omega.
  - inversion_Clear H1; constructor; try assumption; apply H; try assumption.
    omega. apply Crct_up. assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; assumption.                 
    + apply H0; try assumption. omega. apply (proj1 Crct_up). assumption.
  - inversion_Clear H3. apply mkApp_pres_Crct.
    + apply H; assumption.
    + apply ctsCons; try assumption.
      * apply H0; trivial.
      * apply H1; trivial.
  - inversion_Clear H1. econstructor; try eassumption.
    + apply H; try eassumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; try eassumption.
    + apply H0; try eassumption.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. inversion_Clear H8.
    + inversion H9.
    + cbn in *. constructor; try assumption; rewrite k in *; try assumption.
      apply H; try omega.
      * constructor; try assumption.
      * eapply Crct_UP. eassumption. omega.
  - inversion_Clear H2. apply ctsCons; intuition.
  - inversion_Clear H2. constructor; intuition.
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
                  forall a1 args, crctTerm p n a1 -> crctTerms p n args ->
                                  crctTerm p n (whBetaStep bod a1 args).
Proof.
  intros. unfold whBetaStep. apply mkApp_pres_Crct; try assumption.
  apply instantiate_pres_Crct; try assumption.  omega.
Qed.

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


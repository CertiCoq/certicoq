
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L2d.compile.
Require Import L2d.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(***********
Check Term.
Check L2d.compile.Term.
Print L2d.compile.Term.
Goal L2.compile.Term = L2d.compile.Term. reflexivity.
 **************)

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
| ctProof: forall p n t, crctTerm p n t -> crctTerm p n (TProof t)
| ctLam: forall p n nm bod,
           crctTerm p (S n) bod -> crctTerm p n (TLambda nm bod)
| ctLetIn: forall p n nm dfn bod,
             crctTerm p n dfn -> crctTerm p (S n) bod ->
             crctTerm p n (TLetIn nm dfn bod)
| ctApp: forall p n fn arg,
           crctTerm p n fn -> crctTerm p n arg -> crctTerm p n (TApp fn arg)
| ctConst: forall p n pd nm,
    crctEnv p -> LookupDfn nm p pd -> crctTerm p n (TConst nm)
| ctDummy: forall n p str, crctEnv p -> crctTerm p n (TDummy str)
| ctConstructor: forall p n ipkgNm inum cnum ipkg itp cstr npars nargs,
    crctEnv p -> 
    LookupTyp ipkgNm p npars ipkg ->
    getInd ipkg inum = Ret itp ->
    getCnstr itp cnum = Ret cstr ->
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum npars nargs)
| ctCase: forall p n i mch brs,
            crctTerm p n mch -> crctBs p n brs ->
            crctTerm p n (TCase i mch brs)
| ctFix: forall p n ds m,
           crctDs p (n + dlength ds) ds -> m < dlength ds ->
           crctTerm p n (TFix ds m)
(* crctEnvs are closed in both ways *)
with crctEnv: environ Term -> Prop :=
| ceNil: crctEnv nil
| ceTrmCons: forall nm s p,
    crctEnv p -> fresh nm p -> crctTerm p 0 s -> crctEnv ((nm, ecTrm s)::p)
| ceTypCons: forall nm m s p,
    crctEnv p -> fresh nm p -> crctEnv ((nm, ecTyp Term m s)::p)
with crctTerms: environ Term -> nat -> Terms -> Prop :=
| ctsNil: forall p n, crctEnv p -> crctTerms p n tnil
| ctsCons: forall p n t ts,
    crctTerm p n t -> crctTerms p n ts ->
    crctTerms p n (tcons t ts)
with crctBs: environ Term -> nat -> Brs -> Prop :=
| cbsNil: forall p n, crctEnv p -> crctBs p n bnil
| cbsCons: forall p n m t ts,
    crctTerm p n t -> crctBs p n ts ->  crctBs p n (bcons m t ts)
with crctDs: environ Term -> nat -> Defs -> Prop :=
| cdsNil: forall p n, crctEnv p -> crctDs p n dnil
| cdsCons: forall p n nm bod ix ds,
             isLambda bod -> crctTerm p n bod -> crctDs p n ds ->
             crctDs p n (dcons nm bod ix ds).
Hint Constructors crctTerm  crctTerms crctBs crctDs crctEnv.
Scheme crct_ind' := Minimality for crctTerm Sort Prop
  with crcts_ind' := Minimality for crctTerms Sort Prop
  with crctBs_ind' := Minimality for crctBs Sort Prop
  with crctDs_ind' := Minimality for crctDs Sort Prop
  with crctEnv_ind' := Minimality for crctEnv Sort Prop.
Combined Scheme crctCrctTsBsDsEnv_ind from
         crct_ind', crcts_ind', crctBs_ind', crctDs_ind', crctEnv_ind'.

Lemma Crct_WFTrm:
  (forall p n t, crctTerm p n t -> WFTrm t n) /\
  (forall p n ts, crctTerms p n ts -> WFTrms ts n) /\
  (forall p n bs, crctBs p n bs -> WFTrmBs bs n) /\
  (forall p n (ds:Defs), crctDs p n ds -> WFTrmDs ds n) /\
  (forall p, crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; auto.
Qed.

Lemma Crct_CrctEnv:
  (forall p n t, crctTerm p n t -> crctEnv p) /\
  (forall p n bs, crctTerms p n bs -> crctEnv p) /\
  (forall p n bs, crctBs p n bs -> crctEnv p) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctEnv p) /\
  (forall (p:environ Term), crctEnv p -> True).
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; intuition.
Qed.

Lemma Crct_up:
  (forall p n t, crctTerm p n t -> crctTerm p (S n) t) /\
  (forall p n bs, crctTerms p n bs -> crctTerms p (S n) bs) /\
  (forall p n bs, crctBs p n bs -> crctBs p (S n) bs) /\
  (forall p n (ds:Defs), crctDs p n ds -> crctDs p (S n) ds) /\
  (forall p, crctEnv p -> True). 
Proof.
  apply crctCrctTsBsDsEnv_ind; intros; try (solve [constructor; assumption]).
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
  apply crctCrctTsBsDsEnv_ind; intros; try intros j; auto;
  inversion_Clear j;
  try (specialize (H2 _ H3); contradiction);
  try (specialize (H5 _ H6); contradiction);
  try (specialize (H0 _ H3); contradiction);
  try (specialize (H0 _ H1); contradiction);
  try (specialize (H0 _ H6); contradiction);
  try (specialize (H1 _ H4); contradiction);
  try (specialize (H3 _ H4); contradiction);
  try (specialize (H3 _ H6); contradiction).
  - unfold LookupDfn in H1. elim (Lookup_fresh_neq H1 H2). reflexivity.
  - unfold LookupTyp in H1. destruct H1.
    elim (Lookup_fresh_neq H1 H4). reflexivity.
  - specialize (H0 _ H2). contradiction.
Qed.

Lemma Crct_weaken:
  (forall p n t, crctTerm p n t -> 
                 forall nm s, fresh nm p -> crctTerm p 0 s ->
                              crctTerm ((nm,ecTrm s)::p) n t) /\
  (forall p n bs, crctTerms p n bs -> 
                  forall nm s, fresh nm p -> crctTerm p 0 s ->
                               crctTerms ((nm,ecTrm s)::p) n bs) /\
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
  - unfold LookupTyp in *. destruct H1. split; try assumption.
    constructor; try eassumption.
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
  apply crctCrctTsBsDsEnv_ind; intros;
  try (solve[repeat econstructor; intuition]);
  try (econstructor; intuition); try eassumption.
  - unfold LookupDfn in *. constructor.
    apply neq_sym. apply (Lookup_fresh_neq H1 H2). eassumption.
  - unfold LookupTyp in *. destruct H1. split; try eassumption.
    constructor; try eassumption.
    apply neq_sym. apply (Lookup_fresh_neq H1). assumption.
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
  apply crctCrctTsBsDsEnv_ind; intros; subst;
    try (econstructor; eapply H0; reflexivity; intros h; elim H2;
         econstructor; eassumption);
    try (econstructor; eassumption).
  - constructor. eapply H0. reflexivity. intros h. elim H2.
    constructor. assumption.
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
    + unfold LookupTyp in *. intuition.
      eapply Lookup_strengthen. eassumption. reflexivity.
      inversion_Clear H4.
      * elim H5. constructor.
      * assumption.
  - econstructor; try eassumption.
    + eapply H0. reflexivity. intros h. elim H4. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H4.
      apply PoCaseR. assumption.
  - econstructor; try eassumption. eapply H0. reflexivity. intros h.
    elim H3. constructor. assumption.
  - econstructor.
    + eapply H0. reflexivity. intros k. elim H4. constructor. assumption.
    + eapply H2. reflexivity. intros h. elim H4. apply Potl. assumption.
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
  forall p n ipkgNm inum cnum npars nargs,
    crctTerm p n (TConstruct (mkInd ipkgNm inum) cnum npars nargs) ->
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

(*********
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
  - pose proof (Crct_invrt_Rel h0) as k. destruct (Crct_invrt_Rel h0) as [j1 [j2 jx]].
    rewrite tappend_tnil. assumption.
  - destruct (Crct_invrt_App h0) as [j1 [j2 [j3 j4]]].
    apply ctApp; try assumption. destruct t; simpl.
    + inversion h1; assumption.
    + inversion_Clear j3. constructor. assumption.
      apply Crcts_append; assumption.
Qed.
 **********)

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
  - inversion_Clear H0. constructor. assumption. omega.
  - apply ctRel.
    + inversion H0. assumption.
    + inversion H0. omega.
  - inversion_Clear H1; constructor; try assumption; apply H; try assumption.
    omega. apply Crct_up. assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; assumption.                 
    + apply H0; try assumption. omega. apply (proj1 Crct_up). assumption.
  - inversion_Clear H2. constructor.
    + apply H; assumption.
    + apply H0; try assumption.
  - inversion_Clear H2. constructor.
    + eapply H; try eassumption.
    + eapply H0; try eassumption.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. econstructor; try omega.
    + eapply H; try omega.
      * rewrite <- k; assumption.
      * eapply Crct_UP. eassumption. omega.
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


(******************************

(** correctness specification for programs (including local closure) **)
Inductive Crct: environ Term -> nat -> Term -> Prop :=
| CrctWkTrmTrm: forall n p t s nm,
    Crct p n t -> Crct p n s -> fresh nm p -> Crct ((nm,ecTrm s)::p) n t
| CrctWkTrmTyp: forall n p t s nm,
    Crct p n t -> fresh nm p -> forall m, Crct ((nm,ecTyp _ m s)::p) n t
| CrctRel: forall n m p, m < n -> Crct p n prop -> Crct p n (TRel m)
| CrctProof: forall n p t, Crct p n t -> Crct p n (TProof t)
| CrctLam: forall n p nm bod,
    Crct p n prop -> Crct p (S n) bod -> Crct p n (TLambda nm bod)
| CrctLetIn: forall n p nm dfn bod,
    Crct p n dfn -> Crct p (S n) bod -> 
    Crct p n (TLetIn nm dfn bod)
| CrctApp: forall n p fn a args,
    ~ (isApp fn) -> Crct p n fn -> Crct p n a -> Crcts p n args -> 
    Crct p n (TApp fn a args)
| CrctConst: forall n p pd nm,
    Crct p n prop -> LookupDfn nm p pd -> Crct p n (TConst nm)
| CrctConstruct: forall n p ipkgNm inum cnum np na ipkg itp cstr pars,
    Crct p n prop ->
    LookupTyp ipkgNm p pars ipkg ->
    getInd ipkg inum = Ret itp ->
    getCnstr itp cnum = Ret cstr ->
    Crct p n (TConstruct (mkInd ipkgNm inum) cnum np na)
| CrctCase: forall n p cx mch brs,
    Crct p n mch -> CrctBs p n brs -> Crct p n (TCase cx mch brs)
| CrctFix: forall n p ds m,
    Crct p n prop ->    (** convenient for IH *)
    CrctDs p (n + dlength ds) ds -> Crct p n (TFix ds m)
| CrctInd: forall n p ind, Crct p n prop -> Crct p n (TInd ind)
| CrctDummy: forall p n, Crct p n TDummy
with Crcts: environ Term -> nat -> Terms -> Prop :=
     | CrctsNil: forall n p, Crct p n prop -> Crcts p n tnil
     | CrctsCons: forall n p t ts,
         Crct p n t -> Crcts p n ts -> Crcts p n (tcons t ts)
with CrctBs: environ Term -> nat -> Brs -> Prop :=
     | CrctBsNil: forall n p, Crct p n prop -> CrctBs p n bnil
     | CrctBsCons: forall n m p b bs,
         Crct p n b -> CrctBs p n bs -> CrctBs p n (bcons m b bs)
with CrctDs: environ Term -> nat -> Defs -> Prop :=
     | CrctDsNil: forall n p, Crct p n prop -> CrctDs p n dnil
     | CrctDsCons: forall n p dn db dra ds,
         isLambda db ->  Crct p n db -> CrctDs p n ds ->
         CrctDs p n (dcons dn db dra ds).
Hint Constructors Crct Crcts CrctBs CrctDs.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with Crcts_ind' := Minimality for Crcts Sort Prop
  with CrctBs_ind' := Minimality for CrctBs Sort Prop
  with CrctDs_ind' := Minimality for CrctDs Sort Prop.
Combined Scheme CrctCrctsCrctBsCrctDs_ind from
         Crct_ind', Crcts_ind', CrctBs_ind', CrctDs_ind'.


Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall p n ts, CrctBs p n ts -> WFTrmBs ts n) /\
  (forall p (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n).
Proof.
  apply CrctCrctsCrctBsCrctDs_ind; intros; auto.
Qed.

(******
Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall (p:environ Term) (n:nat) (ds:Brs), CrctBs p n ds -> WFTrmBs ds n) /\
  (forall (p:environ Term) (n:nat) (itp:itypPack), CrctTyp p n itp -> True).
apply CrctCrctsCrctBsCrctDs_ind; intros; auto.
Qed.
 ****)

Lemma Crct_WFApp:
  forall p n t, Crct p n t -> WFapp t.
  intros p n t h. eapply WFTrm_WFapp. eapply (proj1 Crct_WFTrm). eassumption.
Qed.

Lemma Crct_up:
  (forall p n t, Crct p n t -> Crct p (S n) t) /\
  (forall p n ts, Crcts p n ts -> Crcts p (S n) ts) /\
  (forall p n ts, CrctBs p n ts -> CrctBs p (S n) ts) /\
  (forall p (n:nat) (ds:Defs), CrctDs p n ds -> CrctDs p (S n) ds).
Proof.
  apply CrctCrctsCrctBsCrctDs_ind; intros;
  try (econstructor; try omega; eassumption).
Qed.

Lemma Crct_UP:
  forall p n t, Crct p n t -> forall m, Crct p (n + m) t.
Proof.
  induction m.
  - replace (n + 0) with n; try omega. assumption.
  - replace (n + (S m)) with (S (n + m)); try omega.
    apply Crct_up. assumption.
Qed.      

Lemma Crct_Up:
  forall n p t, Crct p 0 t -> Crct p n t.
Proof.
  induction n; intros; try assumption. apply Crct_up. intuition.
Qed.

Lemma Crct_Sort:
  forall p n t, Crct p n t -> forall srt, Crct p n (TSort srt).
Proof.
  induction 1; intuition.
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

(**
Lemma CrctsWk: 
  forall p n ts, Crcts p n ts -> forall s nm, Crct p n s ->
           fresh nm p -> Crcts ((nm,ecTrm s)::p) n ts.
induction 1; intros.
- apply CrctsNil. apply CrctWk; assumption.
- apply CrctsCons.
  + apply CrctWk; assumption.
  + apply IHCrcts; assumption.
Qed.

Lemma Crct_WFTrm:
  (forall p n t, Crct p n t -> WFTrm t n) /\
  (forall p n ts, Crcts p n ts -> WFTrms ts n) /\
  (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> WFTrmDs ds n).
apply CrctCrctsCrctDs_ind; intros; auto; subst.
Qed.
**)

Lemma Crct_fresh_Pocc:
  (forall p n t, Crct p n t -> forall nm, fresh nm p -> ~ PoccTrm nm t) /\
  (forall p n ts, Crcts p n ts -> forall nm, fresh nm p -> ~ PoccTrms nm ts) /\
  (forall p n ts, CrctBs p n ts -> forall nm, fresh nm p -> ~ PoccBrs nm ts) /\
  (forall p n (ds:Defs), CrctDs p n ds -> forall nm, fresh nm p ->
                                                     ~ PoccDefs nm ds).
Proof.
  apply CrctCrctsCrctBsCrctDs_ind; intros; intros j;
    try (solve [inversion j]);
    try (solve [inversion_clear j; elim (H0 nm); trivial]);
    try (solve [inversion_clear j; elim (H0 nm); trivial;
                elim (H2 nm); trivial]);
    try (solve [inversion_clear j; elim (H0 nm0); trivial;
                elim (H2 nm0); trivial]);
    try (solve [inversion_clear j; elim (H0 nm); trivial;
                elim (H2 nm); trivial]);
    try (solve [inversion_clear H4; elim (H0 nm0); trivial]).
  - elim (H0 nm0); trivial. inversion H2. assumption.
  - inversion_clear j. elim (H1 nm); assumption. elim (H3 nm); assumption.
    elim (H5 nm); assumption.
  - inversion_Clear j. eelim (fresh_Lookup_fails H2). eassumption.
  - inversion_Clear j. eelim (fresh_Lookup_fails H4).
    destruct H1. eassumption.
  - inversion_Clear j.
    + elim (H1 _ H4). assumption.
    + elim (H3 _ H4); trivial.
Qed.


Lemma Crct_not_bad_Lookup:
  (forall p n s, Crct p n s ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ss, Crcts p n ss ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ss, CrctBs p n ss ->
                 forall nm, LookupDfn nm p (TConst nm) -> False) /\
  (forall p n ds, CrctDs p n ds ->
                 forall nm, LookupDfn nm p (TConst nm) -> False).
Proof.
  apply CrctCrctsCrctBsCrctDs_ind; intros; auto;
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
  - elim (H3 _ H4).
    Grab Existential Variables.
    + reflexivity.
Qed.

Lemma  Crct_weaken:
  (forall p n t, Crct p n t -> 
    forall nm s, fresh nm p -> Crct p n s -> Crct ((nm,ecTrm s)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm s, fresh nm p -> Crct p n s -> Crcts ((nm,ecTrm s)::p) n ts) /\
  (forall p n ts, CrctBs p n ts -> 
    forall nm s, fresh nm p -> Crct p n s -> CrctBs ((nm,ecTrm s)::p) n ts) /\
  (forall p n ds,
      CrctDs p n ds -> 
      forall nm s, fresh nm p -> Crct p n s -> CrctDs ((nm,ecTrm s)::p) n ds).
Proof.
  eapply CrctCrctsCrctBsCrctDs_ind; intros; intuition.
  - apply CrctWkTrmTrm; try assumption. eapply CrctConst; eassumption.
  - eapply CrctConstruct; try eassumption.
    apply H0; try assumption. destruct H1. split.
    + apply Lookup_weaken; eassumption.
    + assumption.
Qed.

Lemma  Crct_Typ_weaken:
  (forall p n t, Crct p n t -> 
    forall nm itp, fresh nm p -> 
                   forall npars, Crct ((nm,ecTyp Term npars itp)::p) n t) /\
  (forall p n ts, Crcts p n ts -> 
    forall nm itp, fresh nm p ->
                 forall npars, Crcts ((nm,ecTyp Term npars itp)::p) n ts) /\
  (forall p n ts, CrctBs p n ts -> 
    forall nm itp, fresh nm p ->
                 forall npars, CrctBs ((nm,ecTyp Term npars itp)::p) n ts) /\
  (forall p n ds, CrctDs p n ds -> 
    forall nm itp, fresh nm p ->
                   forall npars, CrctDs ((nm,ecTyp Term npars itp)::p) n ds).
Proof.
  eapply CrctCrctsCrctBsCrctDs_ind; intros; auto.
  - apply CrctWkTrmTyp; try assumption. eapply CrctConst; try eassumption.
  - eapply CrctConstruct; try eassumption.
    apply H0; try assumption. destruct H1. split.
    + apply Lookup_weaken; eassumption.
    + assumption.
Qed.

Lemma Crct_strengthen:
  (forall pp n t, Crct pp n t -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrm nm t -> Crct p n t) /\
  (forall pp n ts, Crcts pp n ts -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccTrms nm ts -> Crcts p n ts) /\
  (forall pp n ts, CrctBs pp n ts -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccBrs nm ts -> CrctBs p n ts) /\
  (forall pp n ds, CrctDs pp n ds -> 
       forall nm ec p, pp = (nm,ec)::p -> ~ PoccDefs nm ds -> CrctDs p n ds).
Proof.
  eapply CrctCrctsCrctBsCrctDs_ind; intros; auto.
  - inversion H.
  - injection H4; intros. subst. assumption.
  - injection H2; intros. subst. assumption.
  - apply CrctRel; try assumption. eapply H1. eapply H2.
    intros h. inversion h.
  - apply CrctProof; try assumption.
    + eapply H0. eassumption.
      * intros h. elim H2. apply PoProof. assumption.
  - apply CrctProd.
    + eapply H0. eassumption. intros h. inversion h. 
    + eapply H2. eassumption.
      intros h. elim H4. apply PoProdBod. assumption.
  - apply CrctLam.
    + eapply H0. eassumption. intros h. inversion h. 
    + eapply H2. eassumption.
      intros h. elim H4. apply PoLambdaBod. assumption.
  - apply CrctLetIn.
    + eapply H0. eassumption. intros h. elim H4.
      apply PoLetInDfn. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoLetInBod. assumption.
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
    + eapply H0. eapply H4. intros h. inversion h.
    + rewrite H4 in H1.
      assert (j: nm <> ipkgNm).
      { eapply notPocc_TCnstr. eassumption. }
      destruct H1. subst. split; try assumption.
      inversion_Clear H1.
      * elim j. reflexivity.
      * eassumption.
  - eapply CrctCase.
    + eapply H0. eassumption.
      intros h. elim H4. apply PoCaseL. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoCaseR. assumption.
  - apply CrctFix.
    + eapply H0. eassumption. intros h. inversion h.
    + eapply H2. eassumption. intros h. elim H4. apply PoFix. assumption.
  - apply CrctInd. apply (H0 _ _ _ H1). inversion 1. 
  - apply CrctsNil. rewrite H1 in H. inversion H; assumption.
  - apply CrctsCons.
    + eapply H0. eassumption. intros h. elim H4. apply PoThd. assumption.
    + eapply H2. eassumption.
      intros h. elim H4. apply PoTtl. assumption.
  - apply CrctBsNil. eapply H0. eassumption. intros h. inversion h.
  - apply CrctBsCons; try assumption.
    + eapply H0. eassumption. intros h. elim H4. apply PoBhd. assumption.
    + eapply H2. eassumption. intros h. elim H4. apply PoBtl. assumption.
  - apply CrctDsNil. eapply H0. eassumption. intros h. inversion h.
  - apply CrctDsCons; try assumption.
    + eapply H1. eassumption. intros h. elim H5. constructor. assumption.
    + eapply H3. eassumption. intros h. elim H5. apply PoDtl. assumption.
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
               (forall p n bs, CrctBs p n bs -> True) /\
               (forall (p:environ Term) (n:nat) (ds:Defs),
                   CrctDs p n ds -> True)).
  { apply CrctCrctsCrctBsCrctDs_ind; intros; auto;
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
  - myInjection H2. auto.
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
  - myInjection H1. intuition. exists pd; intuition.
    eapply LookupDfn_pres_Crct; eassumption.
Qed.

Lemma Crct_invrt_Prod:
  forall p n prod, Crct p n prod ->
  forall nm bod, prod = TProd nm bod -> Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2).
    apply CrctWkTrmTrm; trivial. apply Crct_up. assumption.
  - assert (j:= IHCrct _ _ H1).
    apply CrctWkTrmTyp; trivial.
  - myInjection H1. assumption.
Qed.

Lemma Crct_invrt_Lam:
  forall p n lam, Crct p n lam ->
  forall nm bod, lam = TLambda nm bod -> Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2).
    apply CrctWkTrmTrm; trivial. apply Crct_up. assumption.
  - assert (j:= IHCrct _ _ H1).
    apply CrctWkTrmTyp; trivial.
  - myInjection H1. assumption.
Qed.

Lemma Crct_invrt_LetIn:
  forall p n letin, Crct p n letin ->
  forall nm dfn bod, letin = TLetIn nm dfn bod ->
     Crct p n dfn /\ Crct p (S n) bod.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ H2). intuition.
    constructor; try assumption. apply Crct_up. assumption.
  - assert (j:= IHCrct _ _ _ H1). intuition. 
  - myInjection H1. intuition.
Qed.

Lemma Crct_invrt_App:
  forall p n app,
    Crct p n app -> forall fn arg args, app = (TApp fn arg args) ->
    Crct p n fn /\ Crct p n arg /\ Crcts p n args /\ ~(isApp fn).
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ _ _ H2). intuition.
  apply (proj2 Crct_weaken); auto.
- assert (j:= IHCrct _ _ _ H1). intuition.
  apply (proj1 (proj2 Crct_Typ_weaken)); auto.
- injection H3; intros; subst. auto.
Qed.

Lemma Crct_invrt_Case:
  forall p n case,
    Crct p n case ->
    forall us cx s,
      case = TCase cx s us -> Crct p n s /\ CrctBs p n us.
Proof.
  induction 1; intros; try discriminate. subst.
  - assert (j:= IHCrct1 _ _ _ eq_refl). intuition.
    + case_eq us; intros; subst.
      * constructor. constructor; try assumption. eapply Crct_Sort. eassumption.
      * { inversion_Clear H3.
          destruct (IHCrct1 (bcons n0 t b) cx s0 eq_refl) as [k0 k2].
          inversion_Clear k2. eapply Crct_weaken; try assumption.
          constructor; try assumption. }
  - assert (j:= IHCrct _ _ _ H1). intuition.
    + case_eq us; intros.
      * constructor. constructor; try assumption. eapply Crct_Sort. eassumption.
      * { subst us t. inversion_Clear H3. 
          destruct (IHCrct (bcons n0 t0 b) cx s0 eq_refl) as [k0 k2].
          inversion_Clear k2.
          eapply (proj2 (proj2 Crct_Typ_weaken)); try assumption.
          constructor; try assumption. }
  - myInjection H1. intuition. 
Qed.

Lemma Crct_invrt_Proof:
  forall p n cast,
    Crct p n cast -> forall t, cast = (TProof t) -> Crct p n t.
induction 1; intros; try discriminate.
- assert (j:= IHCrct1 _ H2). intuition.
- assert (j:= IHCrct _ H1). intuition.
- injection H0; intros; subst. auto.
Qed.
                                   
Lemma Crct_invrt_Fix:
  forall p n gix, Crct p n gix ->
      forall ds m, gix = (TFix ds m) -> CrctDs p (n + dlength ds) ds.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ H2).
    apply Crct_weaken; auto. apply Crct_UP. assumption.
  - assert (j:= IHCrct _ _ H1).
    apply (proj2 (proj2 (proj2 Crct_Typ_weaken))); auto.
  - injection H1; intros; subst. assumption.
Qed.

Lemma Crct_invrt_Construct:
  forall p n construct, Crct p n construct ->
   forall ipkgNm inum cnum np na,
     construct = (TConstruct (mkInd ipkgNm inum) cnum np na) ->
    Crct p n prop /\
    exists npars itypk,
      LookupTyp ipkgNm p npars itypk /\
      exists (ip:ityp), getInd itypk inum = Ret ip /\
                        exists (ctr:Cnstr), getCnstr ip cnum = Ret ctr.
Proof.
  induction 1; intros; try discriminate.
  - assert (j:= IHCrct1 _ _ _ _ _ H2). intuition.
    destruct H4 as [npars [itypk [h1 h2]]]. exists npars, itypk. intuition.
    destruct h1. split; try assumption. apply Lookup_weaken; trivial.
  - assert (j:= IHCrct _ _ _ _ _ H1). intuition.
    destruct H3 as [npars [itypk [h1 h2]]]. exists npars, itypk. intuition.
    destruct h1. split; try assumption. apply Lookup_weaken; trivial.
  - myInjection H3. intuition.
    exists pars, ipkg. intuition.
    exists itp. intuition.
    exists cstr. assumption.
Qed.

Lemma Crct_invrt_any:
  forall p n t, Crct p n t -> Crct p n prop.
Proof.
  induction 1; try (solve[constructor; eassumption]); try assumption.
Qed.

Lemma Crct_App_fn_notApp:
  forall p n fn arg args, Crct p n (TApp fn arg args) -> ~ isApp fn.
intros p n fn arg args h1.
assert (j:= @Crct_invrt_App p n (TApp fn arg args) h1 fn arg args eq_refl).
intuition.
Qed.

Lemma CrctDs_invrt:
  forall n p dts, CrctDs p n dts -> 
    forall m x ix, dnthBody m dts = Some (x, ix) -> Crct p n x.
Proof.
  induction 1; intros.
  - cbn in H0. discriminate.
  - destruct m.
    + cbn in H2. myInjection H2. assumption.
    + eapply IHCrctDs. cbn in H2. eassumption.
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
  induction fn; unfold mkApp; simpl; intros p' nx h0 args h1;
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
  (forall n bs inss, InstantiateBrs tin n bs inss ->
  forall m p, n <= m -> CrctBs p (S m) bs -> Crct p m tin -> CrctBs p m inss) /\
  (forall n ds ids, InstantiateDefs tin n ds ids ->
  forall m p, n <= m -> CrctDs p (S m) ds -> Crct p m tin -> CrctDs p m ids).
Proof.
  intros tin. apply InstInstsBrsDefs_ind; intros; trivial.
  - constructor. omega. eapply Crct_invrt_any. eassumption.
  - destruct (Crct_invrt_Rel H0 eq_refl). apply CrctRel.
    + omega.
    + eapply Crct_Sort. eassumption.
  - eapply Crct_Sort; eassumption.
  - constructor. apply H; try assumption.
    apply(Crct_invrt_Proof H1 eq_refl). 
  - pose proof (Crct_invrt_Prod H1 eq_refl) as h. apply CrctProd.
    + eapply Crct_Sort. eassumption.
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
  - pose proof (Crct_invrt_Lam H1 eq_refl) as h. apply CrctLam.
    + eapply Crct_Sort. eassumption.
    + apply H; trivial. omega. apply (proj1 Crct_up). assumption.
  - destruct (Crct_invrt_LetIn H2 eq_refl). apply CrctLetIn.
    + apply H; trivial.
    + apply H0; intuition. apply (proj1 Crct_up). assumption.
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
  - destruct ind. edestruct (Crct_invrt_Construct H0).
    + reflexivity.
    + destruct H3 as [npars [ip [h1 [it [h2 [ctr h3]]]]]].
      eapply CrctConstruct; try eassumption.
      * eapply Crct_Sort. eassumption.
  - eapply CrctCase.
    + apply H; trivial. 
      destruct (Crct_invrt_Case H2 eq_refl) as [k0 k3]. assumption.
    + apply H0; trivial. 
      destruct (Crct_invrt_Case H2 eq_refl) as [k0 k3]. assumption.
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
  - apply CrctBsNil. eapply Crct_Sort. eassumption.
  - inversion_Clear H2. apply CrctBsCons. 
    + apply H; trivial.
    + apply H0; trivial.                                         
  - apply CrctDsNil. eapply Crct_Sort. eassumption.
  - inversion_Clear H2. apply CrctDsCons. 
    + eapply Instantiate_pres_isLambda; eassumption.
    + apply H; trivial.
    + apply H0; trivial.
Qed.

Lemma instantiate_pres_Crct:
  forall p m bod, Crct p (S m) bod -> forall tin, Crct p m tin -> 
                  forall n, n <= m ->  Crct p m (instantiate tin n bod).
Proof.
  intros.
  apply (proj1 (Instantiate_pres_Crct tin) _ _ _
               (proj1 (instantiate_Instantiate tin) _ _));
    try assumption.
Qed.

Lemma whBetaStep_pres_Crct:
  forall p n bod, Crct p (S n) bod ->
                  forall a1 args, Crct p n a1 -> Crcts p n args ->
                                  Crct p n (whBetaStep bod a1 args).
Proof.
  intros. unfold whBetaStep. apply mkApp_pres_Crct; try assumption.
  apply instantiate_pres_Crct; try assumption.  omega.
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


(*********
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
***************)
***********************)
**************************************)
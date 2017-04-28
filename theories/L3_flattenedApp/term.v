(*** type fields are stripped from term notations and unary applications ***)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Arith.
Require Import Coq.omega.Omega.
Require Export Common.Common.  (* shared namespace *)
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Ltac not_is0 :=
  let hh := fresh "h" in
  intros hh; discriminate.
Ltac not_is1 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j" in
  intros hh; destruct hh as [xx jj]; discriminate.
Ltac not_is2 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.
 Ltac not_is3 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with zz := fresh "z" in
  intros hh; destruct hh as [xx [yy [zz jj]]]; discriminate.
            
            Ltac not_isApp := not_is2.
            Ltac not_isLambda := not_is2.
            Ltac not_isCase := not_is3.
            Ltac not_isFix := not_is2.
            Ltac not_isCast := not_is1.
            Ltac not_isConstruct := not_is3.
  (****
  Ltac not_isApp :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with kk := fresh "k" in
  intros hh; destruct hh as [xx [yy kk]]; discriminate.
Ltac isApp_inv h :=
  let hh := fresh "h"
  with xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j"
  in destruct h as [xx [yy [zz jj]]]; discriminate.
Ltac not_isConstruct :=
  let hh := fresh "h"
  with xx0 := fresh "x"
  with xx1 := fresh "x1"
  with xx2 := fresh "x2"
  with ll := fresh "l" in
  intros hh; destruct hh as [xx0 [xx1 [xx2 l]]]; discriminate.
************************)

Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (ss tt:Terms), ss = tt \/ ss <> tt) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsDefs_ind.
  - induction t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - induction t; cross. intuition.
  - induction t0; cross.
    destruct (name_dec n n0); destruct (H t0); [lft | rght ..].
    (***
  - induction t0; cross.
    destruct (name_dec n n0); destruct (H t0); [lft | rght ..]. 
***)
  - induction t1; cross.
    destruct (name_dec n n0); destruct (H t1_1); destruct (H0 t1_2); 
    [lft | rght ..]. 
  - induction t1; cross. 
    destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..].
  - induction t; cross. destruct (string_dec s s0); [lft | rght].
  - induction t; cross. left. reflexivity.
    (**
  - induction t; cross. destruct (inductive_dec i i0); [lft | rght].
**)
  - induction t0; cross.
    destruct (inductive_dec i i0); destruct (eq_nat_dec n n0);
    destruct (H t0);
    [lft | rght .. ].
  - induction t0; cross.
    destruct (inductive_dec i i0), (H t0), (H0 d0); [lft | rght .. ].
  - induction t; cross. destruct (eq_nat_dec n n0), (H d0); [lft | rght .. ].
  - destruct t; cross. lft.
  - induction tt; cross. lft.
  - induction tt; cross. destruct (H t1); destruct (H0 tt); [lft | rght .. ].
  - induction ee; cross. lft.
  - induction ee; cross.
    destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
    destruct (H t0); destruct (H0 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.

Definition Term_dec := proj1 TermTerms_dec.
Definition Terms_dec := proj1 (proj2 TermTerms_dec).


Fixpoint TrmSize (t:Term) {struct t} : nat :=
  match t with
    | TLambda _ bod => S (TrmSize bod)
    | TLetIn _ dfn bod => S (TrmSize dfn + TrmSize bod)
    | TApp fn a => S (TrmSize fn + TrmSize a)
    | TCase _ mch brs => S (TrmSize mch + TrmDsSize brs)
    | TFix ds n => S 0
    | _ => S 0
  end
with TrmDsSize (ds:Defs) : nat :=
  match ds with
    | dnil => 1
    | dcons _ t1 _ es => S (TrmSize t1 + TrmDsSize es)
  end.


Definition isLambda (t:Term) : Prop :=
  exists nm bod, t = TLambda nm bod.
Lemma IsLambda: forall nm bod, isLambda (TLambda nm bod).
intros. exists nm, bod. reflexivity.
Qed.
Hint Resolve IsLambda.

Lemma isLambda_dec: forall t, {isLambda t}+{~ isLambda t}.
induction t;
  try (solve [right; intros h; unfold isLambda in h;
              elim h; intros x h1; elim h1; intros x0 h2; discriminate]).
left. auto.
Qed.

Definition isApp (t:Term) : Prop :=
  exists fn arg, t = TApp fn arg.
Lemma IsApp: forall fn arg, isApp (TApp fn arg).
intros. exists fn, arg. reflexivity.
Qed.
Hint Resolve IsApp.

Ltac isApp :=
  match goal with
    | |- isApp (TApp ?fn ?arg) => exists fn, arg; reflexivity
  end.

(***
Lemma mkApp_tcons:
  forall (fn arg:Term) (args:Terms), isApp (mkApp fn (tcons arg args)).
Proof.
  induction args; cbn; intros; destruct fn; try isApp.
  - admit.
  - cbn in IHargs. exists (TRel n), arg. reflexivity.
 ***)

Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
induction t;
  try (right; intros h; destruct h as [fn [arg k]]; discriminate). 
left. auto.
Qed.

Definition isFix (t:Term) : Prop :=
  exists ds n, t = TFix ds n.
Lemma IsFix: forall ds n, isFix (TFix ds n).
intros. exists ds, n. reflexivity.
Qed.
Hint Resolve IsFix.

Lemma isFix_dec: forall t, {isFix t}+{~ isFix t}.
induction t;
  try (solve [right; intros h; unfold isFix in h;
              elim h; intros x h1; elim h1; intros x0 h2; discriminate]).
left. auto.
Qed.

Definition isConstruct (t:Term) : Prop :=
  exists i n ts, t = TConstruct i n ts.
Lemma IsConstruct: forall i n ts, isConstruct (TConstruct i n ts).
intros. exists i, n, ts. reflexivity.
Qed.
Hint Resolve IsConstruct.

Lemma isConstruct_dec: forall t, isConstruct t \/ ~ isConstruct t.
induction t;
  try (solve [right; intros h;
              destruct h as [x [nx [ts j]]]; discriminate]).
- left. auto.
Qed.

Definition isProof (t:Term) : Prop := t = TProof.

Lemma isProof_dec: forall t, isProof t \/ ~ isProof t.
Proof.
  destruct t; try (right; intros h; discriminate).
  - left. reflexivity. 
Qed.


(** some utility operations on [Terms] ("lists" of Term) **)
Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
induction ts; simpl; try reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma tappend_cons_lem:
  forall ys t zs,
    tappend ys (tcons t zs) = tappend (tappend ys (tcons t tnil)) zs.
  induction ys; intros tt zzs; simpl.
  - reflexivity.
  - rewrite IHys. reflexivity.
Qed.
  
Lemma tappend_tappend_lem:
  forall xts yts t zts,
       (tappend xts (tappend yts (tcons t zts))) =
       (tappend (tappend xts (tappend yts (tcons t tnil))) zts).
  intros xts yts t zts. rewrite tappend_cons_lem. rewrite tappend_assoc.
  reflexivity.
Qed.

Lemma tappend_mk_canonical:
  forall ts s ss, exists u us, (tappend ts (tcons s ss)) = tcons u us.
Proof.
  destruct ts; intros s ss; simpl.
  - exists s, ss. reflexivity.
  - exists t, (tappend ts (tcons s ss)). reflexivity.
Qed.

Lemma tlength_tappend:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; simpl; intros; try reflexivity.
  - rewrite IHts. reflexivity.
Qed.

Lemma tappend_tcons_tunit:
  forall bs ds cs x,
    tappend bs (tcons x cs) = tappend ds cs -> tappend bs (tunit x) = ds.
Proof.
  induction bs; destruct ds; cbn; intros.
  - assert (j:= f_equal tlength H). cbn in j. omega.
  - injection H. intros. subst x. destruct ds.
    + reflexivity.
    + injection H; intros.
      assert (j:= f_equal tlength H). cbn in j.
      rewrite tlength_tappend in j. omega.
  - destruct cs.
    + discriminate.
    + injection H; intros. assert (j:= f_equal tlength H0).
      rewrite tlength_tappend in j. cbn in j. omega.
  - injection H; intros.  assert (j:= f_equal tlength H0).
    rewrite tlength_tappend in j. cbn in j.
    specialize (IHbs _ _ _ H0). rewrite IHbs. rewrite H1. reflexivity.
Qed.

Fixpoint tmap (fn:Term -> Term) (ts:Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons x xs => tcons (fn x) (tmap fn xs)
  end.

Fixpoint tIn (a:Term) (l:Terms) : Prop :=
    match l with
      | tnil => False
      | tcons b m => b = a \/ tIn a m
    end.

Lemma tIn_tappend1:
  forall u ts ss, tIn u (tappend ts (tcons u ss)).
Proof.
  induction ts; intros ss.
  - simpl. left. reflexivity.
  - simpl. right. apply IHts.
Qed.

Lemma tIn_tappend2:
  forall t ts us, tIn t ts -> tIn t (tappend ts us).
induction ts; intros us h; inversion_Clear h; simpl.
- left. reflexivity.
- right. apply IHts. assumption.
Qed.

Fixpoint tskipn (n:nat) (l:Terms) : option Terms :=
    match n, l with
      | 0, l => Some l
      | S n, tcons a l => tskipn n l
      | S _, tnil => None
    end.

Fixpoint tnth (n:nat) (l:Terms) {struct l} : option Term :=
    match l with
      | tnil => None
      | tcons x xs => match n with
                        | 0 => Some x
                        | S m => tnth m xs
                      end
    end.

Fixpoint dnth (n:nat) (l:Defs) {struct l} : option (def Term) :=
    match l with
      | dnil => None
      | dcons nm tm args xs => match n with
                                 | 0 => Some (mkdef Term nm TAx tm args)
                                 | S m => dnth m xs
                               end
    end.

Definition dnthBody (n:nat) (l:Defs) : option Term :=
  match dnth n l with
    | None => None
    | Some (mkdef _ _ _ x _) => Some x
  end.

Lemma dnthBody_None: forall n ds, n >= dlength ds -> dnthBody n ds = None.
Proof.
  unfold dnthBody.
  induction n; induction ds; cbn; intuition;  inversion H.
Qed.

Lemma dnthBody_Some:
  forall ds n, n < dlength ds -> exists d, dnthBody n ds = Some d.
Proof.
  induction ds; intros nx h.
  - simpl in h. inversion h.
  - destruct nx.
    + simpl. exists t. reflexivity.
    + simpl. apply IHds. simpl in h. omega.
Qed.


(** well-formed terms: locally closed, TApp well-formed
*** not used essentially at the moment
**)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfLambda: forall n nm bod,
            WFTrm bod (S n) -> WFTrm (TLambda nm bod) n
| wfLetIn: forall n nm dfn bod,
             WFTrm dfn n -> WFTrm bod (S n) ->
             WFTrm (TLetIn nm dfn bod) n
| wfApp: forall n fn t, WFTrm fn n -> WFTrm t n -> WFTrm (TApp fn t) n
| wfAx: forall n, WFTrm TAx n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfConstruct: forall n i m1 args,
                 WFTrms args n -> WFTrm (TConstruct i m1 args) n
| wfCase: forall n m mch brs,
            WFTrm mch n -> WFTrmDs brs n ->
            WFTrm (TCase m mch brs) n
| wfFix: forall n defs m,
           WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
| wfPrf: forall n, WFTrm TProof n
with WFTrms: Terms -> nat -> Prop :=
| wfnil: forall n, WFTrms tnil n
| wfcons: forall n t ts, WFTrm t n -> WFTrms ts n -> WFTrms (tcons t ts) n
with WFTrmDs: Defs -> nat -> Prop :=
| wfdnil: forall n, WFTrmDs dnil n
| wfdcons: forall n nm bod arg ds,
             WFTrm bod n -> WFTrmDs ds n ->
             WFTrmDs (dcons nm bod arg ds) n.
Hint Constructors WFTrm WFTrms WFTrmDs.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrms_ind' := Minimality for WFTrms Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsDefs_ind from WFTrm_ind', WFTrms_ind', WFTrmDs_ind'.

Lemma WF_nolift:
  (forall t n, WFTrm t n -> forall i, n <= i -> lift i t = t) /\
  (forall ts n, WFTrms ts n -> forall i, n <= i -> lifts i ts = ts) /\
  (forall ds n, WFTrmDs ds n -> forall i, n <= i -> liftDs i ds = ds).  
Proof.
  apply WFTrmTrmsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H0; try reflexivity; omega);
  try (cbn; rewrite H0, H2; try reflexivity; omega).
  - cbn; case_eq (m ?= i); intros; Compare_Prop; try omega. reflexivity.
Qed.

Lemma WFTrm_up:
  (forall t m, WFTrm t m -> WFTrm t (S m)) /\
  (forall ts m, WFTrms ts m -> WFTrms ts (S m)) /\
  (forall ds m, WFTrmDs ds m -> WFTrmDs ds (S m)).
Proof.
  apply WFTrmTrmsDefs_ind; cbn; intros; constructor; try assumption; omega.
Qed.
  
Lemma tappend_pres_WFTrms:
  forall ts ss m, WFTrms ts m -> WFTrms ss m -> WFTrms (tappend ts ss) m.
Proof.
  induction ts; intros.
  - cbn. assumption.
  - cbn. inversion_Clear H. constructor; intuition.
Qed.

Lemma treverse_pres_WFTrms:
  forall ts m, WFTrms ts m -> WFTrms (treverse ts) m.
Proof.
  induction ts; intros.
  - cbn. constructor.
  - inversion_Clear H. cbn. apply tappend_pres_WFTrms; intuition.
Qed.

Lemma lift_pres_WFTrm:
  (forall t m, WFTrm t m -> forall n, WFTrm (lift n t) (S m)) /\
  (forall ts m, WFTrms ts m -> forall n, WFTrms (lifts n ts) (S m)) /\
  (forall ds m, WFTrmDs ds m -> forall n, WFTrmDs (liftDs n ds) (S m)).
Proof.
  apply WFTrmTrmsDefs_ind; intros; try (solve[cbn; constructor]);
  try (solve[cbn; constructor; intuition]).
  - cbn; case_eq (m ?= n0); intros; Compare_Prop; subst; constructor; omega.
  - cbn; constructor. rewrite liftDs_pres_dlength.
    refine (H0 (n0 + dlength defs)).
Qed. 


Lemma mkEtaLams_pres_WFTrm:
  forall args mx, WFTrms args mx ->
                forall xtra m i x, mx = m + xtra ->
                               WFTrm (mkEtaLams xtra i x args) m.
Proof.
  induction 1; induction xtra; intros; cbn; constructor; cbn; subst;
  try (solve[apply IHxtra; omega]);
  try (rewrite <- plus_n_O in *); try assumption.
                                  constructor. constructor; assumption.
Qed.

Lemma mkEtaArgs_pres_WFtrm:
  forall arty ts m, WFTrms ts m -> WFTrms (mkEtaArgs arty ts) (m + arty).
Proof.
  induction arty; intros.
  - cbn. apply treverse_pres_WFTrms. rewrite <- plus_n_O. assumption.
  - cbn in *. induction H.
    + cbn.
      assert (j: n + S arty = S n + arty). omega.
      rewrite j. apply (IHarty (tunit (TRel 0)) (S n)).
      constructor; intuition.
    + cbn.
      assert (j: n + S arty = S n + arty). omega.
      rewrite j. apply (IHarty _ (S n)); constructor; intuition.
      * constructor. apply (proj1 lift_pres_WFTrm). assumption.
        apply (proj1 (proj2 lift_pres_WFTrm)). assumption.
Qed.
       
Lemma WFTrm_etaExp_cnstr:
  forall xtra ts m, WFTrms ts m ->
               forall i n, WFTrm (etaExp_cnstr i n xtra ts) m.
Proof.
  intros. unfold etaExp_cnstr.
  eapply mkEtaLams_pres_WFTrm; try reflexivity. 
  apply mkEtaArgs_pres_WFtrm. apply treverse_pres_WFTrms.
  assumption.
Qed.
  
(***********
Goal
  forall dts x t, dnthBody x dts = Some t -> forall n, WFTrmDs dts n ->
                  isLambda t.
Proof.
  induction dts; induction x; intros.
  - cbv in H. discriminate.
  - cbv in H. discriminate.
  - cbv in H. myInjection H. inversion_Clear H0. assumption.
  - inversion_Clear H0. eapply IHdts; try eassumption.
Qed.


intros. inversion_Clear H. inversion_Clear H4.
  - unfold dnthBody in H0. cbn in H0. discriminate.
  - inversion_Clear H2.
    + unfold dnthBody in H0. destruct m.
      * cbn in H0. myInjection H0. assumption.
      * cbn in H0. discriminate.
    +         

      induction m; destruct dts; intros.
  - cbn in H0. discriminate.
  - cbn in H0. myInjection H0. inversion_Clear H.  inversion_Clear H3.
    assumption.
  - cbn in H0. discriminate.
  - unfold dnthBody in H0. cbn in H0. destruct (dnth m dts). destruct d.
    myInjection H0. eapply IHm.
                
    eapply IHm. constructor. constructor.

  
  induction dts; induction m; intros.
  - cbn in H0. discriminate.
  - cbn in H0. discriminate.
  - cbn in H0. myInjection H0. inversion_Clear H. eapply IHdts. eapply H.

    eapply IHdts.
    inversion_Clear H. inversion_Clear H4.
  
  
Lemma strip_presWFTrm:
  (forall t n, L2_5.term.WFTrm t n -> WFTrm (strip t) n) /\
  (forall ts n, L2_5.term.WFTrms ts n -> WFTrms (strips ts) n) /\
  (forall ds n, L2_5.term.WFTrmDs ds n -> WFTrmDs (stripDs ds) n).
Proof.
Admitted.
(********************
  apply L2.term.WFTrmTrmsDefs_ind; intros;
  try (cbn; try econstructor; eassumption).
  - cbn. case_eq (isL2Cnstr fn); intros.
    + destruct p, p. rewrite strips_pres_tlength. rewrite <- tcons_hom. admit.
    + induction ts.
      * cbn. constructor; try assumption. intros h.
        destruct h as [x0 [x1 [x2 j]]].         
        destruct fn; cbn in j; try discriminate.
       ****)
*****************)
  
(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:string.

Inductive PoccTrm : Term -> Prop :=
| PoLambdaBod: forall s bod, PoccTrm bod -> PoccTrm (TLambda s bod)
| PoLetInDfn: forall s dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn bod)
| PoLetInBod: forall s dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn bod)
| PoAppL: forall fn a, PoccTrm fn -> PoccTrm (TApp fn a)
| PoAppA: forall fn a, PoccTrm a -> PoccTrm (TApp fn a)
| PoConst: PoccTrm (TConst nm)
     (***
| PoCaseA: forall n mch brs, PoccTrm (TCase (mkInd nm n) mch brs)
***)
| PoCaseL: forall n mch brs, PoccTrm mch -> PoccTrm (TCase n mch brs)
| PoCaseR: forall n mch brs, PoccDefs brs -> PoccTrm (TCase n mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstrI: forall m1 m2 args,
              PoccTrm (TConstruct (mkInd nm m1) m2 args)
| PoCnstrA: forall i m args,
             PoccTrms args -> PoccTrm (TConstruct i m args)
with PoccTrms : Terms -> Prop :=
| PoThd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
| PoTtl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccDefs : Defs -> Prop :=
| PoDhd_bod: forall dn db dra ds,
           PoccTrm db -> PoccDefs (dcons dn db dra ds)
| PoDtl: forall dn db dra ds,
           PoccDefs ds -> PoccDefs (dcons dn db dra ds).
Hint Constructors PoccTrm PoccTrms PoccDefs.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poTrms_ind' := Minimality for PoccTrms Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsDefs_ind from poTrm_ind', poTrms_ind', poDefs_ind'.

Lemma Pocc_TConst: forall s2, PoccTrm (TConst s2) -> nm = s2.
intros s2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TConst: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma Pocc_TCnstr:
  forall ipkgNm inum cnum args,
    PoccTrm (TConstruct ((mkInd ipkgNm inum)) cnum args) ->
    nm = ipkgNm \/ PoccTrms args.
intros ipkgNm inum cnum args h. inversion h; intuition. 
Qed.

Lemma notPocc_TCnstr:
  forall ipkgNm inum cnum args,
    ~ PoccTrm (TConstruct ((mkInd ipkgNm inum)) cnum args) ->
    nm <> ipkgNm /\ ~ PoccTrms args.
intros ipkgNm inum cnum args h. intuition. elim h. rewrite <- H. 
apply PoCnstrI.
Qed.

Lemma PoccTrms_tappendl:
  forall ts us, PoccTrms ts -> PoccTrms (tappend ts us).
induction 1; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappendr:
  forall us, PoccTrms us -> forall ts, PoccTrms (tappend ts us).
induction 1; induction ts0; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
- simpl in IHPoccTrms. apply PoTtl. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappend_tcons:
  forall u, PoccTrm u -> forall ts us, PoccTrms (tappend ts (tcons u us)).
intros. apply PoccTrms_tappendr. apply PoThd. assumption.
Qed.

Lemma PoccTrms_append_invrt:
  forall bs cs, PoccTrms (tappend bs cs) -> PoccTrms bs \/ PoccTrms cs.
induction bs; intros cs h; simpl in h.
- intuition.
- inversion_Clear h.
  * left. apply PoThd. assumption.
  * destruct (IHbs _ H0).
    left. apply PoTtl. assumption.
    right. assumption.
Qed.

Lemma inverse_Pocc_TConstL: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma notPocc_TApp:
  forall t arg, ~ PoccTrm (TApp t arg) -> ~ PoccTrm t /\ ~ PoccTrm arg.
intuition.
Qed.

Lemma Pocc_TApp:
  forall t arg, PoccTrm (TApp t arg) -> PoccTrm t \/ PoccTrm arg.
inversion 1; intuition.
Qed.

Lemma notPocc_TLambda:
  forall n bod, ~ PoccTrm (TLambda n bod) -> ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TLetIn:
  forall n dfn bod, ~ PoccTrm (TLetIn n dfn bod) ->
                   ~ PoccTrm dfn /\ ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TCase:
  forall n mch brs, ~ PoccTrm (TCase n mch brs) ->
                    ~ PoccTrm mch /\ ~ PoccDefs brs.
intuition. 
Qed.

Lemma notPocc_TFix:
  forall ds m, ~ PoccTrm (TFix ds m) -> ~ PoccDefs ds.
intuition. 
Qed.

Lemma notPoccTrms:
  forall t ts, ~ PoccTrms (tcons t ts) -> ~ PoccTrm t /\ ~ PoccTrms ts.
intuition. 
Qed.

Lemma PoccTrms_tcons:
  forall t ts, PoccTrms (tcons t ts) -> PoccTrm t \/ PoccTrms ts.
inversion 1; intuition. 
Qed.

Lemma notPoccDefs:
  forall nm bod rarg ds, ~ PoccDefs (dcons nm bod rarg ds) ->
                         ~ PoccTrm bod /\ ~ PoccDefs ds.
intuition. 
Qed.

Lemma PoccTrms_append:
  forall ts1 ts2, PoccTrms (tappend ts1 ts2) -> PoccTrms ts1 \/ PoccTrms ts2.
  induction ts1; intros ts2 h. simpl in h.
  - right. assumption.
  - inversion_Clear h.
    + left. apply PoThd. assumption.
    + destruct (IHts1 _ H0).
      * left. apply PoTtl. assumption.
      * right. assumption.
Qed.


Lemma tIn_Pocc_Poccs:
  forall t ts us, tIn t ts -> PoccTrm t -> PoccTrms (tappend ts us).
induction ts; intros us h1 h2.
- inversion h1.
- inversion h1.
  + subst. simpl. apply PoThd. assumption.
  + simpl.  apply PoTtl. apply IHts; assumption.
Qed.


(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable (tin:Term).

Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| ILambda: forall n nm bod ibod,
             Instantiate (S n) bod ibod -> 
             Instantiate n (TLambda nm bod) (TLambda nm ibod)
| ILetIn: forall n nm dfn bod idfn ibod,
               Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
               Instantiate n (TLetIn nm dfn bod) (TLetIn nm idfn ibod)
| IApp: forall n t a it ia ,
          Instantiate n t it -> Instantiate n a ia ->
          Instantiate n (TApp t a) (TApp it ia)
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IAx: forall n, Instantiate n TAx TAx
| IConstruct: forall n ind m1 args iargs,
              Instantiates n args iargs ->
              Instantiate n (TConstruct ind m1 args)
                          (TConstruct ind m1 iargs)
| ICase: forall n np s ts is its,
           Instantiate n s is -> InstantiateDefs n ts its ->
           Instantiate n (TCase np s ts) (TCase np is its)
| IFix: forall n d m id, 
          InstantiateDefs (n + dlength d) d id ->
          Instantiate n (TFix d m) (TFix id m)
| IProof: forall n, Instantiate n TProof TProof
| IWrong: forall n, Instantiate n TWrong TWrong                                
with Instantiates: nat -> Terms -> Terms -> Prop :=
| Inil: forall n, Instantiates n tnil tnil
| Icons: forall n t ts it its,
           Instantiate n t it -> Instantiates n ts its ->
           Instantiates n (tcons t ts) (tcons it its)
with InstantiateDefs: nat -> Defs -> Defs -> Prop :=
| Idnil: forall n, InstantiateDefs n dnil dnil
| Idcons: forall n nm bod rarg ds ibod ids,
            Instantiate n bod ibod ->
            InstantiateDefs n ds ids ->
            InstantiateDefs n (dcons nm bod rarg ds)
                            (dcons nm ibod rarg ids).
Hint Constructors Instantiate Instantiates InstantiateDefs.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with Instantiates_ind' := Induction for Instantiates Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstInstsDefs_ind from 
         Instantiate_ind', Instantiates_ind', InstantiateDefs_ind'.

Lemma InstantiateDefs_pres_dlength:
  forall n ds ids, InstantiateDefs n ds ids -> dlength ds = dlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiates_pres_tlength:
  forall n ds ids, Instantiates n ds ids -> tlength ds = tlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiates_no_gen:
  (~ PoccTrm tin) ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, Instantiates n ts ss -> PoccTrms ss -> PoccTrms ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstInstsDefs_ind; intros; auto;
           try (solve [inversion_Clear H0; constructor; intuition]).
  - contradiction.
  - inversion H.
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoLetInBod. intuition.
  - destruct (Pocc_TApp H1) as [hit | hiats]; intuition.
  - inversion_Clear H1.
    + apply PoCaseL. intuition.
    + apply PoCaseR. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoTtl. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoDtl. intuition.
Qed.

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a => TApp (instantiate n t) (instantiate n a)
    | TLambda nm bod => TLambda nm (instantiate (S n) bod)
    | TCase np s ts => TCase np (instantiate n s) (instantiateDefs n ts)
    | TLetIn nm tdef bod =>
         TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TConstruct i m args => TConstruct i m (instantiates n args)
    | x => x
  end
with instantiates (n:nat) (args:Terms) {struct args} : Terms :=
       match args with
         | tnil => tnil
         | tcons t ts => tcons (instantiate n t) (instantiates n ts)
       end
with instantiateDefs (n:nat) (ds:Defs) : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm bod rarg ds =>
           dcons nm (instantiate n bod) rarg (instantiateDefs n ds)
       end.

Lemma instantiates_pres_tlength:
  forall n ds, tlength (instantiates n ds) = tlength ds.
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma instantiateDefs_pres_dlength:
  forall n ds, dlength ds = dlength (instantiateDefs n ds).
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, Instantiates n ts its -> instantiates n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
Proof.
  apply InstInstsDefs_ind; intros; cbn; intuition; try (subst; reflexivity).
  - rewrite nat_compare_EQ. reflexivity.
  - rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
  - rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall ts n, Instantiates n ts (instantiates n ts)) /\
  (forall (ds:Defs) n, InstantiateDefs n ds (instantiateDefs n ds)).
Proof.
  apply TrmTrmsDefs_ind; intros; cbn; try (solve [constructor]);
  try (solve[constructor; intuition]).
  - unfold instantiate. destruct (lt_eq_lt_dec n0 n) as [[h | h] | h].
    + rewrite (proj1 (nat_compare_lt _ _) h). apply IRelLt. assumption.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). subst. apply IRelEq.
    + rewrite (proj1 (nat_compare_gt _ _)). apply IRelGt.
      assumption. assumption.
Qed.

Lemma instant_pres_PoccTrm:
  (forall tbod, PoccTrm tbod -> forall n, PoccTrm (instantiate n tbod)) /\
  (forall ts, PoccTrms ts -> forall n, PoccTrms (instantiates n ts)) /\
  (forall (Ds:Defs), PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsDefs_ind; intros; cbn; try solve [constructor; trivial];
  try (inversion_Clear H1; constructor; eapply H0; eassumption).
Qed.


Lemma instantiate_is_Const:
  forall n tbod,
    instantiate n tbod = TConst nm -> 
    (tbod = TRel n /\ tin = TConst nm) \/ (tbod = TConst nm).
Proof.
  induction tbod; intros h; simpl; intuition; try discriminate.
  - unfold instantiate in h.
    case_eq (nat_compare n n0); intros; rewrite H in h.
    + left. split. rewrite (nat_compare_eq _ _ H). reflexivity. assumption.
    + discriminate.
    + discriminate.
Qed.

Lemma instantiates_tnil:
  forall n, instantiates n tnil = tnil.
Proof.
  reflexivity.
Qed.

Lemma instantiates_pres_tappend:
  forall ts1 ts2 nin,
    instantiates nin (tappend ts1 ts2) =
    tappend (instantiates nin ts1) (instantiates nin ts2).
Proof.
  induction ts1; intros. reflexivity.
  cbn. rewrite IHts1. reflexivity.
Qed.

Lemma instantiates_pres_treverse:
  forall ts nin,
   instantiates nin (treverse ts) = treverse (instantiates nin ts).
Proof.
  induction ts; intros. reflexivity.
  cbn. rewrite instantiates_pres_tappend. rewrite IHts. reflexivity.
Qed.

Lemma instantiate_TConstruct:
  forall args n i m,
    instantiate n (TConstruct i m args) =
    TConstruct i m (instantiates n args).
Proof.
  destruct args; intros; reflexivity.
Qed.

Lemma instantiate_TLambda:
  forall n nm bod,
    instantiate n (TLambda nm bod) =
    TLambda nm (instantiate (S n) bod).
Proof.
 intros; reflexivity.
Qed.

Lemma instantiate_TCase:
  forall n np s ts,
    instantiate n (TCase np s ts) =
    TCase np (instantiate n s) (instantiateDefs n ts).
Proof.
  destruct ts; intros; reflexivity.
Qed.

Lemma instantiate_TFix:
  forall n ds m,
    instantiate n (TFix ds m) =
    TFix (instantiateDefs (n + (dlength ds)) ds) m.
Proof.
  destruct ds; intros; reflexivity.
Qed.

Lemma instantiates_tcons:
   forall n arg args,
    instantiates n (tcons arg args) =
    tcons (instantiate n arg) (instantiates n args).
Proof.
  reflexivity.
Qed.
 
Lemma instantiates_dcons:
   forall n nm t m ds,
    instantiateDefs n (dcons nm t m ds) =
    dcons nm (instantiate n t) m (instantiateDefs n ds).
Proof.
  reflexivity.
Qed.
 
Lemma instantiates_tappend:
  forall args n brgs,
    instantiates n (tappend args brgs) =
    tappend (instantiates n args) (instantiates n brgs).
Proof.
  induction args; intros. reflexivity.
  - change (instantiates n (tcons t (tappend args brgs)) =
            tcons (instantiate n t)
                   (tappend (instantiates n args)
                            (instantiates n brgs))).
    rewrite  instantiates_tcons. rewrite IHargs. reflexivity.
Qed.

Lemma instantiate_TApp_commute:
  forall arg n fn,
    instantiate n (TApp fn arg) =
    TApp (instantiate n fn) (instantiate n arg).
Proof.
  intros. cbn. reflexivity. 
Qed.

Lemma instantiate_mkApp_commute:
  forall fn args n,
    instantiate n (mkApp fn args) =
    mkApp (instantiate n fn) (instantiates n args).
Proof.
  intros. functional induction (mkApp fn args).
  - destruct fn; cbn; try reflexivity. 
  - destruct fn; rewrite IHt; cbn; try reflexivity.
Qed.

Lemma instantiate_noLift:
  (forall t  m, instantiate m (lift m t) = t) /\
  (forall ts m, instantiates m (lifts m ts) = ts) /\
  (forall ds m, instantiateDefs m (liftDs m ds) = ds).
Proof.
  apply TrmTrmsDefs_ind; intros; try reflexivity.
  - unfold lift. case_eq (n ?= m); intros j.
    + cbn. Compare_Prop. subst. rewrite (proj2 (Nat.compare_lt_iff _ _)).
      reflexivity. omega.
    + cbn. Compare_Prop. rewrite (proj2 (Nat.compare_gt_iff _ _)).
      reflexivity. omega.
    + cbn. Compare_Prop. erewrite (proj2 (Nat.compare_lt_iff _ _)).
      reflexivity. omega.
  - cbn. apply f_equal. rewrite <- H at 2. reflexivity.
  - cbn. apply f_equal2.
    + apply H.
    + rewrite <- H0 at 2. reflexivity.
  - cbn. apply f_equal2. apply H. apply H0.
  - cbn. apply f_equal3; try reflexivity. apply H.
  - cbn. apply f_equal2. apply H. apply H0.
  - cbn. rewrite liftDs_pres_dlength.
    apply f_equal2; try reflexivity. apply H.
  - cbn. apply f_equal2. apply H. apply H0.
  - cbn. apply f_equal3; try reflexivity. apply H. apply H0.
Qed.

Lemma lift_lift:
  (forall t i k, i < S k ->
                 lift (S k) (lift i t) = lift i (lift k t)) /\
  (forall ts i k, i < S k ->
                  lifts (S k) (lifts i ts) = lifts i (lifts k ts)) /\
  (forall ds i k, i < S k ->
                  liftDs (S k) (liftDs i ds) = liftDs i (liftDs k ds)).
Proof.
  apply TrmTrmsDefs_ind; intros; try reflexivity.
  - unfold lift at 4; unfold lift at 2.
    case_eq (n ?= i); intros; case_eq (n ?= k); intros;
    repeat Compare_Prop; subst; try omega; cbn.
    + subst. rewrite (@match_cn_Eq i); try reflexivity.
      destruct i. reflexivity. rewrite (@match_cn_Gt _ i).
      reflexivity. omega.
    + rewrite (match_cn_Lt j0); try omega.
      rewrite (@match_cn_Eq i); reflexivity.
    + rewrite (match_cn_Lt j0); try omega.
      rewrite (@match_cn_Lt n). reflexivity. omega.
    + rewrite (@match_cn_Eq k); try omega.
      destruct i. reflexivity.
      rewrite (@match_cn_Gt k). reflexivity. omega.
    + rewrite (match_cn_Lt j). rewrite (@match_cn_Gt n). reflexivity. omega.
    + rewrite (@match_cn_Gt n); try omega.
      destruct i. reflexivity.
      case_eq (n ?= i); intros; Compare_Prop; try omega. reflexivity.
  - cbn. apply f_equal. rewrite H; try omega. reflexivity.
  - cbn. apply f_equal2. apply H. omega. apply H0. omega.
  - cbn. apply f_equal2. apply H. omega. apply H0. omega.
  - cbn. apply f_equal. apply H. omega.
  - cbn. apply f_equal2. apply H. omega. apply H0. omega.
  - simpl. apply f_equal2; try omega.
    assert (j: dlength d = dlength (liftDs (k + dlength d) d)).
    { rewrite liftDs_pres_dlength. reflexivity. }
    assert (j0: dlength d = dlength (liftDs (i + dlength d) d)).
    { rewrite liftDs_pres_dlength. reflexivity. }    
    rewrite H; try rewrite <- j; try rewrite <- j0. reflexivity. omega.
  - cbn. apply f_equal2. rewrite H; try omega. reflexivity.
    rewrite H0. reflexivity. omega.
  - cbn. apply f_equal4; try reflexivity.
    rewrite H; try omega. reflexivity.
    rewrite H0; try omega. reflexivity.
Qed.


Lemma lift_instantiate:
  (forall t nin n,
    nin < S n -> WFTrm tin 0 ->
      lift n (instantiate nin t) = instantiate nin (lift (S n) t)) /\
  (forall ts nin n,
    nin < S n -> WFTrm tin 0 ->
    lifts n (instantiates nin ts) =
    instantiates nin (lifts (S n) ts)) /\
  (forall ds nin n,
    nin < S n -> WFTrm tin 0 ->
    liftDs n (instantiateDefs nin ds) =
    instantiateDefs nin (liftDs (S n) ds)).
Proof.
  apply TrmTrmsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H; try omega; try reflexivity; assumption);
  try (cbn; rewrite H, H0; try omega; try reflexivity; assumption).
  - unfold instantiate at 1. unfold lift at 2.
    case_eq (nin ?= n); intros; case_eq (n ?= S n0); intros;
    repeat Compare_Prop; unfold instantiate; try omega.
    + erewrite (proj1 WF_nolift _ _ H0); try omega.
      rewrite (proj2 (Nat.compare_eq_iff _ _)). reflexivity. assumption.
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      rewrite j. cbn. rewrite (proj2 (Nat.compare_eq_iff _ _)); reflexivity.
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; Compare_Prop; try omega.
      reflexivity.      
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; Compare_Prop; try omega.
      apply f_equal. omega.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega.
      cbn. rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega.
      reflexivity.
  - change
      (TFix (liftDs (n0 + dlength (instantiateDefs (nin + dlength d) d))
                  (instantiateDefs (nin + dlength d) d)) n =
       TFix (instantiateDefs (nin + dlength (liftDs (S n0 + dlength d) d))
                             (liftDs (S n0 + dlength d) d)) n).
    erewrite <- instantiateDefs_pres_dlength.
    rewrite liftDs_pres_dlength.
    apply f_equal2; try reflexivity.
    erewrite H. reflexivity. omega. eassumption.
Qed.
    
Lemma instantiate_lift:
  (forall t nin n,
    n < S nin -> WFTrm tin 0 ->
      lift n (instantiate nin t) = instantiate (S nin) (lift n t)) /\
  (forall ts nin n,
    n < S nin -> WFTrm tin 0 ->
      lifts n (instantiates nin ts) = instantiates (S nin) (lifts n ts)) /\
  (forall t nin n,
    n < S nin -> WFTrm tin 0 ->
      liftDs n (instantiateDefs nin t) = instantiateDefs (S nin) (liftDs n t)).
Proof.
  apply TrmTrmsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H; try omega; try reflexivity; assumption);
  try (cbn; rewrite H, H0; try omega; try reflexivity; assumption).
  - unfold instantiate at 1. unfold lift at 2.
    case_eq (nin ?= n); intros; case_eq (n ?= n0); intros;
    repeat Compare_Prop; unfold instantiate; try omega.
    + subst. rewrite match_cn_Eq; try omega.
      erewrite (proj1 WF_nolift _ _ H0); try omega. reflexivity.
    + subst. rewrite match_cn_Eq; try omega.
      erewrite (proj1 WF_nolift _ _ H0); try omega. reflexivity.
    + rewrite match_cn_Lt; try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; repeat Compare_Prop; try omega.
      * assert (k0: S (Init.Nat.pred n) = n). omega.
        rewrite k0. reflexivity.
      * assert (k0: S (Init.Nat.pred n) = n). omega.
        rewrite k0. reflexivity.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega. cbn.
      rewrite match_cn_Eq; try omega. reflexivity.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega. cbn.
      rewrite match_cn_Lt; try omega. reflexivity.
    + rewrite match_cn_Gt; try omega. cbn. rewrite match_cn_Gt; try omega.
      reflexivity.
  - cbn. apply f_equal2; try reflexivity.
    rewrite H; try assumption.
    + rewrite <- instantiateDefs_pres_dlength. rewrite liftDs_pres_dlength.
      reflexivity.
    + rewrite <- instantiateDefs_pres_dlength. omega.
Qed.

Lemma instantiates_ttake:
  forall ts m n, ttake (instantiates n ts) m = instantiates n (ttake ts m).
Proof.
  induction ts; induction m; intros; try (cbn; reflexivity).
  -  cbn. rewrite IHts. reflexivity.
Qed.

Lemma instantiate_mkEtaLams:
  forall xtra nin i x args,
    instantiate nin (mkEtaLams xtra i x args) =
    mkEtaLams xtra i x (instantiates (nin + xtra) args).
Proof.
  induction xtra; intros.
  - cbn. rewrite plus_0_r. reflexivity.
  - cbn. rewrite IHxtra.
    assert (j: S nin + xtra = nin + S xtra). omega.
    rewrite j. reflexivity.
Qed.                                                  
  
Lemma instantiates_mkEtaArgs:
  forall xtra n ts, WFTrm tin 0 ->
                    mkEtaArgs xtra (instantiates n ts) =
                    instantiates (n + xtra) (mkEtaArgs xtra ts).
Proof.
  induction xtra; intros.
  - cbn. rewrite instantiates_pres_treverse. rewrite <- plus_n_O. reflexivity.
  - cbn. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    erewrite <- IHxtra; try assumption.
    rewrite (proj1 (proj2 (instantiate_lift)));
      try omega; try assumption.
    rewrite instantiates_tcons; try eassumption. reflexivity.
Qed.
               
Lemma instantiate_etaExp:
  forall m i n x, WFTrm tin 0 ->
    etaExp_cnstr i n m tnil = instantiate x (etaExp_cnstr i n m tnil).
Proof.
  induction m; intros. reflexivity.
  - cbn. apply f_equal.
    rewrite instantiate_mkEtaLams. rewrite <- instantiates_mkEtaArgs.
    cbn. reflexivity. assumption.
Qed.

End Instantiate_sec.
End PoccTrm_sec.


(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) : Term := instantiate arg 0 bod.


Definition whCaseStep (cstrNbr:nat) (args:Terms) (brs:Defs): option Term := 
  match dnthBody cstrNbr brs with
    | Some t => Some (mkApp t args)
    | None => None
  end.

(** Unfolding a Fixpoint **)
(** "dts" is a list of the mutual fixpoint definitions
*** "m" tells which of the definitions is being called
**)
Definition whFixStep (dts:Defs) (m:nat) : option Term :=
  let ldts := dlength dts in
  match dnthBody m dts with
    | Some body => Some (fold_left
                           (fun bod ndx => instantiate (TFix dts ndx) 0 bod)
                           (list_to_zero ldts) body)
    | None => None
  end.

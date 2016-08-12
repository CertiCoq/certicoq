(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Logic.JMeq.
Require Import Omega.
Require Import L2.L2.
Require Import L3.term.
Require Import L3.program.
Require Import L3.wndEval.
Require Import L3.wcbvEval.
Require Import L3.wNorm.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Defs := L2.compile.Defs.
Definition L2Environ := AstCommon.environ L2.compile.Term.

Lemma TApp_hom:
  forall fn arg args,
    strip (L2.compile.TApp fn arg args) =
    let sarg := strip arg in
      let sargs := strips args in
      match fn with 
        | L2.compile.TConstruct i n arty =>
          etaExp_cnstr i n arty (tcons sarg sargs)
        | x => mkApp (strip x) (tcons sarg sargs)
       end.
  induction fn; cbn; intros; try reflexivity.
Qed.
    
Lemma TFix_hom:
  forall defs n,
    strip (L2.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm bod,
    strip (L2.compile.TProd nm bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm bod,
    strip (L2.compile.TLambda nm bod)  = TLambda nm (strip bod).
Proof.
  reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn bod,
    strip (L2.compile.TLetIn nm dfn bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n mch brs,
    strip (L2.compile.TCase n mch brs) =
    TCase n (strip mch) (strips brs).
reflexivity.
Qed.

Lemma TConstruct_hom:
  forall i n arty,
    strip (L2.compile.TConstruct i n arty) = etaExp_cnstr i n arty tnil.
Proof.
  reflexivity.  
Qed.

Lemma TInd_hom:
  forall i,
        strip (L2.compile.TInd i) = (TInd i).
Proof.
  reflexivity.
Qed.

Lemma Lookup_hom:
  forall (p:environ L2Term) (s:string) ec,
    Lookup s p ec -> Lookup s (stripEnv p) (stripEC ec).
Proof.
  induction 1; destruct t.
  - cbn. apply LHit.
  - cbn. apply LHit.
  - cbn. apply LMiss; assumption. 
  - cbn. apply LMiss; assumption. 
Qed.

Lemma dlength_hom:
  forall ds, L2.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. cbn. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L2.term.tappend ts us) = tappend (strips ts) (strips us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.


Lemma mkApp_hom:
forall fn args,
  strip (L2.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  induction fn; induction args; cbn; try reflexivity.
  - rewrite L2.term.tappend_tnil. reflexivity.
  - rewrite tappend_hom. rewrite tcons_hom.
    admit.
Admitted.

Lemma instantiate_hom:
    (forall bod arg n, strip (L2.term.instantiate arg n bod) =
                   instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L2.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L2.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - change (strip (L2.term.instantiate arg n t) =
            (instantiate (strip arg) n (strip t))).
    rewrite H. reflexivity.
  - change (TProd n (strip (L2.term.instantiate arg (S n0) t)) =
            (TProd n (instantiate (strip arg) (S n0) (strip t)))).
    rewrite H. reflexivity.
  - change (TLambda n (strip (L2.term.instantiate arg (S n0) t)) =
            (TLambda n (instantiate (strip arg) (S n0) (strip t)))).
    rewrite H. reflexivity.
  - change (TLetIn n (strip (L2.term.instantiate arg n0 t))
                   (strip (L2.term.instantiate arg (S n0) t0)) =
            (TLetIn n (instantiate (strip arg) n0 (strip t))
                    (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H. rewrite H0. reflexivity.
  - change (strip (L2.term.mkApp
                     (L2.term.instantiate arg n t)
                     (L2.compile.tcons (L2.term.instantiate arg n t0)
                                       (L2.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L2.compile.TApp t t0 t1))).
    admit.
  (*************
  rewrite TApp_hom. destruct t; cbn.
  change
    (strip (L2.term.mkApp (L2.term.instantiate arg n t)
                          (L2.compile.tcons (L2.term.instantiate arg n t0)
                                         (L2.term.instantiates arg n t1))) =
     (mkApp (instantiate (strip arg) n (strip t))
            (tcons (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (strips t1))))).
  rewrite <- H. rewrite <- H0. rewrite <- H1. 
  rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
   *********************)
  - cbn. induction n0; try reflexivity. cbn. admit.
    
  - change (TCase p (strip (L2.term.instantiate arg n t))
                    (strips (L2.term.instantiates arg n t0)) =
              (TCase p (instantiate (strip arg) n (strip t))
                     (instantiates (strip arg) n (strips t0)))).
    rewrite H0. rewrite H. reflexivity.
  - change (TFix (stripDs (L2.term.instantiateDefs
                             arg (n0 + L2.term.dlength d) d)) n =
            (TFix (instantiateDefs (strip arg)
                                   (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2.term.instantiate arg n t))
                  (strips (L2.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2.term.instantiate arg n1 t)) n0
                  (stripDs (L2.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H. reflexivity.
Admitted.

(*****
Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L2.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
intros bod arg args.
unfold L1_5.term.whBetaStep, whBetaStep.
rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.
 *****)

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L2.term.whBetaStep bod arg args) =
    mkApp (whBetaStep (strip bod) (strip arg)) (strips args).
Admitted.
(*******
Proof.
  induction args; cbn; intros.
  - unfold L2.term.whBetaStep, whBetaStep.
    rewrite L2.term.mkApp_tnil_ident. apply (proj1 instantiate_hom).
  - unfold L2.term.whBetaStep, whBetaStep.
    unfold L2.term.whBetaStep, whBetaStep in IHargs.
    rewrite <- (proj1 instantiate_hom) in IHargs.
    

 rewrite <- (proj1 instantiate_hom). 
   unfold mkApp.
    destruct (L2.term.instantiate arg 0 bod); cbn.
******)

(*********************
Lemma WcbvEval_hom:
  forall (p:L2Env), 
  (forall t t': L2Term, L2.wcbvEval.WcbvEval p t t' ->
                        L3.wcbvEval.WcbvEval (L3.compile.stripEnv p)
                                             (L3.compile.strip t)
                                             (L3.compile.strip t')) /\
  (forall ts ts', L2.wcbvEval.WcbvEvals p ts ts' ->
                  L3.wcbvEval.WcbvEvals (L3.compile.stripEnv p)
                                        (L3.compile.strips ts)
                                        (L3.compile.strips ts')).
Proof.
  intros p.
  apply L2.wcbvEval.WcbvEvalEvals_ind; cbn; intros; try reflexivity;
  try intuition; try (rewrite <- H; rewrite <- H0; constructor).
  - induction arty.
    + constructor. constructor.
    + cbn. rewrite mkEta_under_Lambda. constructor. 
  - econstructor. unfold LookupDfn in l. unfold LookupDfn. apply (Lookup_hom l).
    assumption.
  - destruct (L2.term.isLambda_dec fn).
    + destruct i as [x0 [x1 j0]]. rewrite j0. induction args; cbn.
      * repeat econstructor. inversion_Clear H0. eassumption.
        rewrite whBetaStep_hom in H1.
        
exact H1.
    


    
  - destruct (L2.term.isLambda_dec fn).
    + destruct i as [x0 [x1 j0]]. rewrite j0. cbn; destruct a1; cbn.
      assert (k:= TApp_hom (L2.compile.TLambda x0 x1)). cbn in k.


    ; destruct args; cbn.
    + econstructor. inversion w. 
    
  - unfold LookupDfn in l. rewrite (Lookup_lookup l).
    econstructor. unfold LookupDfn. apply Lookup_hom.
    inversion_Clear l.

    
    inversion_Clear l. cbn. rewrite string_eq_bool_rfl.
    unfold program.ecAx. unfold AstCommon.ecAx. cbn.
    constructor.
    Check (stripEnv_not_LookupAx p).
    Check (Lookup_hom l). destruct (lookup nm p).
    + constructor. 
    + destruct e.
      * unfold AstCommon.LookupDfn.inversion l.
      * eapply wConst. unfold AstCommon.LookupDfn. Print AstCommon.ecAx.
        unfold AstCommon.ecAx in l.
        change ((@AstCommon.Lookup Term) nm p (AstCommon.ecAx Term)) in l.
        Check (Lookup_hom l).

        rewrite <- H. eapply wConst.
        unfold AstCommon.LookupDfn.
        Check Lookup_hom. apply Lookup_hom.
      unfold LookupAx in l.

    rewrite <- H0. rewrite <- H1.
    
  - myInjection H. myInjection H0. constructor.
  - case_eq (strip p bod); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
  - case_eq (strip p bod); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
  - intuition.
  - case_eq (etaExp_cnstr p i r tnil); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
*******)


(**** L2 and L3 agree on cbv evaluation  ****
Lemma wndEval_types_irrelevant:
  forall (p:L2Environ),
    (forall (t s:L2Term),
       L2.wcbvEval.WcbvEval p t s ->
       WcbvEval (stripEnv p) (strip p t) (strip p s))  /\
    (forall ts ss,
       L2.wcbvEval.WcbvEvals p ts ss ->
       WcbvEvals (stripEnv p) (strips p ts) (strips p ss)).
Proof.
  intros p.
  apply L2.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[constructor; trivial]); try assumption.
  - admit. (** rewrite TConstruct_hom.  cbn. **)
  - unfold LookupAx in l. cbn. assert (j:= Lookup_lookup l). 
    Check j. Check (lookup nm p).
    destruct (lookup nm p).
    + destruct e. refine (wConst _ _). unfold AstCommon.LookupDfn.
    rewrite j.

    
  - rewrite TFix_hom. rewrite TFix_hom. 
    
  - change (strip p t = Some tt) in H0. eapply H; assumption.
  - unfold strip in H. unfold strip in H0. rewrite H in H0.
    myInjection H0. clear H0. unfold etaExp_cnstr in H.
    destruct (cnstrArity p i r).
    + destruct (PeanoNat.Nat.compare (tlength tnil) n).
      * myInjection H. constructor. constructor.
      * myInjection H. clear H. rewrite <- minus_n_O.
        { induction n.
          - simpl. constructor. constructor.
          - change 
              (WcbvEval pp
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)).
            simpl. rewrite mkEta_under_Lambda. constructor. }
      * discriminate.
    + discriminate.
  - rewrite (strip_Ind_invrt H). rewrite (strip_Ind_invrt H0). constructor.
  - unfold strip in H. unfold strip in H0. myInjection H. myInjection H0.
    constructor.
  -





Qed.

***)


(***  scratch below  *****
Section FlatApp.
Variable flatApp: L2Term -> Term.
Fixpoint flatApps (ts:L2Terms) : Terms :=
  match ts with
    | L2.term.tnil => tnil
    | L2.term.tcons s ss => tcons (flatApp s) (flatApps ss)
  end.
Fixpoint flatAppDs (ts:L2Defs) : Defs :=
  match ts with
    | L2.term.dnil => dnil
    | L2.term.dcons nm bod n ds => dcons nm (flatApp bod) n (flatAppDs ds)
  end.
Fixpoint mkApp (fn:Term) (l:L2Terms) : Term :=
    match l with
      | L2.term.tnil => fn
      | L2.term.tcons b t => mkApp (TApp fn (flatApp b)) t
    end.
End FlatApp.

Function flatApp (t:L2Term) : Term :=
  match t with
    | L2.term.TRel n => TRel n
    | L2.term.TSort s => TSort s
    | L2.term.TProd nm bod => TProd nm (flatApp bod)
    | L2.term.TLambda nm bod => TLambda nm (flatApp bod)
    | L2.term.TLetIn nm dfn bod => TLetIn nm (flatApp dfn) (flatApp bod)
    | L2.term.TApp fn arg args =>
      match fn with 
        | L2.term.TConstruct i n =>
             TConstruct i n (tcons (flatApp arg) (flatApps args))
        | x => mkApp flatApp (flatApp x)
                     (tcons (flatApp arg) (flatApps flatApp args))
      end
    | L2.term.TConst nm => TConst nm
    | L2.term.TInd i => TInd i
    | L2.term.TConstruct i n => TConstruct i n tnil
    | L2.term.TCase n mch brs => TCase n (flatApp mch) (flatApps brs)
    | L2.term.TFix ds n => TFix (flatAppDs ds) n
  end.
***)

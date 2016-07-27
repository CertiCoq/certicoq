(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
(******)

Require L2.compile.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Logic.JMeq.
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


Lemma strip_Lam_invrt:
  forall p nm bod tt,
        strip p (L2.compile.TLambda nm bod) = Ret tt ->
        exists sbod, strip p bod = Ret sbod /\ tt = TLambda nm sbod.
Proof.
  induction tt; simpl; intros. 
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TRel n)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TSort s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret TProof) in H.
     destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TProd n tt)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TLambda n tt)) in H.
    destruct (strip p bod).
    + discriminate. 
    + myInjection H. exists tt. intuition.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TLetIn n tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TApp tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TConst s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret TAx) in H.
    destruct (strip p bod); discriminate.    
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TInd i)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TConstruct i n t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TCase p0 tt t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TFix d n)) in H.
    destruct (strip p bod); discriminate.
Qed.

Lemma strip_Prod_invrt:
  forall p nm bod tt,
        strip p (L2.compile.TProd nm bod) = Ret tt ->
        exists sbod, strip p bod = Ret sbod /\ tt = TProd nm sbod.
Proof.
  induction tt; simpl; intros. 
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TRel n)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TSort s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret TProof) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TProd n tt)) in H.
    destruct (strip p bod). 
    + discriminate.
    + myInjection H. exists tt. intuition.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TLambda n tt)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TLetIn n tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TApp tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TConst s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret TAx) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TInd i)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TConstruct i n t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TCase p0 tt t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TFix d n)) in H.
    destruct (strip p bod); discriminate.
Qed.

Lemma strip_Construct_invrt:
  forall p i r tt,
        strip p (L2.compile.TConstruct i r) = Ret tt ->
        etaExp_cnstr p i r tnil = Ret tt.
Proof.
  induction tt; unfold strip; simpl; intros; try assumption.
Qed.
 
Lemma strip_Ind_invrt:
  forall p i tt,
        strip p (L2.compile.TInd i) = Ret tt -> tt = (TInd i).
Proof.
  induction tt;  simpl; intros; try discriminate.
  myInjection H. reflexivity.
Qed.

(********
Lemma WcbvEval_hom:
  forall (p:AstCommon.environ L2Term) L3p, stripEnv p = Ret L3p ->
  (forall t t': L2Term, L2.wcbvEval.WcbvEval p t t' ->
    forall L3t, strip p t = Ret L3t ->
    forall L3t', strip p t' = Ret L3t' ->
        WcbvEval L3p L3t L3t') /\
  (forall ts ts', L2.wcbvEval.WcbvEvals p ts ts' ->
    forall L3ts, strips p ts = Ret L3ts ->
    forall L3ts', strips p ts' = Ret L3ts' ->
                  WcbvEvals L3p L3ts L3ts') /\
  (forall ds ds', L2.wcbvEval.WcbvDEvals p ds ds' -> True).
(*************
    forall L3ds, stripDs p ds = Ret L3ds ->
    forall L3ds', stripDs p ds' = Ret L3ds' ->
                     WcbvDEvals L3p L3ds L3ds').
****************)
Proof.
  intros p L3p hp.
  apply L2.wcbvEval.WcbvEvalEvals_ind; cbn; intros; try reflexivity.
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
  forall p pp, stripEnv p = Some pp -> 
    (forall t s, L2.wcbvEval.WcbvEval p t s ->
     forall tt, strip p t = Some tt -> 
     forall ss, strip p s = Some ss ->
          WcbvEval pp tt ss) /\
    (forall ts ss, L2.wcbvEval.WcbvEvals p ts ss ->
     forall tss, strips p ts = Some tss -> 
     forall sss, strips p ss = Some sss ->
          WcbvEvals pp tss sss).
Proof.
  intros p pp h. apply L2.wcbvEval.WcbvEvalEvals_ind; simpl; intros.
  - destruct (strip_Lam_invrt _ _ _ H) as [x [j1x j2x]].
    destruct (strip_Lam_invrt _ _ _ H0) as [y [j1y j2y]].
    subst. rewrite j1x in j1y. myInjection j1y. constructor.
  - destruct (strip_Prod_invrt _ _ _ H) as [x [j1x j2x]].
    destruct (strip_Prod_invrt _ _ _ H0) as [y [j1y j2y]].
    subst. rewrite j1x in j1y. myInjection j1y. constructor.
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

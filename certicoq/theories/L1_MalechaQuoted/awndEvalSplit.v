(** Split wndEval into contractions (defined first) and
*** congruences (depending on contractions).
**)



Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Setoids.Setoid.
Require Import L1.term.
Require Import L1.program.
Require Import L1.wndEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(*** non-deterministic small step evaluation relation ***)
(*** first the contractions ***)
Inductive awndStep (p:environ) : Term -> Term -> Prop :=
| aConst: forall (s:string) (t:Term),
            LookupDfn s p t -> awndStep p (TConst s) t
| aBeta: forall (nm:name) (ty bod arg:Term) (args:Terms),
           awndStep p (TApp (TLambda nm ty bod) arg args)
                   (whBetaStep bod arg args)
     (* note: [instantiate] is total *)
| aLetIn: forall (nm:name) (dfn ty bod:Term),
            awndStep p (TLetIn nm dfn ty bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* np is the number of parameters of the datatype *)
| aCase0: forall (n:nat) (ty s:Term) (i:inductive) (brs:Terms),
            whCaseStep n tnil brs = Some s ->
            awndStep p (TCase 0 ty (TConstruct i n) brs) s
| aCasen: forall (np:nat) (ty s arg:Term) (i:inductive)
                 (args brs ts:Terms) (n:nat),
            tskipn np (tcons arg args) = Some ts ->
            whCaseStep n ts brs = Some s ->
            awndStep p (TCase np ty (TApp (TConstruct i n) arg args) brs) s
| aFix: forall (dts:Defs) (m:nat) (arg s:Term) (args:Terms),
          whFixStep dts m (tcons arg args) = Some s ->
          awndStep p (TApp (TFix dts m) arg args) s
| aCast: forall t ck ty, awndStep p (TCast t ck ty) t.
Hint Constructors awndStep.

(** now congruence steps, depend on contractions **)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches or Fix ***)
Inductive awndEval (p:environ) : Term -> Term -> Prop :=
| aStep: forall t r, awndStep p t r -> awndEval p t r
| aAppFn:  forall (t r arg:Term) (args:Terms),
              awndStep p t r ->
              awndEval p (TApp t arg args) (mkApp r (tcons arg args))
| aAppArg: forall (t arg brg:Term) (args:Terms),
              awndStep p arg brg ->
              awndEval p (TApp t arg args) (TApp t brg args)
| aAppArgs: forall (t arg:Term) (args brgs:Terms),
              awndEvals p args brgs ->
              awndEval p (TApp t arg args) (TApp t arg brgs)
| aProdTy:  forall (nm:name) (t1 t2 bod:Term),
              awndStep p t1 t2 ->
              awndEval p (TProd nm t1 bod) (TProd nm t2 bod)
| aLamTy:   forall (nm:name) (t1 t2 bod:Term),
              awndStep p t1 t2 ->
              awndEval p (TLambda nm t1 bod) (TLambda nm t2 bod)
| aLetInTy: forall (nm:name) (t1 t2 d bod:Term),
              awndStep p t1 t2 ->
              awndEval p (TLetIn nm d t1 bod) (TLetIn nm d t2 bod)
| aLetInDef:forall (nm:name) (t d1 d2 bod:Term),
              awndStep p d1 d2 ->
              awndEval p (TLetIn nm d1 t bod) (TLetIn nm d2 t bod)
| aCaseTy:  forall (np:nat) (ty uy mch:Term) (brs:Terms),
              awndStep p ty uy ->
              awndEval p (TCase np ty mch brs) (TCase np uy mch brs)
| aCaseArg: forall (np:nat) (ty mch can:Term) (brs:Terms),
              awndStep p mch can ->
              awndEval p (TCase np ty mch brs) (TCase np ty can brs)
| aCaseBrs: forall (np:nat) (ty mch:Term) (brs brs':Terms),
              awndEvals p brs brs' ->
              awndEval p (TCase np ty mch brs) (TCase np ty mch brs')
with awndEvals (p:environ) : Terms -> Terms -> Prop :=
     | aaHd: forall (t r:Term) (ts:Terms), 
               awndStep p t r ->
               awndEvals p (tcons t ts) (tcons r ts)
     | aaTl: forall (t:Term) (ts ss:Terms),
               awndEvals p ts ss ->
               awndEvals p (tcons t ts) (tcons t ss).
Hint Constructors awndEval awndEvals.
Scheme awndEval1_ind := Induction for awndEval Sort Prop
  with awndEvals1_ind := Induction for awndEvals Sort Prop.
Combined Scheme awndEvalEvals_ind from awndEval1_ind, awndEvals1_ind.

Goal 
  forall p t s, wndEval p t s -> WFaEnv p -> WFapp t -> awndEval p t s.
Proof.
  induction 1; intros hp ht; constructor; try (constructor; assumption).
  - eapply aCasen; eassumption.
  - inversion ht.
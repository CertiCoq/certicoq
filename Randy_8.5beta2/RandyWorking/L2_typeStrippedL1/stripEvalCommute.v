Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "." as L2.

Require Import Lists.List.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Arith.Compare_dec.
Require Import Arith.Peano_dec.
Require Import Setoid.
Require L1.L1.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1Term := L1.term.Term.
Definition L1Terms := L1.term.Terms.
Definition L1Defs := L1.term.Defs.

Function strip (t:L1Term) : Term :=
  match t with
    | L1.term.TRel n => TRel n
    | L1.term.TSort s => TSort s
    | L1.term.TCast t _ _ => TCast (strip t)
    | L1.term.TProd nm _ bod => TProd nm (strip bod)
    | L1.term.TLambda nm _ bod => TLambda nm (strip bod)
    | L1.term.TLetIn nm dfn _ bod => TLetIn nm (strip dfn) (strip bod)
    | L1.term.TApp fn arg args => TApp (strip fn) (strip arg) (strips args)
    | L1.term.TConst nm => TConst nm
    | L1.term.TInd i => TInd i
    | L1.term.TConstruct i m => TConstruct i m
    | L1.term.TCase n _ mch brs => TCase n (strip mch) (strips brs)
    | L1.term.TFix ds n => TFix (stripDs ds) n
  end
with strips (ts:L1Terms) : Terms := 
  match ts with
    | L1.term.tnil => tnil
    | L1.term.tcons t ts => tcons (strip t) (strips ts)
  end
with stripDs (ts:L1Defs) : Defs := 
  match ts with
    | L1.term.dnil => dnil
    | L1.term.dcons nm _ t m ds => dcons nm (strip t) m (stripDs ds)
  end.

(*** ???
Lemma strip_absorbs_mkApp_nil:
  forall t, mkApp (strip t) tnil = strip t.
induction t; simpl; try reflexivity.
- rewrite tappend_tnil. reflexivity.
Qed.
Hint Resolve strip_absorbs_mkApp_nil.
****)


Definition optStrip (t:option L1Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L1Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.

Function stripCnstrs (cs:list L1.program.Cnstr) : list Cnstr :=
  match cs with
    | nil => nil
    | cons (L1.program.mkCnstr str arity) cs =>
        cons (mkCnstr str arity) (stripCnstrs cs)
  end.
Function stripItyPack (its:L1.program.itypPack) : L2.program.itypPack :=
  match its with
    | nil => nil
    | (L1.program.mkItyp str itps) :: itpacks =>
         (L2.program.mkItyp str (stripCnstrs itps)) ::
                           stripItyPack itpacks
  end.
Function stripEc (ec:L1.program.envClass) : L2.program.envClass :=
  match ec with
    | L1.program.ecTrm t => L2.program.ecTrm (strip t)
    | L1.program.ecTyp itp => L2.program.ecTyp (stripItyPack itp)
  end.

Fixpoint stripEnv (p:L1.program.environ) : environ :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, (stripEc ec)) (stripEnv q)
  end.

Definition program_Program (pgm:program) : option Program :=
  match L1.malecha_L1.program_Program pgm (ret nil) with
    | Exc str => None
    | Ret pgm => Some {| env:= stripEnv (L1.program.env pgm);
                         main:= strip (L1.program.main pgm) |}
  end.
Definition term_Term (t:term) : option Term :=
  match L1.malecha_L1.term_Term t with
    | Exc str => None
    | Ret trm => Some (strip trm)
  end.

Lemma stripEnv_hom:
  forall str (ec:L1.program.envClass) p,
    stripEnv ((str, ec) :: p) = (str, (stripEc ec))::(stripEnv p).
induction p; destruct ec; try reflexivity.
Qed.

Lemma Lookup_hom:
 forall p s ec, L1.program.Lookup s p ec -> 
               Lookup s (stripEnv p) (stripEc ec).
induction 1; destruct t.
- change (Lookup s ((s, L2.program.ecTrm (strip t)) :: (stripEnv p))
                    (L2.program.ecTrm (strip t))).
  apply L2.program.LHit.
- change (Lookup s ((s, L2.program.ecTyp (stripItyPack i)) :: (stripEnv p))
                    (L2.program.ecTyp (stripItyPack i))).
  apply L2.program.LHit.
- change (Lookup s2 ((s1, L2.program.ecTrm (strip t)) :: (stripEnv p))
                     (stripEc ec)).
  apply L2.program.LMiss; assumption.
- change (Lookup s2 ((s1, L2.program.ecTyp (stripItyPack i)) :: (stripEnv p))
                     (stripEc ec)).
  apply L2.program.LMiss; assumption.
Qed.

Lemma LookupDfn_hom:
 forall p s t, L1.program.LookupDfn s p t -> 
               LookupDfn s (stripEnv p) (strip t).
unfold L1.program.LookupDfn, L2.program.LookupDfn. intros.
assert (j:= Lookup_hom H). exact j.
Qed.

Lemma dlength_hom:
  forall ds, L1.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L1.term.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L1.term.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm ty bod rarg ds,
    stripDs (L1.term.dcons nm ty bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L1.term.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom:
  forall m ds, optStrip (L1.term.dnthBody m ds) = dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma tnth_hom:
 forall ts n, optStrip (L1.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L1.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L1.term.tappend ts us) = tappend (strips ts) (strips us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L1.term.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
induction fn; intros arg args; try reflexivity.
Qed.

Lemma isApp_hom:
  forall t, isApp (strip t) -> L1.term.isApp t.
destruct t; simpl; intros h; destruct h as [x0 [x1 [x2 h]]]; try discriminate. 
- exists t1, t2, t3. reflexivity.
Qed.

Lemma mkApp_tcons_lem1:
  forall fn arg args,
    mkApp (mkApp fn (tcons arg args)) tnil = mkApp fn (tcons arg args).
Proof.
  destruct fn; intros arg args; simpl;
  try rewrite tappend_tnil; try reflexivity.
Qed.

Lemma mkApp_tcons_lem2:
 forall fn ts u s args,
   mkApp fn (tcons u (tappend ts (tcons s args))) =
   mkApp (mkApp fn (tcons u ts)) (tcons s args).
Proof.
  destruct fn; destruct ts; intros; try reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
Qed.

Lemma mkApp_hom:
forall fn args,
  strip (L1.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  induction fn; induction args; simpl; try reflexivity.
  - rewrite tappend_tnil. rewrite L1.term.tappend_tnil. reflexivity.
  - rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
Qed.

Lemma TCast_hom:
  forall tm ck ty, strip (L1.term.TCast tm ck ty) = TCast (strip tm).
reflexivity.
Qed.

Lemma instantiate_tappend_commute:
  forall ts us tin n,
    instantiates tin n (tappend ts us) =
    tappend (instantiates tin n ts) (instantiates tin n us).
induction ts; intros.
- reflexivity.
- change (tcons (instantiate tin n t) (instantiates tin n (tappend ts us)) =
          tcons (instantiate tin n t) (tappend (instantiates tin n ts)
                                               (instantiates tin n us))).
 rewrite IHts. reflexivity.
Qed.

Lemma instantiates_tcons_commute:
  forall tin n t ts,
         (instantiates tin n (tcons t ts)) = 
         (tcons (instantiate tin n t) (instantiates tin n ts)).
intros tin n t ts. reflexivity.
Qed.

Lemma instantiate_mkApp_commute:
forall tin n bod arg args,
  instantiate tin n (mkApp bod (tcons arg args)) =
  mkApp (instantiate tin n bod) (tcons (instantiate tin n arg)
                                       (instantiates tin n args)).
induction bod; simpl; intros; try reflexivity.
- change
    (mkApp (instantiate tin n bod1) 
           (tcons (instantiate tin n bod2)
                     (instantiates tin n (tappend t (tcons arg args)))) =
     mkApp (mkApp (instantiate tin n bod1)
                  (tcons (instantiate tin n bod2)
                         (instantiates tin n t)))
           (tcons (instantiate tin n arg) (instantiates tin n args))).
  rewrite mkApp_idempotent. simpl. 
  rewrite instantiate_tappend_commute. rewrite instantiates_tcons_commute.
  reflexivity.
Qed.

Lemma instantiate_mkApp_nil_commute:
forall tin n bod,
  instantiate tin n (mkApp bod tnil) = mkApp (instantiate tin n bod) tnil.
induction bod; simpl; intros; try reflexivity.
- destruct (lt_eq_lt_dec n n0) as [[h1 | h2 ] | h3].
  + unfold instantiate. rewrite (proj1 (nat_compare_lt _ _) h1). 
    simpl. reflexivity.
  + subst. unfold instantiate. rewrite (proj2 (nat_compare_eq_iff n0 n0)).
    * rewrite mkApp_idempotent. simpl. reflexivity.
    * reflexivity.
  + unfold instantiate. rewrite (proj1 (nat_compare_gt _ _) h3).
    simpl. reflexivity.
- rewrite tappend_tnil.
  change (instantiate tin n (TApp bod1 bod2 t) =
         mkApp (mkApp (instantiate tin n bod1)
                      (tcons (instantiate tin n bod2)
                             (instantiates tin n t)))
                      tnil).
  rewrite mkApp_idempotent. simpl. rewrite tappend_tnil. reflexivity. 
Qed.

Lemma instantiate_hom:
    (forall bod arg n, strip (L1.term.instantiate arg n bod) =
                   instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L1.term.instantiateDefs arg n ds) =
                    instantiateDefs (strip arg) n (stripDs ds)).
apply L1.term.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
- simpl. destruct (lt_eq_lt_dec n n0);
         unfold L1.term.instantiate; unfold instantiate.
  + destruct s.
    * rewrite (proj1 (nat_compare_gt n0 n)); trivial.
    * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
      rewrite mkApp_hom. rewrite tnil_hom. reflexivity.
  + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
- change (TCast (strip (L1.term.instantiate arg n t)) =
         (TCast (instantiate (strip arg) n (strip t)))).
  rewrite H. reflexivity.
- change (TProd n (strip (L1.term.instantiate arg (S n0) t0)) =
         (TProd n (instantiate (strip arg) (S n0) (strip t0)))).
  rewrite H0. reflexivity.
- change (TLambda n (strip (L1.term.instantiate arg (S n0) t0)) =
         (TLambda n (instantiate (strip arg) (S n0) (strip t0)))).
  rewrite H0. reflexivity.
- change (TLetIn n (strip (L1.term.instantiate arg n0 t))
                   (strip (L1.term.instantiate arg (S n0) t1)) =
         (TLetIn n (instantiate (strip arg) n0 (strip t))
                   (instantiate (strip arg) (S n0) (strip t1)))).
  rewrite H. rewrite H1. reflexivity.
- change (strip (L1.term.mkApp
                   (L1.term.instantiate arg n t)
                   (L1.term.tcons (L1.term.instantiate arg n t0)
                                  (L1.term.instantiates arg n t1))) =
          instantiate (strip arg) n (strip (L1.term.TApp t t0 t1))). 
  rewrite TApp_hom. 
  change
    (strip (L1.term.mkApp (L1.term.instantiate arg n t)
                          (L1.term.tcons (L1.term.instantiate arg n t0)
                                         (L1.term.instantiates arg n t1))) =
     (mkApp (instantiate (strip arg) n (strip t))
            (tcons (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (strips t1))))).
  rewrite <- H. rewrite <- H0. rewrite <- H1. 
  rewrite mkApp_hom. rewrite tcons_hom. reflexivity. 
- change (TCase n (strip (L1.term.instantiate arg n0 t0))
                (strips (L1.term.instantiates arg n0 t1)) =
         (TCase n (instantiate (strip arg) n0 (strip t0))
                (instantiates (strip arg) n0 (strips t1)))).
  rewrite H0. rewrite H1. reflexivity.
- change (TFix (stripDs (L1.term.instantiateDefs arg
                                              (n0 + L1.term.dlength d) d)) n =
         (TFix (instantiateDefs (strip arg)
                                (n0 + dlength (stripDs d)) (stripDs d)) n)).
  rewrite H. rewrite dlength_hom. reflexivity.
- change (tcons (strip (L1.term.instantiate arg n t))
                (strips (L1.term.instantiates arg n t0)) =
          tcons (instantiate (strip arg) n (strip t))
                (instantiates (strip arg) n (strips t0))).
  rewrite H. rewrite H0. reflexivity.
- change (dcons n (strip (L1.term.instantiate arg n1 t0)) n0
                  (stripDs (L1.term.instantiateDefs arg n1 d)) =
          dcons n (instantiate (strip arg) n1 (strip t0)) n0
                (instantiateDefs (strip arg) n1 (stripDs d))).
  rewrite H0. rewrite H1. reflexivity.
Qed.


Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L1.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
intros bod arg args.
unfold L1.term.whBetaStep, whBetaStep.
rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.

Lemma TConstruct_hom:  (****  WRONG: arity ****)
  forall i n , strip (L1.term.TConstruct i n) = TConstruct i n.
intros. simpl.  destruct i. reflexivity.
Qed.


Lemma optStrip_match:
  forall x (f:L1Term -> L1Term) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L1.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (strips brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L1.term.whCaseStep. simpl. 
  rewrite <- tnth_hom. destruct (L1.term.tnth n brs); simpl.
  + rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L1.term.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod, strip (L1.term.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm ty bod, strip (L1.term.TLambda nm ty bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L1.term.TLetIn nm dfn ty bod) = TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L1.term.TCase n ty mch brs) = TCase n (strip mch) (strips brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L1Term -> nat -> L1Term) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L1Term),
  (forall (s:L1Term) (n:nat), strip (F s n) = stripF (strip s) n) ->
  strip (fold_left F ns t) = fold_left stripF ns (strip t).
induction ns; intros t h.
- intuition.
- simpl. rewrite IHns.
  + rewrite h. reflexivity.
  + assumption.
Qed.

Lemma pre_whFixStep_hom:
  forall body dts args,
    pre_whFixStep (strip body) (stripDs dts) (strips args) =
    strip (L1.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L1.term.prop). rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L1.term.prop). simpl. reflexivity.
Qed.

Lemma whFixStep_hom:
  forall dts m args,
    optStrip (L1.term.whFixStep dts m args) =
    whFixStep (stripDs dts) m (strips args).
Proof.
  intros dts m args.
  unfold L1.term.whFixStep, whFixStep.
  case_eq (L1.term.dnthBody m dts); intros.
  - rewrite optStrip_hom. rewrite <- pre_whFixStep_hom.
    rewrite <- dnthBody_hom. rewrite H. simpl. reflexivity.
  - rewrite <- dnthBody_hom. rewrite H. reflexivity.
Qed.


(** The goal is to prove that if [wndEval.wndEval p t s] (unstripped),
*** then [wndEval (stripEnv p) (strip t) (strip s)] (stripped).
*** However the unstripped language has steps in type fields where the 
*** stripped language can make no step.  Thus we need "reflexive closure",
*** allowing null steps for the stripped language.
**)
Inductive wndEvalRC: environ -> Term -> Term -> Prop :=
| wERCrfl: forall p t, wndEvalRC p t t
| wERCstep: forall p t s, wndEval p t s -> wndEvalRC p t s.

Inductive wndEvalsRC: environ -> Terms -> Terms -> Prop :=
| wEsRCrfl: forall p ts, wndEvalsRC p ts ts
| wEsRCstep: forall p ts ss, wndEvals p ts ss -> wndEvalsRC p ts ss.

Inductive WcbvEvalRC: environ -> Term -> Term -> Prop :=
| WcERCrfl: forall p t, WcbvEvalRC p t t
| WcERCstep: forall p t s, WcbvEval p t s -> WcbvEvalRC p t s.

Inductive WcbvEvalsRC: environ -> Terms -> Terms -> Prop :=
| WcEsRCrfl: forall p ts, WcbvEvalsRC p ts ts
| WcEsRCstep: forall p ts ss, WcbvEvals p ts ss -> WcbvEvalsRC p ts ss.

Theorem L1wcbvEval_strip_L2WcbvEval:
  forall p, L1.program.WFaEnv p ->
    (forall t s, L1.wcbvEval.WcbvEval p t s -> L1.term.WFapp t ->
          WcbvEval (stripEnv p) (strip t) (strip s)) /\
    (forall ts ss, L1.wcbvEval.WcbvEvals p ts ss -> L1.term.WFapps ts ->
          WcbvEvals (stripEnv p) (strips ts) (strips ss)).
intros p hp.
apply L1.wcbvEval.WcbvEvalEvals_ind; intros; try (solve [constructor]).
- simpl. eapply wCast. inversion H0. intuition.
- eapply wConst. 
  + apply LookupDfn_hom. eassumption.
  + apply H. assert (j:= L1.program.Lookup_pres_WFapp hp l). inversion_Clear j.
    assumption.
- rewrite TApp_hom. inversion H2. subst. eapply wAppLam.
  + rewrite TLambda_hom in H. apply H. assumption.
  + apply H0. assumption.
  + rewrite whBetaStep_hom in H1. apply H1.
    apply L1.term.whBetaStep_pres_WFapp; try assumption.
    * assert (j:= proj1 (L1.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w H7).
      inversion j. assumption.
    * apply (proj1 (L1.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w0). assumption.
- simpl. inversion H1. subst. eapply wLetIn.
  + apply H. assumption.
  + rewrite (proj1 instantiate_hom) in H0. apply H0.
    apply L1.term.instantiate_pres_WFapp; try assumption.
    * apply (proj1 (L1.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w). assumption.
- inversion_Clear H1.
  assert (j:= proj1 (L1.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w H6). 
  inversion_Clear j.
  rewrite TApp_hom. eapply wAppFix.
  + rewrite TFix_hom in H. apply H. assumption.
  + rewrite <- tcons_hom. rewrite <- whFixStep_hom. rewrite e. 
    rewrite optStrip_hom. reflexivity.
  + apply H0. refine (L1.term.whFixStep_pres_WFapp _ H2 _ e).
    * constructor; assumption.
- inversion_Clear H2. rewrite TApp_hom. rewrite TApp_hom. simpl. 
  apply wAppCnstr; intuition.
- inversion_Clear H2. rewrite TApp_hom. rewrite TApp_hom. simpl. 
  apply wAppInd; intuition.
- inversion_Clear H1. rewrite TCase_hom. eapply wCase0.
  + simpl in H. apply H. assumption.
  + rewrite <- tnil_hom. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
    apply f_equal. eassumption.
  + apply H0. refine (L1.term.whCaseStep_pres_WFapp H7 _ _ e). constructor.
- inversion_Clear H1. rewrite TCase_hom. simpl in H. eapply wCasen.
  + apply H. assumption.
  + rewrite <- tcons_hom. rewrite <- tskipn_hom. rewrite e. 
    rewrite optStrips_hom. reflexivity.
  + rewrite <- whCaseStep_hom. rewrite e0. rewrite optStrip_hom. reflexivity.
  + apply H0. refine (L1.term.whCaseStep_pres_WFapp H7 _ _ e0). 
    refine (L1.term.tskipn_pres_WFapp _ _ e).
    assert (j: L1.term.WFapp (L1.term.TApp (L1.term.TConstruct i n) arg args)).
    { refine (proj1 (L1.wcbvEval.wcbvEval_pres_WFapp hp) _ _ _ _).
      apply mch. assumption. assumption. }
    inversion_clear j.
    constructor; assumption.
- inversion_Clear H1. rewrite tcons_hom. rewrite tcons_hom.
  constructor; intuition.
Qed.

Print Assumptions L1wcbvEval_strip_L2WcbvEval.

Function unstrip (t:Term) : L1Term :=
  match t with
    | TRel n => L1.term.TRel n
    | TSort s => L1.term.TSort s
    | TCast t => L1.term.TCast (unstrip t) Cast L1.term.prop
    | TProd nm bod => L1.term.TProd nm L1.term.prop (unstrip bod)
    | TLambda nm bod => L1.term.TLambda nm L1.term.prop (unstrip bod)
    | TLetIn nm dfn bod =>
           L1.term.TLetIn nm (unstrip dfn) L1.term.prop (unstrip bod)
    | TApp fn arg args =>
           L1.term.TApp (unstrip fn) (unstrip arg) (unstrips args)
    | TConst nm => L1.term.TConst nm
    | TInd i => L1.term.TInd i
    | TConstruct i m => L1.term.TConstruct i m
    | TCase n mch brs =>
           L1.term.TCase n L1.term.prop (unstrip mch) (unstrips brs)
    | TFix ds n => L1.term.TFix (unstripDs ds) n
  end
with unstrips (ts:Terms) : L1Terms := 
  match ts with
    | tnil => L1.term.tnil
    | tcons t ts => L1.term.tcons (unstrip t) (unstrips ts)
  end
with unstripDs (ts:Defs) : L1Defs := 
  match ts with
    | dnil => L1.term.dnil
    | dcons nm t m ds =>
           L1.term.dcons nm L1.term.prop (unstrip t) m (unstripDs ds)
  end.

Lemma strip_leftInv_unstrip:
  (forall (t:Term), strip (unstrip t) = t) /\
  (forall ts:Terms, strips (unstrips ts) = ts) /\
  (forall ds:Defs, stripDs (unstripDs ds) = ds).
Proof.
  apply TrmTrmsDefs_ind; simpl; intros;
  try reflexivity; try (rewrite H; reflexivity);
  try (rewrite H; rewrite H0; reflexivity);
  try (rewrite H; rewrite H0; rewrite H1; reflexivity).
Qed.

Definition optUnstrip (t:option Term) : option L1Term :=
  match t with
    | None => None
    | Some t => Some (unstrip t)
  end.
Definition optUnstrips (ts:option Terms) : option L1Terms :=
  match ts with
    | None => None
    | Some ts => Some (unstrips ts)
  end.

Lemma optUnstrip_unhom: forall y, optUnstrip (Some y) = Some (unstrip y).
induction y; simpl; reflexivity.
Qed.
Lemma optUnstrips_unhom: forall y, optUnstrips (Some y) = Some (unstrips y).
induction y; simpl; reflexivity.
Qed.

Function unstripCnstrs (cs:list Cnstr) : list L1.program.Cnstr :=
  match cs with
    | nil => nil
    | cons (mkCnstr str arity) cs =>
        cons (L1.program.mkCnstr str arity) (unstripCnstrs cs)
  end.
Function unstripItyPack (its:itypPack) : L1.program.itypPack :=
  match its with
    | nil => nil
    | (mkItyp str itps) :: itpacks =>
         (L1.program.mkItyp str (unstripCnstrs itps)) ::
                           unstripItyPack itpacks
  end.
Function unstripEc (ec:envClass) : L1.program.envClass :=
  match ec with
    | ecTrm t => L1.program.ecTrm (unstrip t)
    | ecTyp itp => L1.program.ecTyp (unstripItyPack itp)
  end.
Fixpoint unstripEnv (p:environ) : L1.program.environ :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, (unstripEc ec)) (unstripEnv q)
  end.


Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L1.term.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod s; induction s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma L1WFapp_L2WFapp:
  (forall t, L1.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L1.term.WFappTrmsDefs_ind; simpl; constructor; auto.
  - intros h. elim H. apply isApp_hom. assumption.
Qed.


Lemma L2WFapp_L1WFapp:
  (forall t, WFapp t -> L1.term.WFapp (unstrip t)) /\
  (forall ts, WFapps ts -> L1.term.WFapps (unstrips ts)) /\
  (forall ds, WFappDs ds -> L1.term.WFappDs (unstripDs ds)).
Proof.
  apply WFappTrmsDefs_ind; simpl; intros; try (solve [constructor]);
  try (solve [constructor; try assumption; constructor]).
  - constructor; try assumption.
    + intros h. elim H. destruct h as [x0 [x1 [x2 j]]].
      assert (k:= f_equal strip j).
      rewrite (proj1 (strip_leftInv_unstrip)) in k. rewrite k. simpl.
      exists (strip x0), (strip x1), (strips x2). reflexivity.
Qed.


Lemma L1WFaEnv_L2WFaEnv:
  forall p:L1.program.environ, L1.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate.
    + constructor. apply (proj1 (L1WFapp_L2WFapp)). assumption.
    + constructor.
  - assumption.
Qed.

Lemma Lookup_unhom:
 forall nm p ec, 
   Lookup nm p ec -> L1.program.Lookup nm (unstripEnv p) (unstripEc ec).
Proof.
  induction 1; destruct t; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma tappend_unhom:
  forall ts us,
    unstrips (tappend ts us) = L1.term.tappend (unstrips ts) (unstrips us).
 Proof.
   induction ts; intros us; simpl; try reflexivity.
   - rewrite IHts. reflexivity.
Qed.

Lemma mkApp_unhom:
  forall fn args,
    unstrip (mkApp fn args) = L1.term.mkApp (unstrip fn) (unstrips args).
Proof.
  induction fn; induction args; simpl; try reflexivity.
  - rewrite tappend_tnil. rewrite L1.term.tappend_tnil. reflexivity.
  - rewrite tappend_unhom. simpl. reflexivity.
Qed.

Lemma dlength_unhom:
  forall ds, dlength ds = L1.term.dlength (unstripDs ds).
Proof.
  induction ds; simpl.
  - reflexivity.
  - rewrite IHds. reflexivity.
Qed.

Lemma tcons_unhom:
  forall t ts,
    unstrips (tcons t ts) = L1.term.tcons (unstrip t) (unstrips ts).
Proof.
  reflexivity.
Qed.

Lemma dcons_unhom:
  forall nm bod rarg ds,
    unstripDs (dcons nm bod rarg ds) =
    L1.term.dcons nm L1.term.prop (unstrip bod) rarg (unstripDs ds).
reflexivity.
Qed.


Lemma instantiate_unhom: 
  (forall bod tin ni,
    unstrip (instantiate tin ni bod) =
    L1.term.instantiate (unstrip tin) ni (unstrip bod)) /\
  (forall bods tin ni,
    unstrips (instantiates tin ni bods) =
    L1.term.instantiates (unstrip tin) ni (unstrips bods)) /\
  (forall ds tin ni,
    unstripDs (instantiateDefs tin ni ds) =
    L1.term.instantiateDefs (unstrip tin) ni (unstripDs ds)).
Proof.
  apply TrmTrmsDefs_ind; intros;
  try (solve [unfold instantiate, L1.term.instantiate; simpl; reflexivity]).
  - destruct (lt_eq_lt_dec n ni) as [[j1|j2]|j3];
    unfold instantiate, L1.term.instantiate; simpl.
    + rewrite (proj1 (nat_compare_gt _ _) j1). reflexivity.
    + subst. rewrite (proj2 (nat_compare_eq_iff ni ni)); try reflexivity.
      rewrite mkApp_unhom. simpl. reflexivity.
    + rewrite (proj1 (nat_compare_lt _ _) j3). reflexivity.
  - change (unstrip (TCast (instantiate tin ni t)) =
            L1.term.TCast
              (L1.term.instantiate (unstrip tin) ni (unstrip t))
              Cast L1.term.prop).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TProd n (instantiate tin (S ni) t)) =
            L1.term.TProd n L1.term.prop
                          (L1.term.instantiate (unstrip tin) (S ni)
                                               (unstrip t))).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TLambda n (instantiate tin (S ni) t)) =
            L1.term.TLambda n L1.term.prop
                            (L1.term.instantiate (unstrip tin) (S ni)
                                                 (unstrip t))).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TLetIn n (instantiate tin ni t)
                            (instantiate tin (S ni) t0)) =
            L1.term.TLetIn n (L1.term.instantiate
                                (unstrip tin) ni (unstrip t))
                           L1.term.prop
                           (L1.term.instantiate
                              (unstrip tin) (S ni) (unstrip t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstrip (mkApp (instantiate tin ni t)
                           (tcons (instantiate tin ni t0)
                                  (instantiates tin ni t1))) =
            L1.term.mkApp (L1.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1.term.tcons 
                             (L1.term.instantiate 
                                (unstrip tin) ni (unstrip t0))
                             (L1.term.instantiates
                                (unstrip tin) ni (unstrips t1)))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. simpl.
    rewrite mkApp_unhom. reflexivity.
  - change (unstrip (TCase n (instantiate tin ni t)
                           (instantiates tin ni t0)) =
            L1.term.TCase n L1.term.prop
                          (L1.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1.term.instantiates (unstrip tin) ni
                                                (unstrips t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstrip (TFix (instantiateDefs tin (ni + dlength d) d) n) =
            L1.term.TFix
              (L1.term.instantiateDefs (unstrip tin)
                                       (ni + L1.term.dlength (unstripDs d))
                                       (unstripDs d)) n).
    rewrite <- H. rewrite dlength_unhom. simpl. reflexivity.
  - change (unstrips (tcons (instantiate tin ni t)
                            (instantiates tin ni t0)) =
            L1.term.tcons (L1.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1.term.instantiates (unstrip tin) ni
                                                (unstrips t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstripDs (dcons n (instantiate tin ni t) n0
                            (instantiateDefs tin ni d)) =
            L1.term.dcons n L1.term.prop
                          (L1.term.instantiate (unstrip tin) ni (unstrip t))
                          n0
                          (L1.term.instantiateDefs (unstrip tin) ni
                                                   (unstripDs d))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
Qed.

Lemma whBetaStep_unhom:
  forall bod a1 args,
    unstrip (whBetaStep bod a1 args) =
    L1.term.whBetaStep (unstrip bod) (unstrip a1) (unstrips args).
Proof.
  intros bod a1 args. unfold whBetaStep, L1.term.whBetaStep.
  rewrite <- (proj1 instantiate_unhom). rewrite <- mkApp_unhom. reflexivity.
Qed.

Lemma dnthBody_unhom:
  forall m ds,
    optUnstrip (dnthBody m ds) = L1.term.dnthBody m (unstripDs ds).
Proof.
  induction m; induction ds; try intuition.
  - simpl. intuition.
Qed.

Lemma fold_left_unhom:
forall (F:Term -> nat -> Term) 
       (unstripF:L1Term -> nat -> L1Term) (ns:list nat) (t:Term),
  (forall (s:Term) (n:nat), unstrip (F s n) = unstripF (unstrip s) n) ->
  unstrip (fold_left F ns t) = fold_left unstripF ns (unstrip t).
induction ns; intros t h.
- intuition.
- simpl. rewrite IHns.
  + rewrite h. reflexivity.
  + assumption.
Qed.

Lemma pre_whFixStep_unhom:
  forall body dts args,
    unstrip (pre_whFixStep body dts args) = 
    L1.term.pre_whFixStep (unstrip body) (unstripDs dts) (unstrips args).
Proof. 
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1.term.pre_whFixStep;
  simpl; rewrite mkApp_unhom; try reflexivity.
  - rewrite (fold_left_unhom _ 
         (fun (bod : L1.term.Term) (ndx : nat) =>
            L1.term.instantiate
              (L1.term.TFix (unstripDs (dcons n t n0 dts)) ndx) 0 bod)).
    + rewrite <- dcons_unhom. rewrite (proj1 instantiate_unhom). simpl.
      rewrite dlength_unhom. reflexivity.
    + intros. simpl. rewrite (proj1 instantiate_unhom). simpl.
      reflexivity.
  - rewrite (fold_left_unhom _ 
         (fun (bod : L1.term.Term) (ndx : nat) =>
            L1.term.instantiate
              (L1.term.TFix (unstripDs (dcons n t n0 dts)) ndx) 0 bod)).
    + rewrite dlength_unhom. rewrite (proj1 instantiate_unhom).
      rewrite dcons_unhom. rewrite tcons_unhom. reflexivity.
    + intros. rewrite (proj1 instantiate_unhom).
      rewrite dcons_unhom. reflexivity.
Qed.

Lemma whFixStep_unhom:
  forall dts m args,
    optUnstrip (whFixStep dts m args) =
    L1.term.whFixStep (unstripDs dts) m (unstrips args).
Proof.
  intros dts m args.
  unfold L1.term.whFixStep, whFixStep. case_eq (dnthBody m dts); intros.
  - rewrite optUnstrip_unhom. rewrite pre_whFixStep_unhom.
    rewrite <- dnthBody_unhom. rewrite H. simpl. reflexivity.
  - rewrite <- dnthBody_unhom. rewrite H. reflexivity.
Qed.

Lemma tnth_unhom:
 forall ts n, optUnstrip (tnth n ts) = L1.term.tnth n (unstrips ts).
Proof.
  induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma whCaseStep_unhom:
forall n ts brs,
  optUnstrip (whCaseStep n ts brs) = 
  L1.term.whCaseStep n (unstrips ts) (unstrips brs).
Proof.
  destruct n, brs; intros; simpl; try reflexivity.
  - unfold whCaseStep. simpl. rewrite mkApp_unhom. reflexivity.
  - unfold whCaseStep. unfold L1.term.whCaseStep. simpl.
    rewrite <- tnth_unhom. destruct (tnth n brs); simpl.
    + rewrite mkApp_unhom. reflexivity.
    + reflexivity. 
Qed.

Lemma tskipn_unhom:
  forall ts n, optUnstrips (tskipn n ts) = L1.term.tskipn n (unstrips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.


(** L2 WcbvEval is sound for L1 WcbvEval **)
Theorem L2WcbvEval_L1WcbvEval:
  forall p,
    (forall t s, WcbvEval p t s ->
     L1.wcbvEval.WcbvEval (unstripEnv p) (unstrip t) (unstrip s)) /\
    (forall ts ss, WcbvEvals p ts ss ->
     L1.wcbvEval.WcbvEvals (unstripEnv p) (unstrips ts) (unstrips ss)).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; simpl; intros; try (solve [constructor]);
  try (solve [constructor; constructor]);
  try (solve [constructor; assumption]).
  - eapply L1.wcbvEval.wConst; try eassumption. apply (Lookup_unhom l).
  - eapply L1.wcbvEval.wAppLam; try eassumption.
    + rewrite <- whBetaStep_unhom. assumption.
  - eapply L1.wcbvEval.wLetIn; try eassumption.
    + rewrite <- (proj1 instantiate_unhom). assumption.
  - eapply L1.wcbvEval.wAppFix; try eassumption.
    + rewrite <- tcons_unhom. rewrite <- whFixStep_unhom.
      rewrite <- optUnstrip_unhom. apply f_equal. assumption.
  - eapply L1.wcbvEval.wCase0; try eassumption.
    + change (L1.term.whCaseStep n (unstrips tnil) (unstrips brs) =
              Some (unstrip cs)).
      rewrite <- whCaseStep_unhom. rewrite <- optUnstrip_unhom.
      apply f_equal. assumption.
  - eapply L1.wcbvEval.wCasen; try eassumption. 
    + rewrite <- tcons_unhom. rewrite <- tskipn_unhom.
      rewrite <- optUnstrips_unhom. apply f_equal. eassumption.
    + rewrite <- whCaseStep_unhom. rewrite <- optUnstrip_unhom.
      apply f_equal. assumption.
Qed.


(** NO?? strip throws away info **
Goal
  forall L2p p, L2p = stripEnv p ->
    (forall L2t L2s, WcbvEval L2p L2t L2s ->
     forall t, L2t = strip t -> forall s, L2s = strip s ->
                                          L1.wcbvEval.WcbvEval p t s) /\
    (forall L2ts L2ss, WcbvEvals L2p L2ts L2ss ->
     forall ts, L2ts = strips ts -> forall ss, L2ss = strips ss ->
                                          L1.wcbvEval.WcbvEvals p ts ss).
Proof.
  intros L2p p hp.
  apply WcbvEvalEvals_ind; simpl; intros.
  - destruct (Lam_strip_inv _ H) as [t0 [t1 [jtl jtr]]].
    destruct (Lam_strip_inv _ H0) as [s0 [s1 [jsl jsr]]].
    subst.


WcbvEval (stripEnv p) (strip t) (strip s) -> 
     L1.wcbvEval.WcbvEval p t s) /\
    (forall ts ss, WcbvEvals (stripEnv p) (strips ts) (strips ss) ->
     L1.wcbvEval.WcbvEvals p ts ss).
Proof.

Theorem L2WcbvEval_L1wndEval:
  forall (p:L1.program.environ), L1.program.WFaEnv p ->
    (forall t s, WcbvEval (stripEnv p) (strip t) (strip s) -> 
                 L1.term.WFapp t -> L1.wndEval.wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals (stripEnv p) (strips ts) (strips ss) ->
                   L1.term.WFapps ts -> L1.wndEval.wndEvalsRTC p ts ss).
**)




(**** below here scratch ****
Goal
  forall (q:environ), WFaEnv q ->
     forall p1, q = stripEnv p1 -> forall p2, q = stripEnv p2 ->
  (forall (t x:Term), WcbvEval q t x -> 
      forall t1, t = strip t1 -> forall t2, t = strip t2 -> 
     forall s1 s2, L1.wcbvEval.WcbvEval p1 t1 s1 ->
            L1.wcbvEval.WcbvEval p2 t2 s2 -> strip s1 = strip s2) /\
  (forall (ts xs:Terms), WcbvEvals q ts xs -> 
     forall t1s, ts = strips t1s -> forall t2s, ts = strips t2s -> 
     forall s1s s2s, L1.wcbvEval.WcbvEvals p1 t1s s1s ->
            L1.wcbvEval.WcbvEvals p2 t2s s2s -> strips s1s = strips s2s).
Proof.
Admitted.
(***********
  intros q hq p1 hp1 p2 hp2.
  apply WcbvEvalEvals_ind; intros.
  - destruct (Lam_strip_inv _ H) as [x1 [y1 [j1 k1]]]. clear H.
    destruct (Lam_strip_inv _ H0) as [x2 [y2 [j2 k2]]]. clear H0.
    subst.
    refine (WcbvEval_single_valued _ _).
    inversion H1. subst.
    refine (proj1 (L1wcbvEval_strip_L2WcbvEval _) _ _ _ _).


     (proj1 (L1wcbvEval_strip_L2WcbvEval _)).


    refine (proj1 (L1wcbvEval_strip_L2WcbvEval _) _ _ _ _).



Qed.

***********)



Theorem L2wcbvEval_strip_L1WcbvEval:
  forall pp, WFaEnv pp -> forall p, pp = stripEnv p ->
    (forall (tt ss:Term), WcbvEval pp tt ss -> WFapp tt ->
     forall (t:L1Term), tt = strip t -> 
       exists s:L1Term, ss = strip s /\ L1.wcbvEval.WcbvEval p t s)  /\
    (forall tts sss, WcbvEvals pp tts sss -> WFapps tts ->
     forall ts, tts = strips ts ->
       exists ss:L1Terms, sss = strips ss /\ L1.wcbvEval.WcbvEvals p ts ss).
Proof.


Theorem L2wcbvEval_strip_L1WcbvEval:
  forall pp, WFaEnv pp -> forall p, pp = stripEnv p ->
    (forall (tt ss:Term), WcbvEval pp tt ss -> WFapp tt ->
     forall (t:L1Term), tt = strip t -> 
       exists s:L1Term, ss = strip s /\ L1.wcbvEval.WcbvEval p t s)  /\
    (forall tts sss, WcbvEvals pp tts sss -> WFapps tts ->
     forall ts, tts = strips ts ->
       exists ss:L1Terms, sss = strips ss /\ L1.wcbvEval.WcbvEvals p ts ss).
Proof.
  intros pp hpp p hp. apply WcbvEvalEvals_ind; intros.
  - destruct (Lam_strip_inv H0 _) as [x0 [x1 [j0 j1]]]. subst.
    exists (L1.term.TLambda nm L1.term.prop x1). intuition.
    apply L1.wcbvEval.wLam.


    destruct (Lam_strip_inv _ H1) as [y0 [y1 [k0 k1]]].
    subst. simpl in *. apply L1.wcbvEval.wLam.

rewrite H1 in H0.


(*************
Lemma wndEval_types_irrelevant:
  forall p,
    (forall t s, L1.wndEval.wndEval p t s ->
          wndEvalRC (stripEnv p) (strip t) (strip s)) /\
    (forall ts ss, L1.wndEval.wndEvals p ts ss ->
          wndEvalsRC (stripEnv p) (strips ts) (strips ss)).
intros p. apply L1.wndEval.wndEvalEvals_ind; intros.
- apply wERCstep. constructor. apply LookupDfn_hom. assumption.
- apply wERCstep. simpl. rewrite whBetaStep_hom. apply sBeta.
- apply wERCstep. simpl. rewrite (proj1 (instantiate_hom )).
  apply sLetIn.
- apply wERCstep. rewrite TCase_hom. apply sCase0.
  assert (j: optStrip (L1.term.whCaseStep n L1.term.tnil brs) =
             optStrip (Some s)).
  apply f_equal. assumption.
  simpl in j. rewrite <- j. rewrite whCaseStep_hom. reflexivity.
- apply wERCstep. simpl. eapply sCasen.
  rewrite <- tcons_hom. rewrite <- tskipn_hom. rewrite e. reflexivity.
  rewrite <- whCaseStep_hom. rewrite e0. reflexivity.
- apply wERCstep. rewrite TApp_hom. rewrite TFix_hom. apply sFix.
  assert (j: optStrip (L1.term.whFixStep dts m (L1.term.tcons arg args)) = 
             optStrip (Some s)).
  apply f_equal. assumption.
  simpl in j. rewrite <- j. rewrite whFixStep_hom. reflexivity.
  intros h. simpl in h. destruct h as [x0 [x1 [x2 j]]]. discriminate.
- simpl. apply wERCrfl.
- rewrite mkApp_hom. rewrite tcons_hom. rewrite TApp_hom.

- assert (j:= L1.term.mkApp_isApp r arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k.
  simpl.
  inversion H. 
  + rewrite mkApp_goodFn. HERE

- rewrite mkApp_hom. rewrite tcons_hom. (* rewrite TApp_hom. *)
  inversion H.
  + rewrite mkApp_goodFn. simpl.
    * constructor. rewrite TApp_hom. constructor.
    * intros h. elim n. apply (proj1 (isApp_hom _)). assumption.
  + apply wERCstep. apply sAppFn; assumption. 
- rewrite TApp_hom. rewrite TApp_hom.
  inversion_clear H. constructor.
  + apply wERCstep; apply sAppArg; assumption. 
- rewrite TApp_hom. rewrite TApp_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sAppArgs. assumption. 
    (* no step for TProd or TLambda in stripped language *)
- rewrite TProd_hom. rewrite TProd_hom. apply wERCrfl.
- rewrite TLambda_hom. rewrite TLambda_hom. apply wERCrfl.
- rewrite TLetIn_hom. rewrite TLetIn_hom. apply wERCrfl.
- rewrite TLetIn_hom. rewrite TLetIn_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sLetInDef. assumption.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCrfl.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sCaseArg. assumption.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sCaseBrs. assumption.
- rewrite tcons_hom. rewrite tcons_hom. inversion_clear H. constructor.
  + apply wEsRCstep. apply saHd. assumption.
- rewrite tcons_hom. rewrite tcons_hom. inversion_clear H. constructor.
  + apply wEsRCstep. apply saTl. assumption.
Qed.
***********************)

***)
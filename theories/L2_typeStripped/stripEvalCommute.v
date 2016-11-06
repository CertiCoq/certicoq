
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L1g.L1g.
Require Import L2.compile.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gDefs := L1g.compile.Defs.

Definition optStrip (t:option L1gTerm) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L1gTerms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option (L1gTerm * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP
           (b: option (nat * L1gTerms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, strips t, m)
                           end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, strips y, m).
induction y; simpl; reflexivity.
Qed.
                              

Lemma Lookup_hom:
  forall p s ec, Lookup s p ec -> Lookup s (stripEnv p) (stripEC ec).
Proof.
  induction 1; destruct t.
  - change (Lookup s ((s, ecTrm (strip l)) :: (stripEnv p))
                   (ecTrm (strip l))).
    apply LHit.
  - cbn. apply LHit.
  - change (Lookup s2 ((s1, ecTrm (strip l)) :: (stripEnv p))
                   (stripEC ec)).
    apply LMiss; assumption.
  - cbn. apply LMiss; assumption.
Qed.

Lemma LookupDfn_hom:
 forall p s t, LookupDfn s p t -> LookupDfn s (stripEnv p) (strip t).
unfold LookupDfn. intros.
assert (j:= Lookup_hom H). exact j.
Qed.

Lemma dlength_hom:
  forall ds, L1g.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L1g.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L1g.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm ty bod rarg ds,
    stripDs (L1g.compile.dcons nm ty bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L1g.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L1g.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.


Lemma TCast_hom:
  forall tm ty,
    (forall pr, ty <> L1g.compile.TCast pr L1g.compile.prop /\
     strip (L1g.compile.TCast tm ty) = TCast (strip tm)) \/
    (exists pr, ty = L1g.compile.TCast pr L1g.compile.prop /\
     strip (L1g.compile.TCast tm ty) = TProof (strip tm)).
Proof.
  intros. destruct (L1g.term.isProofCast_dec (L1g.compile.TCast tm ty)).
  - right. destruct H as [x0 [x1 jx]]. injection jx. intros. subst.
    exists x1. intuition.
  - left. intros. unfold isProofCast in H. split.
    + intros h. subst.
      assert (j: forall prf prp,
         L1g.compile.TCast tm (L1g.compile.TCast pr L1g.compile.prop) <>
         L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop)).
      { intros. intuition. apply H. exists tm, pr. reflexivity. }
      eapply j. reflexivity.
    + destruct ty; cbn; try reflexivity. destruct ty2; try reflexivity.
      case_eq s; intros; try reflexivity.
      subst. elim H. exists tm, ty1. reflexivity.
Qed.

(*************************
Lemma TCast_hom':
  forall tm ck ty pr,
    ty = L1g.compile.TCast pr ck L1g.compile.prop ->
    strip (L1g.compile.TCast tm ck ty) = TProof (strip tm))

    strip (L1g.compile.TCast tm ck ty) = (TCast (strip tm)) \/
    (exists pr c, ty = L1g.compile.TCast pr c L1g.compile.prop /\
                strip (L1g.compile.TCast tm ck ty) = (TProof (strip tm))).
Proof.
  destruct ty; cbn; try (solve[left; reflexivity]).
  destruct ty2; cbn; try (solve[left; reflexivity]).
  destruct s; cbn; try (left; reflexivity); try (right; reflexivity).
  right. exists ty1, c. intuition.
Qed.
 ************)

Lemma canonicalP_hom:
  forall t, optStripCanP (L1g.term.canonicalP t) = canonicalP (strip t).
Proof.
  intros t. case_eq t; intros; try reflexivity.
  - destruct (L1g.term.isProofCast_dec (L1g.compile.TCast t0 t1)).
    + destruct H0 as [x0 [x1 jx]]. myInjection jx. reflexivity.
    + destruct t1; cbn; try reflexivity. destruct t1_2; cbn; try reflexivity.
      destruct s; reflexivity.
  - destruct t0; cbn; try reflexivity.
    destruct t0_2; try reflexivity.
    destruct t0_2_2; try reflexivity.
    destruct s; reflexivity.
Qed.      

Lemma tnth_hom:
 forall ts n, optStrip (L1g.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L1g.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L1g.compile.tappend ts us) = tappend (strips ts) (strips us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L1g.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
induction fn; intros arg args; try reflexivity.
Qed.

Lemma isApp_hom:
  forall t, isApp (strip t) -> L1g.term.isApp t.
Proof.
  destruct t; cbn; intros h; destruct h as [x0 [x1 [x2 h]]];
  try discriminate.
  - destruct t2; try discriminate.
    destruct t2_2; try discriminate.
    destruct s; try discriminate.
  - exists t1, t2, t3. reflexivity.
Qed.

Lemma isLambda_hom:
  forall t, isLambda (strip t) -> L1g.term.isLambda t.
Proof.
  destruct t; simpl; intros h; destruct h as [x0 [x1 h]]; try discriminate.
  - destruct t2; try discriminate.  
    destruct t2_2; try discriminate.
    destruct s; try discriminate.
  - exists n, t1, t2. reflexivity.
Qed.

Lemma isFix_hom:
  forall t, isFix (strip t) -> L1g.term.isFix t.
Proof.
  destruct t; cbn; intros h; destruct h as [x0 [x1 h]]; try discriminate. 
  - destruct t2; try discriminate.  
    destruct t2_2; try discriminate.
    destruct s; try discriminate.
  - exists d, n. reflexivity.
Qed.

Lemma L1WFapp_L2WFapp:
  (forall t, L1g.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1g.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1g.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L1g.term.WFappTrmsDefs_ind; intros;
  try (solve[cbn; econstructor; auto]).
  - destruct ty; cbn; try constructor; try assumption.
    destruct ty2; cbn; try constructor; try assumption.
    destruct s; constructor; assumption.
  - cbn. constructor; try assumption.
    intros h. elim H. apply isApp_hom. assumption.
Qed.

Lemma L1WFaEnv_L2WFaEnv:
  forall p:environ L1gTerm, L1g.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L1WFapp_L2WFapp)). assumption.
  - assumption.
Qed.

(***
Lemma WFapp_hom:
  (forall t, L1g.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1g.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1g.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
   apply L1g.term.WFappTrmsDefs_ind; cbn; intros;
  try (solve [constructor]);
  try (solve [constructor; intuition]).
  - constructor; try assumption.
    + intros h. assert (j:= isApp_hom _ h). contradiction.
Qed.
 ****)

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
  strip (L1g.compile.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  induction fn; induction args; simpl; try reflexivity.
  - destruct fn2; cbn; try reflexivity.
    destruct fn2_2; cbn; try reflexivity.
    destruct s; cbn; try reflexivity.
  - destruct fn2; cbn; try reflexivity.
    destruct fn2_2; cbn; try reflexivity.
    destruct s; cbn; try reflexivity.
  - rewrite tappend_tnil. rewrite L1g.term.tappend_tnil. reflexivity.
  - rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
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

Lemma instantiates_dcons_commute:
  forall tin n nm t m ds,
         (instantiateDefs tin n (dcons nm t m ds)) = 
         (dcons nm (instantiate tin n t) m (instantiateDefs tin n ds)).
reflexivity.
Qed.

(*****  to remove in favor of term.v  ***
Lemma instantiate_TApp_mkApp:
  forall fn tin n arg args,
      instantiate tin n (TApp fn arg args) =
      mkApp (instantiate tin n fn)
           (tcons (instantiate tin n arg) (instantiates tin n args)).
Proof.
  intros; destruct fn; try reflexivity. 
Qed.
****)
    
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
Proof.
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

(***)
Lemma instantiate_hom:
  (forall bod arg n, strip (L1g.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1g.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L1g.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L1g.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  -  admit.
    (*************
    destruct (isCastProp_dec t0).
     + unfold isCastProp in H1. destruct H1 as [prp k]. subst. 
       cbn. rewrite H. reflexivity.
     + unfold isCastProp in H1.
       assert (j: forall prp, t0 <> L1g.compile.TCast prp L1g.compile.prop).
       { intros prp h. elim H1. exists prp. assumption. }
       destruct t0; cbn; try (rewrite H; reflexivity).
       * { destruct (n ?= n0); try (rewrite H; reflexivity).
           - case_eq arg; intros; try (rewrite H; reflexivity).
             case_eq t1; intros; try (rewrite H; reflexivity).
             case_eq s; intros; try (rewrite H; reflexivity).
             admit. }
       * { destruct (L1g.term.instantiate arg n t0_2); try reflexivity;
           destruct t0_2; rewrite H; try reflexivity;
           destruct s; try rewrite H; try reflexivity.
           admit.
           reflexivity.
           assert (j: ~ isProofCast (L1g.compile.TCast t t0)).
     *******************************)
  - change (TProd n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TProd n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLambda n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TLambda n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLetIn n (strip (L1g.term.instantiate arg n0 t))
                   (strip (L1g.term.instantiate arg (S n0) t1)) =
            (TLetIn n (instantiate (strip arg) n0 (strip t))
                    (instantiate (strip arg) (S n0) (strip t1)))).
    rewrite H. rewrite H1. reflexivity.
  - change (strip (L1g.compile.mkApp
                     (L1g.term.instantiate arg n t)
                     (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                         (L1g.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L1g.compile.TApp t t0 t1))). 
    rewrite TApp_hom. 
    change
      (strip (L1g.compile.mkApp (L1g.term.instantiate arg n t)
                                 (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                                     (L1g.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L1g.term.instantiate arg n t0))
                  (strips (L1g.term.instantiates arg n t1)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (strips t1)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L1g.term.instantiateDefs
                             arg (n0 + L1g.term.dlength d) d)) n =
            (TFix (instantiateDefs (strip arg)
                                   (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L1g.term.instantiate arg n t))
                  (strips (L1g.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L1g.term.instantiate arg n1 t0)) n0
                  (stripDs (L1g.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Admitted.   

(*******************
Lemma instantiate_hom:
  (forall bod arg n, (** ~ isProofCast (L1g.term.instantiate arg n bod) -> **)
                     strip (L1g.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1g.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L1g.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L1g.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  -  destruct (isCastProp_dec t0).
     + unfold isCastProp in H1. destruct H1 as [prp k]. subst. 
       cbn. rewrite H. reflexivity.
     + unfold isCastProp in H1.
       assert (j: forall prp, t0 <> L1g.compile.TCast prp L1g.compile.prop).
       { intros prp h. elim H1. exists prp. assumption. }
       destruct t0; cbn; try (rewrite H; reflexivity).
       * { destruct (n ?= n0); try (rewrite H; reflexivity).
           - case_eq arg; intros; try (rewrite H; reflexivity).
             case_eq t1; intros; try (rewrite H; reflexivity).
             case_eq s; intros; try (rewrite H; reflexivity).
             admit. }
       * { destruct (L1g.term.instantiate arg n t0_2); try reflexivity;
           destruct t0_2; rewrite H; try reflexivity;
           destruct s; try rewrite H; try reflexivity.
           admit.
           reflexivity.
    assert (j: ~ isProofCast (L1g.compile.TCast t t0)).
     { intros k. elim H1. apply instantiate_pres_isProofCast. assumption. }
     destruct (isCastProp_dec t0).
     + unfold isCastProp in H2. destruct H2 as [prp k]. subst.

       
     rewrite (strip_TCast_TCast'); try assumption.
          change
      (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                (L1g.term.instantiate arg n t0)) =
       TCast (instantiate (strip arg) n (strip t))).
     rewrite (strip_TCast_TCast'); try assumption.
     rewrite <- H. reflexivity.
     intros h.  destruct h as [x0 [x1 kx]]. 
     
     rewrite (strip_TCast_TCast'); try assumption.
    change
      (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                (L1g.term.instantiate arg n t0)) =
       instantiate (strip arg) n (TCast (strip t))).
    rewrite (strip_TCast_TCast').
     + rewrite H. reflexivity.
       intros h.  destruct h as [x0 [x1 kx]]. elim H1.
       unfold isProofCast.
       change
      (exists prf prp : L1g.compile.Term,
         (L1g.compile.TCast (L1g.term.instantiate arg n t)
                            (L1g.term.instantiate arg n t0) =
         L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop))).
       exists (L1g.term.instantiate arg n t). rewrite kx.

    rewrite (strip_TCast_TCast').
    assert (j: ~ isProofCast (L1g.compile.TCast t t0)).
    { intros k. elim H1. apply instantiate_pres_isProofCast. assumption. }
    
    change (TCast (strip (L1g.term.instantiate arg n t)) =
            TCast (instantiate (strip arg) n (strip t))).
    rewrite H. reflexivity.
    intros h. destruct h as [x0 [x1 kx]]. elim H1. unfold isProofCast.
    change
      (exists prf prp : L1g.compile.Term,
         (L1g.compile.TCast (L1g.term.instantiate arg n t)
                            (L1g.term.instantiate arg n t0) =
         L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop))).
    exists (L1g.term.instantiate arg n t).

    
    + intros h. elim H1. unfold isProofCast. unfold isProofCast in h.
      destruct h as [prf [prp j]]. cbn.


      apply instantiate_pres_isProofCast.
    rewrite strip_TCast_TCast; try assumption. rewrite H. reflexivity.
    + unfold isProofCast in H1. destruct H1 as [prf [prp j]].
      change
        (~ isProofCast (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                          (L1g.term.instantiate arg n t0))) in H1.
      rewrite j in H1.

      exists (L1g.term.instantiate arg n t).
    + destruct H1 as [x jx]. subst. cbn. rewrite H. reflexivity.
    + rewrite strip_TCast_TCast; try assumption.
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
         instantiate (strip arg) n (TCast (strip t))).
      erewrite <- strip_TCast_TCast; try eassumption.
      rewrite strip_TCast_TCast at 1. rewrite H.
      change
        (instantiate (strip arg) n (TCast (strip t)) =
         instantiate (strip arg) n (strip (L1g.compile.TCast t t0))).
      rewrite strip_TCast_TCast. reflexivity. assumption.

      Check TCast_hom.
      destruct (isCastProp_dec (L1g.term.instantiate arg n t0)).


      
Lemma instantiate_hom:
    (forall bod arg n, strip (L1g.term.instantiate arg n bod) =
                   instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1g.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L1g.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L1g.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - destruct (isCastProp_dec t0).
    + destruct H1 as [x jx]. subst. cbn. rewrite H. reflexivity.
    + rewrite strip_TCast_TCast; try assumption.
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
         instantiate (strip arg) n (TCast (strip t))).
      erewrite <- strip_TCast_TCast; try eassumption.
      rewrite strip_TCast_TCast at 1. rewrite H.
      change
        (instantiate (strip arg) n (TCast (strip t)) =
         instantiate (strip arg) n (strip (L1g.compile.TCast t t0))).
      rewrite strip_TCast_TCast. reflexivity. assumption.

      Check TCast_hom.
      destruct (isCastProp_dec (L1g.term.instantiate arg n t0)).

      
      
      * unfold isCastProp in H2. TCast (instantiate (strip arg) n (strip t)) =
   instantiate (strip arg) n (strip (L1g.compile.TCast t t0))
        destruct H2 as [prp j]. rewrite j. cbn.
      rewrite strip_TCast_TCast; try assumption.
       change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
         instantiate (strip arg) n (TCast (strip t))).
       Check (L1g.term.instantiate_pres_isCastProp). _ _ _ H1).

    + unfold isCastProp in H1.
      assert (j: forall prp, t0 <> L1g.compile.TCast prp L1g.compile.prop). admit.
      rewrite strip_TCast_TCast; try assumption.
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
        instantiate (strip arg) n (TCast (strip t))).
      case_eq (L1g.term.instantiate arg n t0); intros; cbn;
      rewrite H; try reflexivity.
      destruct t2; try reflexivity.
      destruct s; try reflexivity.
      specialize (j t1). rewrite <- H2 in j.
      specialize (H0 arg n). rewrite H2 in H0. cbn in H0.



      
      destruct t0; cbn; try (rewrite H; reflexivity).
      
      rewrite strip_TCast_TCast; try assumption.
      destruct t0; cbn; try (rewrite H; reflexivity).
      * { destruct (n ?= n0); rewrite H.
          -

        
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
        instantiate (strip arg) n (TCast (strip t))).
      destruct t0; cbn; try (rewrite H; reflexivity).
      * 

      
  - destruct (isProofCast_dec (L1g.compile.TCast t t0)).
    + destruct H1 as [x0 [x1 jx]]. myInjection jx. cbn. rewrite H. reflexivity.
    + rewrite (strip_TCast_TCast' H1).
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
        instantiate (strip arg) n (TCast (strip t))).
      rewrite (strip_TCast_TCast').
      * rewrite H. reflexivity.
      * intros h. elim H1. unfold isProofCast. unfold isProofCast in h.
        destruct h as [x0 [x1 jx]]. exists t.

isProofCast
     (L1g.compile.TCast (L1g.term.instantiate arg n t)
                        (L1g.term.instantiate arg n t0)) ->
isProofCast (L1g.compile.TCast t t0)

            
      change
        ()
        
      unfold isProofCast in H1.
      assert (j: forall prf prp,
         L1g.compile.TCast t t0 <>
         L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop)).
      { intros prf prp h. apply H1. exists prf, prp. assumption. }
      HERE
      destruct t0; cbn; try (solve[rewrite H; reflexivity]).
      * destruct (n ?= n0); try (solve[rewrite H; reflexivity]).
        destruct arg; try (solve[rewrite H; reflexivity]).
        destruct arg2; try (solve[rewrite H; reflexivity]).
        destruct s; try (solve[rewrite H; reflexivity]).
        
        elim H1. exists t.

      * rewrite H. reflexivity.

    destruct (TCast_hom t t0) as [h | h]. 
    + change
      (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                (L1g.term.instantiate arg n t0)) =
       instantiate (strip arg) n (strip (L1g.compile.TCast t t0))).
      specialize (h (L1g.term.instantiate arg n t)). destruct h.
      rewrite H2.
      
    destruct (L1g.term.instantiate arg n t)(TCast_hom t t0) as [h | h]. 
    + rewrite h.
      change
        (strip (L1g.compile.TCast (L1g.term.instantiate arg n t)
                                  (L1g.term.instantiate arg n t0)) =
         TCast (instantiate (strip arg) n (strip t))).
    
    
    destruct (TCast_hom t c t0) as [h | h].
    + rewrite h.
    
    destruct (TCast_hom (L1g.term.instantiate arg n t) c
                        (L1g.term.instantiate arg n t0)).destruct (TCast_hom t c t0) as [h | h]. 
rewrite h. rewrite h.
    
    + rewrite H1. rewrite H2. rewrite H.
      
      rewrite H. 
  - change
      (strip (L1g.compile.TCast (L1g.term.instantiate arg n t) c
                                (L1g.term.instantiate arg n t0)) =
       instantiate (strip arg) n (strip (L1g.compile.TCast t c t0))).

admit.
    
        (**********************
  - destruct (L1g.term.isCast_dec t0).
    + destruct i as [x0 [x1 [x2 jx]]]. subst.
      destruct (L1g.term.isProp_dec x2).
      * unfold isProp in H1. subst. cbn. rewrite H. reflexivity.
      * rewrite (notPrf_stripCast H1).

    change
      (strip (L1g.term.instantiate
                arg n (L1g.compile.TCast t c (L1g.compile.TCast x0 x1 x2))) =
       instantiate (strip arg) n (TCast (strip t))).
     change
       (strip (L1g.compile.TCast
                 (L1g.term.instantiate arg n t) c
                 (L1g.compile.TCast (L1g.term.instantiate arg n x0) x1
                                    (L1g.term.instantiate arg n x2))) =
        instantiate (strip arg) n (TCast (strip t))).
     rewrite tCast_hom.
******************)
    
  - change (TProd n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TProd n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLambda n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TLambda n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLetIn n (strip (L1g.term.instantiate arg n0 t))
                   (strip (L1g.term.instantiate arg (S n0) t1)) =
            (TLetIn n (instantiate (strip arg) n0 (strip t))
                    (instantiate (strip arg) (S n0) (strip t1)))).
    rewrite H. rewrite H1. reflexivity.
  - change (strip (L1g.compile.mkApp
                     (L1g.term.instantiate arg n t)
                     (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                         (L1g.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L1g.compile.TApp t t0 t1))). 
    rewrite TApp_hom. 
    change
      (strip (L1g.compile.mkApp (L1g.term.instantiate arg n t)
                                 (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                                     (L1g.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L1g.term.instantiate arg n t0))
                  (strips (L1g.term.instantiates arg n t1)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (strips t1)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L1g.term.instantiateDefs
                             arg (n0 + L1g.term.dlength d) d)) n =
            (TFix (instantiateDefs (strip arg)
                                   (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L1g.term.instantiate arg n t))
                  (strips (L1g.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L1g.term.instantiate arg n1 t0)) n0
                  (stripDs (L1g.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Admitted.
 ****************)

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L1g.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
Proof.
  intros bod arg args.
  unfold L1g.term.whBetaStep, whBetaStep.
  rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.

Lemma TConstruct_hom:
  forall i n arty,
    strip (L1g.compile.TConstruct i n arty) = TConstruct i n arty.
intros. simpl.  destruct i. reflexivity.
Qed.


Lemma optStrip_match:
  forall x (f:L1gTerm -> L1gTerm) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L1g.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (strips brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L1g.term.whCaseStep. simpl. 
  rewrite <- tnth_hom. destruct (L1g.term.tnth n brs); simpl.
  + rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L1g.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod,
    strip (L1g.compile.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm ty bod,
    strip (L1g.compile.TLambda nm ty bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L1g.compile.TLetIn nm dfn ty bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L1g.compile.TCase n ty mch brs) =
    TCase n (strip mch) (strips brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L1gTerm -> nat -> L1gTerm) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L1gTerm),
  (forall (s:L1gTerm) (n:nat), strip (F s n) = stripF (strip s) n) ->
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
    strip (L1g.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1g.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L1g.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L1g.compile.prop). simpl. reflexivity.
Qed.

(******************  fix later *******************
Lemma lookup_hom:
  forall p nm ec,
    lookup nm p = Some ec -> lookup nm (stripEnv p) = Some (stripEC ec).
Proof.
  induction p; intros.
  - discriminate.
  - cbn. unfold string_eq_bool in *. destruct (string_dec nm (fst a)).
    + rewrite e. cbn.

      case_eq (string_eq_bool nm (fst a)); intros.
    + rewrite H0.

Lemma WcbvEval_hom:
  forall p,
    (forall t t', L1g.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L1g.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L1g.wcbvEval.WcbvEvalEvals_ind; cbn; intros; try reflexivity;
  try (solve[constructor; trivial]).
  - refine (wConst _ _ _); try eassumption.
    unfold lookupDfn. unfold lookupDfn in e.
    case_eq (lookup nm p); intros.
    + rewrite H0 in e. destruct e0.
      * myInjection e. rewrite lookup_hom.


        
      change (lookup nm (stripEnv p) = Some (stripEC (AstCommon.ecTrm t))).
    apply Lookup_hom. assumption.
  - refine (wAppLam _ _ _ _); try eassumption.
    + rewrite whBetaStep_hom in H1. eassumption.
  - refine (wLetIn _ _ _ _). eassumption.
    rewrite <- (proj1 instantiate_hom). assumption.
  - refine (wAppFix _ _ _ _ _); try eassumption.
    + rewrite <- dnthBody_hom. destruct (L1g.term.dnthBody m dts).
      * rewrite e. reflexivity.
      * discriminate.
    + rewrite <- tcons_hom. rewrite pre_whFixStep_hom.
      assumption.
  - rewrite mkApp_hom. refine (wAppCong _ _ _ _); try eassumption.
    + intros h. elim n. apply isLambda_hom. assumption.
    + intros h. elim n0. apply isFix_hom. assumption.      
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.


Lemma Prf_strip_inv:
  forall s, TProof = strip s -> s = L1g.compile.TProof.
Proof.
  destruct s; simpl; intros h; try discriminate. reflexivity.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L1g.compile.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L1g.compile.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm ck sty, 
     (L1g.compile.TCast stm ck sty) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, c, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n arty s,
    TConstruct i n arty = strip s -> L1g.compile.TConstruct i n arty = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L1g.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L1g.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L1g.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L1g.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L1g.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L1g.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L1g.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = strips sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L1g.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L1g.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L1g.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L1g.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (strips bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

Theorem L2WcbvEval_L1gWcbvEval:
  forall L2p p, L2p = stripEnv p -> L1g.program.WFaEnv p ->
  forall L2t t, L2t = strip t -> L1g.term.WFapp t ->
  forall L2s, WcbvEval L2p L2t L2s ->
  forall s, L1g.wcbvEval.WcbvEval p t s -> L2s = strip s.
Proof.
  intros.
  refine (WcbvEval_single_valued _ _). eassumption.
  subst. apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_L1gWcbvEval.

Theorem L2WcbvEval_sound_for_L1gwndEval:
  forall L2p L2t L2s, WcbvEval L2p L2t L2s ->
  forall p, L2p = stripEnv p -> L1g.program.WFaEnv p -> 
  forall t, L2t = strip t -> L1g.term.WFapp t ->       
  forall s, L1g.wcbvEval.WcbvEval p t s ->      
            L2s = strip s /\ L1g.wndEval.wndEvalRTC p t s.
Proof.
  intros. repeat split.
  - refine (WcbvEval_single_valued _ _). eassumption.
    subst. apply WcbvEval_hom. assumption.
  - refine (proj1 (L1g.wcbvEval.WcbvEval_wndEvalRTC _) _ _ _ _); assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L1gwndEval.


(*** unstrip: replace every missing type field with [prop]  ***)
Function unstrip (t:Term) : L1gTerm :=
  match t with
    | TProof => L1g.compile.TProof
    | TRel n => L1g.compile.TRel n
    | TSort s => L1g.compile.TSort s
    | TCast t => L1g.compile.TCast (unstrip t) Cast L1g.compile.prop
    | TProd nm bod => L1g.compile.TProd nm L1g.compile.prop (unstrip bod)
    | TLambda nm bod => L1g.compile.TLambda nm L1g.compile.prop (unstrip bod)
    | TLetIn nm dfn bod =>
           L1g.compile.TLetIn nm (unstrip dfn) L1g.compile.prop (unstrip bod)
    | TApp fn arg args =>
      L1g.compile.TApp (unstrip fn) (unstrip arg) (unstrips args)
    | TAx => L1g.compile.TAx
    | TConst nm => L1g.compile.TConst nm
    | TInd i => L1g.compile.TInd i
    | TConstruct i m arty => L1g.compile.TConstruct i m arty
    | TCase n mch brs =>
           L1g.compile.TCase n L1g.compile.prop (unstrip mch) (unstrips brs)
    | TFix ds n => L1g.compile.TFix (unstripDs ds) n
    | TWrong => L1g.compile.TWrong
  end
with unstrips (ts:Terms) : L1gTerms := 
  match ts with
    | tnil => L1g.compile.tnil
    | tcons t ts => L1g.compile.tcons (unstrip t) (unstrips ts)
  end
with unstripDs (ts:Defs) : L1gDefs := 
  match ts with
    | dnil => L1g.compile.dnil
    | dcons nm t m ds =>
           L1g.compile.dcons nm L1g.compile.prop (unstrip t) m (unstripDs ds)
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

Function unstripCnstrs (cs:list Cnstr) : list AstCommon.Cnstr :=
  match cs with
    | nil => nil
    | cons (mkCnstr str arity) cs =>
        cons (AstCommon.mkCnstr str arity) (unstripCnstrs cs)
  end.
Function unstripItyPack (its:itypPack) : AstCommon.itypPack :=
  match its with
    | nil => nil
    | (mkItyp str itps) :: itpacks =>
         (AstCommon.mkItyp str (unstripCnstrs itps)) ::
                           unstripItyPack itpacks
  end.
Function unstripEC (ec:envClass Term) : envClass L1g.compile.Term :=
  match ec with
    | AstCommon.ecTrm t => ecTrm (unstrip t)
    | AstCommon.ecTyp _ npars itp =>
       AstCommon.ecTyp _ npars (unstripItyPack itp)
  end.
Fixpoint unstripEnv (p:environ Term) : environ L1g.compile.Term :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, (unstripEC ec)) (unstripEnv q)
  end.
**********************************)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import Common.Common.
Require Import L2d.L2d.
Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
Require Import L2k.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2dTerm := L2d.compile.Term.
Definition L2dTerms := L2d.compile.Terms.
Definition L2dBrs := L2d.compile.Brs.
Definition L2dDefs := L2d.compile.Defs.


Definition optStrip (t:option L2dTerm) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L2dTerms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option L2dTerm): option Term :=
                           match b with
                             | None => None
                             | Some t => Some (strip t)
                           end.
Definition optStripCanP
           (b: option (nat * L2dTerms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, strips t, m)
                           end.
(**********************
Definition optStrip_split
           (b: option L2d.term.split): option split :=
  match b with
    | None => None
    | Some (L2d.term.mkSplit fsts t lsts) =>
      Some (mkSplit (strips fsts) (strip t) (strips lsts))
  end.
******************)

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrip_hom_None: optStrip (@None L2d.compile.Term) = @None (Term).
  reflexivity.
Qed.

Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y, optStripDnth (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, strips y, m).
induction y; simpl; reflexivity.
Qed.
(*********************
Lemma optStrip_split_hom:
  forall fsts t lsts,
    optStrip_split (Some (L2d.term.mkSplit fsts t lsts)) =
    Some (mkSplit (strips fsts) (strip t) (strips lsts)).
Proof.
  induction fsts; cbn; intros; try reflexivity.
Qed.
 ***********************)

Lemma tlength_hom:
  forall ts, tlength (strips ts) = L2d.term.tlength ts.
Proof.
  induction ts; intros; try reflexivity.
  - cbn. apply f_equal. assumption.
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

Lemma lookup_hom:
  forall p nm ec,
    lookup nm p = Some ec -> lookup nm (stripEnv p) = Some (stripEC ec).
Proof.
  intros p nm ec h. apply Lookup_lookup.
  apply Lookup_hom. apply (lookup_Lookup _ _ h).
Qed.
  
Lemma lookup_hom_None:
  forall p nm,
    lookup nm p = None -> lookup nm (stripEnv p) = None.
Proof.
  induction p; intros.
  - cbn. reflexivity.
  - destruct a. destruct (string_dec nm s).
    + subst. cbn in H. rewrite string_eq_bool_rfl in H. discriminate.
    + cbn. rewrite (string_eq_bool_neq n).
      cbn in H. rewrite (string_eq_bool_neq n) in H.
      apply IHp. assumption.
Qed.
  
Lemma LookupDfn_hom:
  forall p s t, LookupDfn s p t -> LookupDfn s (stripEnv p) (strip t).
Proof.
  unfold LookupDfn. intros.
  assert (j:= Lookup_hom H). exact j.
Qed.

Lemma lookupDfn_hom:
  forall p nm t,
    lookupDfn nm p = Ret t -> lookupDfn nm (stripEnv p) = Ret (strip t).
Proof.
  induction p; intros.
  - cbn in *. discriminate.
  - destruct a. unfold lookupDfn. cbn. unfold lookupDfn in H. cbn in H.
    destruct (string_dec nm s).
    + subst. cbn. cbn in H.
      rewrite string_eq_bool_rfl. rewrite string_eq_bool_rfl in H.
      destruct e; try discriminate.
      * myInjection H. cbn. reflexivity.
    + rewrite (string_eq_bool_neq n). rewrite (string_eq_bool_neq n) in H.
      case_eq (lookup nm p); intros; rewrite H0 in H; try discriminate.
      * rewrite (lookup_hom _ _ H0). destruct e0; try discriminate.
        cbn. myInjection H. reflexivity.
Qed.

Lemma dlength_hom:
  forall ds, L2d.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2d.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L2d.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm bod rarg ds,
    stripDs (L2d.compile.dcons nm bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L2d.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L2d.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma tnth_hom:
 forall ts n, optStrip (L2d.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L2d.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L2d.compile.tappend ts us) = tappend (strips ts) (strips us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg,
    strip (L2d.compile.TApp fn arg) =
    match CanonicalP strip fn (strip arg) with
    | None => TApp (strip fn) (strip arg)
    | Some (i, m, args, npars, nargs) => etaExpand i m args npars nargs
    end.
Proof.
  reflexivity.
Qed.

(***
Lemma TAppCnstr_hom:
  forall i m npars nargs arg args, 
    strip (L2d.compile.TApp (L2d.compile.TConstruct i m npars nargs) arg args) =
    etaExpand i m npars nargs (tcons (strip arg) (strips args)).
Proof.
  intros. reflexivity.
Qed.
 ****)

(***********
Lemma not_isApp_etaExpand_args:
  forall na aArgs F cArgs,
    ~ (exists ts, isApp (F ts)) ->
    ~ exists fn arg args,
        etaExpand_args na aArgs F cArgs = Some (TApp fn arg args).
Proof.
  induction na; induction aArgs; intros; cbn.
  - intros h. destruct h as [x0 [x1 [x2 jx]]]. myInjection jx.
    elim H. exists cArgs. rewrite H0. auto.
  - intros h. destruct h as [x0 [x1 [x2 jx]]]. discriminate.
  - eapply IHna. intros h.
    destruct h as [x0 [x1 [x2 [x3 jx]]]]. discriminate.
  - eapply IHna. eassumption.
Qed.

Goal
  forall na aArgs F cArgs,
  (exists fn arg args,
    etaExpand_args na aArgs F cArgs = Some (TApp fn arg args)) ->
    isApp (F cArgs).
Proof.
  induction na; induction aArgs; cbn; intros.
  - destruct H as [x0 [x1 [x2 jx]]]. myInjection jx. rewrite H. auto.
  - destruct H as [x0 [x1 [x2 jx]]]. discriminate.
  - destruct H as [x0 [x1 [x2 jx]]]. eapply IHna.
    exists x0, x1, x2. rewrite <- jx.
Abort.  

Lemma not_isApp_etaExpand_args:
  forall na aArgs F cArgs,
    (forall ts, ~ isApp (F ts)) ->
    ~ exists fn arg args,
        etaExpand_args na aArgs F cArgs = Some (TApp fn arg args).
Proof.
  induction na; induction aArgs; intros; cbn.
  - intros h. destruct h as [x0 [x1 [x2 jx]]]. myInjection jx.
    eelim H. rewrite H0. auto.
  - intros h. destruct h as [x0 [x1 [x2 jx]]]. discriminate.
  - eapply IHna. intros. not_isApp.
  - eapply IHna. eassumption.
Qed.
 ************)


Lemma not_isApp_nLambda:
  forall F,
    (forall ts, ~ isApp (F ts)) ->
    forall m us, ~ isApp (nLambda m F us).
Proof.
  intros. intros h. elim (H us). destruct m; cbn in h.
  - assumption.
  - destruct h as [y0 [y1 jy]]. discriminate.
Qed.
  

Lemma isApp_hom:
  forall t, isApp (strip t) -> L2d.term.isApp t.
Proof.
Admitted.
(************
  destruct t; intros h; destruct h as [x0 [x1 jx]]; try discriminate.
  - auto.
  - unfold strip in jx. 
    elim (notIsApp_etaExpand i n tnil n0 n1). rewrite jx. auto.
Qed.
 *****************)   

(*********************
  destruct t; cbn; intros h;
    destruct h as [x0 [x1 [x2 h]]]; try discriminate; auto.
  destruct n0.
  - cbn in h.
  induction n1.
  - cbn in h. eelim not_isApp_nLambda.
    + intros. intros k. destruct k as [y0 [y1 [y2 jy]]].
  - elim (not_isApp_etaExpand_args n1 tnil (nLambda n0 (TConstruct i n)) tnil).
    + intros. intros k. destruct n0; cbn in k. 
      * destruct k as [y0 [y1 [y2 jy]]]. discriminate.
      * destruct k as [y0 [y1 [y2 jy]]]. discriminate.
    + induction n1; cbn in h. 
      *{ eelim (not_isApp_nLambda (TConstruct i n)).
         - intros. intros k. destruct k as [y0 [y1 [y2 jy]]]. discriminate.
         - exists x0, x1, x2. eassumption. }
      *{ destruct n1.
         - cbn in *.
        

        cbn. rewrite h. auto.
Qed.
 *******************)

(*************
Lemma isLambda_hom:
  forall t,
    isLambda (strip t) ->
    L2d.term.isLambda t \/ L2d.term.isConstruct t \/  L2d.term.isApp t.
Proof.
  intros t. functional induction (strip t); intros h;
  destruct h as [x0 [x1 jx]]; try discriminate.
  - left. auto.
  - right. right. auto.
  - right. left. auto.
Qed.

Lemma isFix_hom:
  forall t, isFix (strip t) -> L2d.term.isFix t.
Proof.
  induction t; intros; simpl in *;
  try (destruct H as [x0 [x1 jx]]; discriminate); auto.
  - destruct t1; try (destruct H as [x0 [x1 jx]]; discriminate).
    destruct (etaExp_cnstr_Sanity' i n n0 n1 (tcons (strip t2) (strips t3))).
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
  - destruct (etaExp_cnstr_Sanity' i n n0 n1 tnil).
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
  - destruct p. destruct H as [y0 [y1 jy]]. discriminate.
Qed.

Lemma L2WFapp_L2kWFapp:
  (forall t, L2d.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L2d.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ts, L2d.term.WFappBs ts -> WFappBs (stripBs ts)) /\
  (forall ds, L2d.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L2d.term.WFappTrmsBrsDefs_ind; try constructor; auto; intros.
  - destruct fn; auto; try (constructor; try assumption; not_isApp).
    + elim H. auto.
    + change
        (WFapp (match nat_compare (n0 + n1) (S (tlength (strips ts))) with
        | Lt => TWrong
        | _ => etaExp_cnstr i n n0 n1 (tcons (strip t) (strips ts))
        end)).
      destruct (n0 + n1 ?= S (tlength (strips ts))).
      
    + apply etaExp_cnstr_pres_WFapp. constructor; assumption.
    + destruct p. constructor; try assumption. not_isApp.
  - apply etaExp_cnstr_pres_WFapp. constructor.
  - destruct m. constructor; try assumption.
Qed.

Lemma L2WFaEnv_L2kWFaEnv:
  forall p:environ L2Term, L2d.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L2WFapp_L2kWFapp)). assumption.
  - assumption.
  - apply stripEnv_pres_fresh. assumption.
Qed.
 ************)

(***
Lemma WFapp_hom:
  (forall t, L2d.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L2d.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L2d.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
   apply L2d.term.WFappTrmsDefs_ind; cbn; intros;
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

(**********
Lemma mkApp_tcons_lem2:
 forall fn ts u s args,
   mkApp fn (tcons u (tappend ts (tcons s args))) =
   mkApp (mkApp fn (tcons u ts)) (tcons s args).
Proof.
  destruct fn; destruct ts; intros; try reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
Qed.
*************)

(***************** 
Goal
  forall nargs ts arg n computedArgs F,
    WFTrm arg 0 ->
    (forall us m, F (instantiates arg m us) = instantiate arg m (F us)) ->
    (forall us m (F:Terms -> Term),
        instantiate arg m (F us) = instantiate arg (S m) (F us)) ->
    etaExpand_args
      nargs (instantiates arg n ts) F (instantiates arg n computedArgs) =
    instantiate arg n (etaExpand_args nargs ts F computedArgs).
Proof.
  induction nargs; induction ts; intros; try reflexivity.
  - cbn. rewrite <- H0. reflexivity.
  - cbn. rewrite <- H0. reflexivity.
  - cbn. assert (j: nargs >= tlength tnil). cbn. omega.
    rewrite (proj1 (proj2 (instantiate_lift arg))); try assumption; try omega.
    replace (tunit (TRel 0)) with (instantiates arg (S n) (tunit (TRel 0)))
      by reflexivity.
    rewrite <- (instantiates_tappend arg (lifts 0 computedArgs)).
    unfold instantiates at 2.
    rewrite (proj1 (nat_compare_gt (S n) 0)); try omega.
    rewrite <- (IHnargs
                  _ _ _
                  (compile.tappend (lifts 0 computedArgs) (tunit (TRel 0))));
      try eassumption.
    + cbn. 
      admit.
    + intros.
    change
      (TLambda nAnon (F (instantiates arg m us)) =
       TLambda nAnon (instantiate arg (S m) ((F us)))).
    rewrite H0, H1. reflexivity.

    
    rewrite <- H1.    
    change (TLambda nAnon (instantiate arg m (F us)) =
            (TLambda nAnon (instantiate arg (S m) (F us)))).
    apply f_equal2. reflexivity.
     Check (tappend_pres_lifts).



    Goal
  forall nargs ts arg n computedArgs F,
    WFTrm arg 0 ->
    (forall us m, F (instantiates arg m us) = instantiate arg m (F us)) ->
    etaExpand_args
      nargs (instantiates arg n ts)
      (fun b : Terms => TLambda nAnon (F b))
      (instantiates arg n computedArgs) =
    instantiate
      arg n (etaExpand_args nargs ts (fun b : Terms => TLambda nAnon (F b))
                            computedArgs).
Proof.
  induction nargs; induction ts; intros; try reflexivity.
  - cbn. rewrite H0. reflexivity.
  - cbn. rewrite <- H0. reflexivity.
  - cbn. assert (j: nargs >= tlength tnil). cbn. omega.
    rewrite (proj1 (proj2 (instantiate_lift arg))); try assumption; try omega.
    replace (tunit (TRel 0)) with (instantiates arg (S n) (tunit (TRel 0)))
      by reflexivity.
    rewrite <- (instantiates_tappend arg (lifts 0 computedArgs)).
    unfold instantiates at 2.
    rewrite (proj1 (nat_compare_gt (S n) 0)); try omega.
    rewrite <- (IHnargs
                  _ _ _
                  (compile.tappend (lifts 0 computedArgs) (tunit (TRel 0))));
      try eassumption.
    cbn.

    Check (tappend_pres_lifts).


    Goal
  forall nargs ts arg n computedArgs i m,
    WFTrm arg 0 ->
    etaExpand_args
      nargs (instantiates arg n ts)
      (fun b : Terms => TConstruct i m b) (instantiates arg n computedArgs) =
    instantiate
      arg n (etaExpand_args nargs ts
                            (fun b : Terms => TConstruct i m b) computedArgs).
Proof.
  induction nargs; induction ts; intros; try reflexivity.
  - cbn. assert (j: nargs >= tlength tnil). cbn. omega.
    rewrite (proj1 (proj2 (instantiate_lift arg))); try assumption; try omega.
    replace (tunit (TRel 0)) with (instantiates arg (S n) (tunit (TRel 0)))
      by reflexivity.
    rewrite <- (instantiates_tappend arg (lifts 0 computedArgs) _ (S n)).
    unfold instantiates at 2. rewrite (proj1 (nat_compare_gt (S n) 0));
                                try omega.
    Check (IHnargs
             tnil arg n (compile.tappend (lifts 0 computedArgs) (tunit (TRel 0)))
             i m).
    destruct (@isLambda_etaExpand_args
                nargs tnil j
                (fun b : Terms => TConstruct i m b)
             (compile.tappend (lifts 0 computedArgs) (tunit (TRel 0))))
      as [x0 [x1 jx]].
    rewrite jx.
    destruct (@isLambda_etaExpand_args
                nargs tnil j
                (fun b : Terms => TConstruct i m b)
             (compile.tappend (lifts 0 computedArgs) (tunit (TRel 0))))
      as [x0 [x1 jx]].
    rewrite jx.


    unfold instantiate.
  - cbn. rewrite instantiates_at_last. destruct ts.
    + cbn. unfold etaExpand_args.



      Goal
  forall nargs arg n t ts computedArgs i m,
    etaExpand_args nargs (tcons (instantiate arg n t) (instantiates arg n ts))
                   (fun b : Terms => TConstruct i m b) (instantiates arg n computedArgs) =
    instantiate arg n (etaExpand_args nargs (tcons t ts)
                                      (fun b : Terms => TConstruct i m b)
                                      computedArgs).
Proof.
  induction nargs; induction ts; intros; try reflexivity.
  - admit.
  - cbn. rewrite instantiates_at_last. destruct ts.
    + cbn. unfold etaExpand_args.


              
              Goal
  forall npars x3 i m computedArgs arg n t ts,
    etaExpand (fun b : Terms => TConstruct i m b) (instantiates arg n computedArgs)
    (tcons (instantiate arg n t) (instantiates arg n ts)) npars x3 =
  instantiate arg n
    (etaExpand (fun b : Terms => TConstruct i m b) computedArgs (tcons t ts) npars x3).
Proof.
  induction npars; intros.
  - cbn.
 **********************)

Definition istable (F:Terms -> Term) :=
  forall tin n ts, instantiate tin n (F ts) = F ts.

Lemma istable_under_Lambda:
  forall F, istable F -> istable (fun b : Terms => TLambda nAnon (F b)).
Proof.
  unfold istable; intros F h. intros. cbn. rewrite h. reflexivity.
Qed.
  
(**********
Lemma istable_under_etaExpand_args:
  forall nargs aargs F,
    istable F ->
    istable (etaExpand_args nargs aargs F).
Proof.
  induction nargs; induction aargs; unfold istable; cbn;
    intros; try (rewrite H; reflexivity).
  - rewrite IHnargs. reflexivity. apply istable_under_Lambda. trivial.
  - rewrite IHnargs. reflexivity. assumption.
Qed.
    
  
Lemma etaExpand_args_instantiate:
  forall nargs aargs F tin n us,
    istable F ->
    etaExpand_args nargs aargs F us =
    instantiate tin n (etaExpand_args nargs aargs F us).
Proof.
  induction nargs; induction aargs; unfold istable; cbn; intros;
    try (rewrite H; reflexivity).
  - erewrite <- IHnargs. reflexivity. apply istable_under_Lambda. assumption.
  - erewrite <- IHnargs. reflexivity. assumption.
Qed.
 **************)

(**********
Lemma strip_App_not_Constructor:
  forall fn arg,
    ~ L2d.term.isConstruct fn ->
    strip (L2d.compile.TApp fn arg) = TApp (strip fn) (strip arg).
Proof.
  intros. case_eq fn; intros; subst; try reflexivity.
  elim H; auto.
Qed.
 ***********)

Definition App_stable (F:Terms -> Term) :=
  forall ts us, isApp (F ts) -> isApp (F us).
Definition notApp (F:Terms -> Term) :=
  forall ts, ~ isApp (F ts).

Lemma isApp_fn_not_isConstruct:
  forall fn arg,
    isApp (strip (L2d.compile.TApp fn arg)) -> ~ L2d.term.isConstruct fn.
Proof.
Admitted.
(*******************
  intros. intro h. destruct h as [x0 [x1 [x2 [x3 jx]]]]. subst fn.
  change
    (isApp (etaExpand x0 x1 (strips (L2d.compile.tunit arg)) x2 x3)) in H.
  eelim notIsApp_etaExpand. eassumption.
Qed.
 *******************)

(**********
Lemma mkApp_hom:
  forall fn args,
    ~ L2d.term.isApp fn ->
    ~ L2d.term.isConstruct fn ->
    strip (L2d.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  intros fn. destruct (L2d.term.isConstruct_dec fn);
  induction args; intros.
  - rewrite mkApp_tnil_ident. rewrite L2d.term.mkApp_tnil_ident. reflexivity.
  - contradiction.
  -


  - destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.


    Lemma mkApp_hom:
  forall fn args,
    ~ L2d.term.isApp fn ->
    strip (L2d.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  intros fn. destruct (L2d.term.isConstruct_dec fn);
  induction args; intros.
  - rewrite mkApp_tnil_ident. rewrite L2d.term.mkApp_tnil_ident. reflexivity.
  - destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
    rewrite L2d.term.mkApp_goodFn.
    change
      (etaExpand x0 x1 (tcons (strip t) (strips args)) x2 x3 =
       mkApp (etaExpand x0 x1 tnil x2 x3)
             (strips (L2d.compile.tcons t args))).
    specialize (IHargs H H0).
    change
      (strip (L2d.term.mkApp (L2d.compile.TConstruct x0 x1 x2 x3) args) =
       mkApp (etaExpand x0 x1 tnil x2 x3)
             (strips args)) in IHargs.
    rewrite tcons_hom. rewrite mkApp_goodFn.
    case_eq args; intros.
    + rewrite tnil_hom. 

  - rewrite L2d.term.mkApp_goodFn; try assumption.
    rewrite tcons_hom. rewrite mkApp_goodFn.
    + rewrite TApp_hom; try assumption. reflexivity.      
    + intros h. elim H. apply isApp_hom. assumption.
Qed.

Lemma mkApp_hom:
  forall args fn,
    ~ L2d.term.isApp fn ->
    ~ L2d.term.isConstruct fn ->
    strip (L2d.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  induction args; intros.
  - rewrite mkApp_tnil_ident. rewrite L2d.term.mkApp_tnil_ident. reflexivity.
  - rewrite L2d.term.mkApp_goodFn; try assumption.
    rewrite tcons_hom. rewrite mkApp_goodFn.
    + rewrite TApp_hom; try assumption. reflexivity.      
    + intros h. elim H. apply isApp_hom. assumption.
Qed.
*****************)

(*****************
Lemma instantiate_hom:
  (forall bod n, L2d.term.WFTrm bod n -> 
                 forall arg, strip (L2d.term.instantiate arg n bod) =
                             instantiate (strip arg) n (strip bod)) /\
  (forall bods n, L2d.term.WFTrms bods n ->
                  forall arg, strips (L2d.term.instantiates arg n bods) =
                              instantiates (strip arg) n (strips bods)) /\
  (forall bods n, L2d.term.WFTrmBs bods n ->
                  forall arg, stripBs (L2d.term.instantiateBrs arg n bods) =
                              instantiateBrs (strip arg) n (stripBs bods)) /\
  (forall ds n, L2d.term.WFTrmDs ds n  ->
                forall arg, stripDs (L2d.term.instantiateDefs arg n ds) =
                            instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2d.term.WFTrmTrmsBrsDefs_ind; intros;
    try (cbn; reflexivity); try (cbn; rewrite H0; reflexivity).
  - cbn. rewrite (proj1 (nat_compare_gt n m)). reflexivity. omega.
  - cbn. rewrite H0. rewrite H2. reflexivity.
  - destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      change
        (strip
           (L2d.term.instantiate
              arg n (L2d.compile.TApp
                       (L2d.compile.TConstruct x0 x1 x2 x3) t ts)) =
         instantiate (strip arg) n
                     (strip (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      change
        (strip
           (L2d.term.mkApp
              (L2d.term.instantiate
                 arg n (L2d.compile.TConstruct x0 x1 x2 x3))
              (L2d.term.instantiates arg n (L2d.compile.tcons t ts))) =
         instantiate (strip arg) n
                     (strip (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      rewrite mkApp_hom.
      
      
      change
        (strip (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                                (L2d.term.instantiate arg n t)
                                (L2d.term.instantiates arg n ts)) =
         instantiate
           (strip arg)
           n (etaExpand x0 x1 (tcons (strip t) (strips ts)) x2 x3)).
      change
        (etaExpand x0 x1 (tcons (strip (L2d.term.instantiate arg n t))
                                (strips (L2d.term.instantiates arg n ts)))
                                x2 x3 =
         instantiate
           (strip arg)
           n (etaExpand x0 x1 (tcons (strip t) (strips ts)) x2 x3)).
      rewrite H3. rewrite H5.

      admit.
    + rewrite strip_App_not_Constructor; try assumption.
      change
        (strip (L2d.term.mkApp
                  (L2d.term.instantiate arg n fn)
                  (L2d.compile.tcons (L2d.term.instantiate arg n t)
                                    (L2d.term.instantiates arg n ts))) =
         (mkApp (instantiate (strip arg) n (strip fn))
                (tcons (instantiate (strip arg) n (strip t))
                       (instantiates (strip arg) n (strips ts))))).
      rewrite <- H1. rewrite <- H3. rewrite <- H5.
      rewrite mkApp_hom.
      * rewrite tcons_hom. reflexivity.
      * intros h. elim H. eapply (proj1 (shape_isApp _)).
        destruct h as [x0 [x1 [x2 jx]]].
        rewrite (instantiate_pres_shape _ jx). reflexivity.
        eapply WFTrm_shape. assumption.
      * intros h. elim n0. eapply (proj1 (shape_isConstruct _)).
        destruct h as [x0 [x1 [x2 [x3 jx]]]].
        rewrite (instantiate_pres_shape _ jx). reflexivity.
        eapply WFTrm_shape. assumption.
  -


        
         pose proof (instantiate_pres_shape arg jx (WFTrm_shape H0)) as k.
         cbn in k.
         pose proof (@instantiate_pres_shape (WFTrm_shape H0)). jx) as k.
         cbn in k.
        destruct fn; cbn in k; exists x0, x1, x2, x3; try discriminate.
        - 
                              
        erewrite <- instantiate_fixes_Construct in jx.
        exists x0, x1, x2, x3.
        

        eapply (shape_isApp _ _ h).
        Check (instantiate_pres_shape).
        
    * change
        (strip (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                              (L2d.compile.tcons
                                 (L2d.term.instantiate arg n t)

                                 (L2d.term.instantiates arg n ts))) =
         instantiate (strip arg) n (TApp (strip fn) (strip t) (strips ts))).
      change
        (strip (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                              (L2d.compile.tcons
                                 (L2d.term.instantiate arg n t)
                                 (L2d.term.instantiates arg n ts))) =
         mkApp (instantiate (strip arg) n (strip fn))
               (tcons (instantiate (strip arg) n (strip t))
                      (instantiates (strip arg) n (strips ts)))).
      destruct (L2d.term.isApp_dec (L2d.term.instantiate arg n fn)).
      * Check mkApp_hom.


        

      * destruct i as [x0 [x1 [x2 jx]]]. rewrite jx.
        change
          (strip
             (L2d.compile.TApp
                x0 x1 (L2d.term.tappend
                         x2 (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts)))) =
            mkApp (instantiate (strip arg) n (strip fn))
                  (tcons (instantiate (strip arg) n (strip t))
                         (instantiates (strip arg) n (strips ts)))).

        
        assert (instantiate (strip arg) n (strip fn) = )
      * rewrite <- instantiate_mkApp_commute.
        rewrite (L2d.term.mkApp_goodFn _ _ n1).

        
      Check instantiate_mkApp_commute.
      rewrite <- instantiate_mkApp_commute.
      rewrite <- H3. rewrite <- H5. Check mkApp_hom.
                                          

    
  - rewrite L2d.term.instantiate_TApp_mkApp.
    change
      (strip (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                            (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts))) =
       instantiate (strip arg) n (strip (L2d.compile.TApp fn t ts))).
    destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn; try not_isApp.
      unfold L2d.term.instantiate at 1.
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (strip (L2d.term.instantiate arg n t))
                          (strips (L2d.term.instantiates arg n ts)))
                   x2 x3 =
         instantiate (strip arg) n
                     (strip (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (strip (L2d.term.instantiate arg n t))
                          (strips (L2d.term.instantiates arg n ts)))
                   x2 x3 =
         instantiate (strip arg) n
                     (etaExpand (TConstruct x0 x1)
                                (tcons (strip t) (strips ts)) x2 x3)).
      cbn. induction x2; cbn in *.
      * { destruct x3.
          - rewrite H3. rewrite H5.
            rewrite <- tcons_hom.



        
      Eval cbn in (etaExpand (TConstruct x0 x1) (tcons (strip t) (strips ts))).
      unfold etaExpand.
      cbn.
      cbn in H1. destruct x2; cbn in *.
      rewrite H3. rewrite H5.
      * admit.
      * cbn in H1.     
      

      



      change
        (strip
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (strip arg) n
                     (strip (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      
      change
        (strip
           (L2d.compile.TApp
              (L2d.compile.TConstruct x0 x1 x2 x3)
              (L2d.term.instantiate arg n t)
              (L2d.term.instantiates arg n ts)) =
         instantiate
           (strip arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (instantiate (strip arg) n  (strip t))
                             (strips ts)) x2 x3)).
      change
        (etaExpand (TConstruct x0 x1) (tcons (strip t) (strips ts)) x2 x3 =
         instantiate
           (strip arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (strip t) (strips ts)) x2 x3)).

      
      rewrite <- etaExpand_instantiate.
      * admit.
      *
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (strip (L2d.term.instantiate arg n t))
                          (strips (L2d.term.instantiates arg n ts))) x2 x3 =
         etaExpand (TConstruct x0 x1)
                   (instantiates (strip arg) n (tcons (strip t) (strips ts)))
                   x2 x3).


    instantiate
           (strip arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (strip t) (strips ts)) x2 x3)).

      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (strip (L2d.term.instantiate arg n t))
                          (strips (L2d.term.instantiates arg n ts))) x2 x3 =
         instantiate
           (strip arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (strip t) (strips ts)) x2 x3)).
      rewrite H3, H5.
      Check (etaExpand_TConstruct_instantiate x0 x1 (strip arg) n _ x2 x3).

      destruct x2.
      * cbn. rewrite <- H1.

      unfold strip at 1.
      
      change
        (strip
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (tcons (strip (L2d.term.instantiate arg n t))
                             (strips (L2d.term.instantiates arg n ts))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      rewrite H3. rewrite H5.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (strip arg) n
                                    (tcons (strip t) (strips ts))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 (tcons (strip t) (strips ts))).
      * { rewrite H6.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (instantiates
                                     (strip arg) n (tcons (strip t)
                                                          (strips ts)))).
          - rewrite H7.
         


Lemma whBetaStep_hom:
  forall bod arg args,
    L2d.term.WFTrm bod 0 ->
    strip (L2d.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
Proof.
  intros bod arg args h.
  unfold L2d.term.whBetaStep, whBetaStep.
  destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. Check instantiate_hom.
    apply (proj1 instantiate_hom). assumption.
  - rewrite <- (proj1 instantiate_hom); try assumption.
    destruct (L2d.term.isApp_dec (L2d.term.instantiate arg 0 bod)).
    + destruct i as [x0 [x1 [x2 jx]]]. rewrite jx. clear jx.
    change
      (strip (L2d.compile.TApp
                x0 x1 (L2d.term.tappend x2 (L2d.compile.tcons t args))) =
       mkApp (strip (L2d.compile.TApp x0 x1 x2))
             (strips (L2d.compile.tcons t args))).
    destruct (L2d.term.isConstruct_dec x0).
      * { destruct i as [i0 [i1 [i2 [i3 ji]]]]. subst.
        change
          (etaExp_cnstr i0 i1 i2 i3
                        (tcons (strip x1)
                               (strips (L2d.term.tappend
                                          x2 (L2d.compile.tcons t args)))) =
           mkApp (etaExp_cnstr i0 i1 i2 i3
                        (tcons (strip x1) (strips x2)))
                 (strips (L2d.compile.tcons t args))).
        rewrite strips_tappend. rewrite tcons_hom.   
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                        (tcons (strip x1) (strips x2))).
          - rewrite H. rewrite mkApp_goodFn; try not_isApp.
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                         (tcons (strip x1)
                                                (compile.tappend (strips x2) (tcons (strip t) (strips args))))).
        rewrite H0.

        rewrite <- (proj1 instantiate_hom); try assumption.
    rewrite jx. destruct (L2d.term.isConstruct_dec x0).
    + destruct i as [y0 [y1 [y2 [y3 jy]]]]. subst.
      change
        (etaExp_cnstr y0 y1 y2 y3
                      (tcons (strip x1) (strips (L2d.term.tappend x2 args))) =
         mkApp (etaExp_cnstr y0 y1 y2 y3
                             (tcons (strip x1) (strips x2)))
               (strips args)).
      destruct (etaExp_cnstr_Sanity'
                  y0 y1 y2 y3
                  (tcons (strip x1) (strips (L2d.term.tappend x2 args)))),
      (etaExp_cnstr_Sanity'  y0 y1 y2 y3 (tcons (strip x1) (strips x2)));
        rewrite H; rewrite H0.
      * { cbn. destruct args. cbn.
          - apply f_equal3; try reflexivity.
            apply f_equal3; try reflexivity.
            apply f_equal2; try reflexivity.
            rewrite L2d.term.tappend_tnil. reflexivity.
          -
(****
Goal
  forall i n npars nargs arg args,
  etaExp_cnstr i n npars nargs (tcons (strip arg) (strips args)) =
  TApp (etaExp_cnstr i n npars nargs tnil) (strip arg) (strips args).
Proof.
  intros. induction args.
  - cbn. induction npars.
    + cbn.
****)

(****
Lemma mkApp_hom:
forall fn args, ~ L2d.term.isApp fn ->
  strip (L2d.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  intros. destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. reflexivity.
  - rewrite L2d.term.mkApp_goodFn; try assumption. 
    assert (j: ~ isApp (strip fn)).
    { intros h. elim H. apply isApp_hom. assumption. }

  
Admitted.
 ****)

(***
  intros. destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. reflexivity.
  - rewrite L2d.term.mkApp_goodFn; try assumption. rewrite tcons_hom.
    assert (j: ~ isApp (strip fn)).
    { intros h. elim H. apply isApp_hom. assumption. }
    rewrite mkApp_goodFn; try assumption. destruct fn; try (cbn; reflexivity).
    change
      (etaExp_cnstr i n n0 n1 (tcons (strip t) (strips args)) =
       TApp (strip (L2d.compile.TConstruct i n n0 n1)) (strip t) (strips args)).
    change
      (etaExp_cnstr i n n0 n1 (tcons (strip t) (strips args)) =
       TApp (etaExp_cnstr i n n0 n1 tnil) (strip t) (strips args)).
           
    unfold strip in j.
    
  destruct args; try (reflexivity).
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    reflexivity.
  - destruct (L2d.term.isApp_dec fn).
    + admit.
    + rewrite L2d.term.mkApp_goodFn; try assumption.
      destruct (L2d.term.isConstruct_dec fn).
      * { destruct H as [x0 [x1 [x2 [x3 jx]]]]. subst. cbn.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (tcons (strip t) (strips args))).
          - destruct H as [y0 [y1 [y2 jy]]]. rewrite jy.
            destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
            + destruct H as [z0 [z1 [z2 jz]]]. rewrite jz. cbn. rewrite <- jy.



              destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
          
          assert (j:= etaExp_cnstr_Sanity
                        x0 x1 x2 x3 (tcons (strip t) (strips args))).
          rewrite TApp_hom. admit. ; try assumption.

    case_eq fn; intros; try reflexivity.
    cbn. rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
Qed.

Lemma etaExp_spec:
  forall i m npars nargs args,
   ((npars + nargs - (tlength args)) = 0 /\
    etaExp_cnstr i m npars nargs args =
                  TConstruct i m (mkEtaArgs npars nargs args)) \/
   ((npars + nargs - (tlength args)) <> 0 /\
    isLambda (etaExp_cnstr i m npars nargs args)).
Proof.
  intros. unfold etaExp_cnstr. destruct (npars + nargs - (tlength args)).
  - left. auto.
  - right. cbn. auto.
Qed.
***)

Lemma isApp_strip:
  forall fn,
    ~ L2d.term.isConstruct fn ->
    forall arg args, strip (L2d.compile.TApp fn arg args) = TApp (strip fn) (strip arg) (strips args).
Proof.
  destruct fn; cbn; intros; auto. elim H. auto.
Qed.
 ********************)

(************* *************
Goal
  forall i m aArgs npars nargs p,
    WcbvEval p (etaExpand i m aArgs npars nargs)
             (etaExpand i m aArgs npars nargs).
Proof.
  induction aArgs; induction npars; cbn; intros.
  - cbn. repeat constructor.
  -             
 ****************)

(***
Goal
  forall na aArgs tin nin F cArgs,
    instantiate tin nin
                (etaExpand_args_Lam na aArgs F cArgs) =
    etaExpand_args_Lam na (instantiates tin nin aArgs) F
                       (instantiates tin nin cArgs).
Proof.
  induction na; induction aArgs; intros; cbn.
  - admit.



  Goal
  forall aArgs np tin nin i n na,
    instantiate tin nin (etaExpand i n aArgs np na) =
    etaExpand i n (instantiates tin nin aArgs) np na.
Proof.
  induction aArgs; induction np; intros.
  - cbn. unfold etaExpand_args_Construct. destruct na.
    + reflexivity.
    +
****)

(****
Goal
  forall arg n t s,
    CanonicalP strip t (strip s) = Some (i, m, us, np, na) ->
    instantiate (strip arg) n 
      CanonicalP strip (L2d.term.instantiate arg n t)
           (strip (L2d.term.instantiate arg n s)) =
      instantiate (strip arg) n (CanonicalP strip t (strip s)).         
***************)
  
(****
Goal
  forall arg n t s,
    CanonicalP strip t (strip s) = None ->
      CanonicalP strip (L2d.term.instantiate arg n t)
           (strip (L2d.term.instantiate arg n s)) = None.
Proof.
  induction t; intros.
  - cbn. destruct (nat_compare n n0).
    + functional inversion H. subst.
    + reflexivity.
    + reflexivity.
 ***************)

(***  essential *****
Lemma instantiate_hom:
  (forall bod arg n,
     strip (L2d.term.instantiate arg n bod) =
     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n,
     strips (L2d.term.instantiates arg n bods) =
     instantiates (strip arg) n (strips bods)) /\
  (forall bods arg n,
     stripBs (L2d.term.instantiateBrs arg n bods) =
     instantiateBrs (strip arg) n (stripBs bods)) /\
  (forall ds arg n,
          stripDs (L2d.term.instantiateDefs arg n ds) =
     instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2d.compile.TrmTrmsBrsDefs_ind; intros; try (cbn; reflexivity);
  try (cbn; rewrite H; reflexivity).
  - cbn. destruct (lt_eq_lt_dec n0 n); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_lt n0 n)); try omega. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_gt n0 n)); trivial.
  - cbn. rewrite H. rewrite H0. reflexivity.
  - change
      (strip (L2d.compile.TApp (L2d.term.instantiate arg n t)
                               (L2d.term.instantiate arg n t0)) =
       instantiate (strip arg) n (strip (L2d.compile.TApp t t0))).
    rewrite TApp_hom. rewrite TApp_hom.
    rewrite H0. rewrite H.

    destruct (CanonicalP strip (L2d.term.instantiate arg n t)
                         (strip (L2d.term.instantiate arg n t0))).
    + repeat (destruct p). 
      destruct (CanonicalP strip t (strip t0)).
      * repeat (destruct p).

      
    - admit. (***  cbn. rewrite H. rewrite H0. reflexivity. ***)
  - change
      (strip (L2d.term.instantiate arg n2 (L2d.compile.TConstruct i n n0 n1)) =
       instantiate (strip arg) n2 (strip (L2d.compile.TConstruct i n n0 n1))).
    unfold strip at 3.
    cbn. destruct n0.
    +
    
      (strip (term.instantiate arg n0 (L2d.compile.TConstruct i n t)) =
       TConstruct i n (instantiates (strip arg) n0 (strips t))).
    rewrite <- H; trivial.
  - change
     (TCase i (strip (L2d.term.instantiate arg n t))
            (stripBs (L2d.compile.instantiateBrs arg n b)) =
      TCase i (instantiate (strip arg) n (strip t))
            (instantiateBrs (strip arg) n (stripBs b))).
    rewrite H; trivial. rewrite H0; trivial.
  - change
      (TFix
         (stripDs (L2d.term.instantiateDefs
                     arg (n0 + (L2d.compile.dlength d)) d)) n =
       TFix (instantiateDefs
               (strip arg) (n0 + (dlength (stripDs d))) (stripDs d)) n).
    rewrite H. rewrite stripDs_pres_dlength. reflexivity.
  - rewrite L2d.stripEvalCommute.instantiates_tcons_commute.
    rewrite tcons_hom. rewrite tcons_hom. rewrite instantiates_tcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2d.stripEvalCommute.instantiates_bcons_commute.
    rewrite bcons_hom. rewrite bcons_hom. rewrite instantiateBs_bcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2d.stripEvalCommute.instantiates_dcons_commute.
    rewrite dcons_hom. rewrite dcons_hom. rewrite instantiateDs_dcons.
    rewrite <- H; trivial. rewrite H0; trivial.
Qed.
 *****************)

Lemma nLambda_isLambda:
  forall np F, exists G, (nLambda (S np) F) = fun b => TLambda nAnon (G b).
Proof.
  induction np; intros; cbn; exists F; reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm bod,
    strip (L2d.compile.TLambda nm bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma whBetaStep_hom:
  forall bod arg,
    strip (L2d.term.whBetaStep bod arg) =
    whBetaStep (strip bod) (strip arg).
Proof.
Admitted.
(*************
  intros. unfold L2d.term.whBetaStep, whBetaStep.
  Check (proj1 instantiate_hom).
  rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.
 **************)

(************* MAIN *************
Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2d.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2d.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L2d.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
    try (solve[constructor; trivial]).
  - unfold strip. destruct np.
    + unfold etaExpand. unfold etaExpand_args_Construct. destruct na.
      * econstructor. econstructor.
      *{ destruct (isLambda_etaExpand_args_Lam_Lam
                     na tnil (TConstruct i r) (tunit (TRel 0))).
         - dstrctn H. rewrite j. constructor.
         - dstrctn H. rewrite j. constructor. }
    + unfold etaExpand. destruct (nLambda_isLambda np (TConstruct i r)).
      rewrite H.
      destruct (isLambda_etaExpand_args_Lam_Lam na tnil x tnil). 
      * dstrctn H0. rewrite j. constructor.
      * dstrctn H0. rewrite j. constructor.
  - cbn. econstructor; try eassumption.
    + apply lookupDfn_hom. eassumption.
  - rewrite TApp_hom. cbn. destruct (CanonicalP strip fn (strip a1)).
    + admit.  (**** eta expand  ***
destruct p0 as [[[[y0 y1] y2] y3] y4].
      destruct (isLambda_etaExpand y4 y2 y0 y1 y3) as [h|[h|h]].
      * dstrctn h. rewrite j. eapply wAppLam.
          unfold lifts. unfold compile.tappend. induction na.
         - cbn. econstructor. econstructor. econstructor. econstructor.
               *****************)
    + rewrite TLambda_hom in H. eapply wAppLam; try eassumption.
Check whBetaStep_hom.

unfold etaExpand_args_Lam.
  - cbn. destruct np; cbn.
    + destruct na; cbn. econstructor.

  - cbn. destruct np; cbn.
    + destruct na; cbn.
      * constructor. constructor.
      * assert (j: na >= tlength tnil). cbn. omega.
        destruct (@na_isLambda_etaExpand_args
                 na tnil j (fun b => TConstruct i r b)
                 (tunit (TRel 0))) as [x0 [x1 jx]].
        rewrite jx. constructor.
    + assert (j: na >= tlength tnil). cbn. omega.
      destruct (@na_isLambda_etaExpand_args
                  na tnil j (fun b => TConstruct i r b) tnil)
        as [x0 [x1 jx]]. rewrite jx. constructor.
  - cbn. econstructor; try eassumption. apply lookupDfn_hom. assumption.
  - destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      inversion_Clear w.
    + simpl. destruct fn; cbn; try inversion_Clear w.

      cbn in H. econstructor; try eassumption.

      
    + rewrite (isApp_strip n a1 args). eapply wAppLam. eassumption. eapply H0.
      change
        (WcbvEval (stripEnv p) (strip (L2d.term.whBetaStep bod a1' args)) (strip s)) in H1.


      unfold strip at 1 in H1. eapply H1.
      cbn.
      change
        (WcbvEval (stripEnv p) (strip (L2d.compile.TApp fn a1 args)) (strip s)).
      change
        (WcbvEval (stripEnv p) (strip (L2d.compile.TApp fn a1 args)) (strip s)).

  - cbn. eapply wAppLam.
    + apply H. 
    + apply H0. 
    + rewrite whBetaStep_hom in H1. assumption.
  - cbn. eapply wLetIn.
    + apply H. 
    + rewrite <- (proj1 instantiate_hom). assumption.
  - cbn. eapply wAppFix.
    + eapply H.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite <- pre_whFixStep_hom in H0. eapply H0.
  - destruct (WcbvEvals_tcons_tcons H0) as [a' [args' j]]. rewrite j in H0.
    cbn. rewrite mkApp_hom. eapply wAppCong. try eassumption.
    + intros h. elim n. apply isLambda_hom. assumption.
    + intros h. elim n0. apply isFix_hom. assumption.
    + rewrite j. cbn in H0. assumption.
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
*****)

(*******************  broken from here  *****
Lemma instantiate_hom:
  (forall bod n, L2d.term.WFTrm bod n -> 
                 forall arg, strip (L2d.term.instantiate arg n bod) =
                             instantiate (strip arg) n (strip bod)) /\
  (forall bods n, L2d.term.WFTrms bods n ->
                  forall arg, strips (L2d.term.instantiates arg n bods) =
                              instantiates (strip arg) n (strips bods)) /\
  (forall bods n, L2d.term.WFTrmBs bods n ->
                  forall arg, stripBs (L2d.term.instantiateBrs arg n bods) =
                              instantiateBrs (strip arg) n (stripBs bods)) /\
  (forall ds n, L2d.term.WFTrmDs ds n  ->
                forall arg, stripDs (L2d.term.instantiateDefs arg n ds) =
                            instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2d.term.WFTrmTrmsBrsDefs_ind; intros;
    try (cbn; reflexivity); try (cbn; rewrite H0; reflexivity).
  - cbn. rewrite (proj1 (nat_compare_gt n m)). reflexivity. omega.
  - cbn. rewrite H0. rewrite H2. reflexivity.
  - rewrite L2d.term.instantiate_TApp_mkApp.
    change
      (strip (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                            (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts))) =
       instantiate (strip arg) n (strip (L2d.compile.TApp fn t ts))).
    destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      unfold L2d.term.instantiate at 1.
      rewrite L2d.term.mkApp_goodFn; try not_isApp.
      change
        (strip
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (tcons (strip (L2d.term.instantiate arg n t))
                             (strips (L2d.term.instantiates arg n ts))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      rewrite H3. rewrite H5.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (strip arg) n
                                    (tcons (strip t) (strips ts))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (strip t) (strips ts)))).
      destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 (tcons (strip t) (strips ts))).
      * { rewrite H6.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (instantiates
                                     (strip arg) n (tcons (strip t)
                                                          (strips ts)))).
          - rewrite H7.
         

      
    destruct (L2d.term.isApp_dec (L2d.term.instantiate arg n fn)).
    + destruct i as [x0 [x1 [x2 jx]]]. rewrite jx.

      
    + rewrite L2d.term.mkApp_goodFn; try assumption.
      destruct (L2d.term.isConstruct_dec (L2d.term.instantiate arg n fn)).
      * destruct i as [x0 [x1 [x2 [x3 jx]]]]. rewrite jx.
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (tcons (strip (L2d.term.instantiate arg n t))
                               (strips (L2d.term.instantiates arg n ts))) =
           instantiate (strip arg) n (strip (L2d.compile.TApp fn t ts))).
        rewrite H3. rewrite H5.
        assert (k: fn = TConstruct x0 x1 tnil).


  (***************
  - destruct (L2d.term.isConstruct_dec t).
    + change (strip (L2d.term.mkApp
                       (L2d.term.instantiate arg n t)
                       (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                         (L2d.term.instantiates arg n t1))) =
              instantiate (strip arg) n (strip (L2d.compile.TApp t t0 t1))).
      destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn;
        [ | intros h; cbn in h; destruct h as [y0 [y1 [y2 jy]]]; discriminate].
      rewrite TAppCnstr_hom. unfold L2d.term.instantiate at 1.
      change
        (etaExp_cnstr x0 x1 x2 x3 
                      (tcons (strip (L2d.term.instantiate arg n t0))
                             (strips (L2d.term.instantiates arg n t1))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (strip t0) (strips t1)))).
      rewrite H1. rewrite H0.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (strip arg) n
                                    (tcons (strip t0) (strips t1))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (strip t0) (strips t1)))).
      destruct (etaExp_spec x0 x1 x2 x3 (tcons (strip t0) (strips t1)))
        as [[j0 j1] | [j0 j1]];
      destruct  (etaExp_spec x0 x1 x2 x3
                             (instantiates (strip arg) n
                                           (tcons (strip t0) (strips t1))))
        as [[k0 k1] | [k0 k1]];
      rewrite instantiates_pres_tlength in *; try contradiction.
      * cbn in H.
      
      * destruct j1 as [z0 [z1 [z2 jz]]]. rewrite jz;
          destruct k1 as [w0 [w1 [w2 kw]]]; rewrite kw.
        
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (instantiates (strip arg) n (tcons (strip t0) (strips t1))) =
           instantiate (strip arg) n (TConstruct z0 z1 z2))




   
    rewrite TApp_hom. 
    change
      (strip (L2d.term.mkApp
                (L2d.term.instantiate arg n t)
                (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                   (L2d.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
     ****************)
  - cbn. unfold etaExp_cnstr. cbn.
    replace (n0 + n1 - 0) with (n0 + n1); try omega.
    induction n0.
    + cbn.
    
  - change (TCase p (strip (L2d.term.instantiate arg n t0))
                  (stripDs (L2d.term.instantiateDefs arg n d)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiateDefs (strip arg) n (stripDs d)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L2d.term.instantiateDefs
                             arg (n0 + L2d.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2d.term.instantiate arg n t))
                  (strips (L2d.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2d.term.instantiate arg n1 t0)) n0
                  (stripDs (L2d.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.
 ****************************)

(*****************  broken from here  ************
Lemma instantiate_hom:
  (forall bod arg n, strip (L2d.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n, strips (L2d.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
  (forall bods arg n, stripBs (L2d.term.instantiateBrs arg n bods) =
                    instantiateBrs (strip arg) n (stripBs bods)) /\
  (forall ds arg n, stripDs (L2d.term.instantiateDefs arg n ds) =
                    instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2d.compile.TrmTrmsBrsDefs_ind; intros; try (cbn; reflexivity);
    try (cbn; rewrite H; reflexivity).
  - cbn. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - cbn. rewrite H. rewrite H0. reflexivity.
  - admit.
    (***************
  - destruct (L2d.term.isConstruct_dec t).
    + change (strip (L2d.term.mkApp
                       (L2d.term.instantiate arg n t)
                       (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                         (L2d.term.instantiates arg n t1))) =
              instantiate (strip arg) n (strip (L2d.compile.TApp t t0 t1))).
      destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn;
        [ | intros h; cbn in h; destruct h as [y0 [y1 [y2 jy]]]; discriminate].
      rewrite TAppCnstr_hom. unfold L2d.term.instantiate at 1.
      change
        (etaExp_cnstr x0 x1 x2 x3 
                      (tcons (strip (L2d.term.instantiate arg n t0))
                             (strips (L2d.term.instantiates arg n t1))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (strip t0) (strips t1)))).
      rewrite H1. rewrite H0.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (strip arg) n
                                    (tcons (strip t0) (strips t1))) =
         instantiate (strip arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (strip t0) (strips t1)))).
      destruct (etaExp_spec x0 x1 x2 x3 (tcons (strip t0) (strips t1)))
        as [[j0 j1] | [j0 j1]];
      destruct  (etaExp_spec x0 x1 x2 x3
                             (instantiates (strip arg) n
                                           (tcons (strip t0) (strips t1))))
        as [[k0 k1] | [k0 k1]];
      rewrite instantiates_pres_tlength in *; try contradiction.
      * cbn in H.
      
      * destruct j1 as [z0 [z1 [z2 jz]]]. rewrite jz;
          destruct k1 as [w0 [w1 [w2 kw]]]; rewrite kw.
        
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (instantiates (strip arg) n (tcons (strip t0) (strips t1))) =
           instantiate (strip arg) n (TConstruct z0 z1 z2))




   
    rewrite TApp_hom. 
    change
      (strip (L2d.term.mkApp
                (L2d.term.instantiate arg n t)
                (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                   (L2d.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
     ****************)
  - cbn. unfold etaExp_cnstr. cbn.
    replace (n0 + n1 - 0) with (n0 + n1); try omega.
    induction n0.
    + cbn.
    
  - change (TCase p (strip (L2d.term.instantiate arg n t0))
                  (stripDs (L2d.term.instantiateDefs arg n d)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiateDefs (strip arg) n (stripDs d)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L2d.term.instantiateDefs
                             arg (n0 + L2d.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2d.term.instantiate arg n t))
                  (strips (L2d.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2d.term.instantiate arg n1 t0)) n0
                  (stripDs (L2d.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.
  
Lemma whBetaStep_hom:
  forall bod arg args,
    L2d.term.WFTrm bod 0 ->
    strip (L2d.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
Proof.
  intros bod arg args h.
  unfold L2d.term.whBetaStep, whBetaStep.
  destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    apply (proj1 instantiate_hom). assumption.
  - rewrite <- (proj1 instantiate_hom); try assumption.
    destruct (L2d.term.isApp_dec (L2d.term.instantiate arg 0 bod)).
    + destruct i as [x0 [x1 [x2 jx]]]. rewrite jx. clear jx.
    change
      (strip (L2d.compile.TApp
                x0 x1 (L2d.term.tappend x2 (L2d.compile.tcons t args))) =
       mkApp (strip (L2d.compile.TApp x0 x1 x2))
             (strips (L2d.compile.tcons t args))).
    destruct (L2d.term.isConstruct_dec x0).
      * { destruct i as [i0 [i1 [i2 [i3 ji]]]]. subst.
        change
          (etaExp_cnstr i0 i1 i2 i3
                        (tcons (strip x1)
                               (strips (L2d.term.tappend
                                          x2 (L2d.compile.tcons t args)))) =
           mkApp (etaExp_cnstr i0 i1 i2 i3
                        (tcons (strip x1) (strips x2)))
                 (strips (L2d.compile.tcons t args))).
        rewrite strips_tappend. rewrite tcons_hom.   
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                        (tcons (strip x1) (strips x2))).
          - rewrite H. rewrite mkApp_goodFn; try not_isApp.
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                         (tcons (strip x1)
                                                (compile.tappend (strips x2) (tcons (strip t) (strips args))))).
        rewrite H0.

        rewrite <- (proj1 instantiate_hom); try assumption.
    rewrite jx. destruct (L2d.term.isConstruct_dec x0).
    + destruct i as [y0 [y1 [y2 [y3 jy]]]]. subst.
      change
        (etaExp_cnstr y0 y1 y2 y3
                      (tcons (strip x1) (strips (L2d.term.tappend x2 args))) =
         mkApp (etaExp_cnstr y0 y1 y2 y3
                             (tcons (strip x1) (strips x2)))
               (strips args)).
      destruct (etaExp_cnstr_Sanity'
                  y0 y1 y2 y3
                  (tcons (strip x1) (strips (L2d.term.tappend x2 args)))),
      (etaExp_cnstr_Sanity'  y0 y1 y2 y3 (tcons (strip x1) (strips x2)));
        rewrite H; rewrite H0.
      * { cbn. destruct args. cbn.
          - apply f_equal3; try reflexivity.
            apply f_equal3; try reflexivity.
            apply f_equal2; try reflexivity.
            rewrite L2d.term.tappend_tnil. reflexivity.
          -


        
      * rewrite H.      Check mkApp_hom.
  - destruct args.
    + rewrite L2d.term.mkApp_tnil_ident. cbn. rewrite mkApp_tnil_ident.
      apply (proj1 instantiate_hom). assumption.
    + rewrite L2d.term.mkApp_goodFn; try assumption.
      change
        (strip (L2d.compile.TApp (L2d.term.instantiate arg 0 bod) t args) =
         mkApp (instantiate (strip arg) 0 (strip bod))
               (tcons (strip t) (strips args))).
      rewrite mkApp_goodFn.
      * admit.        
      * intros k. elim n. apply strip_pres_isApp.
        rewrite (proj1 instantiate_hom); assumption.       
Qed.


        rewrite mkApp_hom.
  - apply f_equal2; try reflexivity.
    rewrite <- (proj1 instantiate_hom). reflexivity. assumption.
  - inversion_Clear h; try omega; try cbn; try not_isApp.
Qed.

(***
Lemma TConstruct_hom:
  forall i n args,
    strip (L2d.compile.TConstruct i n args) = TConstruct i n args.
intros. simpl.  destruct i. reflexivity.
Qed.
***)

Lemma optStrip_match:
  forall x (f:L2Term -> L2Term) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L2d.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (stripDs brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L2d.term.whCaseStep. cbn. 
  rewrite <- dnthBody_hom. destruct (compile.dnthBody n brs); simpl.
  + destruct p as [x0 x1]. cbn. rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L2d.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod,
    strip (L2d.compile.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.


Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L2d.compile.TLetIn nm dfn ty bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L2d.compile.TCase n ty mch brs) =
    TCase n (strip mch) (stripDs brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L2Term -> nat -> L2Term) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L2Term),
  (forall (s:L2Term) (n:nat), strip (F s n) = stripF (strip s) n) ->
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
    strip (L2d.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L2d.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L2d.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L2d.compile.prop). simpl. reflexivity.
Qed.

Lemma tsplit_hom:
  forall ix arg args,
    optStrip_split (L2d.term.tsplit ix arg args) =
    tsplit ix (strip arg) (strips args).
Proof.
  intros ix arg args.
  functional induction (L2d.term.tsplit ix arg args); cbn; intros.
  - reflexivity.
  - destruct n. elim y. reflexivity.
  - destruct ls; cbn; reflexivity.
  - case_eq (tsplit m (strip t) (strips ts)); intros.
    + destruct s.
      assert (j0:= L2d.term.tsplit_sanity m t ts). rewrite e1 in j0.
      assert (j1:= tsplit_sanity m (strip t) (strips ts)).
      rewrite H in j1. destruct j1.
      assert (j2: tlength (strips ts) = tlength fsts + tlength lsts).
      { apply (f_equal tlength) in H0. rewrite tlength_tappend in H0.
        cbn in H0. omega. }
      rewrite tlength_hom in j2. rewrite j2 in j0. rewrite H1 in j0. omega.
    + reflexivity.
  - destruct (tsplit m (strip t) (strips ts)).
    + destruct s0. rewrite e1 in IHo. rewrite optStrip_split_hom in IHo.
      myInjection IHo. reflexivity.
    + rewrite e1 in IHo.  rewrite optStrip_split_hom in IHo.
      discriminate.
Qed.

Lemma optStripCanP_hom':
  forall z, optStripCanP (Some z) =
            Some (fst (fst z), strips (snd (fst z)), snd z).
intros. destruct z as [[z0 z1] z2]. cbn. reflexivity.
Qed.

Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2d.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2d.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L2d.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[constructor; trivial]).
  - cbn. econstructor; try eassumption. apply lookupDfn_hom. assumption.
  - cbn. eapply wAppLam.
    + apply H. 
    + apply H0. 
    + rewrite whBetaStep_hom in H1. assumption.
  - cbn. eapply wLetIn.
    + apply H. 
    + rewrite <- (proj1 instantiate_hom). assumption.
  - cbn. eapply wAppFix.
    + eapply H.
    + apply H0.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite tlength_hom. assumption.
    + rewrite <- pre_whFixStep_hom in H1. eapply H1.
  - destruct (WcbvEvals_tcons_tcons H0) as [a' [args' j]]. rewrite j in H0.
    cbn. rewrite mkApp_hom. eapply wAppCong. try eassumption.
    + intros h. elim n. apply isLambda_hom. assumption.
    + intros h. elim n0. apply isFix_hom. assumption.
    + rewrite j. cbn in H0. assumption.
  - cbn. eapply wAppFixCong1; try eassumption.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite tlength_hom. assumption. 
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    +

      
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.

(** WcbvEval_hom is nice, but it is stronger than necessary to prove 
*** certiL2_to_L2Correct (in instances.v).
**)
Corollary strip_pres_eval:
  forall (p:environ L2d.compile.Term) (t tv:L2d.compile.Term),
    L2d.wcbvEval.WcbvEval p t tv ->
    exists stv, WcbvEval (stripEnv p) (strip t) stv.
Proof.
  intros. exists (strip tv). apply (proj1 (WcbvEval_hom _)).
  assumption.
Qed.

Corollary wcbvEval_hom:
  forall p n t t',
    L2d.wcbvEval.wcbvEval p n t = Ret t' ->
    exists m, wcbvEval (stripEnv p) m (strip t) = Ret (strip t').
Proof.
  intros. 
  assert (j1:= proj1 (L2d.wcbvEval.wcbvEval_WcbvEval p n) _ _ H).
  assert (k0:= proj1 (WcbvEval_hom p) _ _ j1).
  assert (j2:= @WcbvEval_wcbvEval (stripEnv p) (strip t) (strip t') k0).
  destruct j2 as [ny jny].
  exists ny. eapply jny. omega.
Qed.


Lemma Prf_strip_inv:
  forall s st, TProof st = strip s ->
              exists t, s = L2d.compile.TProof t /\ st = strip t.
Proof.
  destruct s; simpl; intros h; try discriminate.
  intros. myInjection H. exists s. intuition.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L2d.compile.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L2d.compile.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm sty, 
     (L2d.compile.TCast stm sty) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n arty s,
    TConstruct i n arty = strip s -> L2d.compile.TConstruct i n arty = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L2d.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L2d.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L2d.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L2d.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L2d.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L2d.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L2d.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = stripDs sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, d. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L2d.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L2d.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L2d.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L2d.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (stripDs bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

Definition excStrip (t:exception L2Term) : exception Term :=
  match t with
    | Exc str => Exc str
    | Ret t => Ret (strip t)
  end.


Theorem L2WcbvEval_sound_for_L2WcbvEval:
  forall (p:environ L2d.compile.Term) (t:L2d.compile.Term) (L2s:Term),
    WcbvEval (stripEnv p) (strip t) L2s ->
  forall s, L2d.wcbvEval.WcbvEval p t s -> L2s = strip s.
Proof.
  intros. refine (WcbvEval_single_valued _ _).
  - eassumption.
  - apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L2WcbvEval.


Lemma sound_and_complete:
  forall (p:environ L2d.compile.Term) (t s:L2d.compile.Term),
    L2d.wcbvEval.WcbvEval p t s ->
    WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros p t s h. apply (proj1 (WcbvEval_hom p)). assumption.
Qed.

Lemma sac_complete:
  forall p t s, L2d.wcbvEval.WcbvEval p t s ->
                WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros. apply sound_and_complete. assumption.
Qed.

Lemma sac_sound:
  forall p t s, L2d.wcbvEval.WcbvEval p t s ->
  forall L2s, WcbvEval (stripEnv p) (strip t) L2s -> L2s = strip s.
Proof.
  intros p t s h1 L2s h2.
  apply (WcbvEval_single_valued h2). apply (sound_and_complete h1).
Qed. 
Print Assumptions sac_sound.

 *******************************)

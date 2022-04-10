Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.

Require Import Common.Common.

From MetaCoq.Template Require Import BasicAst Ast.
From MetaCoq.Erasure Require Import EAst EAstUtils.

Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
Require Import L2k.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2dTerm := EAst.term.
Definition L2dTerms := list EAst.term.
Definition L2dBrs := list (branch EAst.term).
Definition L2dDefs := list (def EAst.term).

From MetaCoq.Erasure Require Import ESpineView EWcbvEvalEtaInd EWellformed EEtaExpanded.

Definition term_flags :=
  {|
    has_tBox := true;
    has_tRel := true;
    has_tVar := false;
    has_tEvar := false;
    has_tLambda := true;
    has_tLetIn := true;
    has_tApp := true;
    has_tConst := true;
    has_tConstruct := true;
    has_tCase := true;
    has_tProj := true;
    has_tFix := true;
    has_tCoFix := false
  |}.

Definition env_flags := 
  {| has_axioms := false;
    has_cstr_params := false;
    term_switches := term_flags |}.

Local Existing Instance env_flags.

Section OnGlobalEnv.
  Context (Σ : global_context).

  Notation compile := (compile Σ).

  Definition compile_terms ts := list_terms (map compile ts).
  
  Definition compile_br (br : list name * EAst.term) :=
    (List.rev (fst br), compile (snd br)).

  Definition compile_brs ts := list_Brs (map compile_br ts).

  Definition compile_def d :=
    {| dname := dname d; dbody := compile d.(dbody); rarg := d.(rarg) |}.

  Definition compile_defs ts := list_Defs (map compile_def ts).

Definition optcompile (t:option L2dTerm) : option Term :=
  match t with
    | None => None
    | Some t => Some (compile t)
  end.
Definition optcompile_terms (ts:option L2dTerms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (compile_terms ts)
  end.
Definition optcompileDnth (b: option L2dTerm): option Term :=
                           match b with
                             | None => None
                             | Some t => Some (compile t)
                           end.
Definition optcompileCanP
           (b: option (nat * L2dTerms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, compile_terms t, m)
                           end.
(**********************
Definition optcompile_split
           (b: option L2d.term.split): option split :=
  match b with
    | None => None
    | Some (L2d.term.mkSplit fsts t lsts) =>
      Some (mkSplit (compile_terms fsts) (compile t) (compile_terms lsts))
  end.
******************)

Lemma optcompile_hom: forall y, optcompile (Some y) = Some (compile y).
induction y; simpl; reflexivity.
Qed.
Lemma optcompile_hom_None: optcompile (@None L2dTerm) = @None (Term).
  reflexivity.
Qed.

Lemma optcompile_terms_hom: forall y, optcompile_terms (Some y) = Some (compile_terms y).
induction y; simpl; reflexivity.
Qed.
Lemma optcompileDnth_hom:
  forall y, optcompileDnth (Some y) = Some (compile y).
induction y; simpl; reflexivity.
Qed.
Lemma optcompileCanP_hom:
  forall y n m, optcompileCanP (Some (n, y, m)) = Some (n, compile_terms y, m).
induction y; simpl; reflexivity.
Qed.
(*********************
Lemma optcompile_split_hom:
  forall fsts t lsts,
    optcompile_split (Some (L2d.term.mkSplit fsts t lsts)) =
    Some (mkSplit (compile_terms fsts) (compile t) (compile_terms lsts)).
Proof.
  induction fsts; cbn; intros; try reflexivity.
Qed.
 ***********************)

Lemma tlength_hom:
  forall ts, tlength (compile_terms ts) = List.length ts.
Proof.
  induction ts; intros; try reflexivity.
  - cbn. apply f_equal. assumption.
Qed.

From Coq Require Import ssreflect.
From MetaCoq.Template Require Import utils.
From MetaCoq.Erasure Require Import EGlobalEnv EExtends.

Lemma Lookup_hom:
  forall s ec, lookup_env Σ s = Some ec -> 
    ∑ Σ', extends Σ' Σ × lookup s (compile_ctx Σ) = Some (compile_global_decl Σ' ec).
Proof.
  induction Σ; cbn => //.
  intros s ec.
  case: eqb_specT.
  - intros -> [= <-].
    exists g. split. now exists [a].
    destruct a as [kn d]; cbn.
    now rewrite eqb_refl.
  - intros neq hl.
    destruct (IHg _ _ hl) as [Σ' [ext hl']].
    exists Σ'. split.
    destruct ext as [Σ'' ->]. now exists (a :: Σ'').
    destruct a as [kn d]; cbn.
    cbn in neq; case: eqb_specT => //.
Qed.
  
Lemma lookup_hom_None:
  forall nm,
    lookup_env Σ nm = None -> lookup nm (compile_ctx Σ) = None.
Proof.
  induction Σ; intros.
  - cbn. reflexivity.
  - destruct a. cbn in *.
    destruct (eqb_spec nm k) => //.
    now apply IHg.
Qed.
  
(*Lemma LookupDfn_hom:
  forall p s t, LookupDfn s p t -> LookupDfn s (compile_ctx Σ) (compile t).
Proof.
  unfold LookupDfn. intros.
  assert (j:= Lookup_hom H). exact j.
Qed.

Lemma lookupDfn_hom:
  forall p nm t,
    lookupDfn nm p = Ret t -> lookupDfn nm (compile_ctx Σ) = Ret (compile t).
Proof.
  induction p; intros.
  - cbn in *. discriminate.
  - destruct a. unfold lookupDfn. cbn. unfold lookupDfn in H. cbn in H.
    destruct (kername_eq_dec nm k).
    + subst. cbn. cbn in H.
      rewrite eq_kername_refl. rewrite eq_kername_refl in H.
      destruct e; try discriminate.
      * myInjection H. cbn. reflexivity.
    + rewrite (eq_kername_bool_neq n). rewrite (eq_kername_bool_neq n) in H.
      case_eq (lookup nm p); intros; rewrite H0 in H; try discriminate.
      * rewrite (lookup_hom _ _ H0). destruct e0; try discriminate.
        cbn. myInjection H. reflexivity.
Qed.
*)

Lemma dlength_hom:
  forall ds, List.length ds = dlength (compile_defs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, compile_terms (cons t ts) = tcons (compile t) (compile_terms ts).
reflexivity.
Qed.

Lemma tnil_hom: compile_terms nil = tnil.
reflexivity.
Qed.
(* 
Lemma dcons_hom:
  forall nm bod rarg ds,
    compile_defs (L1g.compile.dcons nm bod rarg ds) =
    dcons nm (compile bod) rarg (compile_defs ds).
reflexivity.
Qed. *)
(* 
Lemma dnil_hom: compile_defs L1g.compile.dnil = dnil.
reflexivity.
Qed. *)
(* 
Lemma dnthBody_hom: 
  forall m ds, optcompileDnth (option_map fst (L1g.compile.dnthBody m ds)) =
               dnthBody m (compile_defs ds).
induction m; induction ds; try intuition auto.
- simpl. unfold dnthBody. simpl. apply IHm.
Qed. *)

Lemma tnth_hom:
 forall ts n, optcompile (List.nth_error ts n) = tnth n (compile_terms ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

(* Lemma tskipn_hom: *)
(*   forall ts n, optcompile_terms (List.skipn n ts) = tskipn n (compile_terms ts). *)
(* induction ts; simpl; intros n; case n; try reflexivity; trivial. *)
(* Qed. *)

Lemma tappend_hom:
  forall ts us : list EAst.term,
    compile_terms (List.app ts us) = tappend (compile_terms ts) (compile_terms us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  cbn. f_equal. apply IHts.
Qed.

(* Lemma TApp_hom:
  forall fn arg,
    compile (TApp fn arg) =
    match CanonicalP compile fn (compile arg) with
    | None => TApp (compile fn) (compile arg)
    | Some (F, args, npars, nargs) => etaExpand F args npars nargs
    end.
Proof.
  reflexivity.
Qed. *)

(***
Lemma TAppCnstr_hom:
  forall i m npars nargs arg args, 
    compile (L2d.compile.TApp (L2d.compile.TConstruct i m npars nargs) arg args) =
    etaExpand i m npars nargs (tcons (compile arg) (compile_terms args)).
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

(*****
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
  forall t, isApp (compile t) -> L2d.term.isApp t.
Proof.
Admitted.
(************
  destruct t; intros h; destruct h as [x0 [x1 jx]]; try discriminate.
  - auto.
  - unfold compile in jx. 
    elim (notIsApp_etaExpand i n tnil n0 n1). rewrite jx. auto.
Qed.
 *****************)   

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
    isLambda (compile t) ->
    L2d.term.isLambda t \/ L2d.term.isConstruct t \/  L2d.term.isApp t.
Proof.
  intros t. functional induction (compile t); intros h;
  destruct h as [x0 [x1 jx]]; try discriminate.
  - left. auto.
  - right. right. auto.
  - right. left. auto.
Qed.

Lemma isFix_hom:
  forall t, isFix (compile t) -> L2d.term.isFix t.
Proof.
  induction t; intros; simpl in *;
  try (destruct H as [x0 [x1 jx]]; discriminate); auto.
  - destruct t1; try (destruct H as [x0 [x1 jx]]; discriminate).
    destruct (etaExp_cnstr_Sanity' i n n0 n1 (tcons (compile t2) (compile_terms t3))).
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
  - destruct (etaExp_cnstr_Sanity' i n n0 n1 tnil).
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
    + rewrite H0 in H. destruct H as [x0 [x1 jx]]. discriminate.
  - destruct p. destruct H as [y0 [y1 jy]]. discriminate.
Qed.

Lemma L2WFapp_L2kWFapp:
  (forall t, L2d.term.WFapp t -> WFapp (compile t)) /\
  (forall ts, L2d.term.WFapps ts -> WFapps (compile_terms ts)) /\
  (forall ts, L2d.term.WFappBs ts -> WFappBs (compileBs ts)) /\
  (forall ds, L2d.term.WFappDs ds -> WFappDs (compile_defs ds)).
Proof.
  apply L2d.term.WFappTrmsBrsDefs_ind; try constructor; auto; intros.
  - destruct fn; auto; try (constructor; try assumption; not_isApp).
    + elim H. auto.
    + change
        (WFapp (match nat_compare (n0 + n1) (S (tlength (compile_terms ts))) with
        | Lt => TWrong
        | _ => etaExp_cnstr i n n0 n1 (tcons (compile t) (compile_terms ts))
        end)).
      destruct (n0 + n1 ?= S (tlength (compile_terms ts))).
      
    + apply etaExp_cnstr_pres_WFapp. constructor; assumption.
    + destruct p. constructor; try assumption. not_isApp.
  - apply etaExp_cnstr_pres_WFapp. constructor.
  - destruct m. constructor; try assumption.
Qed.

Lemma L2WFaEnv_L2kWFaEnv:
  forall p:environ L2Term, L2d.program.WFaEnv p -> WFaEnv (compile_ctx Σ).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L2WFapp_L2kWFapp)). assumption.
  - assumption.
  - apply compile_ctx_pres_fresh. assumption.
Qed.
 ************)

(***
Lemma WFapp_hom:
  (forall t, L2d.term.WFapp t -> WFapp (compile t)) /\
  (forall ts, L2d.term.WFapps ts -> WFapps (compile_terms ts)) /\
  (forall ds, L2d.term.WFappDs ds -> WFappDs (compile_defs ds)).
Proof.
   apply L2d.term.WFappTrmsDefs_ind; cbn; intros;
  try (solve [constructor]);
  try (solve [constructor; intuition]).
  - constructor; try assumption.
    + intros h. assert (j:= isApp_hom _ h). contradiction.
Qed.
 ****)
(* 
Lemma mkApp_tcons_lem1:
  forall fn arg args,
    L1g.compile.mkApp (L1g.compile.mkApp fn (cons arg args)) nil = L1g.compile.mkApp fn (cons arg args).
Proof.
  destruct fn; intros arg args; simpl;
  try rewrite tappend_tnil; try reflexivity.
Qed. *)

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
Lemma compile_App_not_Constructor:
  forall fn arg,
    ~ L2d.term.isConstruct fn ->
    compile (L2d.compile.TApp fn arg) = TApp (compile fn) (compile arg).
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
    isApp (compile (tApp fn arg)) -> ~ EAstUtils.isConstruct fn.
Proof.
Admitted.





(*******************
  intros. intro h. destruct h as [x0 [x1 [x2 [x3 jx]]]]. subst fn.
  change
    (isApp (etaExpand x0 x1 (compile_terms (L2d.compile.tunit arg)) x2 x3)) in H.
  eelim notIsApp_etaExpand. eassumption.
Qed.
 *******************)

(**********
Lemma mkApp_hom:
  forall fn args,
    ~ L2d.term.isApp fn ->
    ~ L2d.term.isConstruct fn ->
    compile (L2d.term.mkApp fn args) = mkApp (compile fn) (compile_terms args).
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
    compile (L2d.term.mkApp fn args) = mkApp (compile fn) (compile_terms args).
Proof.
  intros fn. destruct (L2d.term.isConstruct_dec fn);
  induction args; intros.
  - rewrite mkApp_tnil_ident. rewrite L2d.term.mkApp_tnil_ident. reflexivity.
  - destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
    rewrite L2d.term.mkApp_goodFn.
    change
      (etaExpand x0 x1 (tcons (compile t) (compile_terms args)) x2 x3 =
       mkApp (etaExpand x0 x1 tnil x2 x3)
             (compile_terms (L2d.compile.tcons t args))).
    specialize (IHargs H H0).
    change
      (compile (L2d.term.mkApp (L2d.compile.TConstruct x0 x1 x2 x3) args) =
       mkApp (etaExpand x0 x1 tnil x2 x3)
             (compile_terms args)) in IHargs.
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
    compile (L2d.term.mkApp fn args) = mkApp (compile fn) (compile_terms args).
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
                 forall arg, compile (L2d.term.instantiate arg n bod) =
                             instantiate (compile arg) n (compile bod)) /\
  (forall bods n, L2d.term.WFTrms bods n ->
                  forall arg, compile_terms (L2d.term.instantiates arg n bods) =
                              instantiates (compile arg) n (compile_terms bods)) /\
  (forall bods n, L2d.term.WFTrmBs bods n ->
                  forall arg, compileBs (L2d.term.instantiateBrs arg n bods) =
                              instantiateBrs (compile arg) n (compileBs bods)) /\
  (forall ds n, L2d.term.WFTrmDs ds n  ->
                forall arg, compile_defs (L2d.term.instantiateDefs arg n ds) =
                            instantiateDefs (compile arg) n (compile_defs ds)).
Proof.
  apply L2d.term.WFTrmTrmsBrsDefs_ind; intros;
    try (cbn; reflexivity); try (cbn; rewrite H0; reflexivity).
  - cbn. rewrite (proj1 (nat_compare_gt n m)). reflexivity. omega.
  - cbn. rewrite H0. rewrite H2. reflexivity.
  - destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      change
        (compile
           (L2d.term.instantiate
              arg n (L2d.compile.TApp
                       (L2d.compile.TConstruct x0 x1 x2 x3) t ts)) =
         instantiate (compile arg) n
                     (compile (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      change
        (compile
           (L2d.term.mkApp
              (L2d.term.instantiate
                 arg n (L2d.compile.TConstruct x0 x1 x2 x3))
              (L2d.term.instantiates arg n (L2d.compile.tcons t ts))) =
         instantiate (compile arg) n
                     (compile (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      rewrite mkApp_hom.
      
      
      change
        (compile (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                                (L2d.term.instantiate arg n t)
                                (L2d.term.instantiates arg n ts)) =
         instantiate
           (compile arg)
           n (etaExpand x0 x1 (tcons (compile t) (compile_terms ts)) x2 x3)).
      change
        (etaExpand x0 x1 (tcons (compile (L2d.term.instantiate arg n t))
                                (compile_terms (L2d.term.instantiates arg n ts)))
                                x2 x3 =
         instantiate
           (compile arg)
           n (etaExpand x0 x1 (tcons (compile t) (compile_terms ts)) x2 x3)).
      rewrite H3. rewrite H5.

      admit.
    + rewrite compile_App_not_Constructor; try assumption.
      change
        (compile (L2d.term.mkApp
                  (L2d.term.instantiate arg n fn)
                  (L2d.compile.tcons (L2d.term.instantiate arg n t)
                                    (L2d.term.instantiates arg n ts))) =
         (mkApp (instantiate (compile arg) n (compile fn))
                (tcons (instantiate (compile arg) n (compile t))
                       (instantiates (compile arg) n (compile_terms ts))))).
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
        (compile (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                              (L2d.compile.tcons
                                 (L2d.term.instantiate arg n t)

                                 (L2d.term.instantiates arg n ts))) =
         instantiate (compile arg) n (TApp (compile fn) (compile t) (compile_terms ts))).
      change
        (compile (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                              (L2d.compile.tcons
                                 (L2d.term.instantiate arg n t)
                                 (L2d.term.instantiates arg n ts))) =
         mkApp (instantiate (compile arg) n (compile fn))
               (tcons (instantiate (compile arg) n (compile t))
                      (instantiates (compile arg) n (compile_terms ts)))).
      destruct (L2d.term.isApp_dec (L2d.term.instantiate arg n fn)).
      * Check mkApp_hom.


        

      * destruct i as [x0 [x1 [x2 jx]]]. rewrite jx.
        change
          (compile
             (L2d.compile.TApp
                x0 x1 (L2d.term.tappend
                         x2 (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts)))) =
            mkApp (instantiate (compile arg) n (compile fn))
                  (tcons (instantiate (compile arg) n (compile t))
                         (instantiates (compile arg) n (compile_terms ts)))).

        
        assert (instantiate (compile arg) n (compile fn) = )
      * rewrite <- instantiate_mkApp_commute.
        rewrite (L2d.term.mkApp_goodFn _ _ n1).

        
      Check instantiate_mkApp_commute.
      rewrite <- instantiate_mkApp_commute.
      rewrite <- H3. rewrite <- H5. Check mkApp_hom.
                                          

    
  - rewrite L2d.term.instantiate_TApp_mkApp.
    change
      (compile (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                            (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts))) =
       instantiate (compile arg) n (compile (L2d.compile.TApp fn t ts))).
    destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn; try not_isApp.
      unfold L2d.term.instantiate at 1.
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (compile (L2d.term.instantiate arg n t))
                          (compile_terms (L2d.term.instantiates arg n ts)))
                   x2 x3 =
         instantiate (compile arg) n
                     (compile (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (compile (L2d.term.instantiate arg n t))
                          (compile_terms (L2d.term.instantiates arg n ts)))
                   x2 x3 =
         instantiate (compile arg) n
                     (etaExpand (TConstruct x0 x1)
                                (tcons (compile t) (compile_terms ts)) x2 x3)).
      cbn. induction x2; cbn in *.
      * { destruct x3.
          - rewrite H3. rewrite H5.
            rewrite <- tcons_hom.



        
      Eval cbn in (etaExpand (TConstruct x0 x1) (tcons (compile t) (compile_terms ts))).
      unfold etaExpand.
      cbn.
      cbn in H1. destruct x2; cbn in *.
      rewrite H3. rewrite H5.
      * admit.
      * cbn in H1.     
      

      



      change
        (compile
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (compile arg) n
                     (compile (L2d.compile.TApp
                               (L2d.compile.TConstruct x0 x1 x2 x3) t ts))).
      
      change
        (compile
           (L2d.compile.TApp
              (L2d.compile.TConstruct x0 x1 x2 x3)
              (L2d.term.instantiate arg n t)
              (L2d.term.instantiates arg n ts)) =
         instantiate
           (compile arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (instantiate (compile arg) n  (compile t))
                             (compile_terms ts)) x2 x3)).
      change
        (etaExpand (TConstruct x0 x1) (tcons (compile t) (compile_terms ts)) x2 x3 =
         instantiate
           (compile arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (compile t) (compile_terms ts)) x2 x3)).

      
      rewrite <- etaExpand_instantiate.
      * admit.
      *
      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (compile (L2d.term.instantiate arg n t))
                          (compile_terms (L2d.term.instantiates arg n ts))) x2 x3 =
         etaExpand (TConstruct x0 x1)
                   (instantiates (compile arg) n (tcons (compile t) (compile_terms ts)))
                   x2 x3).


    instantiate
           (compile arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (compile t) (compile_terms ts)) x2 x3)).

      change
        (etaExpand (TConstruct x0 x1)
                   (tcons (compile (L2d.term.instantiate arg n t))
                          (compile_terms (L2d.term.instantiates arg n ts))) x2 x3 =
         instantiate
           (compile arg) n
           (etaExpand (TConstruct x0 x1)
                      (tcons (compile t) (compile_terms ts)) x2 x3)).
      rewrite H3, H5.
      Check (etaExpand_TConstruct_instantiate x0 x1 (compile arg) n _ x2 x3).

      destruct x2.
      * cbn. rewrite <- H1.

      unfold compile at 1.
      
      change
        (compile
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (tcons (compile (L2d.term.instantiate arg n t))
                             (compile_terms (L2d.term.instantiates arg n ts))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      rewrite H3. rewrite H5.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (compile arg) n
                                    (tcons (compile t) (compile_terms ts))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 (tcons (compile t) (compile_terms ts))).
      * { rewrite H6.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (instantiates
                                     (compile arg) n (tcons (compile t)
                                                          (compile_terms ts)))).
          - rewrite H7.
         


Lemma whBetaStep_hom:
  forall bod arg args,
    L2d.term.WFTrm bod 0 ->
    compile (L2d.term.whBetaStep bod arg args) =
    whBetaStep (compile bod) (compile arg) (compile_terms args).
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
      (compile (L2d.compile.TApp
                x0 x1 (L2d.term.tappend x2 (L2d.compile.tcons t args))) =
       mkApp (compile (L2d.compile.TApp x0 x1 x2))
             (compile_terms (L2d.compile.tcons t args))).
    destruct (L2d.term.isConstruct_dec x0).
      * { destruct i as [i0 [i1 [i2 [i3 ji]]]]. subst.
        change
          (etaExp_cnstr i0 i1 i2 i3
                        (tcons (compile x1)
                               (compile_terms (L2d.term.tappend
                                          x2 (L2d.compile.tcons t args)))) =
           mkApp (etaExp_cnstr i0 i1 i2 i3
                        (tcons (compile x1) (compile_terms x2)))
                 (compile_terms (L2d.compile.tcons t args))).
        rewrite compile_terms_tappend. rewrite tcons_hom.   
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                        (tcons (compile x1) (compile_terms x2))).
          - rewrite H. rewrite mkApp_goodFn; try not_isApp.
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                         (tcons (compile x1)
                                                (compile.tappend (compile_terms x2) (tcons (compile t) (compile_terms args))))).
        rewrite H0.

        rewrite <- (proj1 instantiate_hom); try assumption.
    rewrite jx. destruct (L2d.term.isConstruct_dec x0).
    + destruct i as [y0 [y1 [y2 [y3 jy]]]]. subst.
      change
        (etaExp_cnstr y0 y1 y2 y3
                      (tcons (compile x1) (compile_terms (L2d.term.tappend x2 args))) =
         mkApp (etaExp_cnstr y0 y1 y2 y3
                             (tcons (compile x1) (compile_terms x2)))
               (compile_terms args)).
      destruct (etaExp_cnstr_Sanity'
                  y0 y1 y2 y3
                  (tcons (compile x1) (compile_terms (L2d.term.tappend x2 args)))),
      (etaExp_cnstr_Sanity'  y0 y1 y2 y3 (tcons (compile x1) (compile_terms x2)));
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
  etaExp_cnstr i n npars nargs (tcons (compile arg) (compile_terms args)) =
  TApp (etaExp_cnstr i n npars nargs tnil) (compile arg) (compile_terms args).
Proof.
  intros. induction args.
  - cbn. induction npars.
    + cbn.
****)

(****
Lemma mkApp_hom:
forall fn args, ~ L2d.term.isApp fn ->
  compile (L2d.term.mkApp fn args) = mkApp (compile fn) (compile_terms args).
Proof.
  intros. destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. reflexivity.
  - rewrite L2d.term.mkApp_goodFn; try assumption. 
    assert (j: ~ isApp (compile fn)).
    { intros h. elim H. apply isApp_hom. assumption. }

  
Admitted.
 ****)

(***
  intros. destruct args.
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. reflexivity.
  - rewrite L2d.term.mkApp_goodFn; try assumption. rewrite tcons_hom.
    assert (j: ~ isApp (compile fn)).
    { intros h. elim H. apply isApp_hom. assumption. }
    rewrite mkApp_goodFn; try assumption. destruct fn; try (cbn; reflexivity).
    change
      (etaExp_cnstr i n n0 n1 (tcons (compile t) (compile_terms args)) =
       TApp (compile (L2d.compile.TConstruct i n n0 n1)) (compile t) (compile_terms args)).
    change
      (etaExp_cnstr i n n0 n1 (tcons (compile t) (compile_terms args)) =
       TApp (etaExp_cnstr i n n0 n1 tnil) (compile t) (compile_terms args)).
           
    unfold compile in j.
    
  destruct args; try (reflexivity).
  - rewrite L2d.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    reflexivity.
  - destruct (L2d.term.isApp_dec fn).
    + admit.
    + rewrite L2d.term.mkApp_goodFn; try assumption.
      destruct (L2d.term.isConstruct_dec fn).
      * { destruct H as [x0 [x1 [x2 [x3 jx]]]]. subst. cbn.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (tcons (compile t) (compile_terms args))).
          - destruct H as [y0 [y1 [y2 jy]]]. rewrite jy.
            destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
            + destruct H as [z0 [z1 [z2 jz]]]. rewrite jz. cbn. rewrite <- jy.



              destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
          
          assert (j:= etaExp_cnstr_Sanity
                        x0 x1 x2 x3 (tcons (compile t) (compile_terms args))).
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

Lemma isApp_compile:
  forall fn,
    ~ L2d.term.isConstruct fn ->
    forall arg args, compile (L2d.compile.TApp fn arg args) = TApp (compile fn) (compile arg) (compile_terms args).
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
    CanonicalP compile t (compile s) = Some (i, m, us, np, na) ->
    instantiate (compile arg) n 
      CanonicalP compile (L2d.term.instantiate arg n t)
           (compile (L2d.term.instantiate arg n s)) =
      instantiate (compile arg) n (CanonicalP compile t (compile s)).         
***************)
  
(****
Goal
  forall arg n t s,
    CanonicalP compile t (compile s) = None ->
      CanonicalP compile (L2d.term.instantiate arg n t)
           (compile (L2d.term.instantiate arg n s)) = None.
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
     compile (L2d.term.instantiate arg n bod) =
     instantiate (compile arg) n (compile bod)) /\
  (forall bods arg n,
     compile_terms (L2d.term.instantiates arg n bods) =
     instantiates (compile arg) n (compile_terms bods)) /\
  (forall bods arg n,
     compileBs (L2d.term.instantiateBrs arg n bods) =
     instantiateBrs (compile arg) n (compileBs bods)) /\
  (forall ds arg n,
          compile_defs (L2d.term.instantiateDefs arg n ds) =
     instantiateDefs (compile arg) n (compile_defs ds)).
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
      (compile (L2d.compile.TApp (L2d.term.instantiate arg n t)
                               (L2d.term.instantiate arg n t0)) =
       instantiate (compile arg) n (compile (L2d.compile.TApp t t0))).
    rewrite TApp_hom. rewrite TApp_hom.
    rewrite H0. rewrite H.

    destruct (CanonicalP compile (L2d.term.instantiate arg n t)
                         (compile (L2d.term.instantiate arg n t0))).
    + repeat (destruct p). 
      destruct (CanonicalP compile t (compile t0)).
      * repeat (destruct p).

      
    - admit. (***  cbn. rewrite H. rewrite H0. reflexivity. ***)
  - change
      (compile (L2d.term.instantiate arg n2 (L2d.compile.TConstruct i n n0 n1)) =
       instantiate (compile arg) n2 (compile (L2d.compile.TConstruct i n n0 n1))).
    unfold compile at 3.
    cbn. destruct n0.
    +
    
      (compile (term.instantiate arg n0 (L2d.compile.TConstruct i n t)) =
       TConstruct i n (instantiates (compile arg) n0 (compile_terms t))).
    rewrite <- H; trivial.
  - change
     (TCase i (compile (L2d.term.instantiate arg n t))
            (compileBs (L2d.compile.instantiateBrs arg n b)) =
      TCase i (instantiate (compile arg) n (compile t))
            (instantiateBrs (compile arg) n (compileBs b))).
    rewrite H; trivial. rewrite H0; trivial.
  - change
      (TFix
         (compile_defs (L2d.term.instantiateDefs
                     arg (n0 + (L2d.compile.dlength d)) d)) n =
       TFix (instantiateDefs
               (compile arg) (n0 + (dlength (compile_defs d))) (compile_defs d)) n).
    rewrite H. rewrite compile_defs_pres_dlength. reflexivity.
  - rewrite L2d.compileEvalCommute.instantiates_tcons_commute.
    rewrite tcons_hom. rewrite tcons_hom. rewrite instantiates_tcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2d.compileEvalCommute.instantiates_bcons_commute.
    rewrite bcons_hom. rewrite bcons_hom. rewrite instantiateBs_bcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2d.compileEvalCommute.instantiates_dcons_commute.
    rewrite dcons_hom. rewrite dcons_hom. rewrite instantiateDs_dcons.
    rewrite <- H; trivial. rewrite H0; trivial.
Qed.

Lemma nLambda_isLambda:
  forall np F, exists G, (nLambda (S np) F) = fun b => TLambda nAnon (G b).
Proof.
  induction np; intros; cbn; exists F; reflexivity.
Qed.
 *****************)

Lemma TLambda_hom:
  forall nm bod,
    compile (tLambda nm bod) = TLambda nm (compile bod).
Proof.
  intros. now simp_compile.
Qed.

(* Lemma whBetaStep_hom:
  forall bod arg,
    compile (L1g.term.whBetaStep bod arg) =
    whBetaStep (compile bod) (compile arg).
Proof.
Admitted. *)
(*************
  intros. unfold L2d.term.whBetaStep, whBetaStep.
  Check (proj1 instantiate_hom).
  rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.
 **************)

End OnGlobalEnv.

(************* MAIN *************)

Lemma well_formed_pres (efl := all_env_flags) Σ : wf_glob Σ -> Qpreserves (wellformed Σ) Σ.
Proof. Admitted.
From Equations Require Import Equations.

Lemma compile_mkApps Σ fn args :
  negb (EAst.isApp fn) ->
  compile Σ (mkApps fn args) =
    match construct_viewc fn with
    | view_construct kn c => 
      match lookup_constructor_pars_args Σ kn c with
      | Some (npars, nargs) => 
        let args := map (compile Σ) args in
        let '(args, rest) := MCList.chop nargs args in
        TmkApps (TConstruct kn c (list_terms args)) (list_terms rest)
      | None =>
        let args := compile_terms Σ args in
        TConstruct kn c args
      end
    | view_other fn nconstr =>
        TmkApps (compile Σ fn) (compile_terms Σ args)
    end.
Proof.
  intros napp; simp compile.
  destruct (construct_viewc fn) eqn:vc.
  - destruct lookup_constructor_pars_args as [[]|] eqn:heq.
    destruct args eqn:hargs. cbn.
    * destruct n1 => //.
    * set (v := TermSpineView.view _).
      destruct (TermSpineView.view_mkApps v) as [hf [vn eq]] => //.
      rewrite eq /=. rewrite heq /=. now simp_compile.
    * destruct args eqn:hargs => //.
      set (v := TermSpineView.view _).
      destruct (TermSpineView.view_mkApps v) as [hf [vn eq]] => //.
      rewrite eq /=. rewrite heq /=. now simp_compile.
  - destruct args eqn:hargs => //.
    simp compile. now cbn.  
    set (v := TermSpineView.view _).
    destruct (TermSpineView.view_mkApps v) as [hf [vn eq]] => //.
    rewrite eq /= vc /=. now simp_compile.
Qed.

From Coq Require Import ssrbool.

Lemma wellformed_lookup_inductive_pars Σ kn mdecl :
  wf_glob Σ ->
  lookup_minductive Σ kn = Some mdecl -> mdecl.(ind_npars) = 0.
Proof.
  induction 1; cbn => //.
  case: eqb_spec => [|].
  - intros ->. destruct d => //. intros [= <-].
    cbn in H0. now eapply eqb_eq in H0.
  - intros _. eapply IHwf_glob.
Qed.

Lemma wellformed_lookup_constructor_pars {Σ kn c mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) -> mdecl.(ind_npars) = 0.
Proof.
  intros wf. cbn -[lookup_minductive].
  destruct lookup_minductive eqn:hl => //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma lookup_constructor_pars_args_spec {Σ ind n mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind n = Some (mdecl.(ind_npars), cdecl.2).
Proof.
  cbn -[lookup_constructor] => wfΣ.
  destruct lookup_constructor as [[[mdecl' idecl'] [pars args]]|] eqn:hl => //.
  intros [= -> -> <-]. cbn. f_equal.
Qed.

Lemma wellformed_lookup_constructor_pars_args {Σ ind n} :
  wf_glob Σ ->
  wellformed Σ 0 (EAst.tConstruct ind n) ->
  ∑ args, lookup_constructor_pars_args Σ ind n = Some (0, args).
Proof.
  intros wfΣ wf. cbn -[lookup_constructor] in wf.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  exists cdecl.2.
  pose proof (wellformed_lookup_constructor_pars wfΣ hl).
  eapply lookup_constructor_pars_args_spec in hl => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_params {Σ ind c b pars cdecl} :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
Proof.
  intros hwf.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive.
  destruct lookup_minductive as [mdecl|] eqn:hl => /= //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma compile_mkApps_wf (P : Term -> Prop) Σ k fn args :
  wf_glob Σ -> 
  ~~ EAst.isApp fn ->
  wellformed Σ k (mkApps fn args) ->
  (match construct_viewc fn with
  | view_construct kn c => 
    match lookup_constructor_pars_args Σ kn c with
    | Some (0, nargs) => 
      let cargs := map (compile Σ) args in
      let '(cargs, rest) := MCList.chop nargs cargs in
      P (TmkApps (TConstruct kn c (list_terms cargs)) (list_terms rest))
    | _ => True
    end
  | view_other fn nconstr =>
      P (TmkApps (compile Σ fn) (list_terms (map (compile Σ) args)))
  end) ->
  P (compile Σ (mkApps fn args)).
Proof.
  intros wfΣ napp.
  rewrite wellformed_mkApps // => /andP[] wffn wfargs.
  destruct construct_viewc eqn:vc.
  + rewrite compile_mkApps // vc.
    destruct (wellformed_lookup_constructor_pars_args wfΣ wffn).
    rewrite e. cbn.
    destruct chop eqn:eqch => //.
  + intros ht. rewrite compile_mkApps // vc //.
Qed.

Lemma compile_decompose Σ f :
  compile Σ f =
  let (fn, args) := decompose_app f in
    match construct_viewc fn with
    | view_construct kn c => 
      match lookup_constructor_pars_args Σ kn c with
      | Some (npars, nargs) => 
        let args := map (compile Σ) args in
        let '(args, rest) := MCList.chop nargs args in
        TmkApps (TConstruct kn c (list_terms args)) (list_terms rest)
      | None =>
        let args := compile_terms Σ args in
        TConstruct kn c args
      end
    | view_other fn nconstr =>
        TmkApps (compile Σ fn) (compile_terms Σ args)
    end.
Proof.
  destruct (decompose_app f) eqn:da.
  rewrite (decompose_app_inv da). apply compile_mkApps.
  now eapply decompose_app_notApp.
Qed.

Lemma compile_mkApps_eta (P : Term -> Prop) Σ fn args :
  wf_glob Σ -> 
  ~~ EAst.isApp fn ->
  isEtaExp Σ (mkApps fn args) ->
  (match construct_viewc fn with
  | view_construct kn c => 
    forall pars nargs, 
    lookup_constructor_pars_args Σ kn c = Some (pars, nargs) ->
    let cargs := map (compile Σ) args in
    let '(cargs, rest) := MCList.chop nargs cargs in
    P (TmkApps (TConstruct kn c (list_terms cargs)) (list_terms rest))
  | view_other fn nconstr =>
      P (TmkApps (compile Σ fn) (list_terms (map (compile Σ) args)))
  end) ->
  P (compile Σ (mkApps fn args)).
Proof.
  intros wfΣ napp.
  move/isEtaExp_mkApps.
  rewrite decompose_app_mkApps //. apply/negbTE: napp.
  destruct construct_viewc eqn:vc.
  + rewrite /isEtaExp_app.
    destruct lookup_constructor_pars_args as [[]|] eqn:hl.
    rewrite compile_decompose decompose_app_mkApps // /= hl.
    move=> /andP[] /Nat.leb_le hargs etaargs.
    move/(_ _ _ eq_refl).
    destruct chop eqn:eqch => //.
    move => /andP[] => //.
  + intros ht. rewrite compile_mkApps // vc //.
Qed.

Inductive Forall2_terms (P : Term -> Term -> Prop) : Terms -> Terms -> Prop :=
  | Forall2_nil_terms : Forall2_terms P tnil tnil
  | Forall2_cons_terms t t' l l' : P t t' -> Forall2_terms P l l' -> Forall2_terms P (tcons t l) (tcons t' l').

Section Reverse_Induction.
  Lemma trev_list_ind :
    forall P:Terms -> Type,
      P tnil ->
        (forall (a:Term) (l:Terms), P (treverse l) -> P (treverse (tcons a l))) ->
        forall l, P (treverse l).
  Proof.
    induction l; auto.
  Qed.

  Theorem trev_ind :
    forall P:Terms -> Type,
      P tnil ->
      (forall x l, P l -> P (tappend l (tcons x tnil))) -> forall l, P l.
  Proof.
    intros.
    generalize (treverse_involutive l).
    intros E; rewrite <- E.
    apply (trev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (treverse l0)).
    auto.
  Qed.

End Reverse_Induction.

Derive Signature for WcbvEval.
Derive NoConfusion for Term Terms.

Lemma TmkApps_tappend f args args' : TmkApps f (tappend args args') = TmkApps (TmkApps f args) args'.
Proof.
  induction args in args' |- * using trev_ind.
  - cbn => //. 
  - cbn.
    rewrite IHargs /=.
    rewrite -tappend_assoc. rewrite IHargs //=. 
Qed.

Lemma eval_mkAppsConstruct_inv' :
  forall p t x, WcbvEval p t x -> 
  forall f args, t = TmkApps f args -> 
  forall i r args', f = TConstruct i r args' -> 
  args = tnil /\ exists argsv, WcbvEvals p args' argsv /\ x = TConstruct i r argsv.
Proof.
  intros p t x ev f args.
  induction args in f, t, x, ev |- *using trev_ind. cbn.
  - intros -> i r args' ->.
    split => //. 
    depind ev; try discriminate. exists args'. split => //.
  - cbn.
    intros ht i r args' ->.
    rewrite ht in ev. rewrite !TmkApps_tappend /= in ev.
    cbn in ev. depelim ev.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. subst fn'.
    destruct H as [? [? []]]. elim H3. now eauto.
Qed.

Lemma eval_TmkApps_Construct_inv :
  forall p i r args' args x, WcbvEval p (TmkApps (TConstruct i r args') args) x -> 
  args = tnil /\ exists argsv, WcbvEvals p args' argsv /\ x = TConstruct i r argsv.
Proof.
  intros. eapply eval_mkAppsConstruct_inv'; trea.
Qed.

Lemma TApp_TmkApps f l t : TApp (TmkApps f l) t = TmkApps f (tappend l (tunit t)).
Proof.
  rewrite TmkApps_tappend //.
Qed.

Lemma eval_to_mkApps_Construct_inv_gen :
  forall p t x, WcbvEval p t x -> 
  forall f args, x = TmkApps f args ->
  args <> tnil -> ~ isConstruct f. 
Proof.
  intros p t x ev f args -> hargs.
  destruct args using trev_ind. congruence. cbn in ev.
  rewrite -TApp_TmkApps in ev. clear IHargs. clear hargs.
  depind ev; auto.
  destruct H as [? [? []]].
  destruct args using trev_ind. cbn in *. apply H1. 
  clear IHargs.
  intros [ind [n [args' eq]]].
  subst f. eapply IHev1. rewrite TApp_TmkApps. reflexivity.
  now do 3 eexists.
Qed.

Definition eq_nil_dec l : l = tnil \/ l <> tnil.
Proof.
  destruct l; auto. right; congruence.
Qed.

Lemma eval_to_mkApps_Construct_inv p t ind c args args' :
  WcbvEval p t (TmkApps (TConstruct ind c args) args') -> args' = tnil.
Proof.
  move/eval_to_mkApps_Construct_inv_gen.
  intros Hf.
  specialize (Hf (TConstruct ind c args) _ eq_refl).
  destruct (eq_nil_dec args') => //.
  specialize (Hf H). elim Hf. now do 3 eexists.
Qed.


(* Lemma tappend_compile_terms : tappend (compile_terms Σ l) (compile_terms Σ l') = compile_terms (l ++ l'). *)

Lemma compile_tApp Σ t a (P : Term -> Prop) k :
  wf_glob Σ -> 
  wellformed Σ k (tApp t a) ->
  (let (fn, args) := decompose_app (tApp t a) in
  match construct_viewc fn with
  | view_construct kn c => 
    match lookup_constructor_pars_args Σ kn c with
    | Some (0, nargs) => 
      let cargs := map (compile Σ) args in
      let '(cargs, rest) := MCList.chop nargs cargs in
      (args <> [] /\ t = mkApps (tConstruct kn c) (remove_last args) /\ a = last args a) ->
      P (TmkApps (TConstruct kn c (list_terms cargs)) (list_terms rest))
    | _ => True
    end
  | view_other fn nconstr =>
      P (TApp (compile Σ t) (compile Σ a))
  end) ->
  P (compile Σ (tApp t a)).
Proof.
  intros wfΣ wf.
  rewrite (compile_decompose _ (tApp t a)).
  destruct decompose_app eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  pose proof (EInduction.decompose_app_app _ _ _ _ da).
  destruct construct_viewc eqn:vc.
  + eapply EEtaExpandedFix.decompose_app_tApp_split in da as [Ha Ht].
    cbn in wf.
    move: wf => /andP[]. rewrite Ha wellformed_mkApps // => /andP[] wfc wfl wft.
    destruct (wellformed_lookup_constructor_pars_args wfΣ wfc).
    rewrite e. cbn.
    destruct chop eqn:eqch => //. 
    intros. apply H1. intuition auto.
  + pose proof (decompose_app_notApp _ _ _ da).
    pose proof (EInduction.decompose_app_app _ _ _ _ da).
    eapply EEtaExpandedFix.decompose_app_tApp_split in da as [Ha Ht].
    rewrite Ha Ht.
    rewrite compile_mkApps // vc.
    rewrite TApp_TmkApps.
    rewrite -(tappend_hom _ (remove_last l) [_]).
    rewrite -remove_last_last //. 
Qed.

Derive Signature for crctTerms.

Lemma crctTerm_tmkApps Σ n f args : 
  crctTerm Σ n f ->
  crctTerms Σ n args ->
  crctTerm Σ n (TmkApps f args).
Proof.
  induction args in f |- *. cbn; auto.
  intros hf hargs. depelim hargs.
  cbn. eapply IHargs => //. constructor => //.
Qed. 

From MetaCoq.SafeChecker Require PCUICTypeChecker.

Ltac simp_eta_in := match goal with [ H : is_true (isEtaExp _ _) |- _ ] => simp_eta in H end.

Lemma compile_isLambda Σ t : EAst.isLambda t -> isLambda (compile Σ t).
Proof. destruct t => //. now simp_compile. Qed.

Lemma wellformed_eta_crct {Σ} t :
  isEtaExp_env Σ -> wf_glob Σ ->
  crctEnv (compile_ctx Σ) ->
  forall k, wellformed Σ k t ->
  isEtaExp Σ t -> 
  crctTerm (compile_ctx Σ) k (compile Σ t).
Proof.
  intros etaΣ wfΣ crctΣ.
  revert t. apply: EInduction.MkAppsInd.rec; cbn [wellformed]; intros; try simp_eta_in; simp_eta; simp_compile.
  all:intros; simp_compile; rtoProp; intuition auto; try cbn in *; try constructor; eauto.
  - now eapply Nat.ltb_lt.
  - simp_compile. 
    move: H2; rewrite wellformed_mkApps // => /andP[] wfc wfu.
    move/isEtaExp_mkApps: H3. 
    rewrite decompose_app_mkApps //. destruct t => //.
    eapply compile_mkApps_wf => //. rewrite wellformed_mkApps //. now erewrite wfc, wfu.
    destruct construct_viewc.
    * destruct lookup_constructor_pars_args as [[[] nargs]|] eqn:heq => //.
      cbn. rewrite PCUICTypeChecker.chop_firstn_skipn.
      move/andP=> [] etaind etau.
      assert (All (fun t => crctTerm (compile_ctx Σ) k (compile Σ t)) u).
      { clear -X wfu etau. repeat toAll. eapply All_impl; tea; cbn; intuition auto. }
      eapply crctTerm_tmkApps. constructor.
      2:{ eapply (All_firstn (n:=nargs)) in X0. rewrite firstn_map.
          induction X0; constructor; auto. }
      2:{ eapply (All_skipn (n:=nargs)) in X0. rewrite skipn_map.
        induction X0; constructor; auto. }
      unfold isEtaExp_app in etaind. rewrite heq in etaind.
      eapply Nat.leb_le in etaind. todo "crctInd".
    * move/andP=> [] etat etau.
      eapply crctTerm_tmkApps; eauto.
      todo "all".
  - econstructor; tea. todo "const".
  - todo "eta".
  - todo "case".
  - destruct s as [[] ?]. simp_compile.
    destruct (lookup_record_projs) eqn:hprojs.
    all:todo "projs".
  - cbn. rewrite -dlength_hom. 
    rewrite Nat.add_comm. eapply forallb_All in H1. eapply forallb_All in H0.
    eapply All_mix in X; tea. clear H0; eapply All_mix in X. 2:exact H1. clear H1.
    move: X. generalize (#|m| + k).
    induction 1; try solve [constructor; cbn; auto].
    intuition auto.
    move/andP: a0 => [] isl etab.
    constructor; eauto.
    now eapply compile_isLambda.
  - cbn. rewrite -dlength_hom.
    todo "missing condition in wellformed idx < #|mfix|".
Admitted.

Lemma wellformed_eta_crctEnv {Σ} :
  isEtaExp_env Σ -> wf_glob Σ ->
  crctEnv (compile_ctx Σ).
Proof.
  induction Σ; cbn.
  - constructor.
  - move/andP=> [] etad etae wf. depelim wf.
    destruct d.
    * cbn. destruct c as [[b|]]; econstructor; eauto.
      todo "fresh". 
      eapply wellformed_eta_crct => //. eauto.
      todo "fresh".
    * constructor; eauto.
      todo "fresh".
Qed.
    
Lemma isLambda_substl s t : EAst.isLambda t -> EAst.isLambda (ECSubst.substl s t).
Proof. induction s in t |- * => //.
  intros isl. cbn. 
  eapply IHs. destruct t => //.
Qed.

Local Lemma decompose_app_app t u f l : decompose_app (tApp t u) = (f, l) -> l <> [].
Proof.
  intros da.
  pose proof (decompose_app_inv da).
  intros ->. cbn in H. subst f.
  now move: (decompose_app_notApp _ _ _ da).
Defined.

Lemma list_terms_app l l' : list_terms (l ++ l') = tappend (list_terms l) (list_terms l').
Proof.
  induction l in l' |- *.
  - cbn; auto.
  - cbn. now f_equal.
Qed.

Lemma compile_terms_tappend Σ l l' : 
  compile_terms Σ (l ++ l') = tappend (compile_terms Σ l) (compile_terms Σ l').
Proof.
  rewrite /compile_terms map_app list_terms_app //.
Qed.

Lemma isLambda_compile Σ f : 
  ~~ EAst.isLambda f -> ~ isLambda (compile Σ f).
Proof.
  intros nf. move=> [] na [] bod.
  destruct f; simp_compile => /= //.
  2:{ destruct p as [[] ?]; simp_compile => /= //.
      destruct lookup_record_projs => /= //. }
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  destruct construct_viewc.
  destruct lookup_constructor_pars_args as [[[] args]|] => //; cbn; destruct chop eqn:eqc; 
  destruct (list_terms l1) using trev_ind => //; rewrite -TApp_TmkApps //.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
Qed.

Lemma isBox_compile Σ f : 
  ~~ EAstUtils.isBox f -> compile Σ f <> TProof.
Proof.
  intros nf.
  destruct f; simp_compile => /= //.
  2:{ destruct p as [[] ?]; simp_compile => /= //.
      destruct lookup_record_projs => /= //. }
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  destruct construct_viewc.
  destruct lookup_constructor_pars_args as [[[] args]|] => //; cbn; destruct chop eqn:eqc; 
  destruct (list_terms l1) using trev_ind => //; rewrite -TApp_TmkApps //.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
Qed.

Lemma isFix_compile Σ f : 
  ~~ EAstUtils.isFix f -> ~ isFix (compile Σ f).
Proof.
  move=> nf [] defs [n].
  destruct f; simp_compile => /= //.
  2:{ destruct p as [[] ?]; simp_compile => /= //.
      destruct lookup_record_projs => /= //. }
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  destruct construct_viewc.
  destruct lookup_constructor_pars_args as [[[] args]|] => //; cbn; destruct chop eqn:eqc; 
  destruct (list_terms l1) using trev_ind => //; rewrite -TApp_TmkApps //.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
Qed.

Lemma isConstructApp_compile Σ f : 
  ~~ EWcbvEval.isConstructApp f -> ~ isConstruct (compile Σ f).
Proof.
  move=> nf [] i [] n [] args.
  destruct f; simp_compile => /= //.
  2:{ destruct p as [[] ?]; simp_compile => /= //.
      destruct lookup_record_projs => /= //. }
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  destruct construct_viewc. 
  { exfalso. rewrite (decompose_app_inv da) in nf.
    rewrite EWcbvEval.isConstructApp_mkApps // in nf. }
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
Qed.

(* Lemma compile_tApp_etaexp Σ k f a :
  wf_glob Σ ->
  wellformed Σ k (tApp f a) ->
  isEtaExp Σ f ->
  isEtaExp Σ a ->
  compile Σ (tApp f a) = TApp (compile Σ f) (compile Σ a).
Proof.
  intros wfΣ wf etaf etaa.
  eapply compile_tApp; tea => //.
  destruct decompose_app eqn:da.
  destruct construct_viewc eqn:vc => //.
  destruct lookup_constructor_pars_args as [[[] args']|] eqn:hl => // /=.
  destruct chop eqn:eqc.
  intros [Hl [Hf Ha]].
  subst f.
  move: etaf.
  move/isEtaExp_mkApps => /=.
  rewrite decompose_app_mkApps // /=.
  move/andP => []. rewrite /isEtaExp_app hl. move/Nat.leb_le => /= etaind etal.
  move: wf. rewrite -[tApp _ _](mkApps_app _ _ [a]).
  rewrite wellformed_mkApps //.
  move/andP=> [wfc wfargs].
  eapply compile_mkApps_wf => //.
  rewrite wellformed_mkApps //. erewrite wfc.
  rewrite forallb_app in wfargs. now move/andP: wfargs.
  simpl. rewrite hl.
  rewrite PCUICTypeChecker.chop_firstn_skipn.
  rewrite PCUICTypeChecker.chop_firstn_skipn in eqc. noconf eqc.
  rewrite TApp_TmkApps.
  f_equal. f_equal. rewrite {1}(remove_last_last l a Hl).
  f_equal. rewrite map_app firstn_app. len. 
  replace (args' - #|remove_last l|) with 0 by lia. cbn.
  now rewrite app_nil_r.
  rewrite {1}(remove_last_last l a Hl) map_app skipn_app.
  rewrite list_terms_app. f_equal. len.
  replace (args' - #|remove_last l|) with 0 by lia.
  rewrite skipn_0 -Ha //.
Qed. *)

Lemma isEtaExp_tApp_nConstruct {Σ f a} : 
  isEtaExp Σ (tApp f a) -> ~~ isConstructApp (tApp f a) -> isEtaExp Σ f && isEtaExp Σ a.
Proof.
  intros eta nc.
  move/isEtaExp_tApp: eta.
  destruct decompose_app eqn:da.
  destruct construct_viewc. 
  rewrite (decompose_app_inv da) in nc.
  case/negP: nc. rewrite /isConstructApp decompose_app_mkApps //.
  now move/and4P => [] _ _ -> ->.
Qed.

Lemma isConstructApp_tApp {f a} : EWcbvEval.isConstructApp (tApp f a) = EWcbvEval.isConstructApp f.
Proof.
  rewrite /EWcbvEval.isConstructApp. cbn.
  now rewrite head_tApp.
Qed.
(* Lemma isConstruct_compile Σ k f : 
  wf_glob Σ ->
  wellformed Σ k f ->
  isEtaExp Σ f ->
  ~~ isConstructApp f -> ~ isConstruct (compile Σ f).
Proof.
  move=> wfΣ wf etaf nf [] ind [] n [] args.
  destruct f; simp_compile => /= //.
  2:{ destruct p as [[] ?]; simp_compile => /= //.
      destruct lookup_record_projs => /= //. }
  move/(isEtaExp_tApp_nConstruct etaf): nf => /andP[etaf1 etaf2].
  rewrite (compile_tApp_etaexp k) //.
Qed. *)

Lemma instantiate_TmkApps a k f l :
  instantiate a k (TmkApps f l) = 
  TmkApps (instantiate a k f) (instantiates a k l).
Proof.
  induction l using trev_ind; auto.
  rewrite TmkApps_tappend.
  cbn -[instantiate instantiates].
  rewrite instantiate_TApp_commute IHl //.
  cbn -[instantiate].
  rewrite instantiates_tappend /= TmkApps_tappend //.
Qed.

From MetaCoq.Erasure Require Import EInduction ECSubst.

Lemma compile_mkApps_eta_fn Σ f args : isEtaExp Σ f -> 
  compile Σ (mkApps f args) = TmkApps (compile Σ f) (list_terms (map (compile Σ) args)).
Proof.
  intros ef.
  destruct (decompose_app f) eqn:df.
  rewrite (decompose_app_inv df) in ef |- *.
  rewrite -mkApps_app.
  move/isEtaExp_mkApps: ef.
  pose proof (decompose_app_notApp _ _ _ df).
  rewrite decompose_app_mkApps /= //. destruct t => //.
  rewrite compile_decompose.
  rewrite decompose_app_mkApps /= //. destruct t => //.
  destruct (construct_viewc t) eqn:vc.
  + move=> /andP[] etanl etal.
    destruct lookup_constructor_pars_args as [[pars args']|] eqn:hl => //.
    cbn. 
    rewrite PCUICTypeChecker.chop_firstn_skipn.
    rewrite compile_decompose.
    rewrite decompose_app_mkApps // /= hl.
    rewrite PCUICTypeChecker.chop_firstn_skipn.
    rewrite -TmkApps_tappend.
    move: etanl. rewrite /isEtaExp_app hl.
    move/Nat.leb_le => hl'.
    rewrite firstn_map. 
    rewrite firstn_app.
    assert (args' - #|l| = 0) as -> by lia.
    rewrite firstn_O // app_nil_r. f_equal. f_equal.
    rewrite firstn_map //. rewrite map_app skipn_map.
    rewrite -tappend_hom /compile_terms map_app -skipn_map.
    rewrite skipn_app. len. 
    assert (args' - #|l| = 0) as -> by lia.
    now rewrite skipn_0.
    move: etanl. rewrite /isEtaExp_app hl //.
  + move => /andP[] etat etal.
    rewrite (compile_decompose _ (mkApps t l)).
    rewrite decompose_app_mkApps //. destruct t => //.
    rewrite vc. rewrite -TmkApps_tappend. f_equal.
    now rewrite tappend_hom.
Qed.

Lemma negbF b : ~~ b -> b -> False.
Proof. destruct b => //. Qed.

Lemma compile_mkApps_nConstructApp_nApp Σ f args : 
  ~~ EAst.isApp f ->
  ~~ EWcbvEval.isConstructApp (mkApps f args) -> 
  compile Σ (mkApps f args) = TmkApps (compile Σ f) (list_terms (map (compile Σ) args)).
Proof.
  intros napp nc.
  rewrite compile_decompose decompose_app_mkApps.
  apply/negbTE: napp.
  destruct construct_viewc => //.
  exfalso.
  apply (negbF nc). rewrite EWcbvEval.isConstructApp_mkApps //.
Qed.

Lemma compile_mkApps_nConstructApp Σ f args : 
  ~~ EWcbvEval.isConstructApp (mkApps f args) -> 
  compile Σ (mkApps f args) = TmkApps (compile Σ f) (list_terms (map (compile Σ) args)).
Proof.
  intros nc.
  destruct (decompose_app f) eqn:da.
  rewrite (decompose_app_inv da) -mkApps_app in nc *.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite compile_mkApps_nConstructApp_nApp //.
  rewrite (compile_mkApps_nConstructApp_nApp _ t) //.
  move: nc; rewrite !EWcbvEval.isConstructApp_mkApps //.
  rewrite -TmkApps_tappend. f_equal. now rewrite -tappend_hom.
Qed.

Lemma isConstruct_csubst a k t : 
  ~~ EAst.isApp t ->
  ~~ EAstUtils.isConstruct t -> 
  EAstUtils.isConstruct (EAstUtils.head (csubst a k t)) -> 
  t = tRel k.
Proof.
  induction t => /= //.
  destruct (Nat.compare_spec k n) => //.
  intros; f_equal; auto.
Qed.

Arguments instantiate _ _ !tbod.

Lemma compile_csubst Σ a k b : 
  wf_glob Σ ->
  isEtaExp Σ a ->
  isEtaExp Σ b ->
  compile Σ (ECSubst.csubst a k b) = instantiate (compile Σ a) k (compile Σ b).
Proof.
  intros wfΣ.
  revert b k.
  apply: MkAppsInd.rec. all:intros *. 
  all:cbn -[instantiateBrs instantiateDefs]; try intros until k; simp_eta;
     intros; simp_compile; try solve [cbn -[instantiateBrs instantiateDefs];
     try f_equal; rtoProp; 
     intuition eauto; eauto].

  - cbn. destruct Nat.compare => //; reflexivity.
  - cbn. rewrite csubst_mkApps.
    eapply (compile_mkApps_eta (fun x => compile Σ (mkApps (csubst a k t) (map (csubst a k) u)) =
    instantiate (compile Σ a) k x)); eauto.
    destruct construct_viewc eqn:vc.
    * intros pars args hl.
      move: H3; rewrite isEtaExp_Constructor => /andP[] etai etau.
      set (cargs := map _ u). simpl.
      rewrite PCUICTypeChecker.chop_firstn_skipn.
      specialize (H1 k).
      rewrite compile_decompose.
      rewrite decompose_app_mkApps // /= hl.
      rewrite PCUICTypeChecker.chop_firstn_skipn.
      rewrite instantiate_TmkApps. f_equal.
      2:{ rewrite !skipn_map /cargs.
         clear -H2 etau X. repeat toAll.
        eapply (All_skipn (n:=args)) in etau.
        induction etau.
        - constructor; auto.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now apply p. }
      rewrite instantiate_TConstruct. f_equal.
      rewrite !firstn_map.
      { clear -H2 etau X. repeat toAll.
        eapply (All_firstn (n:=args)) in etau.
        induction etau.
        - constructor; auto.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now apply p. }
    * rewrite instantiate_TmkApps.
      move/isEtaExp_mkApps: H3; rewrite decompose_app_mkApps //. now move/negbTE: H.
      rewrite vc. move=> /andP[] etat etau.
      rewrite -H1 //.
      rewrite compile_mkApps_eta_fn. now eapply etaExp_csubst. f_equal.
      { clear -X H2 etau. repeat toAll. induction etau.
        - constructor.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now apply p. }
  - rewrite map_map_compose. 
    set (brs' := map _ l). cbn in brs'.
    set (brs'0 := map _ l). simpl.
    rewrite instantiate_TCase. rtoProp; intuition auto. f_equal; eauto.
    clear -X H0 H2.
    { subst brs' brs'0. repeat toAll. induction H2.
    - constructor.
    - cbn -[instantiateBrs]. rewrite instantiateBrs_equation.
      f_equal; eauto. destruct p. len. now eapply e. }
  - todo "projs".
  - rewrite map_map_compose. set (mfix' := map _ m).
    simpl. rewrite instantiate_TFix. f_equal.
    clear -X H H0. repeat toAll.
    rewrite -dlength_hom. 
    subst mfix'. rewrite Nat.add_comm.
    revert k.
    induction H0.
    * constructor.
    * intros k. cbn -[instantiateDefs]. rewrite instantiateDefs_equation.
      destruct p; len. rewrite Nat.add_succ_r.
      move/andP: i => [] isl etai.
      f_equal; eauto. eapply (IHAll (S k)).
Qed.

Lemma WcbvEval_hom (fl := EWcbvEval.target_wcbv_flags) :
  forall Σ, isEtaExp_env Σ -> wf_glob Σ ->
  forall t t', 
    wellformed Σ 0 t ->
    isEtaExp Σ t -> 
    EWcbvEval.eval Σ t t' ->
    WcbvEval (compile_ctx Σ) (compile Σ t) (compile Σ t').
Proof.
  intros Σ etaΣ wfΣ.
  eapply 
    (EWcbvEvalEtaInd.eval_preserve_mkApps_ind fl Σ _ 
      (wellformed Σ)) => //.
  { intros. } (* eapply EWcbvEval.eval_wellformed. }*)
  all:intros *.

  - intros ev [IHev wfa wfb etaa etab].
    intros ev' [IHev' wft wft' etat etat'].
    eapply compile_tApp with (k := 0) => //. cbn; now rewrite wfa wft.
    destruct decompose_app eqn:da.
    simp_compile in IHev.
    destruct (construct_viewc t0).
    * destruct lookup_constructor_pars_args as [[[] args]|]=> // /=.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in ev.
      eapply EWcbvEval.eval_construct' in ev as [? []]. solve_discr.
    * econstructor; tea.
  - intros ev [IHev wfa wfb etaa etab].
    intros ev' [IHev' wft wft' etat etat'].
    intros ev'' [IHev'' wfc wfr etac etar].
    eapply compile_tApp with (k := 0) => //. cbn; now rewrite wfa wft.
    simp_compile in IHev.
    destruct decompose_app eqn:da.
    destruct (construct_viewc t).
    * destruct lookup_constructor_pars_args as [[[] args]|]=> // /=.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in ev.
      eapply EWcbvEval.eval_construct' in ev as [? []]. solve_discr.
    * econstructor; tea.
      unfold whBetaStep.
      rewrite -compile_csubst //. now simp_eta in etab. 
  - intros ev [IHev wfa wfb etaa etab] etab1.
    intros ev' [IHev' wft wft' etat etat'].
    simp_compile. econstructor; tea.
    rewrite -compile_csubst //.
  - intros hbrs ev [IHev wfa wfb etaa etab].
    intros isp hnth hskip hbr.
    intros ev' [IHev' wft wft' etat etat'].
    simp_compile.
    rewrite compile_mkApps // /= in IHev. 
    move: wfb; rewrite wellformed_mkApps // => /andP[] wfc wfargs.
    destruct (wellformed_lookup_constructor_pars_args wfΣ wfc) as [nargs eq].
    rewrite eq in IHev.
    destruct chop eqn:eqc.
    set (brs' := map _ brs). cbn.
    assert (pars = 0).
    { now eapply constructor_isprop_pars_decl_params in isp. }
    subst pars. rewrite skipn_0 in hbr.
    move: etab. rewrite EEtaExpanded.isEtaExp_mkApps_napp // /=.
    move/andP => []. rewrite /isEtaExp_app /= eq /= => /Nat.leb_le hnargs hargs.
    cbn in IHev. 
    rewrite /constructor_isprop_pars_decl in isp.
    unfold lookup_constructor_pars_args in eq.
    destruct lookup_constructor as [[[mdecl idecl] cdecl']|] eqn:hc => //.
    cbn in isp. noconf isp. cbn in eq. noconf eq. cbn in hskip.
    rewrite PCUICTypeChecker.chop_firstn_skipn in eqc.
    rewrite -hskip in eqc. rewrite skipn_all2 in eqc. now len. noconf eqc.
    cbn in IHev.
    econstructor; tea.
    rewrite firstn_all2; len. lia.
    unfold whCaseStep.
    noconf eqc.
    rewrite (constructor_isprop_pars_decl)
    rewrite sk
    (* eapply (f_equal (@List.length _)) in H. len in H. cbn in H. *)
    (* rewrite skipn_length in H. assert (nargs = #|args|) by lia. *)
    (* subst nargs. clear H hnargs. *)
    (* rewrite firstn_all2. now len. *)
    todo "subst".
  - (* Fix case *) intros _.
    rename f5 into f.
    intros ev [IHev wff wffix etaf etafix].
    intros unffix etafn eva [IHeva wfa wfav etaa etaav].
    move=> evapp [IHevapp wftapp wfres etaapp etares].
    move/isEtaExp_tApp.
    eapply compile_tApp with (k := 0) => //.
    { cbn; now rewrite wff wfa. }
    destruct decompose_app eqn:da.
    destruct construct_viewc eqn:vc.
    * destruct lookup_constructor_pars_args as [[[] args]|]=> // /=.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in ev.
      eapply EWcbvEval.eval_construct' in ev as [? []]. solve_discr.
    * move=> /and4P[etat etal etaf' etaa'].
      simp_compile in IHev.
      set (mfix' := map _ mfix) in *.  
      eapply (wAppFix (x := compile Σ fn)); tea.
      { rewrite /mfix'. todo "whfix". }
      move: IHevapp.
      change (tApp fn av) with (mkApps fn [av]).
      assert (isl : EAst.isLambda fn).
      { move: etafix; cbn. simp_eta. intros hfix. 
        unfold cunfold_fix in unffix. destruct nth_error eqn:hnth => //.
        noconf unffix. eapply nth_error_forallb in hfix; tea. cbn in hfix.
        move/andP: hfix => [] isl _.
        eapply (isLambda_substl (fix_subst mfix)) in isl. 
        destruct ECSubst.substl => //. }
      destruct fn => //.
      eapply compile_mkApps_wf; tea.
      cbn. auto.
  - (* No cofixpoints allowed *) 
    intros cunfcof etafn etaargs.
    move=> ev [IHev wfd wfcof wfdiscr etacof].
    move: wfcof. rewrite wellformed_mkApps //.
  - (* No cofixpoints allowed *) 
    intros cunfcof etafn etaargs.
    move=> ev [IHev wfd wfcof wfdiscr etacof].
    move: wfcof. rewrite wellformed_mkApps //.
  - (* Declarations *)
    intros hdecl res hbod hev.
    move => [] IHev wfbo wfr etab etares.
    simp_compile. econstructor; tea. todo "lookups".
  - move=> ev [IHev wfd wfcstr etad etacof] iisprop lenargs hnfh.
    move=> ev' [IHev' wfarg wfres etaargs etares].
    simp_compile.
    destruct (lookup_record_projs) eqn:hl; simp_compile. cbn.
    2:{ todo "wf projs". }
    move: IHev.
    unfold lookup_record_projs in hl.
    destruct lookup_inductive as [[mdecl idecl]|] eqn:hl' => //. noconf hl.
    eapply (compile_mkApps_wf) => // /=; tea.
    destruct lookup_constructor_pars_args as [[[] args']|]=> // /=.
    move: wfcstr; cbn. rewrite wellformed_mkApps //.
    move=> /andP[] wfc wfargs. cbn -[lookup_constructor] in wfc.
    unfold lookup_inductive in hl'.
    destruct lookup_minductive eqn:hm => //.
    pose proof (wellformed_lookup_inductive_pars _ wfΣ hm).
    destruct chop eqn:eqch.
    intros evd.
    (* generalize (eval_to_mkApps_Construct_inv _ _ _ _ evd) => eql0. *)
    (* destruct l0 => //. *)
    rewrite PCUICTypeChecker.chop_firstn_skipn in eqch. noconf eqch.
    (* eapply (f_equal (@List.length _)) in H0. rewrite skipn_length /= map_length in H0. *)
    (* assert (args' >= #|args|). lia. cbn in evd. *)
    (* rewrite firstn_all2 in evd. len. lia. *)
    econstructor; tea. cbn. len. 
    (* rewrite tlength_hom. *)
    (* change (#|ind_projs idecl| =? #|args|) with (#|ind_projs idecl| == #|args|). *)
    (* case: eqb_spec => lenargs. *)
    (* { f_equal. assert (pars = 0). *)
      (* admit. admit. } *)
      admit.
    (* { cbn in hl'. admit. } *)
  - intros [hif' wff wff' etaf etaf'].
    intros IHapp. intros nlam.
    intros eva [iheva wfa wfa' etaa etaa'].
    intros etaapp'.
    eapply compile_tApp; tea. cbn. now erewrite wff, wfa.
    destruct decompose_app eqn:da.
    destruct construct_viewc eqn:vc.
    * destruct lookup_constructor_pars_args as [[[] args']|] eqn:hl => // /=.
      destruct chop eqn:hc.
      intros [Hl [Hf11 Ha]].
      change (tApp f' a') with (mkApps f' [a']).
      clear IHapp. rewrite Hf11 in ev.
      eapply EWcbvEval.eval_construct' in ev as [? []]. subst f'.
      exfalso. move: nlam. rewrite !negb_or. rtoProp; intuition auto.
      apply/negP: H0. rewrite negbK. unfold isConstructApp.
      rewrite decompose_app_mkApps //.
    * eapply (compile_tApp _ _ _ 0) => //. cbn. now rewrite wff' wfa'.
      destruct (decompose_app (tApp f' a')) eqn:da'.
      destruct (construct_viewc t0) eqn:vc'.
      { destruct lookup_constructor_pars_args as [[[] args']|] eqn:hl => // /=.
        pose proof (decompose_app_inv da').
        eapply (f_equal EWcbvEval.isConstructApp) in H.
        rewrite isConstructApp_tApp in H.
        rewrite EWcbvEval.isConstructApp_mkApps /= /EWcbvEval.isConstructApp /= in H.
        clear -nlam H. }
      constructor; eauto.
      rewrite !negb_or in nlam. rtoProp; intuition auto.
      eapply (isLambda_compile Σ) in H. contradiction.
      eapply (isFix_compile Σ) in H3; auto.
      eapply (isConstructApp_compile Σ) in H3; auto.
      eapply (isBox_compile Σ) in H1. contradiction.
  - intros hl hargs evargs eta wfa wfa' IHargs.
    eapply compile_mkApps_wf; eauto.
    simpl. rewrite (lookup_constructor_pars_args_spec wfΣ hl).
    rewrite PCUICTypeChecker.chop_firstn_skipn.
    pose proof (wellformed_lookup_constructor_pars wfΣ hl).
    rewrite firstn_all2. len. move: hargs; rewrite /EWcbvEval.cstr_arity => ->. lia.
    rewrite H.
    eapply compile_mkApps_wf; eauto.
    simpl. rewrite (lookup_constructor_pars_args_spec wfΣ hl) H.
    rewrite PCUICTypeChecker.chop_firstn_skipn.
    rewrite firstn_all2. len. rewrite -(All2_length IHargs).
    move: hargs; rewrite /EWcbvEval.cstr_arity => ->. lia.
    constructor. clear -IHargs.
    induction IHargs; cbn; constructor; intuition auto.
    now destruct r.
  - intros isat wf eta.
    destruct t => //; simp_compile; econstructor. constructor.
Qed.


(*******************  broken from here  *****
Lemma instantiate_hom:
  (forall bod n, L2d.term.WFTrm bod n -> 
                 forall arg, compile (L2d.term.instantiate arg n bod) =
                             instantiate (compile arg) n (compile bod)) /\
  (forall bods n, L2d.term.WFTrms bods n ->
                  forall arg, compile_terms (L2d.term.instantiates arg n bods) =
                              instantiates (compile arg) n (compile_terms bods)) /\
  (forall bods n, L2d.term.WFTrmBs bods n ->
                  forall arg, compileBs (L2d.term.instantiateBrs arg n bods) =
                              instantiateBrs (compile arg) n (compileBs bods)) /\
  (forall ds n, L2d.term.WFTrmDs ds n  ->
                forall arg, compile_defs (L2d.term.instantiateDefs arg n ds) =
                            instantiateDefs (compile arg) n (compile_defs ds)).
Proof.
  apply L2d.term.WFTrmTrmsBrsDefs_ind; intros;
    try (cbn; reflexivity); try (cbn; rewrite H0; reflexivity).
  - cbn. rewrite (proj1 (nat_compare_gt n m)). reflexivity. omega.
  - cbn. rewrite H0. rewrite H2. reflexivity.
  - rewrite L2d.term.instantiate_TApp_mkApp.
    change
      (compile (L2d.term.mkApp (L2d.term.instantiate arg n fn)
                            (L2d.compile.tcons
                               (L2d.term.instantiate arg n t)
                               (L2d.term.instantiates arg n ts))) =
       instantiate (compile arg) n (compile (L2d.compile.TApp fn t ts))).
    destruct (L2d.term.isConstruct_dec fn).
    + destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      unfold L2d.term.instantiate at 1.
      rewrite L2d.term.mkApp_goodFn; try not_isApp.
      change
        (compile
           (L2d.compile.TApp (L2d.compile.TConstruct x0 x1 x2 x3)
                            (L2d.term.instantiate arg n t)
                            (L2d.term.instantiates arg n ts)) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (tcons (compile (L2d.term.instantiate arg n t))
                             (compile_terms (L2d.term.instantiates arg n ts))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      rewrite H3. rewrite H5.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (compile arg) n
                                    (tcons (compile t) (compile_terms ts))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3 (tcons (compile t) (compile_terms ts)))).
      destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 (tcons (compile t) (compile_terms ts))).
      * { rewrite H6.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (instantiates
                                     (compile arg) n (tcons (compile t)
                                                          (compile_terms ts)))).
          - rewrite H7.
         

      
    destruct (L2d.term.isApp_dec (L2d.term.instantiate arg n fn)).
    + destruct i as [x0 [x1 [x2 jx]]]. rewrite jx.

      
    + rewrite L2d.term.mkApp_goodFn; try assumption.
      destruct (L2d.term.isConstruct_dec (L2d.term.instantiate arg n fn)).
      * destruct i as [x0 [x1 [x2 [x3 jx]]]]. rewrite jx.
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (tcons (compile (L2d.term.instantiate arg n t))
                               (compile_terms (L2d.term.instantiates arg n ts))) =
           instantiate (compile arg) n (compile (L2d.compile.TApp fn t ts))).
        rewrite H3. rewrite H5.
        assert (k: fn = TConstruct x0 x1 tnil).


  (***************
  - destruct (L2d.term.isConstruct_dec t).
    + change (compile (L2d.term.mkApp
                       (L2d.term.instantiate arg n t)
                       (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                         (L2d.term.instantiates arg n t1))) =
              instantiate (compile arg) n (compile (L2d.compile.TApp t t0 t1))).
      destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn;
        [ | intros h; cbn in h; destruct h as [y0 [y1 [y2 jy]]]; discriminate].
      rewrite TAppCnstr_hom. unfold L2d.term.instantiate at 1.
      change
        (etaExp_cnstr x0 x1 x2 x3 
                      (tcons (compile (L2d.term.instantiate arg n t0))
                             (compile_terms (L2d.term.instantiates arg n t1))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (compile t0) (compile_terms t1)))).
      rewrite H1. rewrite H0.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (compile arg) n
                                    (tcons (compile t0) (compile_terms t1))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (compile t0) (compile_terms t1)))).
      destruct (etaExp_spec x0 x1 x2 x3 (tcons (compile t0) (compile_terms t1)))
        as [[j0 j1] | [j0 j1]];
      destruct  (etaExp_spec x0 x1 x2 x3
                             (instantiates (compile arg) n
                                           (tcons (compile t0) (compile_terms t1))))
        as [[k0 k1] | [k0 k1]];
      rewrite instantiates_pres_tlength in *; try contradiction.
      * cbn in H.
      
      * destruct j1 as [z0 [z1 [z2 jz]]]. rewrite jz;
          destruct k1 as [w0 [w1 [w2 kw]]]; rewrite kw.
        
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (instantiates (compile arg) n (tcons (compile t0) (compile_terms t1))) =
           instantiate (compile arg) n (TConstruct z0 z1 z2))




   
    rewrite TApp_hom. 
    change
      (compile (L2d.term.mkApp
                (L2d.term.instantiate arg n t)
                (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                   (L2d.term.instantiates arg n t1))) =
       (mkApp (instantiate (compile arg) n (compile t))
              (tcons (instantiate (compile arg) n (compile t0))
                     (instantiates (compile arg) n (compile_terms t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
     ****************)
  - cbn. unfold etaExp_cnstr. cbn.
    replace (n0 + n1 - 0) with (n0 + n1); try omega.
    induction n0.
    + cbn.
    
  - change (TCase p (compile (L2d.term.instantiate arg n t0))
                  (compile_defs (L2d.term.instantiateDefs arg n d)) =
            (TCase p (instantiate (compile arg) n (compile t0))
                   (instantiateDefs (compile arg) n (compile_defs d)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (compile_defs (L2d.term.instantiateDefs
                             arg (n0 + L2d.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (compile arg) (n0 + dlength (compile_defs d)) (compile_defs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (compile (L2d.term.instantiate arg n t))
                  (compile_terms (L2d.term.instantiates arg n t0)) =
            tcons (instantiate (compile arg) n (compile t))
                  (instantiates (compile arg) n (compile_terms t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (compile (L2d.term.instantiate arg n1 t0)) n0
                  (compile_defs (L2d.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (compile arg) n1 (compile t0)) n0
                  (instantiateDefs (compile arg) n1 (compile_defs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.
 ****************************)

(*****************  broken from here  ************
Lemma instantiate_hom:
  (forall bod arg n, compile (L2d.term.instantiate arg n bod) =
                     instantiate (compile arg) n (compile bod)) /\
  (forall bods arg n, compile_terms (L2d.term.instantiates arg n bods) =
                    instantiates (compile arg) n (compile_terms bods)) /\
  (forall bods arg n, compileBs (L2d.term.instantiateBrs arg n bods) =
                    instantiateBrs (compile arg) n (compileBs bods)) /\
  (forall ds arg n, compile_defs (L2d.term.instantiateDefs arg n ds) =
                    instantiateDefs (compile arg) n (compile_defs ds)).
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
    + change (compile (L2d.term.mkApp
                       (L2d.term.instantiate arg n t)
                       (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                         (L2d.term.instantiates arg n t1))) =
              instantiate (compile arg) n (compile (L2d.compile.TApp t t0 t1))).
      destruct i as [x0 [x1 [x2 [x3 jx]]]]. subst.
      rewrite L2d.term.mkApp_goodFn;
        [ | intros h; cbn in h; destruct h as [y0 [y1 [y2 jy]]]; discriminate].
      rewrite TAppCnstr_hom. unfold L2d.term.instantiate at 1.
      change
        (etaExp_cnstr x0 x1 x2 x3 
                      (tcons (compile (L2d.term.instantiate arg n t0))
                             (compile_terms (L2d.term.instantiates arg n t1))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (compile t0) (compile_terms t1)))).
      rewrite H1. rewrite H0.
      change
        (etaExp_cnstr x0 x1 x2 x3
                      (instantiates (compile arg) n
                                    (tcons (compile t0) (compile_terms t1))) =
         instantiate (compile arg) n
                     (etaExp_cnstr x0 x1 x2 x3
                                   (tcons (compile t0) (compile_terms t1)))).
      destruct (etaExp_spec x0 x1 x2 x3 (tcons (compile t0) (compile_terms t1)))
        as [[j0 j1] | [j0 j1]];
      destruct  (etaExp_spec x0 x1 x2 x3
                             (instantiates (compile arg) n
                                           (tcons (compile t0) (compile_terms t1))))
        as [[k0 k1] | [k0 k1]];
      rewrite instantiates_pres_tlength in *; try contradiction.
      * cbn in H.
      
      * destruct j1 as [z0 [z1 [z2 jz]]]. rewrite jz;
          destruct k1 as [w0 [w1 [w2 kw]]]; rewrite kw.
        
        change
          (etaExp_cnstr x0 x1 x2 x3
                        (instantiates (compile arg) n (tcons (compile t0) (compile_terms t1))) =
           instantiate (compile arg) n (TConstruct z0 z1 z2))




   
    rewrite TApp_hom. 
    change
      (compile (L2d.term.mkApp
                (L2d.term.instantiate arg n t)
                (L2d.compile.tcons (L2d.term.instantiate arg n t0)
                                   (L2d.term.instantiates arg n t1))) =
       (mkApp (instantiate (compile arg) n (compile t))
              (tcons (instantiate (compile arg) n (compile t0))
                     (instantiates (compile arg) n (compile_terms t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
     ****************)
  - cbn. unfold etaExp_cnstr. cbn.
    replace (n0 + n1 - 0) with (n0 + n1); try omega.
    induction n0.
    + cbn.
    
  - change (TCase p (compile (L2d.term.instantiate arg n t0))
                  (compile_defs (L2d.term.instantiateDefs arg n d)) =
            (TCase p (instantiate (compile arg) n (compile t0))
                   (instantiateDefs (compile arg) n (compile_defs d)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (compile_defs (L2d.term.instantiateDefs
                             arg (n0 + L2d.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (compile arg) (n0 + dlength (compile_defs d)) (compile_defs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (compile (L2d.term.instantiate arg n t))
                  (compile_terms (L2d.term.instantiates arg n t0)) =
            tcons (instantiate (compile arg) n (compile t))
                  (instantiates (compile arg) n (compile_terms t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (compile (L2d.term.instantiate arg n1 t0)) n0
                  (compile_defs (L2d.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (compile arg) n1 (compile t0)) n0
                  (instantiateDefs (compile arg) n1 (compile_defs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.
  
Lemma whBetaStep_hom:
  forall bod arg args,
    L2d.term.WFTrm bod 0 ->
    compile (L2d.term.whBetaStep bod arg args) =
    whBetaStep (compile bod) (compile arg) (compile_terms args).
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
      (compile (L2d.compile.TApp
                x0 x1 (L2d.term.tappend x2 (L2d.compile.tcons t args))) =
       mkApp (compile (L2d.compile.TApp x0 x1 x2))
             (compile_terms (L2d.compile.tcons t args))).
    destruct (L2d.term.isConstruct_dec x0).
      * { destruct i as [i0 [i1 [i2 [i3 ji]]]]. subst.
        change
          (etaExp_cnstr i0 i1 i2 i3
                        (tcons (compile x1)
                               (compile_terms (L2d.term.tappend
                                          x2 (L2d.compile.tcons t args)))) =
           mkApp (etaExp_cnstr i0 i1 i2 i3
                        (tcons (compile x1) (compile_terms x2)))
                 (compile_terms (L2d.compile.tcons t args))).
        rewrite compile_terms_tappend. rewrite tcons_hom.   
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                        (tcons (compile x1) (compile_terms x2))).
          - rewrite H. rewrite mkApp_goodFn; try not_isApp.
        destruct (etaExp_cnstr_Sanity' i0 i1 i2 i3
                                         (tcons (compile x1)
                                                (compile.tappend (compile_terms x2) (tcons (compile t) (compile_terms args))))).
        rewrite H0.

        rewrite <- (proj1 instantiate_hom); try assumption.
    rewrite jx. destruct (L2d.term.isConstruct_dec x0).
    + destruct i as [y0 [y1 [y2 [y3 jy]]]]. subst.
      change
        (etaExp_cnstr y0 y1 y2 y3
                      (tcons (compile x1) (compile_terms (L2d.term.tappend x2 args))) =
         mkApp (etaExp_cnstr y0 y1 y2 y3
                             (tcons (compile x1) (compile_terms x2)))
               (compile_terms args)).
      destruct (etaExp_cnstr_Sanity'
                  y0 y1 y2 y3
                  (tcons (compile x1) (compile_terms (L2d.term.tappend x2 args)))),
      (etaExp_cnstr_Sanity'  y0 y1 y2 y3 (tcons (compile x1) (compile_terms x2)));
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
        (compile (L2d.compile.TApp (L2d.term.instantiate arg 0 bod) t args) =
         mkApp (instantiate (compile arg) 0 (compile bod))
               (tcons (compile t) (compile_terms args))).
      rewrite mkApp_goodFn.
      * admit.        
      * intros k. elim n. apply compile_pres_isApp.
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
    compile (L2d.compile.TConstruct i n args) = TConstruct i n args.
intros. simpl.  destruct i. reflexivity.
Qed.
***)

Lemma optcompile_match:
  forall x (f:L2Term -> L2Term) (g:Term -> Term), 
    (forall z, compile (f z) = g (compile z)) ->
    optcompile (match x with Some y => Some (f y) | None => None end) =
    match (optcompile x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optcompile (L2d.term.whCaseStep n ts brs) =
    whCaseStep n (compile_terms ts) (compile_defs brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L2d.term.whCaseStep. cbn. 
  rewrite <- dnthBody_hom. destruct (compile.dnthBody n brs); simpl.
  + destruct p as [x0 x1]. cbn. rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, compile (L2d.compile.TFix defs n) = TFix (compile_defs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod,
    compile (L2d.compile.TProd nm ty bod) = TProd nm (compile bod).
reflexivity.
Qed.


Lemma TLetIn_hom:
  forall nm dfn ty bod,
    compile (L2d.compile.TLetIn nm dfn ty bod) =
    TLetIn nm (compile dfn) (compile bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    compile (L2d.compile.TCase n ty mch brs) =
    TCase n (compile mch) (compile_defs brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L2Term -> nat -> L2Term) 
       (compileF:Term -> nat -> Term) (ns:list nat) (t:L2Term),
  (forall (s:L2Term) (n:nat), compile (F s n) = compileF (compile s) n) ->
  compile (fold_left F ns t) = fold_left compileF ns (compile t).
induction ns; intros t h.
- intuition.
- simpl. rewrite IHns.
  + rewrite h. reflexivity.
  + assumption.
Qed.

Lemma pre_whFixStep_hom:
  forall body dts args,
    pre_whFixStep (compile body) (compile_defs dts) (compile_terms args) =
    compile (L2d.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L2d.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (compile t0) n0 (compile_defs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L2d.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (compile t0) n0 (compile_defs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L2d.compile.prop). simpl. reflexivity.
Qed.

Lemma tsplit_hom:
  forall ix arg args,
    optcompile_split (L2d.term.tsplit ix arg args) =
    tsplit ix (compile arg) (compile_terms args).
Proof.
  intros ix arg args.
  functional induction (L2d.term.tsplit ix arg args); cbn; intros.
  - reflexivity.
  - destruct n. elim y. reflexivity.
  - destruct ls; cbn; reflexivity.
  - case_eq (tsplit m (compile t) (compile_terms ts)); intros.
    + destruct s.
      assert (j0:= L2d.term.tsplit_sanity m t ts). rewrite e1 in j0.
      assert (j1:= tsplit_sanity m (compile t) (compile_terms ts)).
      rewrite H in j1. destruct j1.
      assert (j2: tlength (compile_terms ts) = tlength fsts + tlength lsts).
      { apply (f_equal tlength) in H0. rewrite tlength_tappend in H0.
        cbn in H0. omega. }
      rewrite tlength_hom in j2. rewrite j2 in j0. rewrite H1 in j0. omega.
    + reflexivity.
  - destruct (tsplit m (compile t) (compile_terms ts)).
    + destruct s0. rewrite e1 in IHo. rewrite optcompile_split_hom in IHo.
      myInjection IHo. reflexivity.
    + rewrite e1 in IHo.  rewrite optcompile_split_hom in IHo.
      discriminate.
Qed.

Lemma optcompileCanP_hom':
  forall z, optcompileCanP (Some z) =
            Some (fst (fst z), compile_terms (snd (fst z)), snd z).
intros. destruct z as [[z0 z1] z2]. cbn. reflexivity.
Qed.

Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2d.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (compile_ctx Σ) (compile t) (compile t')) /\
    (forall ts ts', L2d.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (compile_ctx Σ) (compile_terms ts) (compile_terms ts')).
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
Corollary compile_pres_eval:
  forall (p:environ L2d.compile.Term) (t tv:L2d.compile.Term),
    L2d.wcbvEval.WcbvEval p t tv ->
    exists stv, WcbvEval (compile_ctx Σ) (compile t) stv.
Proof.
  intros. exists (compile tv). apply (proj1 (WcbvEval_hom _)).
  assumption.
Qed.

Corollary wcbvEval_hom:
  forall p n t t',
    L2d.wcbvEval.wcbvEval p n t = Ret t' ->
    exists m, wcbvEval (compile_ctx Σ) m (compile t) = Ret (compile t').
Proof.
  intros. 
  assert (j1:= proj1 (L2d.wcbvEval.wcbvEval_WcbvEval p n) _ _ H).
  assert (k0:= proj1 (WcbvEval_hom p) _ _ j1).
  assert (j2:= @WcbvEval_wcbvEval (compile_ctx Σ) (compile t) (compile t') k0).
  destruct j2 as [ny jny].
  exists ny. eapply jny. omega.
Qed.


Lemma Prf_compile_inv:
  forall s st, TProof st = compile s ->
              exists t, s = L2d.compile.TProof t /\ st = compile t.
Proof.
  destruct s; simpl; intros h; try discriminate.
  intros. myInjection H. exists s. intuition.
Qed.
  
Lemma Lam_compile_inv:
  forall nm bod s, TLambda nm bod = compile s ->
   exists sty sbod, 
     (L2d.compile.TLambda nm sty sbod) = s /\ bod = compile sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_compile_inv:
  forall nm bod s, TProd nm bod = compile s ->
   exists sty sbod, 
     (L2d.compile.TProd nm sty sbod) = s /\ bod = compile sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_compile_inv:
  forall tm s, TCast tm = compile s ->
   exists stm sty, 
     (L2d.compile.TCast stm sty) = s /\ tm = compile stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Construct_compile_inv:
  forall i n arty s,
    TConstruct i n arty = compile s -> L2d.compile.TConstruct i n arty = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_compile_inv:
  forall srt s, TSort srt = compile s -> L2d.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_compile_inv:
  forall i s, TInd i = compile s -> L2d.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_compile_inv:
  forall nm s, TConst nm = compile s -> L2d.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_compile_inv:
  forall ds n s, TFix ds n = compile s ->
    exists sds, (L2d.compile.TFix sds n) = s /\ ds = compile_defs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_compile_inv:
  forall fn arg args s, TApp fn arg args = compile s ->
    exists sfn sarg sargs,
      (L2d.compile.TApp sfn sarg sargs) = s /\
      fn = compile sfn /\ arg = compile sarg /\ args = compile_terms sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_compile_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = compile s ->
    exists sdfn sty sbod,
      (L2d.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = compile sdfn /\ bod = compile sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_compile_inv:
  forall m mch brs s, TCase m mch brs = compile s ->
    exists sty smch sbrs, (L2d.compile.TCase m sty smch sbrs = s) /\
              mch = compile smch /\ brs = compile_defs sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, d. intuition.
Qed.

Lemma tnil_compile_inv:
  forall ts, tnil = compile_terms ts -> ts = L2d.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_compile_inv:
  forall t ts us, tcons t ts = compile_terms us ->
    exists st sts, (L2d.compile.tcons st sts = us) /\ 
                   t = compile st /\ ts = compile_terms sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_compile_inv:
  forall nm t m ts us, dcons nm t m ts = compile_defs us ->
    exists ty st sts, (L2d.compile.dcons nm ty st m sts = us) /\ 
                   t = compile st /\ ts = compile_defs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L2d.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (compile_terms ts) (compile_defs bs) = Some (compile t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optcompile_hom.
  apply f_equal. assumption.
Qed.

Definition exccompile (t:exception L2Term) : exception Term :=
  match t with
    | Exc str => Exc str
    | Ret t => Ret (compile t)
  end.


Theorem L2WcbvEval_sound_for_L2WcbvEval:
  forall (p:environ L2d.compile.Term) (t:L2d.compile.Term) (L2s:Term),
    WcbvEval (compile_ctx Σ) (compile t) L2s ->
  forall s, L2d.wcbvEval.WcbvEval p t s -> L2s = compile s.
Proof.
  intros. refine (WcbvEval_single_valued _ _).
  - eassumption.
  - apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L2WcbvEval.


Lemma sound_and_complete:
  forall (p:environ L2d.compile.Term) (t s:L2d.compile.Term),
    L2d.wcbvEval.WcbvEval p t s ->
    WcbvEval (compile_ctx Σ) (compile t) (compile s).
Proof.
  intros p t s h. apply (proj1 (WcbvEval_hom p)). assumption.
Qed.

Lemma sac_complete:
  forall p t s, L2d.wcbvEval.WcbvEval p t s ->
                WcbvEval (compile_ctx Σ) (compile t) (compile s).
Proof.
  intros. apply sound_and_complete. assumption.
Qed.

Lemma sac_sound:
  forall p t s, L2d.wcbvEval.WcbvEval p t s ->
  forall L2s, WcbvEval (compile_ctx Σ) (compile t) L2s -> L2s = compile s.
Proof.
  intros p t s h1 L2s h2.
  apply (WcbvEval_single_valued h2). apply (sound_and_complete h1).
Qed. 
Print Assumptions sac_sound.

 *******************************)
 *)
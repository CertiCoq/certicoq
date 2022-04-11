Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.

Require Import Common.Common.

From Coq Require Import ssreflect ssrbool.
From Equations Require Import Equations.

From MetaCoq.Template Require Import BasicAst Ast utils.
From MetaCoq.Erasure Require Import EAst EAstUtils EGlobalEnv EExtends.
From MetaCoq.Erasure Require Import ESpineView EWcbvEvalEtaInd EWellformed EEtaExpanded.
Import utils.

Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
Require Import L2k.wcbvEval.

Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

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
    has_tProj := false;
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

  Lemma tlength_hom:
    forall ts, tlength (compile_terms ts) = List.length ts.
  Proof.
    induction ts; intros; try reflexivity.
    - cbn. apply f_equal. assumption.
  Qed.

Lemma Lookup_hom :
  wf_glob Σ ->
  forall s ec, lookup_env Σ s = Some ec -> 
    ∑ Σ', [× extends Σ' Σ, wf_global_decl Σ' ec & lookup s (compile_ctx Σ) = Some (compile_global_decl Σ' ec)].
Proof.
  induction Σ; cbn => //.
  intros s ec.
  case: eqb_specT.
  - intros -> ? [= <-].
    exists g. split. now exists [a].
    now depelim s.
    destruct a as [kn d]; cbn.
    now rewrite eqb_refl.
  - intros neq d hl.
    forward IHg. now depelim s.
    destruct (IHg _ _ hl) as [Σ' [ext hl']].
    exists Σ'. split => //.
    destruct ext as [Σ'' ->]. now exists (a :: Σ'').
    destruct a as [kn d']; cbn.
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


Lemma tappend_hom:
  forall ts us : list EAst.term,
    compile_terms (List.app ts us) = tappend (compile_terms ts) (compile_terms us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  cbn. f_equal. apply IHts.
Qed.

  
End OnGlobalEnv.

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
  rewrite decompose_app_mkApps //.
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

Definition preserves_some_gen {A B} (t : option A) (f : A -> B) (t' : option B) := forall b, t = Some b -> t' = Some (f b).

Definition preserves_some {A} (t t' : option A) : Prop := preserves_some_gen t id t'.

Lemma preserves_some_refl {A} (t : option A) : preserves_some t t.
Proof.
  now intros b.
Qed.

Lemma lookup_constructor_pars_args_extends {Σ Σ' ind c} : 
  wf_glob Σ' ->
  extends Σ Σ' ->
  EWellformed.isSome (lookup_constructor Σ ind c) ->
  lookup_constructor_pars_args Σ' ind c = lookup_constructor_pars_args Σ ind c.
Proof.
  intros wfΣ ext.
  rewrite /lookup_constructor_pars_args.
  destruct lookup_constructor eqn:hl => /= //.
  now rewrite (extends_lookup_constructor wfΣ ext _ _ _ hl).
Qed.

Lemma decompose_app_napp {t} : ~~ EAst.isApp t -> decompose_app t = (t, []).
Proof.
  intros napp. destruct t => //.
Qed.

Import ELiftSubst.

Lemma wf_mkApps Σ k f args : reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma compile_extends Σ Σ' t : 
  wf_glob Σ' ->
  extends Σ Σ' ->
  forall k, wellformed Σ k t ->
  compile Σ t = compile Σ' t.
Proof.
  intros wfΣ ext.
  funelim (compile Σ t); simpl; simp_compile => //.
  all:try intros; rtoProp; intuition eauto; f_equal; eauto.
  all:repeat match goal with [ H : forall x, In x _ -> _ |- _ ] => eapply In_All in H end.
  - f_equal. solve_all.
  - f_equal. move/andP: H0 => [] _ wffix. solve_all.
  - move/wf_mkApps: H1 => [] wffn wfargs.
    rewrite compile_decompose decompose_app_napp //.
    destruct construct_viewc eqn:vc.
    simpl in wffn.
    destruct lookup_constructor_pars_args as [[npars nargs]|] eqn:hl.
    simpl; rewrite PCUICTypeChecker.chop_firstn_skipn.
    rewrite compile_decompose decompose_app_mkApps //.
    rewrite compile_decompose decompose_app_mkApps //. cbn.
    rewrite (compile_decompose _ (mkApps t args)) decompose_app_mkApps //.
    rewrite vc. f_equal; eauto. unfold compile_terms. f_equal. solve_all.
  - destruct chop eqn:hc.
    move/wf_mkApps: H0 => [wff wfargs].
    rewrite compile_decompose decompose_app_mkApps // /=.
    rewrite (lookup_constructor_pars_args_extends wfΣ ext wff) /= Heq.
    assert (map (compile Σ) args = map (compile Σ') args) as <- by solve_all.
    now rewrite hc.
  - rewrite compile_decompose decompose_app_mkApps // /=.
    move/wf_mkApps: H0 => [] wfc wfargs.
    rewrite (lookup_constructor_pars_args_extends wfΣ ext wfc) Heq.
    f_equal. unfold compile_terms. f_equal. solve_all.
Qed.

Lemma compile_global_decl_extends Σ Σ' t : 
  wf_glob Σ' ->
  extends Σ Σ' ->
  wf_global_decl Σ t ->
  compile_global_decl Σ t = compile_global_decl Σ' t.
Proof.
  intros wfΣ ext.
  destruct t => /= //.
  destruct c as [[b|]] => //=.
  intros wfb; f_equal. eapply compile_extends; tea.
Qed.

Lemma lookup_env_lookup {Σ c decl} : 
  wf_glob Σ ->
  lookup_env Σ c = Some decl ->
  lookup c (compile_ctx Σ) = Some (compile_global_decl Σ decl).
Proof.
  move=> wfΣ /(Lookup_hom wfΣ) [Σ' [ext wf ->]]. f_equal. 
  eapply compile_global_decl_extends => //.
Qed.

Lemma exnNth_nth_error {A} (l : list A) n t :
  nth_error l n = Some t ->
  exnNth l n = Ret t.
Proof.
  induction l in n |- *; destruct n; cbn => //; auto.
  intros [= <-]. reflexivity.
Qed.

Lemma compile_crctInd {Σ ind mdecl idecl} :
  wf_glob Σ ->
  lookup_inductive Σ ind = Some (mdecl, idecl) ->
  crctInd (compile_ctx Σ) ind (ibody_ityp idecl).
Proof.
  move=> wfΣ.
  unfold lookup_inductive, lookup_minductive.
  destruct lookup_env eqn:hl => /= //.
  eapply lookup_env_lookup in hl => //.
  destruct g => //.
  destruct nth_error eqn:hnth => //.
  intros [= <- <-]. econstructor. red.
  split. eapply lookup_Lookup. cbn. rewrite hl //.
  { eapply nth_error_Some_length in hnth.
    unfold ibodies_itypPack. destruct (ind_bodies m) => //. cbn in hnth; lia. }
  cbn. unfold ibodies_itypPack, getInd.
  eapply exnNth_nth_error. rewrite nth_error_map hnth //.
Qed.

Lemma compile_crctCnstr Σ ind n args mdecl idecl cdecl : 
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  tlength args = EWcbvEval.cstr_arity mdecl cdecl ->
  crctCnstr (compile_ctx Σ) ind n args.
Proof.
  intros wfΣ.
  rewrite /lookup_constructor.
  destruct lookup_inductive as [[mdecl' idecl']|] eqn:hl => /= //.
  destruct nth_error eqn:hnth => //. intros [= <- <- <-].
  intros hlen.
  econstructor. eapply compile_crctInd; tea.
  rewrite /getCnstr. cbn.
  eapply exnNth_nth_error. rewrite nth_error_map hnth //.
  cbn. rewrite hlen. destruct p as [cname arity]; cbn.
  rewrite /EWcbvEval.cstr_arity. cbn.
  move: hl. rewrite /lookup_inductive. destruct lookup_minductive eqn:hl' => /= //.
  destruct (nth_error (ind_bodies m) _) => //. intros [= <- <-].  
  now rewrite (wellformed_lookup_inductive_pars _ wfΣ hl').
Qed.

Lemma wellformed_eta_crct {Σ} t :
  isEtaExp_env Σ -> wf_glob Σ ->
  crctEnv (compile_ctx Σ) ->
  forall k, wellformed Σ k t ->
  isEtaExp Σ t -> 
  crctTerm (compile_ctx Σ) k (compile Σ t).
Proof.
  intros etaΣ wfΣ crctΣ.
  revert t. apply: EInduction.MkAppsInd.rec; cbn [wellformed]; intros; try simp_eta_in; simp_eta; simp_compile.
  all:intros; simp_compile; rtoProp; intuition auto; try cbn -[lookup_constructor lookup_inductive] in *; try constructor; eauto.
  - now eapply Nat.ltb_lt.
  - simp_compile. 
    move: H2; rewrite wellformed_mkApps // => /andP[] wfc wfu.
    move/isEtaExp_mkApps: H3. 
    rewrite decompose_app_mkApps //.
    eapply compile_mkApps_wf => //. rewrite wellformed_mkApps //. now erewrite wfc, wfu.
    destruct construct_viewc.
    * destruct (wellformed_lookup_constructor_pars_args wfΣ wfc) as [cargs eq]. rewrite eq.
      cbn. rewrite PCUICTypeChecker.chop_firstn_skipn.
      move/andP=> [] etaind etau.
      assert (All (fun t => crctTerm (compile_ctx Σ) k (compile Σ t)) u).
      { clear -X wfu etau. repeat toAll. eapply All_impl; tea; cbn; intuition auto. }
      eapply crctTerm_tmkApps. constructor.
      2:{ eapply (All_firstn (n:=cargs)) in X0. rewrite firstn_map.
          induction X0; constructor; auto. }
      2:{ eapply (All_skipn (n:=cargs)) in X0. rewrite skipn_map.
        induction X0; constructor; auto. }
      unfold isEtaExp_app in etaind. rewrite eq in etaind.
      eapply Nat.leb_le in etaind.
      simpl in wfc. 
      destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl.
      eapply compile_crctCnstr; tea. cbn.
      rewrite firstn_map tlength_hom. rewrite firstn_length. 
      assert (Nat.min cargs #|u| = cargs) as -> by lia.
      rewrite /EWcbvEval.cstr_arity.
      rewrite (lookup_constructor_pars_args_spec wfΣ hl) in eq. noconf eq. now rewrite H2.
      by [].
    * move/andP=> [] etat etau.
      eapply crctTerm_tmkApps; eauto.
      repeat toAll. clear -etau etaΣ wfΣ crctΣ. induction etau; cbn; constructor; auto.
      now apply p.
  - destruct lookup_env as [[]|] eqn:hl => //.
    destruct c as [[]] => //. cbn in *.
    eapply lookup_env_lookup in hl.
    econstructor; tea.
    unfold LookupDfn. eapply lookup_Lookup => //. exact hl. auto.
  - move: H0. rewrite /isEtaExp_app.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
    rewrite (lookup_constructor_pars_args_spec wfΣ hl).
    have hpars := wellformed_lookup_constructor_pars wfΣ hl.
    rewrite hpars. cbn. move/Nat.leb_le => hpars'.
    eapply compile_crctCnstr; eauto. cbn. rewrite /EWcbvEval.cstr_arity. lia.
  - destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
    econstructor.
    eapply compile_crctInd; tea. eauto.
    repeat toAll. clear -etaΣ wfΣ crctΣ H2.
    induction H2; cbn; constructor; auto.
    rewrite List.rev_length. now apply p. 
  - cbn. rewrite -dlength_hom. 
    move/andP: H1 => [] hn H1. clear hn.
    rewrite Nat.add_comm. eapply forallb_All in H1. eapply forallb_All in H0.
    eapply All_mix in X; [|exact H0]. clear H0; eapply All_mix in X; [|exact H1]. clear H1.
    move: X. generalize (#|m| + k).
    induction 1; try solve [constructor; cbn; auto].
    intuition auto. 
    move/andP: a0 => [] isl etab.
    constructor; eauto.
    now eapply compile_isLambda.
  - cbn. rewrite -dlength_hom. move/andP: H1 => [] /Nat.ltb_lt //.
Qed.

Lemma compile_fresh kn Σ : fresh_global kn Σ -> fresh kn (compile_ctx Σ).
Proof.
  induction 1; cbn. constructor.
  destruct x as [kn' d]. constructor => //. cbn in H. congruence.
Qed.

Lemma wellformed_eta_crctEnv {Σ} :
  isEtaExp_env Σ -> wf_glob Σ ->
  crctEnv (compile_ctx Σ).
Proof.
  induction Σ; cbn.
  - constructor.
  - move/andP=> [] etad etae wf. depelim wf.
    destruct d.
    * cbn. destruct c as [[b|]]; econstructor; eauto.
      now apply compile_fresh.
      eapply wellformed_eta_crct => //. eauto.
      now apply compile_fresh.
    * constructor; eauto.
      now apply compile_fresh.
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

Import EWcbvEval.

Lemma isEtaExp_tApp_nConstruct {Σ f a} : 
  isEtaExp Σ (tApp f a) -> ~~ isConstructApp (tApp f a) -> isEtaExp Σ f && isEtaExp Σ a.
Proof.
  intros eta nc.
  move/isEtaExp_tApp: eta.
  destruct decompose_app eqn:da.
  destruct construct_viewc. 
  rewrite (decompose_app_inv da) in nc.
  case/negP: nc. rewrite /isConstructApp head_mkApps //.
  now move/and4P => [] _ _ -> ->.
Qed.

Lemma isConstructApp_tApp {f a} : isConstructApp (tApp f a) = isConstructApp f.
Proof.
  rewrite /isConstructApp. cbn.
  now rewrite head_tApp.
Qed.

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
  rewrite decompose_app_mkApps /= //.
  rewrite compile_decompose.
  rewrite decompose_app_mkApps /= //.
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
    rewrite decompose_app_mkApps //.
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
  rewrite compile_decompose decompose_app_mkApps //.
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

Lemma compile_csubst Σ a n k b : 
  wf_glob Σ ->
  isEtaExp Σ a ->
  isEtaExp Σ b ->
  wellformed Σ (n + k) b ->
  compile Σ (ECSubst.csubst a k b) = instantiate (compile Σ a) k (compile Σ b).
Proof.
  intros wfΣ.
  revert b n k.
  apply: MkAppsInd.rec. all:intros *. 
  all:cbn -[instantiateBrs instantiateDefs lookup_inductive lookup_constructor]; try intros until k; simp_eta;
     intros; simp_compile; try solve [cbn -[instantiateBrs instantiateDefs lookup_inductive lookup_constructor];
     try f_equal; rtoProp; 
     intuition eauto; eauto].

  - cbn. destruct Nat.compare => //; reflexivity.
  - cbn. f_equal; eauto. eapply H => //. rewrite -Nat.add_succ_r in H2; tea.
  - cbn. f_equal; eauto. eapply H => //. rtoProp; intuition eauto. now move/andP: H3.
    eapply H0 => //; rtoProp; intuition eauto. rewrite -Nat.add_succ_r in H4; tea.
  - move/wf_mkApps: H4 => [] wft wfu.  rewrite csubst_mkApps.
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
         clear -H2 wfu etau X. repeat toAll.
        eapply (All_skipn (n:=args)) in etau.
        induction etau.
        - constructor; auto.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. eapply p; eauto. eapply p. eapply p. }
      rewrite instantiate_TConstruct. f_equal.
      rewrite !firstn_map.
      { clear -H2 wfu etau X. repeat toAll.
        eapply (All_firstn (n:=args)) in etau.
        induction etau.
        - constructor; auto.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now eapply p. }
    * rewrite instantiate_TmkApps.
      move/isEtaExp_mkApps: H3; rewrite decompose_app_mkApps //.
      rewrite vc. move=> /andP[] etat etau.
      rewrite -(H1 n) //.
      rewrite compile_mkApps_eta_fn. now eapply etaExp_csubst. f_equal.
      { clear -X H2 wfu etau. repeat toAll. induction etau.
        - constructor.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now eapply p. }
  - rewrite map_map_compose.
    move/andP: H2 => [] /andP[] wfi wft wfl.
    set (brs' := map _ l). cbn in brs'.
    set (brs'0 := map _ l). simpl.
    rewrite instantiate_TCase. rtoProp; intuition auto. f_equal; eauto.
    clear -X wfl H0 H2.
    { subst brs' brs'0. repeat toAll. induction wfl.
    - constructor.
    - cbn -[instantiateBrs]. rewrite instantiateBrs_equation.
      f_equal; eauto. destruct p. rewrite List.rev_length. destruct p. apply (e n); eauto.
      eapply wellformed_up; tea. lia. }
  - rewrite map_map_compose. set (mfix' := map _ m).
    simpl. rewrite instantiate_TFix. f_equal.
    clear -X H H0 H1.
    move/andP: H1 => [] _ H1. repeat toAll.
    rewrite -dlength_hom. 
    subst mfix'. rewrite Nat.add_comm.
    revert H1. generalize #|m|.
    induction 1.
    * constructor.
    * cbn -[instantiateDefs]. rewrite instantiateDefs_equation.
      destruct p; len. move: p => [] /andP[] isl etai wfx.
      f_equal; eauto. apply (e n0) => //. eapply wellformed_up; tea. lia.
Qed.

Fixpoint substl_rev terms k body :=
  match terms with
  | [] => body
  | term :: terms => substl_rev terms k (csubst term (#|terms| + k) body)
  end.

From MetaCoq.Erasure Require Import ELiftSubst.

Lemma csubst_substl_comm a n terms k body :
  closed a ->
  forallb (closedn 0) terms ->
  csubst a (n + k) (substl_rev terms k body) = 
  substl_rev terms k (csubst a (n + #|terms| + k) body).
Proof.
  induction terms in k, body |- *.
  - cbn. intros. now rewrite Nat.add_0_r.
  - cbn. move=> cla /andP[] cla0 clts.
    rewrite IHterms //. f_equal.
    rewrite !closed_subst //.
    rewrite -Nat.add_assoc (Nat.add_comm n).
    rewrite distr_subst_rec. cbn. lia_f_equal.
    rewrite subst_closed //. eapply closed_upwards; tea. lia.
Qed.

Lemma substl_rev_app {terms terms' k body} : 
  forallb (closedn 0) terms ->
  forallb (closedn 0) terms' ->
  substl_rev (terms ++ terms') k body = 
  substl_rev terms k (substl_rev terms' k body).
Proof.
  induction terms in body |- *; cbn => //.
  move=> /andP[] cla clt clt'.
  rewrite IHterms //. f_equal.
  rewrite csubst_substl_comm //. f_equal. now len.
Qed.

Lemma substl_substl_rev terms k body :
  forallb (closedn 0) terms ->
  fold_left (fun bod term : term => csubst term k bod) (List.rev terms) body = substl_rev terms k body.
Proof.
  revert k body.
  induction terms using rev_ind; intros k body.
  - cbn. reflexivity.
  - rewrite forallb_app => /andP[] clterms /=; rewrite andb_true_r => clx.
    cbn. rewrite List.rev_app_distr /=. rewrite IHterms //.
    rewrite substl_rev_app //. now rewrite /= clx.
Qed.

Definition t_fix_subst (ds : Defs) :=
  let fix aux (n : nat) : Terms :=
	  match n with
    | 0 => tnil
    | S n0 => tcons (TFix ds n0) (aux n0)
    end in
  aux (dlength ds).

Lemma compile_fix_subst Σ mfix :
  compile_terms Σ (fix_subst mfix) = t_fix_subst (list_Defs (map (compile_def Σ) mfix)).
Proof.
  unfold fix_subst, t_fix_subst.
  rewrite -dlength_hom.
  induction #|mfix|; cbn; auto.
  f_equal. simp_compile. cbn. reflexivity.
  now rewrite -IHn.
Qed.

Fixpoint tfold_left {A} (f : A -> Term -> A) l acc := 
  match l with
  | tnil => acc
  | tcons b t => tfold_left f t (f acc b)
  end.

Lemma instantiate_fold mfix bod :
  fold_left
    (fun (bod : Term) (ndx : nat) =>
      instantiate (TFix mfix ndx) 0 bod)
    (list_to_zero (dlength mfix)) bod = 
  tfold_left (fun bod term => instantiate term 0 bod) (t_fix_subst mfix) bod.
Proof.
  unfold t_fix_subst.
  induction (dlength mfix) in bod |- *; cbn; auto.
Qed.
 
Lemma wellformed_csubst Σ t n k u :
  wellformed Σ 0 t -> 
  wellformed Σ (S (n + k)) u -> 
  wellformed Σ (n + k) (ECSubst.csubst t k u).
Proof.
  intros.
  rewrite ECSubst.closed_subst //.
  now eapply wellformed_closed.
  rewrite -{1}(Nat.add_0_l k). cbn. eapply wellformed_subst_eq => /= //.
  rewrite andb_true_r //. eapply wellformed_up; tea. lia. now rewrite Nat.add_comm.
Qed.

Lemma substl_fold_left Σ terms k body :
  wf_glob Σ ->
  forallb (isEtaExp Σ) terms ->
  isEtaExp Σ body ->
  wellformed Σ (#|terms| + k) body ->
  forallb (wellformed Σ 0) terms ->
  compile Σ (fold_left (fun bod term : term => csubst term k bod) terms body) = 
  tfold_left (fun bod term => instantiate term k bod) (list_terms (map (compile Σ) terms)) (compile Σ body).
Proof.
  intros wfΣ.
  revert k body.
  induction terms; intros k body.
  - cbn. reflexivity.
  - rewrite /= => /andP[] etax etaterms etab wfb /andP[] clx clterms.
    cbn. rewrite IHterms //. now eapply etaExp_csubst.
    eapply wellformed_csubst => //.
    rewrite (compile_csubst _ (S #|terms|)) //.
Qed.

Lemma compile_substl Σ a b : 
  wf_glob Σ ->
  forallb (isEtaExp Σ) a ->
  forallb (wellformed Σ 0) a ->
  isEtaExp Σ b ->
  wellformed Σ #|a| b ->
  compile Σ (substl (List.rev a) b) = instantiatel (list_terms (map (compile Σ) a)) 0 (compile Σ b).
Proof.
  intros wf etaa cla etab.
  repeat toAll.
  unfold substl. rewrite substl_substl_rev. solve_all.
  now eapply wellformed_closed.
  induction cla in b, etab |- *; cbn => //.
  rewrite !Nat.add_0_r. cbn. intros wfb. rewrite IHcla.
  now eapply etaExp_csubst.
  eapply (wellformed_csubst _ _ 0) => //. apply p.
  f_equal. 
  rewrite tlength_hom. eapply (compile_csubst _ 1) => //. apply p.
Qed.

Lemma compile_substl_nrev Σ a b : 
  wf_glob Σ ->
  forallb (isEtaExp Σ) a ->
  forallb (wellformed Σ 0) a ->
  isEtaExp Σ b ->
  wellformed Σ #|a| b ->
  compile Σ (substl a b) = instantiatel (list_terms (map (compile Σ) (List.rev a))) 0 (compile Σ b).
Proof.
  intros wf etaa wfa etab wfb.
  rewrite -(List.rev_involutive a) compile_substl // ?forallb_rev //. now len.
  f_equal. now rewrite List.rev_involutive.
Qed.

Lemma nth_error_bnth {brs : list (list name × term)} {n br f} :
  nth_error brs n = Some br ->
  bnth n (list_Brs (map f brs)) = Some (f br).
Proof.
  induction brs in n, br |- *; destruct n; cbn; auto => //.
  intros [= <-]. destruct (f a). now cbn.
  intros h. specialize (IHbrs _ _ h). 
  now destruct (f a); cbn.
Qed.

Lemma nth_error_dnth {mfix : list (def term)} {n fn f} :
  nth_error mfix n = Some fn ->
  dnth n (list_Defs (map f mfix)) = Some (f fn).
Proof.
  induction mfix in n |- *; destruct n; cbn; auto => //.
  intros [= <-]. now destruct (f a).
Qed.

Lemma compile_whFixStep Σ mfix idx rarg fn : 
  wf_glob Σ ->
  wellformed Σ 0 (tFix mfix idx) ->
  isEtaExp Σ (tFix mfix idx) ->
  cunfold_fix mfix idx = Some (rarg, fn) ->
  whFixStep (list_Defs (map (compile_def Σ) mfix)) idx = Some (compile Σ fn).
Proof.
  unfold cunfold_fix, whFixStep. simp_eta.
  intros wfΣ cla eta.
  destruct nth_error eqn:hnth => //.
  intros [= <- <-].
  rewrite (nth_error_dnth hnth).
  destruct d as [dbody] => /=. f_equal.
  rewrite instantiate_fold.
  cbn in cla. move/andP: cla => [hn cla].
  rewrite substl_fold_left //.
  { now eapply isEtaExp_fix_subst => //. }
  { eapply nth_error_forallb in eta; tea. now move/andP: eta. }
  {  eapply nth_error_forallb in cla => //; tea. cbn in cla. len. rewrite fix_subst_length.
    now rewrite Nat.add_0_r in cla. }
  { eapply wellformed_fix_subst => //. } 
  f_equal. now rewrite -compile_fix_subst.
Qed.

Lemma Qpreserves_wellformed Σ : wf_glob Σ -> Qpreserves (fun n x => wellformed Σ n x) Σ.
Proof.
  intros clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn; intuition auto; try solve [constructor; auto].
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    eapply on_case; rtoProp; intuition auto. solve_all.
    eapply on_fix. solve_all. move/andP: H => [] _ ha. solve_all.
  - red. intros kn decl.
    move/(lookup_env_wellformed clΣ).
    unfold wf_global_decl. destruct cst_body => //.
  - red. move=> hasapp n t args. rewrite wellformed_mkApps //. 
    split; intros; rtoProp; intuition auto; solve_all.
  - red. cbn => //.
    (* move=> hascase n ci discr brs. simpl.
    destruct lookup_inductive eqn:hl => /= //.
    split; intros; rtoProp; intuition auto; solve_all. *)
  - red. move=> hasproj n p discr. now cbn in hasproj.
  - red. move=> t args clt cll.
    eapply wellformed_substl. solve_all. now rewrite Nat.add_0_r.
  - red. move=> n mfix idx. cbn. unfold wf_fix.
    split; intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
  - red. move=> n mfix idx. cbn.
    split; intros; rtoProp; intuition auto; solve_all.
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
    (EWcbvEvalEtaInd.eval_preserve_mkApps_ind fl (efl := env_flags) Σ _ 
      (wellformed Σ) (Qpres := Qpreserves_wellformed wfΣ)) => //; eauto.
  { intros. eapply EWcbvEval.eval_wellformed => //; tea. }
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
      rewrite -(compile_csubst _ 1) //. now simp_eta in etab. 
  - intros ev [IHev wfa wfb etaa etab] etab1 wfb1.
    intros ev' [IHev' wft wft' etat etat'].
    simp_compile. econstructor; tea.
    rewrite -(compile_csubst _ 1) //.
  - intros hbrs ev [IHev wfa wfb etaa etab].
    intros isp hnth hskip hbr wfbr.
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
    rewrite firstn_all2; len.
    unfold whCaseStep.
    rewrite (nth_error_bnth hnth).
    rewrite List.rev_length. rewrite tlength_hom.
    case: Nat.eqb_spec => //; try congruence.
    intros _. rewrite /iota_red skipn_0.
    f_equal. rewrite compile_substl //.
    now eapply nth_error_forallb in hbrs; tea.
    rewrite hbr //.
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
      { rewrite /mfix'. eapply compile_whFixStep; tea => //. }
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
  - (* Declarations *)
    intros hdecl res hbod hev.
    move => [] IHev wfbo wfr etab etares.
    simp_compile. econstructor; tea.
    eapply lookup_env_lookup in hdecl; tea.
    rewrite /lookupDfn hdecl /compile_global_decl.
    destruct decl as [[body'|]] => //. unfold exceptionMonad.ret. f_equal.
    now noconf hbod.
  - (* Congruence *)
    intros [hif' wff wff' etaf etaf'].
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
      apply/negP: H0. rewrite negbK. rewrite isConstructApp_mkApps //.
    * eapply (compile_tApp _ _ _ 0) => //. cbn. now rewrite wff' wfa'.
      destruct (decompose_app (tApp f' a')) eqn:da'.
      destruct (construct_viewc t0) eqn:vc'.
      { destruct lookup_constructor_pars_args as [[[] args']|] eqn:hl => // /=.
        pose proof (decompose_app_inv da').
        eapply (f_equal EWcbvEval.isConstructApp) in H.
        rewrite isConstructApp_tApp in H.
        rewrite EWcbvEval.isConstructApp_mkApps /= /EWcbvEval.isConstructApp /= in H.
        clear -nlam H. exfalso. move: nlam; rewrite !negb_or [isConstructApp _]H => /andP[] //. }
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
    move: hargs. rewrite /EWcbvEval.cstr_arity H /= => <-.
    rewrite PCUICTypeChecker.chop_firstn_skipn. epose proof (lenargs := All2_length IHargs).
    rewrite firstn_all2. len.
    rewrite !skipn_all2; len.
    econstructor. clear -IHargs.
    induction IHargs; cbn; constructor; intuition auto.
    now destruct r.
  - intros isat wf eta.
    destruct t => //; simp_compile; econstructor. constructor.
Qed.

Lemma compile_sound (wfl := EWcbvEval.target_wcbv_flags) {Σ t t'} : 
  isEtaExp_env Σ -> wf_glob Σ ->
  wellformed Σ 0 t ->
  isEtaExp Σ t -> 
  EWcbvEval.eval Σ t t' ->
  forall v, WcbvEval (compile_ctx Σ) (compile Σ t) v -> v = compile Σ t'.
Proof.
  intros etaΣ wfΣ wft etat ev v ev'.
  apply (WcbvEval_single_valued ev').
  now eapply WcbvEval_hom.
Qed. 
Print Assumptions compile_sound.

Definition program := environ Term * Term.

From MetaCoq.Erasure Require Import EProgram.

Definition compile_program (e : eprogram) : program :=
  (compile_ctx e.1, compile e.1 e.2).

Definition wf_program (p : program) := 
  crctEnv p.1 /\ crctTerm p.1 0 p.2.

Lemma wf_compile (p : eprogram) : 
  expanded_eprogram_cstrs p ->
  wf_eprogram env_flags p ->
  wf_program (compile_program p).
Proof.
  destruct p as [env main].
  unfold expanded_eprogram_cstrs.
  move/andP=> [etae etamain] [wfe wfmain]. cbn in *.
  split; cbn.
  - eapply wellformed_eta_crctEnv => //.
  - eapply wellformed_eta_crct => //.
    eapply wellformed_eta_crctEnv => //.
Qed. 

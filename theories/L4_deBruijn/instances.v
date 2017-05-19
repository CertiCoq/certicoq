Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L3.compile.
Require Import L4.L3_to_L4.
Require Import L4.L3_to_L3_eta.
Require Import L3.instances.

Require Import BinNat.
Require Import certiClasses2.

Definition L3_eta_Program := Program Term.
Typeclasses Opaque L3_eta_Program.

Instance bigStepOpSemL3_etaTerm:
  BigStepOpSem L3_eta_Program L3_eta_Program :=
  bigStepOpSemL3Term.

Global Instance ObsSubtermL3_eta : ObserveNthSubterm L3_eta_Program :=
  L3.instances.ObsSubtermL.

Global Instance QuestionHeadTermL3_eta : QuestionHead L3_eta_Program :=
  L3.instances.QuestionHeadTermL.

Instance WfL3_etaTerm : GoodTerm L3_eta_Program :=
  WfL3Term.

Global Instance certiL3_eta: CerticoqLanguage L3_eta_Program := {}.

Global  Instance certiL3_to_L3_eta: 
  CerticoqTranslation (cTerm certiL3) (cTerm certiL3_eta) :=
  fun p => Ret (L3_to_L3_eta.Program_Program p).

Global Instance certiL3_to_L3_eta_correct :
  CerticoqTranslationCorrect certiL3 certiL3_eta.
Proof.
  (* WIP *)
Admitted.

Definition dummyEnvBigStep {E T: Type}  (bt : BigStepOpSem T T)
: BigStepOpSem (E * T) (E * T) :=
  (fun e v => (fst e) = (fst v) /\ (snd e) ⇓ (snd v)).

Definition dummyEnvWf {E T: Type}  (bt : GoodTerm T)
: GoodTerm (E * T) :=
  (fun e => goodTerm (snd e)).

(* very low priority *)
Existing Instance dummyEnvBigStep | 1000000.
(* very low priority *)
Existing Instance dummyEnvWf | 1000000.

Let L4Term := prod ienv  L4.expression.exp.

Instance certiL4eval: BigStepOpSem L4.expression.exp L4.expression.exp := eval.
Global Instance L4_evaln : BigStepOpSemExec (ienv * L4.expression.exp)
                                            (ienv * L4.expression.exp) :=
  fun n p => match  (eval_n n (snd p)) with
             | Some v => Result (fst p,v)
             | None => Error "None" None
                           end.


Instance certiL4wf: GoodTerm L4.expression.exp :=
 L4.expression.exp_wf (0%N).

Definition question_head (Q : Question) (ie : ienv) (e : L4.expression.exp) :=
  match Q with
  | Abs => match e with
            Lam_e _ _ => true
          | _ => false
          end
  | Cnstr i n =>
    match e with
    | Con_e (i', n') args =>
      if eq_dec i i' then N.eqb (N.of_nat n) n' else false
    | _ => false
    end
  end.

Global Instance QuestionHeadTermL : QuestionHead (ienv * L4.expression.exp) :=
  fun q t => question_head q (fst t) (snd t).

Fixpoint exps_nthopt (n:nat) (xs:exps): option exp :=
  match n, xs with 
    | 0%nat, expression.econs h _ => Some h
    | S n, expression.econs _ t => exps_nthopt n t
    | _, _ => None
  end.

Definition observe_nth_subterm n (e : exp) :=
  match e with
  | Con_e _ args => exps_nthopt n args
  | _ => None
  end.

Global Instance ObsSubtermTermL : ObserveNthSubterm (ienv * L4.expression.exp) :=
  fun n t => match observe_nth_subterm n (snd t) with
          | None => None
          | Some e => Some (fst t, e)
          end.

Global Instance certiL4: CerticoqLanguage (ienv * L4.expression.exp) := {}.

Global  Instance certiL3_eta_to_L4: 
  CerticoqTranslation (cTerm certiL3_eta) (cTerm certiL4)  :=
  fun p =>
    Ret ( L4.L3_to_L4.inductive_env (AstCommon.env p),
   (L3_to_L4.translate_program (AstCommon.env p) (main p))).

Require Import L4.L3_to_L4_correct.

Lemma same_args_same_obs n t e t' :
  same_args same_obs t e = true -> tnth n t = Some t' ->
  exists e', exps_nthopt n e = Some e' /\ same_obs t' e' = true.
Proof.
  clear.
  revert t e t'; induction n; intros *; simpl.
  destruct t; simpl; intros; try destruct e; try discriminate.
  injection H0. intros ->. exists e. now apply andb_prop in H as [Ht' Ha].

  intros Ha Ht. destruct t; destruct e; try discriminate.
  simpl in Ha. apply andb_prop in Ha as [Hte Ht0].
  eapply IHn; eauto.
Qed.

Global Instance certiL3_eta_to_L4_correct :
  CerticoqTranslationCorrect certiL3_eta certiL4.
Proof.
  split.
{ red; unfold certiClasses.translate, goodTerm, WfL3Term.
  intros. red in H. red in H.
  pose proof (proj1 L3.program.Crct_CrctEnv _ _ _ H).
  unfold certiL3_eta_to_L4. hnf.
  simpl. destruct s. simpl in *.
  unfold L3_to_L4.translate_program. simpl.
  unfold translate. simpl.
  now apply exp_wf_lets. }

{ red; unfold certiClasses.translate, goodTerm, WfL3Term. intros.
  assert(He:=proj1 L3.program.Crct_CrctEnv _ _ _ H).
  repeat red in H0.
  destruct s. destruct sv.
  destruct H0. 
  pose proof (L3_to_L4_correct.translate_correct' env _ _ _ He H H0 H1). 
  simpl in H2. unfold certiL3_eta_to_L4. 
  destruct H2 as [sv' [evsv obs]].
  eexists (inductive_env env, sv');
    split. repeat red. split. simpl; auto. simpl.
  { apply evsv. }
  clear evsv He H1 H0 H. revert main0 sv' obs. clear.
  apply (TrmTrmsBrsDefs_ind
             (fun (main : Term) => forall (sv' : exp),
                  same_obs main sv' = true ->
                  {| main := main; AstCommon.env := env0 |} ⊑ (inductive_env env, sv'))
             (fun ts => forall d i n n0 es, same_args same_obs ts es = true ->
                 obsLeOp (observeNthSubterm n0 {| main := TConstruct i n ts; AstCommon.env := env0 |})
                         (observeNthSubterm n0 (inductive_env env, Con_e d es)))
             (fun _ => True) (fun _ => True));
        try constructor;
        try (match goal with |- yesPreserved _ _ => intros q; destruct q end);
        intros; try red; trivial; try constructor.
  rename H0 into obs.
  simpl in *; unfold questionHead. simpl.
  destruct sv'; trivial; intros; simpl in *; try discriminate.
  destruct d; simpl in *.
  destruct inductive_dec; simpl; trivial. subst.
  destruct PeanoNat.Nat.eq_dec; simpl; trivial. subst. simpl.
  unfold eq_decb in obs. unfold eq_dec in obs. simpl in obs. 
  destruct inductive_dec; simpl in *; subst; try contradiction || discriminate.
  destruct PeanoNat.Nat.eq_dec; simpl in *; try discriminate. subst n.
  rewrite Nnat.N2Nat.id. apply N.eqb_refl.
  
  destruct sv'; intros; try discriminate.
  simpl in H0. apply andb_prop in H0.
  destruct H0 as [_ obs]. now apply H.
  
  destruct es; simpl in *.
  unfold observeNthSubterm, ObsSubtermTermL, ObsSubtermL.
  simpl. 
  unfold instances.observe_nth_subterm. simpl. destruct n0; simpl; constructor.
  discriminate.

  unfold observeNthSubterm, ObsSubtermTermL, ObsSubtermL.
  unfold instances.observe_nth_subterm.
  simpl. 
  destruct es; simpl in H1; try discriminate.
  apply andb_prop in H1 as [Ht Ht0].
  destruct n0; simpl.
  constructor. apply (H _ Ht).

  specialize (H0 d i n n0 es Ht0).
  unfold observeNthSubterm, ObsSubtermTermL, ObsSubtermL in *.
  unfold instances.observe_nth_subterm in *. simpl in H0. apply H0. }
Qed.


Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_2_to_L4_5.
Require Import DecidableClass.

(** Fix or remove *)
Global Instance L4_2_eval : BigStepOpSem L4_2_Term L4_2_Term := fun _ _ => True.

Require Import Common.TermAbs.

Global Instance L4_2_evaln
  : BigStepOpSemExec (ienv * L4_2_Term) (ienv * L4_2_Term) :=
  fun n e => match (@polyEval.eval_n (Named.TermAbsImpl variables.NVar polyEval.L4Opid) n (snd e)) with
          | None => Error "None" None
          | Some v => Result (fst e, v)
          end.


(** Fix or remove *)
Global Instance : GoodTerm L4_2_Term :=
  fun e  => False.

(** Fix or remove *)
Global Instance QuestionHeadTermL42 : QuestionHead (prod ienv L4_2_Term) :=
fun q t => false.

(** Fix or remove *)
Global Instance ObsSubtermTermL42 : ObserveNthSubterm (prod ienv L4_2_Term) :=
  fun n t => None.

(** Fix or remove *)
Global Instance certiL4_2: CerticoqLanguage (prod ienv L4_2_Term) := {}.

Global Instance certiL4_to_L4_2: 
  CerticoqTotalTranslation (cTerm certiL4) (cTerm certiL4_2) :=
  fun p => (fst p, (tL4_to_L4_2 (snd p))).


Global Program Instance : BigStepOpSem L4_5_Term L4_5_Term := eval.

(** all variables must be user variables *)
Global Program Instance : GoodTerm L4_5_Term :=
  fun e  => varsOfClass (all_vars e) true /\ isprogram e /\ fixwf e = true.

Require Import DecidableClass.
Global Instance QuestionHeadTermL45 : QuestionHead (prod ienv L4_5_Term) :=
fun q t =>
match q, snd t with
| Cnstr ind ci, oterm (NDCon dc _) _ =>
  let (ind2, ci2) := dc in
  andb (decide (ind=ind2)) (decide (N.of_nat ci =ci2))
| Abs, oterm NLambda _ => true
| _, _ => false
end.

Global Instance ObsSubtermTermL45 : ObserveNthSubterm (prod ienv L4_5_Term) :=
  fun n t =>
    let (env, t) := t in
    match t with
    | oterm (NDCon dc _) lbt =>
      List.nth_error  (List.map (fun b => (env, get_nt b)) lbt) n
    | _ => None
    end.

Global Instance certiL4_5: CerticoqLanguage (prod ienv L4_5_Term) := {}.


Global Instance certiL4_2_to_L4_5: 
  CerticoqTotalTranslation (cTerm certiL4_2) (cTerm certiL4_5) :=
  fun p => (fst p, (L4_2_to_L4_5  (snd p))).


Require Import L4.variables.

Definition L5Term :Type := (@NTerm NVar L5Opid).

Global Instance L4_5_evaln
  : BigStepOpSemExec (ienv * L4_5_Term) (ienv * L4_5_Term) :=
  fun n e => match (@L4_2_to_L4_5.eval_n (Named.TermAbsImpl variables.NVar L4_5Opid) n (snd e)) with
          | None => Error "None" None
          | Some v => Result (fst e, v)
          end.

Global Program Instance : BigStepOpSem L5Term L5Term := eval_c.

(* may need to strengthened: consider adding the predicated nt_wf and fixwf.
It seems that there is currently there is no proof that cps_cvt nt_wf.
A more direct alternative to nt_wf could be the predicate that says that the conversion from
L5 to L5a succeeds.  *)
Global Program Instance : GoodTerm L5Term := closed (*isprogram *).

Global Instance L5_evaln
  : BigStepOpSemExec (ienv * L5Term) (ienv * L5Term) :=
  fun n e => match (@L4_5_to_L5.eval_n (Named.TermAbsImpl variables.NVar L5Opid) n (snd e)) with
          | Result v => Result (fst e, v)
          | Error s t => Error s (option_map (fun p => (fst e, p)) t)
          | OutOfTime t => OutOfTime (fst e, t)
          end.

Global Instance QuestionHeadTermL5 : QuestionHead (ienv * L5Term) :=
fun q t =>
match q, snd t with
| Cnstr ind ci, oterm (CDCon dc _) _ =>
  let (ind2, ci2) := dc in
  andb (decide (ind=ind2)) (decide (N.of_nat ci =ci2))
| Abs, oterm CLambda _ => true
| _, _ => false
end.

Global Instance ObsSubtermTermL5 : ObserveNthSubterm (ienv * L5Term) :=
  fun n t =>
    let (env, t) := t in
    match t with
    | oterm (CDCon dc _) lbt =>
      List.nth_error  (List.map (fun b => (env, get_nt b)) lbt) n
    | _ => None
    end.

Global Instance certiL5: CerticoqLanguage (ienv * L5Term) := {}.


Lemma haltContAp (t: L5Term):  eval_c (Ret_c haltCont t) t.
Proof.
  unfold haltCont.
  rewrite eval_ret.
  simpl. unfold subst. simpl.
  apply eval_Halt_c.
Qed.

Global Instance certiL4_5_to_L5:
  CerticoqTotalTranslation (cTerm certiL4_5) (cTerm certiL5):=
  (fun x => (fst x, Ret_c (cps_cvt (snd x)) haltCont)).

Definition oldTranslation : (cTerm certiL4_5) -> (cTerm certiL5):=
  (fun x => (fst x, (cps_cvt (snd x)))).

Require Import SquiggleEq.tactics.
Require Import ExtLib.Data.ListNth.

(* Move to L4_5_to_L5 *)
Hint Unfold isprogram : eval.
Hint Resolve @eval_yields_value' @eval_preseves_varclass 
  @eval_preseves_wf @eval_preserves_closed conj
  @cps_cvt_val_closed @cps_cvt_closed @eval_preserves_fixwf @eval_end: eval.

Require Import Btauto.
Lemma valueObsEq (senv: ienv) : forall (sv:L4_5_Term), is_value sv ->
                                                  (senv, sv) ⊑ (senv, cps_cvt_val sv).
Proof using.
  intros ? Hisv.
  induction Hisv; simpl. (* this is proof by induction, not coinduction *)
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor.
  + unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    destruct q; auto. unfold implb. btauto.
  + clear H. rename H0 into Hind. intros ?. cbn. repeat rewrite List.map_map.
    repeat rewrite nth_error_map.
    remember (List.nth_error es n) as esso.
    destruct esso as [ess | ]; try constructor.
    simpl. apply Hind.
    eapply List.nth_error_In.
    symmetry. eassumption.
- constructor; compute; intros qn; [ destruct qn | ]; try constructor.
Qed.
                                                  
Require Import L4.variables.
Require Import L4.varInterface.


  Hint Unfold certiClasses.translate liftTotal bigStepEval certiClasses.bigStepEval
       liftBigStepException translateT certiL4_5_to_L5  bigStepEval dummyEnvBigStep
       yesPreserved questionHead QuestionHeadTermL45 QuestionHeadTermL5
       BigStepOpSem_instance_1  BigStepOpSem_instance_0
       goodTerm dummyEnvWf goodTerm GoodTerm_instance_0
       GoodTerm_instance_1: certiclasses.

  Require Import Morphisms.
Global Instance evalPreservesGood :
  Proper (eval ==> Basics.impl) (@goodTerm L4_5_Term _).
Proof using.
  intros e v Hev Hg.
  hnf. autounfold with certiclasses eval in *. repnd.
  dands; eauto with eval typeclass_instances.
Qed.

(* all variants of the correctness property need this part *)
Lemma goodPres45 : goodPreserving (ienv * L4_5_Term) (ienv * L5Term).
Proof using.
  simpl. red. intros ? Hgood.
  unfold certiClasses.translate, liftTotal, bigStepEval,
  liftBigStepException, translateT, certiL4_5_to_L5. simpl.
  simpl. hnf. simpl.
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_1, isprogram, closed in Hgood.
  destruct s as [? s]; simpl in *. repnd.
  hnf. simpl. symmetry. rewrite cps_cvt_aux_fvars; auto. rewrite Hgood2. refl.
Qed.

Global Instance certiL4_5_to_L5Correct: CerticoqTranslationCorrect certiL4_5 certiL5.
(* Again, proof by induction *)
Proof.
  constructor.
- exact goodPres45.
- red. intros ? ? Hgood Heval.
  destruct Heval as [Heq Heval].
  destruct s as [senv s].
  destruct sv as [? sv]. symmetry in Heq.
  simpl in *. subst.
  exists (senv, (cps_cvt_val sv)).
  unfold certiClasses.translate, liftTotal, bigStepEval,
  liftBigStepException, translateT, certiL4_5_to_L5. simpl.
  repeat progress (unfold bigStepEval, dummyEnvBigStep; simpl).
  unfold BigStepOpSem_instance_1. simpl.
  simpl. unfold bigStepEval, dummyEnvBigStep. simpl.
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_1 in Hgood.
  simpl in *. repnd. destruct Hgood1 as [Hclosed Hwf].
  rename Hgood0 into Hvc. rename Hgood into Hfixwf.
  dands;[reflexivity | | ].
  + pose proof
         (cps_cvt_corr _ _ Hwf Hfixwf Hvc Heval
                       Hclosed haltCont
                       eq_refl
                       ((cps_cvt_val sv)))
      as Hcps.
    apply Hcps. clear Hcps.
    hnf in Heval.
    rewrite (cps_val_ret_flip sv); try split; eauto with eval typeclass_instances.
    unfold haltCont.
    apply haltContAp.
    
  + hnf in Heval. apply eval_yields_value' in Heval.
    revert Heval. clear.
    apply valueObsEq.
Qed.


Require Import L4.L5a.

(* Fix. Define subst and evaluation on L5a by going to L5 via a bijection? *)
Global Program Instance : BigStepOpSem L4.L5a.cps  L4.L5a.cps :=
  fun _ _ => True.

(** Fix *)
Global Program Instance : GoodTerm L4.L5a.cps := fun x => False.

(* FIX!! *)
Global Instance QuestionHeadTermL5a : QuestionHead (ienv * L4.L5a.cps) :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermTermL5a: ObserveNthSubterm (ienv * L4.L5a.cps) :=
fun n t => None.

Global Instance certiL5a: CerticoqLanguage (ienv * L4.L5a.cps) := {}.

Global Instance certiL5_to_L5a: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL5a)  :=
  fun e =>
   match L4.L5a.translateCPS (snd e) with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e5a => exceptionMonad.Ret (fst e, e5a)
  end.

Definition certiL5_to_L5aOld : 
  CerticoqTranslation (cTerm certiL5) (ienv * L4.L5a.val_c)  :=
  fun e =>
   match L4.L5a.translateVal (snd e) with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e5a => exceptionMonad.Ret (fst e, e5a)
  end.


Require Import Template.Template.
Open Scope nat_scope.
Quote Recursively Definition p0L1 := (fun vl vr:nat => vl + vr). 

Require Import L2.instances.

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)
Open Scope string_scope.


Fixpoint even (n:nat) : bool :=
  match n with
    | O => true
    | (S n') => odd n'
  end
with odd n : bool :=
  match n with
    | O => false
    | (S n') => even n'
  end.

Require Import String.
Require Import List.
Import ListNotations.



Require Import Program.


Definition print4 (t: cTerm certiL4_5) : string :=
(tprint "" NVar2string  L4_5_to_L5.L4_5OpidString  (snd t)).

Definition print5 (t: cTerm certiL5) : string :=
(tprint "" NVar2string  L4_5_to_L5.L5OpidString  (snd t)).

Require Import L1g.instances.

Definition ctranslateEvalL5a
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm certiL5)}
   (p: program) (n:nat) : bigStepResult (option L5a.cps)  (option L5a.val_c) :=
  mapBigStepRes (L5a.translateCPS ∘ snd) (L5a.translateVal ∘ snd) (ctranslateEval certiL5 p n).

(*
Require Import L1g.instances.
Require Import L2.instances.
Require Import L2_5.instances.
Require Import L2.instances.
  

Quote Recursively Definition v0L1 := 0. 
  
Definition v0L45 := Eval vm_compute in ( (ctranslateTo certiL4_5 v0L1)).
Print v0L45.
Definition p0L5New := Eval vm_compute in (exception_map certiL4_5_to_L5 v0L45).
Definition p0L5Old := Eval vm_compute in (exception_map oldTranslation v0L45).


Eval compute in (exception_map print5 p0L5New).
Eval compute in (exception_map print5 p0L5Old).

Eval compute in (exception_map snd (bind p0L5New certiL5_to_L5a)).
(*
Ret
         (Ret_c
            (Cont_c (3%positive, nNamed "k")
               (Ret_c (KVar_c (3%positive, nNamed "k"))
                  (Con_c (mkInd "Coq.Init.Datatypes.nat" 0, 0%N) [])))
            (Cont_c (3%positive, nNamed "k") (Halt_c (KVar_c (3%positive, nNamed "k")))))
 *)
Eval compute in (exception_map snd (bind p0L5Old certiL5_to_L5aOld)).

(*
(Cont_c (3%positive, nNamed "k")
            (Ret_c (KVar_c (3%positive, nNamed "k"))
               (Con_c (mkInd "Coq.Init.Datatypes.nat" 0, 0%N) [])))
*)

Quote Recursively Definition evo := (andb (even 0) (odd 1)).

Eval vm_compute in (exception_map print4 (ctranslateTo certiL4_2 evo)).
Eval vm_compute in (exception_map print5 (ctranslateTo certiL5 evo)).

Check  @cps_cvt_corr.
 ***)

(*
     = Ret
         ([("Coq.Init.Datatypes.nat", 0,
           [{|
            itypNm := "nat";
            itypCnstrs := [{| CnstrNm := "O"; CnstrArity := 0 |},
                          {| CnstrNm := "S"; CnstrArity := 1 |}] |}])],
         Cont_c 5%positive
           (Ret_c (KVar_c 5%positive) (Con_c (mkInd "Coq.Init.Datatypes.nat" 0, 0%N) nil)))
     : exception (cTerm certiL5a)
*)


Require Import Common.certiClasses3.

Section Temp.

  Local Instance L4_5bs : BigStepOpSem (prod ienv L4_5_Term).
  apply dummyEnvBigStep. eauto with typeclass_instances.
  Defined.
  Local Instance L5bs : BigStepOpSem (prod ienv (@NTerm NVar L5Opid)).
  apply dummyEnvBigStep. eauto with typeclass_instances.
  Defined.


Local Instance L4_5MkApply : MkApply  (ienv * L4_5_Term) :=
    fun f a => let (senv,f) := f in let (_, a) := a in (senv, App_e f a).

  Definition extractL5Core (t:L5Term) :=
    match t with
      (*  L4_5_to_L5.Ret_c core haltCont => core *)
      oterm CRet [bterm [] core; _] => core
      | _ => oterm CRet [] (* impossible, hence garbage *)
    end.

  Local Instance L5MkApply : MkApply  (ienv * L5Term) :=
    fun f a => let (senv,f) := f in
            let (_, a) := a in
            let a := extractL5Core a in
            (senv, mkAppHalt (val_outer f) a).
  
  (*TODO: re add after ending sections *)

  Hint Unfold L5bs  bigStepEval : certiclasses.

  Require Import L4_5_to_L5.
  (* Move *)
  
(*
Lemma evalc_terminal
     : forall e v,
      eval_c e v -> eval_c v v.
Proof using.
  intros ? ? Heval.
  induction Heval; auto;[]. (* eval_halt_c case. fix. require some kind of an is_value.
A ugly hacky way would be to require that it is the vps_cvt_val of something. *)
Abort.

Lemma evalc_halt
     : forall hv v,
      eval_c (Halt_c hv) v <-> eval_c hv v.
Proof using.
  intros.
  split; intros Hyp.
  - inversion Hyp. subst. eapply evalc_terminal; eauto.
  - (* need the is_value hyp? *)
Abort.    
 *)

Lemma goodSubterms25 : forall o lbt,
    @goodTerm L4_5_Term _ (oterm o lbt)
    -> forall nt, In (bterm [] nt) lbt  -> goodTerm nt.
Proof using.
  intros ? ? Hg ? Hin. autounfold with certiclasses eval in *.
  unfold closed in *. simpl in *.
  repnd.
  rewrite  list.flat_map_empty in Hg2.
  autorewrite with SquiggleEq in Hg0.
  specialize (Hg2 _ Hin).
  simpl in *.
  dands; auto.
  - intros ? Hc. apply Hg0. apply in_flat_map. eexists; dands; eauto.
  - ntwfauto.
  - rewrite Bool.andb_true_iff in Hg. apply proj2 in Hg.
    rewrite list.ball_true in Hg. apply Hg.
    apply in_map_iff. eexists; dands; eauto. reflexivity.
Qed. 

Require Import SquiggleEq.list.
Lemma goodSubtermsApp : forall (a b: L4_5_Term),
    goodTerm a
    -> goodTerm b
    -> goodTerm (App_e a b).
Proof using.
  autounfold with certiclasses in *.
  intros ? ? H1g H2g.
  unfold App_e. 
  rwsimplC. unfold compose. simpl.
  unfold isprogram, closed in *.
  simpl. rwsimplC. repnd.
  dands; eauto with SquiggleEq.
  - rwHyps. refl.
  - ntwfauto. rewrite  or_false_r in HntwfIn. subst. ntwfauto.
Qed.


Lemma value_cps_val (v : L4_5_Term) :
  is_value v -> closed v -> eval_c (cps_cvt_val v) (cps_cvt_val v).
Proof using.
  intros Hisv Hcl.
  destruct Hisv; try (apply eval_Val_c; reflexivity).
  inversion Hcl.
Qed. (** need to fix eval_c to make this true *)

Lemma value_cps_val_only (v : L4_5_Term) vc:
  eval_c (cps_cvt_val v) vc -> vc= (cps_cvt_val v).
Proof using.
  intros Hev.
  destruct v.
  inversion Hev;subst. invertsn H.
  rename l into o.
  destruct o; invertsna Hev Hevv; auto; provefalse.
  - destruct l0; invertsn Hevv. destruct b. destruct l; invertsn Hevv.
    destruct l; invertsn Hevv. destruct l0; invertsn Hevv.
  - clear Hevv.  rename Hevv0 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv.  rename Hevv0 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv Hevv0.  rename Hevv1 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
  - clear Hevv Hevv0 Hevv1.  rename Hevv2 into Hevv.
    destruct l0 as [ | ? l]; invertsn Hevv.
    destruct b. do 2 (destruct l0 as [ | ? l0]; invertsn Hevv).
    destruct l as [ | ? l]; invertsn Hevv.
Qed.


Lemma obsLinkableL45:
  compObsPreservingLinkable  (ienv * L4_5_Term) (ienv * L5Term).
Abort.
(***************************8
Proof.
  intros ?. 
  revert s.
  cofix.
  intros ? Hgood.
  constructor. constructor.
  intros ? Heval.
  simpl.
  destruct Heval as [Heq Heval].
  destruct s as [senv s].
  destruct sv as [? sv]. symmetry in Heq.
  simpl in *. subst.
  exists (senv, (cps_cvt_val sv)).
  pose proof (evalPreservesGood _ _ Heval Hgood) as Hgoodsv.
  pose proof (eval_yields_value' _ _ Heval) as Hvalue.
  repeat progress autounfold with certiclasses.
  simpl in *. 
  dands; [ reflexivity | | | | ].

  + simpl in Hgood. autounfold with certiclasses in Hgood. simpl in Hgood.
    simpl in Hgood. autounfold with certiclasses in Hgood. simpl in Hgood.
    repnd.
    destruct Hgood1 as [Hclosed Hwf].
    rename Hgood0 into Hvc. rename Hgood into Hfixwf.    pose proof
         (cps_cvt_corr _ _ Hwf Hfixwf Hvc Heval
                       Hclosed haltCont
                       eq_refl
                       ((cps_cvt_val sv)))
      as Hcps.
    apply Hcps. clear Hcps.
    hnf in Heval.
    rewrite (cps_val_ret_flip sv); try split; eauto with eval typeclass_instances.
    unfold haltCont.
    apply haltContAp.
  + hnf in Heval. apply eval_yields_value' in Heval.
    revert Heval. clear. intros Hisv.
    let tac := compute; intros qn;  destruct qn; constructor in
    induction Hisv; simpl; [tac | tac |  | tac].
    unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    destruct q; auto. unfold implb. btauto.
  + clear dependent s. intros n.
    unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    inversion Hvalue;
    (* Not induction. Even though the arguments of constructors are all values, 
     they may be lambdas, and after application, they may need computation *)
    simpl; try (clear obsLinkableL45; compute; constructor; fail). subst.
    repeat rewrite List.map_map.
    repeat rewrite nth_error_map.
    remember (List.nth_error es n) as esso.
    destruct esso as [ess | ]; try constructor.
    specialize (obsLinkableL45 (senv, ess)).
    symmetry in Heqesso. apply nth_error_In in Heqesso.
    assert (ident : goodTerm (senv, ess)) by
      (eapply goodSubterms25;[apply Hgoodsv | apply in_map; assumption]).
    specialize (obsLinkableL45 ident).
    invertsn obsLinkableL45.
    unfold translateT, certiL4_5_to_L5 in obsLinkableL45.
    simpl in *.
    revert obsLinkableL45.
    assert (Hp:forall A B, (A<->B)->(A->B)) by tauto.
    apply Hp. clear Hp.
    apply compObsLeLinkRespectsSameVal;[ reflexivity | ].
    intros ?.
    apply and_iff_compat_l.
    simpl.  unfold haltCont.
    repeat (autounfold with certiclasses eval in ident;  simpl in ident). repnd.
    rewrite (cps_val_ret_flip ess); unfold isprogram; eauto; try reflexivity.
    simpl.
    rewrite eval_ret. simpl. unfold subst. simpl.
    split; intros Hyp.
    * inversion Hyp; try (inversion H0; fail); subst. apply value_cps_val; eauto.
    * apply value_cps_val_only in Hyp; eauto. subst. apply eval_Halt_c.

  + intros Hq ? Hga. unfold mkApp, L4_5MkApply, L5MkApply. simpl.
    destruct svArg as [clear  svArg]. simpl. hnf in Hga. simpl in *. clear clear.
    specialize (obsLinkableL45 (senv, App_e sv svArg)).
    assert (ident : goodTerm (senv, App_e sv svArg)) by (apply goodSubtermsApp; auto).
    specialize (obsLinkableL45 ident).
    invertsn obsLinkableL45.
    unfold translateT, certiL4_5_to_L5 in obsLinkableL45.
    simpl in *. unfold mkAppHalt. unfold cps_cvt_apply in obsLinkableL45.
    constructor.
    revert obsLinkableL45.
    assert (Hp:forall A B, (A<->B)->(A->B)) by tauto.
    apply Hp. clear Hp.
    apply compObsLeLinkRespectsSameVal;[ reflexivity | ].
    unfold sameValues. intros v.
    apply and_iff_compat_l.
    simpl.  rewrite eval_ret. simpl.
    assert (forall (l1 l2 r: L5Term), l1=l2 -> (eval_c l1 r <-> eval_c l2 r)) as Hp by (intros;subst;tauto).
    apply Hp. clear Hp.
    unfold subst. change_to_ssubst_aux8; [ | apply list.disjoint_nil_r ].
    Local Transparent ssubst_aux ssubst_bterm_aux sub_filter.
    autounfold with certiclasses in Hgoodsv.
    unfold isprogram, closed in *.
    assert (free_vars (cps_cvt sv) = []) as Hs.
      (symmetry; rewrite cps_cvt_aux_fvars ; repnd; auto).
    assert (free_vars (cps_cvt svArg) = []) as Hsa by
      (symmetry; rewrite cps_cvt_aux_fvars ; repnd; auto; congruence).
    simpl.
    rewrite (fst ssubst_aux_trivial5) at 1; [ | simpl; rewrite Hs; apply list.disjoint_nil_l ].
    rewrite (fst ssubst_aux_trivial5); [ | simpl; rewrite Hsa; apply list.disjoint_nil_l ].
    unfold cps_cvt_apply_aux,  L4_5_to_L5.Ret_c,  L4_5_to_L5.KLam_c.
    repeat f_equal.
    apply cps_val_outer. apply is_valueb_corr. eapply eval_yields_value'; eauto.
    Fail idtac.
Abort.
************************)
  End Temp.
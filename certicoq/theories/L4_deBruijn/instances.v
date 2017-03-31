Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L3.compile.
Require Import L4.L3_to_L4.
Require Import L3.instances.

Require Import BinNat.

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

Instance certiL4wf: GoodTerm L4.expression.exp :=
 L4.expression.exp_wf (0%N).


Require Import certiClasses2.

Definition question_head (Q : Question) (ie : ienv) (e : L4.expression.exp) :=
  match Q with
  | Abs => match e with
            Lam_e _ _ => true
          | Fix_e _ _ => true
          | _ => false
          end
  | Cnstr i n =>
    match e with
    | Con_e (i', n') args =>
      if eq_dec i i' then N.eqb (N.of_nat n) n' else false
    | _ => false
    end
  end.
(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead (ienv * L4.expression.exp) :=
  fun q t => question_head q (fst t) (snd t).

(* FIX!! *)
Global Instance ObsSubtermTermL : ObserveNthSubterm (ienv * L4.expression.exp) :=
fun n t => None.

Global Instance certiL4: CerticoqLanguage (ienv * L4.expression.exp) := {}.

Global  Instance certiL3_to_L4: 
  CerticoqTranslation (cTerm certiL3) (cTerm certiL4)  :=
fun p => Ret ( L4.L3_to_L4.inductive_env (AstCommon.env p),
   (L3_to_L4.translate_program (AstCommon.env p) (main p))).

Require Import L4.L3_to_L4_correct.

Lemma eval_env e : wf_environ e -> exists e', eval_env (translate_env e) e'.
Proof.
  induction 1.
  - exists nil; constructor.
  - destruct IHwf_environ.
    simpl.
    pose proof (L3_to_L4_correct.translate_correct e t).
    eexists.
    constructor. apply H2.
Admitted.

Global Instance certiL3_to_L4_correct :
  CerticoqTranslationCorrect certiL3 certiL4.
Proof.
  split.
  - red; unfold certiClasses.translate, goodTerm, WfL3Term.
    intros.
    pose proof (L3_to_L4_correct.Crct_wf_environ _ _ H).
    unfold certiL3_to_L4. hnf.
    simpl. destruct s. simpl in *.
    unfold translate_program. simpl.
    unfold translate. simpl.
    now apply exp_wf_lets.

  - red; unfold certiClasses.translate, goodTerm, WfL3Term. intros.
    pose (Crct_wf_environ _ _ H). destruct s, sv. cbn in *.
    destruct H0. subst env0.
    pose proof (L3_to_L4_correct.translate_correct env _ _ w H H0).
    simpl in H1.
    destruct (eval_env _ w).
    specialize (H1 _ H2).
    eexists (inductive_env env, _). split. repeat red. split. simpl.
    reflexivity.
    simpl. repeat red. apply H1.
    { constructor. red. simpl. reflexivity.
      intros. constructor. }
Qed.


Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_2_to_L4_5.


Global  Program Instance : BigStepOpSem L4_5_Term L4_5_Term := eval.

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


Global Instance certiL4_to_L4_5: 
  CerticoqTotalTranslation (cTerm certiL4) (cTerm certiL4_5) :=
  fun p => (fst p, (L4_2_to_L4_5 (tL4_to_L4_2 (snd p))) ).

  


Require Import L4.variables.

Definition L5Term :Type := (@NTerm NVar L5Opid).

Global Program Instance : BigStepOpSem L5Term L5Term := eval_c.

(* may need to strengthened: consider adding the predicated nt_wf and fixwf.
It seems that there is currently there is no proof that cps_cvt nt_wf.
A more direct alternative to nt_wf could be the predicate that says that the conversion from
L5 to L5a succeeds.  *)
Global Program Instance : GoodTerm L5Term := closed (*isprogram *).

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

Definition haltCont : L5Term := KLam_c contVar (Halt_c (vterm contVar)).

Lemma haltContAp t : eval_c (Ret_c haltCont t) t.
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
  induction Hisv; simpl.
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor; compute; intros qn; [ destruct qn | ]; constructor.
- constructor.
  + unfold yesPreserved, questionHead, QuestionHeadTermL45, QuestionHeadTermL5; cbn.
    destruct q; auto. unfold implb. btauto.
  + clear H. rename H0 into Hind. intros ?. cbn. repeat rewrite List.map_map.
    repeat rewrite  list.nth_error_map.
    remember (List.nth_error es n) as esso.
    destruct esso as [ess | ]; try constructor.
    simpl. apply Hind.
    eapply List.nth_error_In.
    symmetry. eassumption.
- constructor; compute; intros qn; [ destruct qn | ]; try constructor.
Qed.
                                                  
Require Import L4.variables.
Require Import L4.varInterface.
Global Instance certiL4_5_to_L5Correct: CerticoqTranslationCorrect certiL4_5 certiL5.
Proof.
  constructor.
- simpl. red. intros ? Hgood.
  unfold certiClasses.translate, liftTotal, bigStepEval,
  liftBigStepException, translateT, certiL4_5_to_L5. simpl.
  simpl. hnf. simpl.
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_0, isprogram, closed in Hgood.
  destruct s as [? s]; simpl in *. repnd.
  hnf. simpl. symmetry. rewrite cps_cvt_aux_fvars; auto. rewrite Hgood2. refl.
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
  unfold goodTerm, dummyEnvWf, goodTerm, GoodTerm_instance_0 in Hgood.
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

Definition exception_map {A B:Type} (f: A->B) (e: exception A) : exception B:=
match e with
| Ret a => Ret (f a)
| Exc s => Exc s
end.

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


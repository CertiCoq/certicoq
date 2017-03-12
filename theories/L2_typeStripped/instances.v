Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import L2.term.
Require Import certiClasses.
Require Import Common.Common.
Require Import L1g.instances.
Require Import certiClasses2.
Require Import L2.stripEvalCommute.

Instance bigStepOpSemL2Term: BigStepOpSem (Program L2.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL2Term: GoodTerm (Program L2.compile.Term) :=
  fun _  => True.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L2.compile.Term) :
  (L2.compile.Term * (list L2.compile.Term)) :=
  match t with
    | TApp fn arg args => (fn, cons arg (Terms_list args))
    | s => (s, nil)
  end.

Global Instance QuestionHeadL2Term: QuestionHead (Program L2.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL2Term :
  ObserveNthSubterm (Program L2.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ , subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Global Instance certiL2Eval: BigStepOpSem (Program L2.compile.Term).
  apply BigStepOpWEnv.
  apply WcbvEval.
Defined.

Global Instance certiL2: CerticoqLanguage (Program L2.compile.Term).

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.

(***
Goal
  forall (p q:Program L1g.compile.Term),
    bigStepOpSemL1gTerm p q ->
    forall (q': Program Term),
      bigStepOpSemL2Term (certiL1g_to_L2 p) q' ->
              yesPreserved q q'.
Proof.
  intros. unfold yesPreserved. intros r. induction r.
  - unfold questionHead. destruct q, q', p.
    destruct QuestionHeadL1gTerm, QuestionHeadL2Term; try reflexivity.
    unfold bigStepOpSemL1gTerm, BigStepOpWEnv in H.
    unfold bigStepOpSemL2Term, BigStepOpWEnv in H0. cbn in *.
    destruct H, H0. rewrite H1 in *. rewrite H2 in *. subst.
    destruct main1, main0; cbn in *; try inversion H0.
    + subst.
    destruct main, main0; try reflexivity.  unfold BigStepOpWEnv in H. destruct H.
    
    destruct main, main0; cbn; try reflexivity; try destruct main1; try reflexivity.

  
***)

Global Instance certiL1g_to_L2Correct :
  CerticoqTranslationCorrect certiL1g certiL2.
Proof.
  split.
  - intros ? ?. cbn. unfold translateT, certiL1g_to_L2. trivial.
    (* The GoodTerm instance of L1g and L2 may need to be strengthened 
       to complete the next subgoal. Currently, they evaluete to True.
     *)
  - intros ? ?. 
    repeat progress (unfold bigStepEval, bigStepEvalSame,
                     liftBigStepException, bigStepOpSemL1gTerm,
                     translate, translateT, BigStepOpWEnv,
                     liftTotal, certiL2Eval, certiL1g_to_L2,
                     observeNthSubterm).
    cbn. intros. destruct H0. destruct s, sv. cbn in H1. subst env.
    cbn in H0. cbn. clear H. (* ?? *)
    exists (stripProgram {| main := main0; env := env0 |}).
    cbn. split. split. 
    + apply (proj1 (stripEvalCommute.WcbvEval_hom _) _ _ H0).
    + reflexivity.
    + constructor.
      * { unfold yesPreserved. intros. unfold stripProgram, implb.
          unfold questionHead, QuestionHeadL2Term, QuestionHeadL1gTerm.
          destruct q. cbn. destruct main0; cbn; try reflexivity.
          - destruct main0_1; cbn; try reflexivity.
            destruct (decide (i = i0)); cbn; try reflexivity.
            destruct (PeanoNat.Nat.eqb n n0); try reflexivity.
          - destruct (decide (i = i0)); cbn; try reflexivity.
            destruct (PeanoNat.Nat.eqb n n0); try reflexivity.
          - cbn. destruct main0; cbn; try reflexivity.
            destruct main0_1; try reflexivity. }
      * { intros. unfold observeNthSubterm.
          destruct (ObsSubtermL1gTerm n (@mkPgm L1g.compile.Term main0 env0));
            try constructor.
          destruct (ObsSubtermL2Term
                      n (stripProgram (@mkPgm L1g.compile.Term main0 env0))).
          - constructor. constructor.
            + unfold yesPreserved. intros. unfold questionHead.
              destruct q.
              * { destruct p, main1; try reflexivity.
                  - admit.
                  - admit. }
              * case_eq (QuestionHeadL1gTerm Abs p);
                case_eq (QuestionHeadL2Term Abs p0); intros; try reflexivity.
                admit.
            + intros. admit.
          - admit.
Admitted.


(***************              
                  ObsSubtermL2Term, ObsSubtermL1gTerm.
          destruct main0; cbn; try constructor.
          - destruct main0_1; cbn; try constructor.
            induction n; induction (L1g.compile.Terms_list t); cbn.
            + constructor. constructor. admit. admit.
            + constructor. constructor. admit. admit.
            + cbn. rewrite (proj2 (List.nth_error_None nil n)).
              admit. admit.
            + admit.
          - admit. }
Admitted.
******************)              


(***************************

    + unfold yesPreserved. intros. unfold stripProgram, implb.
      unfold questionHead, QuestionHeadL2Term, instances.QuestionHeadL2Term.
      destruct q. cbn. destruct main0; cbn; try reflexivity.
      * destruct main0_1; cbn; try reflexivity.
        destruct (decide (i = i0)); cbn; try reflexivity.
        destruct (PeanoNat.Nat.eqb n n0); try reflexivity.
      * destruct (decide (i = i0)); cbn; try reflexivity.
        destruct (PeanoNat.Nat.eqb n n0); try reflexivity.
      * cbn. destruct main0; cbn; try reflexivity.
        destruct main0_1; try reflexivity.
    + intros. unfold observeNthSubterm. 
      unfold ObsSubtermL2Term, instances.ObsSubtermL2Term.
      destruct main0; cbn; try constructor.
      * { destruct main0_1; cbn; try constructor.
          induction n; cbn.
          - constructor. constructor.
            + unfold yesPreserved. intros. induction q.
              destruct main0_2; cbn; try reflexivity.
              * destruct main0_2_1; cbn; try reflexivity.
                destruct (decide (i0 = i1)); cbn; try reflexivity.
                destruct (PeanoNat.Nat.eqb n n2); reflexivity.
              * destruct (decide (i0 = i1)); cbn; try reflexivity.
                destruct (PeanoNat.Nat.eqb n n2); reflexivity.
              * destruct main0_2; cbn; try reflexivity.
                destruct main0_2_1; cbn; try reflexivity.
            + intros. destruct main0_2; cbn; try constructor.
              * { destruct main0_2_1; cbn; try constructor.
                  destruct n; cbn.
                  - constructor. constructor.
                    + unfold yesPreserved. intros. destruct q.
                
                
              * destruct (decide (i0 = ind2)); cbn; try reflexivity.
              cbn.

      
      
    exists (stripProgram sv). cbn. repeat split.
    + apply (proj1 (stripEvalCommute.WcbvEval_hom (env s)) _ _ H0).
    + destruct s, sv. cbn in H1. rewrite H1. cbn. reflexivity.
    + admit.
    + intros. unfold observeNthSubterm,
              ObsSubtermL2Term, instances.ObsSubtermL2Term.
      destruct sv. cbn. unfold flattenApp, instances.flattenApp.
      destruct main; cbn; try constructor.
      * { destruct (L1g.term.isConstruct_dec main1) as [[x0 [x1 [x2 j]]] | j].
          - subst main1. cbn.
            destruct (List.nth_error (main2 :: L1g.compile.Terms_list t) n).
            + destruct
                (List.nth_error
                   (compile.strip main2 :: Terms_list (compile.strips t)) n).
              * constructor. constructor. unfold yesPreserved. intros.
                unfold implb. unfold questionHead.
                destruct (instances.QuestionHeadL2Term
                            q {| main := t0; env := env |}).
                destruct q. cbn. destruct t1; cbn. cbn in H0. cbn in H1.
                subst env.

                
                unfold instances.QuestionHeadL2Term.
                destruct (instances.QuestionHeadL2Term
                            q {| main := t0; env := env |}).
                destruct q. cbn.

                admit.
              * cbn in H0. rewrite H1 in H0. cbn in H0.
                rewrite j in H1. cbn in H1. subst env. subst main1.
Admitted.    
***************************)
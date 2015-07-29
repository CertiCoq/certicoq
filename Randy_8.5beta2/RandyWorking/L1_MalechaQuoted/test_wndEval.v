Add LoadPath "../common" as Common.
Add LoadPath "." as L1.
Require Import Template.Template.
Require Import Relations.Relation_Operators.
Require Import Common.RandyPrelude.
Require Import L1.L1.  (* whole L1 library is exported by L1.L1 *)

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.

(***  TESTING eval ***)
Ltac tran_step := eapply rt_trans; [eapply rt_step|].
Ltac dfn_unfold := unfold lookupDfn; simpl; try reflexivity.
Ltac const_step :=
  first [tran_step; [eapply sConst; dfn_unfold|] | eapply sConst; dfn_unfold].
Ltac main_step := simpl main; const_step.
(* unfolding *)
Ltac beta_unfold := unfold whBetaStep, instantiate; simpl.
Ltac fix_unfold := unfold whFixStep, instantiate; simpl.
Ltac case_unfold := unfold whCaseStep; simpl.
Ltac all_unfold := beta_unfold; fix_unfold; case_unfold.
(* contracting redexes *)
Ltac beta_step := first [tran_step; [eapply sBeta|] | eapply sBeta].
Ltac letIn_step := first [tran_step; [eapply sLetIn; beta_step|] |
                          eapply sLetIn; beta_step].
Ltac fix_step := first [tran_step; [eapply sFix; beta_step|] |
                          eapply sFix; beta_step].
(* congruences *)
Ltac appFn_step := all_unfold;
                first [tran_step; [eapply sAppFn|] | eapply sAppFn].
Ltac appArg_step := all_unfold;
                   (first [tran_step; [eapply sAppArg|] | eapply sAppArg]).
Ltac appArgs0_step := try tran_step; [eapply sAppArgs; eapply saHd |].
Ltac appArgs1_step := try tran_step; [eapply sAppArgs; eapply saTl |].
Ltac appArgs2_step :=
  try tran_step; [eapply sAppArgs; eapply saTl; eapply saTl |].
Ltac caseArg_step := first [tran_step; [eapply sCaseArg|] | eapply sCaseArg].
Ltac run := all_unfold;
           first [const_step|beta_step|letIn_step|fix_step|
                  appFn_step|appArg_step|caseArg_step].


Definition prog0 := Set.
Definition prog1 := list bool.
Definition prog2 := list (let x := bool in x).
Eval compute in prog1.
Eval compute in (list (let x := bool in x)).

Inductive dt : Set := DT : bool -> bool -> dt.
Definition fn := (let x:= DT true in x).
Eval compute in fn.
Quote Recursively Definition p_fn := fn.
Quote Definition q_fn := (DT true).
Lemma DTfn:
  match program_Program p_fn (Ret nil), term_Term q_fn with
    | Ret p, Ret q => wndEvalTC (env p) (main p) q
    | _, _ => True
  end.
simpl. eapply wETCtrn. apply wETCstep. eapply sConst. apply LHit.
 apply wETCstep. apply sLetIn. 
Qed.

Quote Recursively Definition p_appl := (fn true).
Quote Definition q_appl := (DT true true).
Goal 
  match program_Program p_appl (Ret nil), term_Term q_appl with
    | Ret p, Ret q => wndEvalTC (env p) (main p) q
    | _, _ => True
  end.
simpl. eapply wETCtrn. apply wETCstep. apply sAppFn.
eapply sConst. apply LHit. unfold mkApp.
eapply wETCtrn. apply wETCstep. apply sAppFn. apply sLetIn.
unfold instantiate. unfold Compare_dec.nat_compare.
rewrite mkApp_idempotent. unfold mkApp. unfold tappend.
 apply wETCstep. 

Quote Definition q_appl := (DT true true true).

Goal 
  match program_Program p_appl (Ret nil), term_Term q_appl with
    | Ret p, Ret q => clos_refl_trans _ (wndEval (env p)) (main p) q
    | _, _ => True
  end.
simpl. tran_step. eapply sAppFn. eapply sLetIn.
 unfold instantiate, Compare_dec.nat_compare.
rewrite mkApp_idempotent. rewrite mkApp_idempotent.
unfold mkApp. unfold tappend.
tran_step. eapply sAppFn. eapply sLetIn.
 unfold instantiate, Compare_dec.nat_compare.
rewrite mkApp_idempotent. unfold mkApp. unfold tappend.




(***  Coq raises "anomaly" error *)
CoInductive Stream : Set :=
  Seq : nat -> Stream -> Stream.
CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).
(* Quote Recursively Definition From := from. Coq raises "anomaly" error *) 


(** destructing a parameterised datatype **)
Inductive nelst (A:Set) : Set := 
| nenl: A -> nelst A
| necns: A -> nelst A -> nelst A.
Definition nehd (A:Set) (ls:nelst A) : A :=
  match ls with
    | nenl a => a
    | necns a _ => a
  end.
Quote Recursively Definition p_nehd :=
  (@nehd bool (@necns bool true (@nenl bool false))). Print p_nehd.
Quote Definition q_nehd :=
  Eval compute in (@nehd bool (@necns bool true (@nenl bool false))).
Goal 
let p := program_Program p_nehd nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_nehd).
simpl. appFn_step. const_step. apply lConstrHit. 
beta_step. beta_unfold. beta_step. beta_unfold.
tran_step. eapply sCasen. unfold whCaseStep. unfold tnth.
unfold tskipn. unfold mkApp. (* here is where the parameter is skipped *)
reflexivity.
beta_step. beta_unfold. beta_step. beta_unfold.
eapply rt_refl.
Qed.

Inductive ne_lst: Set -> Type := 
| ne_nl: forall (A:Set), A -> ne_lst A
| ne_cns: forall (A:Set), A -> ne_lst A -> ne_lst A.
Definition ne_hd (A:Set) (ls:ne_lst A) : A :=
  match ls with
    | ne_nl A a => a
    | ne_cns A a _ => a
  end.
Quote Recursively Definition p_ne_hd :=
  (@ne_hd bool (@ne_cns bool true (@ne_nl bool false))). Print p_ne_hd.
Quote Definition q_ne_hd :=
  Eval compute in (@ne_hd bool (@ne_cns bool true (@ne_nl bool false))).
Goal 
let p := program_Program p_ne_hd nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_ne_hd).
simpl. appFn_step. const_step. apply lConstrHit. 
beta_step. beta_unfold. beta_step. beta_unfold.
tran_step. eapply sCasen. unfold whCaseStep. unfold tnth.
unfold tskipn. unfold mkApp. (* here is where the parameter is skipped *)
reflexivity.
beta_step. beta_unfold. beta_step. beta_unfold. beta_step. beta_unfold.
eapply rt_refl.
Qed.

Inductive lst (A:Set) : Set := 
| nl: lst A
| cns: A -> lst A -> lst A.
Definition hd (A:Set) (ls:lst A) (default:A) : A :=
  match ls with
    | nl => default
    | cns a _ => a
  end.
Quote Recursively Definition p_hd := (hd bool (cns bool true (nl bool)) false).
Quote Definition q_hd :=
  Eval compute in (hd bool (cns bool true (nl bool)) false).
Goal 
let p := program_Program p_hd nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_hd).
simpl. appFn_step. const_step. apply lConstrHit. 
beta_step. beta_unfold. beta_step. beta_unfold.
beta_step. beta_unfold.
tran_step. eapply sCasen. reflexivity.
beta_step. beta_unfold. beta_step. beta_unfold.
eapply rt_refl.
Qed.


Inductive tm (A:Set) : Set := 
| vv: nat -> tm A 
| cc: A -> tm A.
Definition occIn (A:Set) (t:tm A) : nat :=
  match t with
    | vv m => m
    | cc _ => 0
end.
Quote Recursively Definition p_occIn := (occIn bool (cc bool true)).
Quote Definition q_occIn := Eval compute in (occIn bool (cc bool true)).
Print q_occIn.
Goal 
let p := program_Program p_occIn nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_occIn).
simpl main. simpl. appFn_step. const_step. apply lConstrHit. 
beta_step. beta_unfold. beta_step. beta_unfold.
tran_step. eapply sCasen. (* look here *) case_unfold. reflexivity.
beta_step. beta_unfold.
eapply rt_refl.
Qed.


Definition paramCase (n m l:nat) (f:nat->nat) : nat :=
  match n with
    | 0 => f m
    | S _ => f l
end.
Quote Recursively Definition p_paramCase := paramCase.
Print p_paramCase.

(***
Require Import Vectors.Vector.
Print Fin.t.
Print Vector.t.
Open Scope vector_scope.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n :=
  Eval cbv delta beta in (map2 plus).
Print vplus.

Definition vplus01 :=
  (vplus 1 (cons nat 0 0 (Vector.nil nat)) (cons nat 1 0 (Vector.nil nat))).
Quote Recursively Definition p_vplus01 := vplus01.
Quote Definition q_vplus01 := Eval compute in vplus01.
Print q_vplus01.
Goal 
  let p := program_Program p_vplus01 List.nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_vplus01).
simpl main. const_step. apply lConstrHit. appFn_step. const_step.
beta_step. beta_unfold.
beta_step. beta_unfold.
beta_step. beta_unfold.
fix_step. fix_unfold.
beta_step. beta_unfold.
beta_step. beta_unfold.
appFn_step. eapply sCasen.
appFn_step. beta_step. beta_unfold.
appFn_step. beta_step. beta_unfold.
appFn_step. beta_step. beta_unfold.
beta_step. beta_unfold.
appFn_step. eapply sCasen.
appFn_step. beta_step. beta_unfold.
appFn_step. beta_step. beta_unfold.
appFn_step. beta_step. beta_unfold.
beta_step. beta_unfold.
appArgs0_step. fix_step. fix_unfold.
appArgs0_step. beta_step. beta_unfold.
appArgs0_step. beta_step. beta_unfold.
appArgs0_step. eapply sCase0. case_unfold.
appArgs2_step. eapply saHd. fix_step. fix_unfold.
appArgs2_step. eapply saHd. beta_step. beta_unfold.
appArgs2_step. eapply saHd. beta_step. beta_unfold.
appArgs2_step. eapply saHd. appFn_step. eapply sCasen. case_unfold.
appArgs2_step. eapply saHd. beta_step. beta_unfold.
appArgs2_step. eapply saHd. eapply sCasen. case_unfold.
eapply rt_refl. 
Qed.



***)

Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Recursively Definition p_typedef := typedef.
Quote Definition q_typedef := Eval compute in typedef.
Goal 
  let p := program_Program p_typedef nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_typedef).
simpl main. const_step. apply lConstrHit. beta_step. all_unfold. beta_step.
eapply rt_refl. 
Qed.

Definition constructor := (fun (A:Type) (s:A -> A) => s) Nat S.
Quote Recursively Definition p_constructor := constructor.
Quote Definition q_constructor := Eval compute in constructor.
Goal
  let p := program_Program p_constructor nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_constructor).
simpl main. const_step. apply lConstrHit. beta_step. all_unfold.
beta_step. eapply rt_refl.
Qed.

Eval lazy in (S (1+1)).  (** = 3, not really lazy **)
Eval hnf in (S (1+1)).  (** = S (1+1) **)
Eval lazy in (let x := 1 + 1 in x).  (** = 2, not really lazy **)
Eval hnf in (let x := 1 + 1 in x).  (** = S (0+1) **)

Definition Let' := let a := 2 in (plus 1 a).
Quote Recursively Definition p_Let := Let'.
Quote Definition q_Let := Eval compute in Let'.
Goal 
  let p := program_Program p_Let nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_Let).
simpl main. const_step. apply lConstrHit.
letIn_step. all_unfold. appFn_step. const_step. 
apply lConstrMiss. admit. apply lConstrHit. tran_step. eapply sFix.
all_unfold. reflexivity.
beta_step. beta_step. all_unfold. tran_step. eapply sCasen. all_unfold.
reflexivity.
beta_step. all_unfold. appArg_step. apply sFix. all_unfold. reflexivity.
appArg_step. beta_step. appArg_step. beta_step. appArg_step. 
eapply sCase0. all_unfold. reflexivity.
eapply rt_refl.
Qed.


Definition anon := (fun (_:nat) => 1 + 3) (3 * 3).
Quote Recursively Definition p_anon := anon.
Quote Definition q_anon := Eval compute in anon.
Goal 
  let p := program_Program p_anon nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_anon).
simpl main. const_step. apply lConstrHit.
beta_step. all_unfold. appFn_step. const_step. 
apply lConstrMiss. admit. apply lConstrMiss. admit. apply lConstrHit.
 tran_step. eapply sFix. all_unfold. reflexivity.
beta_step. beta_step. all_unfold.
tran_step. eapply sCasen. all_unfold. reflexivity.
beta_step. appArg_step. eapply sFix. all_unfold. reflexivity.
appArg_step. beta_step. all_unfold.
appArg_step. beta_step. appArg_step. eapply sCase0. all_unfold. reflexivity.
eapply rt_refl.
Qed.

(**** 
Parameter axiom:nat.
Quote Recursively Definition p_axiom := (let x := axiom in 2 * x).
Print p_axiom.
(** axiom becomes match term of a Case statement, and cannot be 
*** made Canonical, blocking evaluation  **)
Goal clos_refl_trans _ (wndEval p_axiom) (main p_axiom) q_ans.
unfold main; simpl.
tran_step. eapply sLetIn. simpl instantiate.
   eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sAppFn. eapply sConst. unfold lookupDfn. simpl.
tran_step. eapply sFix. unfold whFixStep. simpl.
tran_step. eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sCase. eapply canA. unfold whCaseStep. simpl.
tran_step. eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sAppFn. eapply sConst. unfold lookupDfn. simpl.
tran_step. eapply sFix. unfold whFixStep. simpl.
tran_step. eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sBeta. unfold instantiate. simpl.
tran_step. eapply sCase. 
Abort.
****)

(* redex in type field of a Fixpoint *)
Fixpoint testFix1_1 (n:(@id Set nat)) : (@id Set nat) :=
  match n with
    | 0 => (@id nat n : @id Set nat)
    | S m => m
  end.
Quote Recursively Definition x_testFix1_1 := testFix1_1.
Print x_testFix1_1.


(* testing instantiation in Case and Fix branches *)
Section FN.
Inductive fnat : Set := SS: fnat -> fnat | OO.
Variable nn:fnat.
Definition ftestCase (n:fnat) : fnat :=
  match n with
    | OO => nn
    | SS m => m
end.
End FN.
Quote Recursively Definition p_ftestCase := (ftestCase (SS OO) OO) .
Quote Definition q_ftestCase:= Eval compute in (ftestCase (SS OO) OO) .
Print q_ftestCase.
Print p_ftestCase.
Goal 
let p := program_Program p_ftestCase nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_ftestCase).
simpl. appFn_step. const_step. apply lConstrHit. beta_step. beta_unfold.
beta_step. beta_unfold.
tran_step. eapply sCase0. all_unfold. reflexivity.
eapply rt_refl.
Qed.



Section NN.
Variable nn:nat.
Definition testCase (n:nat) : nat :=
  match n with
    | 0 => nn
    | S m => m
end.
Fixpoint testFix (n:nat) : nat :=
  match n with
    | 0 => nn
    | S m => testFix m
end.
Fixpoint testFix1 (n:nat) : nat :=
  match n with
    | 0 => nn
    | S m => m
end.
End NN.

Quote Recursively Definition p_testCase := (testCase 1 0) .
Quote Definition q_testCase:= Eval compute in (testCase 1 0) .
Print q_testCase.
Print p_testCase.
Goal 
let p := program_Program p_testCase nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_testCase).
simpl. appFn_step. const_step. beta_step. beta_unfold.
beta_step. beta_unfold.
tran_step. eapply sCase0. 
eapply rt_refl.
Qed.

Quote Recursively Definition p_testCase' := (testCase 0 1) .
Quote Definition q_testCase':= Eval compute in (testCase 0 1) .
Print q_testCase'.
Print p_testCase'.
Goal 
let p := program_Program p_testCase' nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_testCase').
simpl. appFn_step. const_step. beta_step. beta_unfold.
beta_step. beta_unfold.
tran_step. eapply sCasen. all_unfold.
beta_step. beta_unfold.
eapply rt_refl.
Qed.

Quote Definition x_testFix := Eval compute in testFix.
Print x_testFix.
Quote Definition x_testFix1 := Eval compute in testFix1.
Print x_testFix1.

Quote Recursively Definition p_testFix := (testFix 1 1) .
Quote Definition q_testFix:= Eval compute in (testFix 1 1) .
Goal 
let p := program_Program p_testFix nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_testFix).
simpl. appFn_step. const_step. 
beta_step. all_unfold.
fix_step. beta_step. all_unfold. tran_step. eapply sCasen.
beta_step. all_unfold. fix_step. beta_step. all_unfold.
tran_step. eapply sCase0. 
eapply rt_refl.
Qed.

Quote Recursively Definition p_testFix1 := (testFix1 1 1) .
Quote Definition q_testFix1:= Eval compute in (testFix1 1 1) .
Goal 
let p := program_Program p_testFix1 nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_testFix1).
simpl. appFn_step. const_step.
beta_step. all_unfold.
fix_step. beta_step. all_unfold.  tran_step. eapply sCasen.
beta_step; all_unfold. 
eapply rt_refl.
Qed.

Fixpoint testFix2 (nn n:nat) : nat :=
  match n with
    | 0 => nn
    | S m => testFix2 nn m
end.
Quote Definition x_testFix2 := Eval compute in testFix2.
Print x_testFix2.
Quote Recursively Definition p_testFix2 := (testFix2 1 1) .
Quote Definition q_testFix2 := Eval compute in (testFix2 1 1) .
Goal 
let p := program_Program p_testFix2 nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_testFix2).
simpl. appFn_step. const_step. fix_step.
beta_step. all_unfold.
beta_step. all_unfold.
tran_step. eapply sCasen.
beta_step. all_unfold.
fix_step. beta_step. all_unfold. beta_step. all_unfold.
tran_step. eapply sCase0.
eapply rt_refl.
Qed.


Definition plus22 := (plus 2 2).
Quote Recursively Definition p_plus22 := plus22.
Quote Definition q_plus22 := Eval compute in plus22.
Goal 
let p := program_Program p_plus22 nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_plus22).
simpl main. const_step.
appFn_step. const_step. fix_step. beta_step. 
beta_step. all_unfold. tran_step. eapply sCasen. all_unfold.
beta_step. all_unfold.
appArg_step. fix_step. all_unfold. 
appArg_step. beta_step. all_unfold. appArg_step.
beta_step. all_unfold. appArg_step. 
eapply sCasen. all_unfold.
appArg_step. beta_step. all_unfold.
appArg_step. appArg_step. fix_step. appArg_step.  appArg_step. beta_step.
appArg_step. appArg_step. beta_step. beta_unfold.  appArg_step. appArg_step.
eapply sCase0. all_unfold.
eapply rt_refl.
Qed.

(**
Quote Recursively Definition p_fst01 := (fst (0, 1)).
Quote Recursively Definition p_snd01 := (snd (0, 1)).
Print p_fst01.
Quote Definition zero_syntax := 0.
Goal clos_refl_trans _ (wndEval p_fst01) (main p_fst01) zero_syntax.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
eapply rt_refl.
Qed.

Local Open Scope bool.
Local Open Scope list.

Fixpoint evenP (n m:nat) {struct m} : bool :=
  match m with
    | 0 => true
    | S p => (oddP p) || (evenP n p)
  end
with oddP (n:nat) : bool :=
  match n with
    | 0 => false
    | S p => evenP 0 p
  end.

Quote Recursively Definition p_evenP := (evenP 2 1).
Eval compute in (evenP 2 1).
Print p_evenP.
Quote Definition q_true := true.
Quote Definition q_false := false.

Goal clos_refl_trans _ (wndEval p_evenP) (main p_evenP) q_true.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
unfold q_true. eapply rt_refl.
Qed.
***)

(** Case **)
Inductive xxyy: Set := xx | yy.
Definition simplCase : xxyy -> bool :=
  fun xy:xxyy => 
    match xy with
      | xx => true
      | yy => false
    end.
Quote Recursively Definition p_simplCase := (simplCase yy).
Print p_simplCase.
Quote Definition q_simplCase := Eval compute in (simplCase yy).
Print q_simplCase.
Goal  
  let p := program_Program p_simplCase nil
  in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_simplCase).
simpl main. appFn_step. const_step. beta_step. beta_unfold. 
tran_step. eapply sCase0. all_unfold.
eapply rt_refl.
Qed.

(** mutual recursion over mutual inductive defns **)
Inductive even : nat -> Prop :=
| eZ: even 0
| eSO: forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| oSE: forall n, odd ( n).

Inductive tree : Set :=
  node : nat -> forest -> tree
with forest : Set :=
     | leaf : bool -> forest
     | fcons : tree -> forest -> forest.

Fixpoint tree_size (t:tree) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition sherwood:forest := fcons (node 1 (leaf true)) (leaf false).
Quote Recursively Definition p_forest_size := (forest_size sherwood).
Quote Definition q_forest_size := Eval compute in (forest_size sherwood).
Print p_forest_size.
Goal 
let p := program_Program p_forest_size nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_forest_size).
simpl main. appFn_step. const_step.
fix_step. beta_step. beta_unfold. caseArg_step. const_step. case_step. 
beta_step. beta_unfold. beta_step. beta_unfold. appFn_step. const_step.
fix_step. beta_step. beta_unfold. beta_step. beta_unfold. caseArg_step.  
fix_step. all_unfold. caseArg_step. beta_step. all_unfold. caseArg_step. 
case_step. all_unfold. caseArg_step. beta_step. all_unfold. caseArg_step.
beta_step. all_unfold. caseArg_step. appArg_step. fix_step. all_unfold.
caseArg_step. appArg_step. beta_step. all_unfold.
caseArg_step. appArg_step. case_step. all_unfold.
caseArg_step. appArg_step. beta_step. all_unfold.
case_step. beta_step. all_unfold.
appArg_step. fix_step. all_unfold.
 appArg_step. beta_step. all_unfold.
 appArg_step. beta_step. all_unfold.
 appArg_step. case_step. all_unfold.
 appArg_step. beta_step. all_unfold. 
appArg_step. appArg_step. fix_step. all_unfold.
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  case_step. all_unfold. 
appArg_step. appArg_step. fix_step. all_unfold.
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  case_step. all_unfold. 
appArg_step. appArg_step.  beta_step. all_unfold. 
eapply rt_refl.
Qed.

(*** instantiate in a branch of a mutual fixpoint ***)
Section S1.
Variable nn:nat.
Fixpoint tree_size1 (t:tree) : nat :=
  match t with
    | node a f => S (forest_size1 f)
  end
with forest_size1 (f:forest) : nat :=
       match f with
         | leaf b => nn
         | fcons t f1 => (tree_size1 t + forest_size1 f1)
       end.
End S1.
Quote Definition x_tree_size1 := Eval compute in tree_size1.
Print x_tree_size1.

Quote Recursively Definition p_forest_size1 := (forest_size1 1 sherwood).
Quote Definition q_forest_size1 := Eval compute in (forest_size1 1 sherwood).
Goal 
let p := program_Program p_forest_size1 nil
in clos_refl_trans _ (wndEval (env p)) (main p) (term_Term q_forest_size1).
simpl main. appFn_step. const_step. beta_step. beta_unfold.
fix_step. beta_step. beta_unfold. caseArg_step. const_step. case_step. 
beta_step. beta_unfold. beta_step. beta_unfold. appFn_step. const_step.
fix_step. beta_step. beta_unfold. beta_step. beta_unfold. caseArg_step.  
fix_step. all_unfold. caseArg_step. beta_step. all_unfold. caseArg_step. 
case_step. all_unfold. caseArg_step. beta_step. all_unfold. caseArg_step.
beta_step. all_unfold. caseArg_step. appArg_step. fix_step. all_unfold.
caseArg_step. appArg_step. beta_step. all_unfold.
caseArg_step. appArg_step. case_step. all_unfold.
caseArg_step. appArg_step. beta_step. all_unfold.
case_step. beta_step. all_unfold.
appArg_step. fix_step. all_unfold.
 appArg_step. beta_step. all_unfold.
 appArg_step. beta_step. all_unfold.
 appArg_step. case_step. all_unfold.
 appArg_step. beta_step. all_unfold. 
appArg_step. appArg_step. fix_step. all_unfold.
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  case_step. all_unfold. 
appArg_step. appArg_step. fix_step. all_unfold.
appArg_step. appArg_step.  beta_step. all_unfold. 
appArg_step. appArg_step.  case_step. all_unfold. 
appArg_step. appArg_step.  beta_step. all_unfold. 
eapply rt_refl.
Qed.





(***

Inductive wwzz: Set := ww (_:xxyy)| zz (_:nat) (_:xxyy) (_:bool).
Definition foo : nat -> bool -> wwzz -> wwzz := 
  fun (n:nat) (b:bool) (x:wwzz) =>
    match n,x,b with
      | 0, _, true => ww xx
      | 0, _, false => ww yy
      | S m, ww x, b => zz m x b
      | S m, zz n x b1, b => zz m x b
    end.
Quote Definition q_foo := Eval cbv delta[foo] in foo.
Print q_foo.
Quote Recursively Definition q_foop := foo.
Print q_foop.
Eval compute in (foo 0 true (ww xx)).
Quote Definition q_foo0ty := (foo 0 true (ww xx)).
Print q_foo0ty.
Definition fooSfy := (foo 1 true (zz 0 yy false)).
Eval compute in fooSfy.
Quote Definition q_fooSfy := (foo 1 true (zz 0 yy false)).
Print q_fooSfy.
Quote Definition q_wwxx := Eval compute in (ww xx).
Print q_wwxx.
Quote Definition q_wwyy := Eval compute in (ww yy).
Print q_wwyy.
Quote Definition q_zzS := (zz 0 yy true).
Print q_zzS.

Goal clos_refl_trans _ (wndEval q_foop) q_foo0ty q_wwxx.
unfold q_foo0ty, q_wwxx. eapply rt_trans. eapply rt_step. apply sAppFn. eapply sConst. simpl lookupDfn.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. eapply canC. unfold whCaseStep. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. eapply canC.
unfold whCaseStep. simpl. eapply rt_refl.
Qed.

Goal clos_refl_trans _ (wndEval q_foop) q_fooSfy q_zzS.
unfold q_fooSfy. eapply rt_trans.
eapply rt_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. eapply canA. unfold whCaseStep. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. eapply canA. unfold whCaseStep. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta. unfold instantiate. simpl.
unfold q_zzS. eapply rt_refl.
Qed.


(** fixpoint **)
Fixpoint bar (n p:nat) {struct n} :=
  match n with
    | S (S m) => bar m 0
    | S m => bar m 0
    | 0 => p
  end.
Quote Definition q_bar := Eval compute in bar.
Print q_bar.
Quote Recursively Definition q_barp := (bar 1 0).
Print q_barp.
Quote Definition q_zero := 0.

Goal clos_refl_trans _ (wndEval q_barp) (main q_barp) q_zero.
unfold main. simpl. 
eapply rt_trans. eapply rt_step. eapply sAppFn. eapply sConst.
unfold lookupDfn. simpl.
eapply rt_trans. eapply rt_step. eapply sFix. unfold whFixStep. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta.
unfold instantiate, mkApp. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta.
unfold instantiate, mkApp. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. apply canA.
unfold whCaseStep. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta.
unfold instantiate, mkApp. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. apply canC.
unfold whCaseStep. simpl.
eapply rt_trans. eapply rt_step. eapply sFix. unfold whFixStep. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta.
unfold instantiate, mkApp. simpl.
eapply rt_trans. eapply rt_step. eapply sBeta.
unfold instantiate, mkApp. simpl.
eapply rt_trans. eapply rt_step. eapply sCase. apply canC.
unfold whFixStep. simpl. unfold q_zero. eapply rt_refl.
Qed.



(*** tests ***)
(** delta and beta reduction **)
Definition II := fun (A:Type) (a:A) => a.
Quote Definition II_2_term := (II nat 2).
Print II_2_term.
Quote Recursively Definition II_2_program := (II nat 2).
Print II_2_program.
Quote Definition two_term := 2.

Goal clos_trans _ (wndEval II_2_program) (main II_2_program) two_term.
eapply t_trans.
- eapply t_step. eapply sAppFn. eapply sConst.
- simpl lookupDfn. eapply t_trans. 
  + eapply t_step. eapply sBeta.
  + unfold instantiate, mkApp. simpl. eapply t_step. eapply sBeta.
Qed.

Definition test := fun (n m:nat) => (m, n).
Quote Recursively Definition test_program := (test 1 0).
Print test_program.
Quote Definition test_ans := (0, 1).
Goal clos_trans _ (wndEval test_program) (main test_program) test_ans.
eapply t_trans. simpl main.
- eapply t_step. eapply sAppFn. eapply sConst.
- simpl lookupDfn. eapply t_trans.
  + eapply t_step. eapply sBeta.
  + simpl instantiate. simpl mkApp.
    * eapply t_step. eapply sBeta.
Qed.


Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Eval compute in (slowFib 0).
Eval compute in (slowFib 1).
Eval compute in (slowFib 2).
Eval compute in (slowFib 3).
Eval compute in (slowFib 4).
Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Definition one_syntax := 1.
Quote Recursively Definition p_slowFib2 := (slowFib 2).

Lemma slowFib1:
  clos_refl_trans _ (wndEval p_slowFib1) (main p_slowFib1) one_syntax.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
eapply rt_refl.
Qed.

Goal clos_refl_trans _ (wndEval p_slowFib2) (main p_slowFib2) one_syntax.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
eapply rt_refl.
Qed.


Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Eval compute in (fib 0).
Eval compute in (fib 1).
Eval compute in (fib 2).
Eval compute in (fib 3).
Eval compute in (fib 4).
Quote Recursively Definition p_fib0 := (fib 0).
Quote Recursively Definition p_fib1 := (fib 1).

Goal clos_refl_trans _ (wndEval p_fib0) (main p_fib0) zero_syntax.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
eapply rt_refl.
Qed.



Goal clos_refl_trans _ (wndEval p_fib1) (main p_fib1) one_syntax.
unfold main. simpl.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sFix. unfold whFixStep; simpl.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg.
 eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCaseArg. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canC. simpl whCaseStep.
tran_step. eapply sAppFn. eapply sConst. simpl lookupDfn.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sCase. eapply canA. simpl whCaseStep.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
tran_step. eapply sBeta. simpl instantiate. simpl mkApp.
eapply rt_refl.
Qed.

***)
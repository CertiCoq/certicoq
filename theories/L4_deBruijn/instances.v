Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L3.compile.
Require Import L4.L3_to_L4.
Require Import L3.instances.

Require Import BinNat.

Definition dummyEnvBigStep {E T: Type}  (bt : BigStepOpSem T)
: BigStepOpSem (E * T) :=
  (fun e v => (fst e) = (fst v) /\ (snd e) ⇓ (snd v)).

Definition dummyEnvWf {E T: Type}  (bt : GoodTerm T)
: GoodTerm (E * T) :=
  (fun e => goodTerm (snd e)).

(* very low priority *)
Existing Instance dummyEnvBigStep | 1000000.
(* very low priority *)
Existing Instance dummyEnvWf | 1000000.

Let L4Term := prod ienv  L4.expression.exp.

Instance certiL4eval : BigStepOpSem L4.expression.exp := eval.


Instance certiL4wf: GoodTerm L4.expression.exp :=
 L4.expression.exp_wf (0%N).


Global Instance certiL4: CerticoqLanguage (ienv * L4.expression.exp) := {}.

Global  Instance certiL3_to_L4: 
  CerticoqTranslation (cTerm certiL3) (cTerm certiL4)  :=
fun p => Ret ( L4.L3_to_L4.inductive_env (AstCommon.env p),
   (L3_to_L4.translate_program (AstCommon.env p) (main p))).

Global  Instance failed: 
  CerticoqTranslationCorrect (Program L3.compile.Term) L4Term.
constructor.
Focus 2.
- intros ? ? Hwf He.
  destruct Hwf.
  unfold certiClasses.translate,
    certiL3_to_L4, liftBigStepException, bigStepEval.
  unfold translate_program.
(*  Fail eapply L3_to_L4_correct.translate_correct.  *)
(* not applicable!! do we need to change the end to end correctness property?, 
  or can the L3_to_L4 translation syntactically preserve big step eval? *)
Abort.

Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_2_to_L4_5.


Global  Program Instance : BigStepOpSem L4_5_Term := eval.

(** all variables must be user variables *)
Global Program Instance : GoodTerm L4_5_Term :=
  fun e  => varsOfClass (all_vars e) true /\ isprogram e.

Global Instance certiL4_5: CerticoqLanguage (prod ienv L4_5_Term) := {}.


Global Instance certiL4_to_L4_5: 
  CerticoqTotalTranslation (cTerm certiL4) (cTerm certiL4_5) :=
  fun p => (fst p, (L4_2_to_L4_5 (tL4_to_L4_2 (snd p))) ).

Require Import L4.variables.

Definition L5Term :Type := (@NTerm NVar L5Opid).

Global Program Instance : BigStepOpSem L5Term := eval_c.

Global Program Instance : GoodTerm L5Term := isprogram.

Global Instance certiL5: CerticoqLanguage (ienv * L5Term) := {}.

Global Instance certiL4_5_to_L5:
  CerticoqTotalTranslation (cTerm certiL4_5) (cTerm certiL5):=
  (fun x => (fst x,  (cps_cvt (snd x)))).

Require Import L4.L5a.

(* Fix. Define subst and evaluation on L5a by going to L5 via a bijection? *)
Global Program Instance : BigStepOpSem L4.L5a.val_c := fun _ _ => True.

(** Fix *)
Global Program Instance : GoodTerm L4.L5a.val_c := fun x => False.

Global Instance certiL5a: CerticoqLanguage (ienv * L4.L5a.val_c) := {}.

Global Instance certiL5_to_L5a: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL5a)  :=
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


(***
Eval vm_compute in (exception_map print4 (ctranslateTo certiL4_2 p0L1)).
Eval vm_compute in (exception_map print5 (ctranslateTo certiL5 p0L1)).
Eval vm_compute in ( (ctranslateTo certiL5 p0L1)).

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


  










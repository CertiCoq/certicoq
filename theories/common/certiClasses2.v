Require Import Common.exceptionMonad.
Require Import Common.certiClasses.
Require Import Coq.Unicode.Utf8.
Require Import List.
Generalizable Variables Src Dst Inter Term Value SrcValue DstValue InterValue.

(* Some values, e.g. constructors, can have subterms.
   This operation allows asking for the nth subterm.
   When trying to observe the nth subterm of a value having only m (m<n)
   subterms, all bets are off about the returned value.
*)
Class ObserveNthSubterm (Value:Type) :=
  observeNthSubterm: nat -> Value -> option Value.

Section YesNoQuestions.

(* Zoe's suggestion for Question *)
Inductive Question : Set  := 
| Cnstr : Ast.inductive -> nat -> Question 
| Abs : Question.


(** Given a value of a language, we can observe it by asking it yes/no
questions. 
 [Cnstr i n] represents the question "Are you the nth constructor
      of the inductive i?".
 [Abs] represents the question "Are you an abstraction
    (do you represent a lambda or fixpoint)?".
A value can respond "yes" to many such questions.
Thus, the compiler is allowed to to use the same representation for
different types.

Regarding Erasure:
If a value [v] has sort Prop, then in L1g, 
  [questionHead _ v is] supposed to be false.
We can then do whatever we want with such values.
Another choice is that if a value [v] is a constructor 
(and not, e.g., a lambda or fix) of sort Prop, then in L1g, 
[questionHead _ v is] supposed to be false.

After erasure,
  [questionHead (Cnstr _ _) \box] is false
  [questionHead Abs \box] is true.
Note that \box eventually becomes a fixpoint.
*)
Class QuestionHead (Value:Type) := questionHead: Question -> Value -> bool.

(** A value in the destination should say "yes" to all the questions
   to which the corresponding source value said "yes"
**)
Definition yesPreserved
           `{QuestionHead SrcValue} `{QuestionHead DstValue}
           (s: SrcValue) (d: DstValue) :=
  forall (q:Question), implb (questionHead q s) (questionHead q d) = true.


Section ObsLe.

(* Typically, Src=SrcValue *)
Context `{QuestionHead SrcValue} `{ObserveNthSubterm SrcValue} 
   `{QuestionHead DstValue} `{ObserveNthSubterm DstValue}.

(* obsLe extends yesPreserved to corresponding subterms *)   
(* Coinductive, in case we add support for Coq's coinductive types later on.
Currently, [Inductive] should suffice 
*)
CoInductive obsLe : SrcValue -> DstValue -> Prop :=
| sameObs : forall (s : SrcValue) (d : DstValue),
    yesPreserved s d
    -> (forall n:nat, obsLeOp (observeNthSubterm n s) (observeNthSubterm n d))
    -> obsLe s d
with obsLeOp : option SrcValue -> option DstValue -> Prop :=
(* defining this using pattern matching confuses the strict positivity checker.
  Can this part be defined outside generically, using induction? *)
| obsSome: forall s d, obsLe s d -> obsLeOp (Some s) (Some d)
| obsNone: forall d, obsLeOp None d.

End ObsLe.

Notation "s ⊑ t" := (obsLe s t) (at level 65).


Class CerticoqLanguage (Term Value:Type)
  `{BigStepOpSem Term Value} `{GoodTerm Term} 
   `{QuestionHead Value} `{ObserveNthSubterm Value} 
:= 
{
  (* Sensible, but not needed yet.
  goodPreserved : forall (s v : Term), 
    goodTerm s
    -> s ⇓ v
    -> goodTerm v
  *)
}.



Global Arguments CerticoqLanguage Term Value {H} {H0} {H1} {H2}.

(* The final correctness property is just the conjunction of goodPreserving and obsPreserving.
The lemma [composeCerticoqTranslationCorrect] below
shows that composes correctness proofs of adjacent translations. *)
Class CerticoqTranslationCorrect
  `{CerticoqLanguage Src SrcValue} 
  `{CerticoqLanguage Dst DstValue}
  `{CerticoqTranslation Src Dst} := 
{
  certiGoodPres2 : goodPreserving Src Dst;
  obsePres : obsPreserving Src Dst obsLe;
}.

Global Arguments CerticoqTranslationCorrect
  {Src} {SrcValue} {H} {H0} {H1} {H2} H3 {Dst} {DstValue} {H4} {H5} {H6} {H7} H8 {H9}.

Lemma obsLeTrns
   `{QuestionHead SrcValue} `{ObserveNthSubterm SrcValue} 
   `{QuestionHead InterValue} `{ObserveNthSubterm InterValue} 
   `{QuestionHead DstValue} `{ObserveNthSubterm DstValue} :
   forall   (s : SrcValue) (i : InterValue) (d : DstValue),
  s ⊑ i
  -> i ⊑ d 
  -> s ⊑ d.
Proof.
  (************
  induction 1. intros.
  constructor.  Set Printing All.
  - unfold yesPreserved. intros.
    unfold yesPreserved in H5. specialize (H5 q).
    inversion H7. subst.   
    unfold yesPreserved in H8. specialize (H8 q).
    inversion H7. subst.
    unfold yesPreserved in H10. specialize (H10 q).
    unfold implb in *.
**********)
  cofix.
  intros ? ? ? Ha Hb.
  inversion Ha as [ss is Hah Has]. subst. clear Ha.
  inversion Hb as [is ds Hbh Hbs]. subst. clear Hb.
  constructor; auto.
- unfold yesPreserved in *. intros q.
  specialize (Hah q).
  specialize (Hbh q).
  destruct (questionHead q s); simpl in *;[| reflexivity]. 
  rewrite Hah in Hbh. assumption.
- clear Hah Hbh. intros n.
  specialize (Has n).
  specialize (Hbs n).
  destruct Has;[| constructor ].
  inversion Hbs. subst. clear Hbs.
  constructor. eauto.
Qed.

Global Instance composeCerticoqTranslationCorrect
  `{Ls: CerticoqLanguage Src SrcValue}
  `{Li: CerticoqLanguage Inter InterValue}
  `{Ld: CerticoqLanguage Dst DstValue}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
(* we don't need a translation for the value type, although typically Src=SrcValue*)
  {Ht1: CerticoqTranslationCorrect Ls Li}
  {Ht2: CerticoqTranslationCorrect Li Ld}
    : CerticoqTranslationCorrect Ls Ld.
Proof.
  destruct Ht1, Ht2.
  constructor;[eapply composePreservesGood; eauto; fail|].
  intros ? ? Hgood Hev.
  apply obsePres0 in Hev;[| assumption].
  apply certiGoodPres3 in Hgood.
  unfold composeTranslation, translate in *.
  destruct (t1 s); compute in Hev; try contradiction.
  destruct Hev as [iv Hev].
  destruct Hev as [Hev Hoeq].
  apply obsePres1 in Hev;[| assumption].
  destruct Hev as [dv Hc].
  exists dv. compute.
  compute in Hc. split;[tauto|].
  apply proj2 in Hc. revert Hc Hoeq. clear.
  intros ? ?.
  eapply obsLeTrns with (i:=iv); eauto.
Qed.

End YesNoQuestions.

Notation "s ⊑ t" := (obsLe s t) (at level 65).


(** Here are some other correctness properties that we may be interested in: *)

(** A translation can be proved correct trivially if the questionHead function
in the destination says yes to everything. This property of 
the questionHead function enforces that
if it says "yes" to some constructor of an inductive type, it must say
"no" to all other constructors of the SAME inductive type 
**)

Definition nonTrivialQuestionHead (Value : Type)
  `{@QuestionHead Value} : Prop:=
forall (v:Value) (i: Ast.inductive) n, 
  (questionHead (Cnstr i n) v = true)
  -> forall m, m<>n ->  questionHead (Cnstr i m) v = false.
  
(** We can also ask every language to declare their notion of application 
as a function of type Term->Value->Term.
Then, in obsLe, we can also exploit 
observations on values resulting from applications of functions to values. 
**)


(* can be used to get the Term type from an instance *)
Definition cTerm `{CerticoqLanguage Term Value} : Type := Term.
(* can be used to get the Value type from an instance *)
Definition cValue `{CerticoqLanguage Term Value} : Type := Term.

Arguments cTerm {Term} {Value} {H} {H0} {H1} {H2} _.
Arguments cValue {Term} {Value} {H} {H0} {H1} {H2} _.


Arguments CerticoqLanguage Term {Value} {H} {H0} {H1} {H2}.

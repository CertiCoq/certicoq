Require Import Common.exceptionMonad.
Require Import Common.certiClasses.
Require Import Coq.Unicode.Utf8.
Require Import List.
Generalizable Variables Src Dst Inter Term Value SrcValue DstValue InterValue.

From MetaCoq Require BasicAst.
Require Import Coq.btauto.Btauto.
Require Import Morphisms.

Global Instance  liftLeRefl {A:Type} (R: A -> A -> Prop)
  {rl: Reflexive R} : Reflexive (liftLe R).
Proof using.
  intros x. destruct x; constructor; auto.
Defined.

(** Some values, e.g. constructors, can have subterms.
   This operation allows asking for the nth subterm.
   When trying to observe the nth subterm of a value having only m (m<n)
   subterms, all bets are off about the returned value.
 *)
Class ObserveNthSubterm (Value:Type) :=
  observeNthSubterm: nat -> Value -> option Value.

Section YesNoQuestions.

(* Zoe's suggestion for Question *)
Inductive Question : Set  := 
| Cnstr : BasicAst.inductive -> nat -> Question
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
  TODO: consider using liftLe *)
| obsSome: forall s d, obsLe s d -> obsLeOp (Some s) (Some d)
| obsNone: forall d, obsLeOp None d.


(** Sometimes, the greatest fixedpoint is obtained at \omega.
*)
Inductive obsLeInd : nat -> SrcValue -> DstValue -> Prop :=
| obsLeS: forall m (s : SrcValue) (d : DstValue),
    yesPreserved s d
    -> (forall n:nat, liftLe (obsLeInd m) (observeNthSubterm n s) (observeNthSubterm n d))
    -> obsLeInd (S m) s d
| obsLeO: forall s d, obsLeInd O s d. (** \top element in the space of relations *)

(** this part is generally easy and unconditional *)
Lemma fromCoInd s d:
  obsLe s d -> forall m, obsLeInd m s d.
Proof using.
  intros Hc m. revert Hc. revert s. revert d.
  induction m as [ | m Hind]; intros ? ? Hc;
    [ constructor; fail
    | destruct Hc as [? ? Hyes Hsub];
      constructor; [ assumption | ] ].
  intros n. specialize (Hsub n).
  inversion Hsub; subst; clear Hsub; constructor; eauto.
Qed.

(** This part is generally hard and conditional.
Here, it is unconditional. [obsLe] does not depend on computations.
However, in certiclasses3, where obsLe mentions computation, we may need the 
big step eval in LambdaANF to be deterministic.
*)
Lemma toCoInd s d:
  (forall m, obsLeInd m s d) -> obsLe s d.
Proof using.
  revert s d.
  cofix toCoInd. intros ? ? Hi. pose proof Hi as Hib.
  specialize (Hi 1); inversion Hi as [ ? ? ? Hyes Hsub | ]; subst. clear Hi.
  constructor; [ assumption | ].
  intros ?.
  specialize (Hsub n).
  inversion Hsub; subst; clear Hsub; constructor.
  apply toCoInd. revert H3. revert H4. revert Hib.
  clear.
  intros.
  specialize (Hib (S m)).
  inversion Hib as  [ ? ? ? _ Hsubb | ]. subst. clear Hib.
  specialize (Hsubb n).
  rewrite <- H3, <- H4 in Hsubb.
  inversion Hsubb. assumption.
Qed.  

Global Instance  yesPreservedRefl: Reflexive (@yesPreserved SrcValue _ SrcValue _).
Proof using.
  intros x q. unfold implb. btauto. 
Qed.

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

Lemma yesPreservedTransitive {SrcValue InterValue DstValue:Type}
         `{QuestionHead SrcValue} 
   `{QuestionHead InterValue} 
   `{QuestionHead DstValue} 
      (s : SrcValue) (i : InterValue) (d : DstValue):
  yesPreserved s i
  -> yesPreserved i d 
  -> yesPreserved s d.
Proof using.
  unfold yesPreserved. intros Hyesi Hyesd q.
  specialize (Hyesi q).
  specialize (Hyesd q).
  destruct (questionHead q s); simpl in *;[| reflexivity]. 
  rewrite Hyesi in Hyesd. assumption.
Qed.



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
  cofix obsLeTrns.
  intros ? ? ? Ha Hb.
  inversion Ha as [ss is Hah Has]. subst. clear Ha.
  inversion Hb as [is ds Hbh Hbs]. subst. clear Hb.
  constructor; auto;
    [eauto using (@yesPreservedTransitive SrcValue InterValue DstValue); fail
    |].
 clear Hah Hbh. intros n.
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
  intros ? ? ? Hgood Hev.
  unfold goodPreserving, obsPreserving in *.
  eapply obsePres0 with (o:=o) in Hev; [| assumption].
  eapply certiGoodPres3 with (o:=o) in Hgood.
  unfold composeTranslation, translate in *.
  destruct (t1 o s); compute in Hev; try contradiction.
  destruct Hev as [iv Hev].
  destruct Hev as [Hev Hoeq].
  edestruct obsePres1 with (o:=o) as [dv [Hsd Hsubd]].
  now apply Hgood. eassumption. 

  exists dv. compute.
  compute in Hsd. split;[tauto|].
  eapply obsLeTrns with (i0 := iv); assumption.
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
forall (v:Value) (i: BasicAst.inductive) n,
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
Definition cValue `{CerticoqLanguage Term Value} : Type := Value.

Arguments cTerm {Term} {Value} {H} {H0} {H1} {H2} _.
Arguments cValue {Term} {Value} {H} {H0} {H1} {H2} _.


Arguments CerticoqLanguage Term {Value} {H} {H0} {H1} {H2}.

Definition evalPreservesGoodness `{Ls: BigStepOpSem Src SrcValue}
  `{GoodTerm Src} `{GoodTerm SrcValue} :=
  forall (s:Src) (sv: SrcValue),
    s ⇓ sv -> goodTerm s -> goodTerm sv.

(* This can be typically be easily proven by induction on sv *)
Definition valueTypeTranslateLe (SrcValue DstValue : Type)
           `{CerticoqTranslation SrcValue DstValue}
           `{QuestionHead SrcValue}
           `{QuestionHead DstValue}
           `{ObserveNthSubterm SrcValue}
           `{ObserveNthSubterm DstValue} : Prop :=
  forall (o: Opt) (sv: SrcValue) (dv: DstValue),
    translate _ DstValue o sv = Ret dv -> sv ⊑ dv.

Lemma certicoqTranslationCorrect_suff1
  `{Ls: CerticoqLanguage Src SrcValue}
  `{Ld: CerticoqLanguage Dst DstValue}
  {t1 : CerticoqTranslation Src Dst}
  {t1v : CerticoqTranslation SrcValue DstValue}
  (bgs : bigStepPreserving Src Dst)
  (gp: goodPreserving Src Dst)
  (vt : valueTypeTranslateLe SrcValue DstValue)
  :
  CerticoqTranslationCorrect Ls Ld.
Proof using.
  constructor;[assumption|].
  intros ? ? ? Hgs Hev.
  unfold bigStepPreserving in *.
  eapply bgs with (o:=o) in Hev;[| assumption].
  hnf in Hev.
  specialize (gp s o Hgs).
  specialize (vt o sv).
  destruct (translate Src Dst o s); simpl in *; try contradiction.
  destruct (translate SrcValue DstValue o sv) as [ | dv]; simpl in *; try contradiction.
  eauto.
Qed.



(* For the case when the type of terms and values is the same. In many lemmas
  IsValue only needs to be complete (not sound) *)
Definition valuePredTranslateLe (Src Dst : Type)
           `{CerticoqTranslation Src Dst}
           `{IsValue Src}
           `{QuestionHead Src}
           `{QuestionHead Dst}
           `{ObserveNthSubterm Src}
           `{ObserveNthSubterm Dst} : Prop :=
  forall (o: Opt) (sv: Src) (dv: Dst),
    isValue sv -> translate _ Dst o sv = Ret dv -> sv ⊑ dv.

Lemma certicoqTranslationCorrect_suff2
  `{Ls: CerticoqLanguage Src SrcValue}
  `{Ld: CerticoqLanguage Dst DstValue}
  {t1 : CerticoqTranslation Src Dst}
  {t1v : CerticoqTranslation SrcValue DstValue}
  (bgs : bigStepPreserving Src Dst)
  (gp: goodPreserving Src Dst)
  {isv : IsValue SrcValue}
  (vt : valuePredTranslateLe SrcValue DstValue)
  (isvc : IsValueComplete) (* soundness is not needed. *)
  :
  CerticoqTranslationCorrect Ls Ld.
Proof using.
  constructor;[assumption|].
  intros ? ? ? Hgs Hev.
  pose proof Hev as Hevb.
  unfold bigStepPreserving in bgs.
  eapply bgs with (o:=o) in Hev;[| assumption].
  apply isvc in Hevb.
  hnf in Hev.
  specialize (gp s o Hgs).
  specialize (vt o sv).
  destruct (translate Src Dst o s); simpl in *; try contradiction.
  destruct (translate SrcValue DstValue o sv) as [ | dv]; simpl in *; try contradiction.
  eauto.
Qed.

Definition valuePredTranslateYesPreserved (Src Dst : Type)
           `{CerticoqTranslation Src Dst}
           `{IsValue Src}
           `{QuestionHead Src}
           `{QuestionHead Dst}
           `{ObserveNthSubterm Src}
           `{ObserveNthSubterm Dst} : Prop :=
  forall (o:Opt) (sv: Src) (dv: Dst),
    isValue sv -> translate _ Dst o sv = Ret dv ->
    yesPreserved sv dv.

Definition valuePredTranslateObserveNthCommute (Src Dst : Type)
           `{CerticoqTranslation Src Dst}
           `{IsValue Src}
           `{QuestionHead Src}
           `{QuestionHead Dst}
           `{ObserveNthSubterm Src}
           `{ObserveNthSubterm Dst} : Prop :=
  forall (o:Opt) (sv: Src) (dv: Dst) n,
    isValue sv -> translate _ Dst o sv = Ret dv ->
    option_map (translate _ Dst o) (observeNthSubterm n sv) =
    option_map (@Ret _) (observeNthSubterm n dv)
    /\ (match (observeNthSubterm n sv)  with
       | Some s => isValue s
       | None => True
       end).


Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Lemma valuePredTranslateLe_suff  (Src Dst : Type)
           `{CerticoqTranslation Src Dst}
           `{IsValue Src}
           `{QuestionHead Src}
           `{QuestionHead Dst}
           `{ObserveNthSubterm Src}
           `{ObserveNthSubterm Dst} :
  valuePredTranslateObserveNthCommute Src Dst
  -> valuePredTranslateYesPreserved Src Dst
  -> valuePredTranslateLe Src Dst.
Proof using.
  intros Ho Hy.
  cofix valuePredTranslateLe_suff.
  intros ? ? ? Hv Ht.
  constructor;[eauto|].
  intros.
  specialize (Ho o _ _ n Hv Ht).
  destruct (observeNthSubterm n sv);[| constructor].
  simpl in Ho. repnd.
  destruct (observeNthSubterm n dv); inverts Ho0.
  constructor. 
  eapply valuePredTranslateLe_suff; eauto.
Qed.  
  
Lemma certicoqTranslationCorrect_suff3
  `{Ls: CerticoqLanguage Src SrcValue}
  `{Ld: CerticoqLanguage Dst DstValue}
  {t1 : CerticoqTranslation Src Dst}
  {t1v : CerticoqTranslation SrcValue DstValue}
  {isv : IsValue SrcValue}
  (bgs : bigStepPreserving Src Dst)
  (gp: goodPreserving Src Dst)
  (vty : valuePredTranslateYesPreserved SrcValue DstValue)
  (vto : valuePredTranslateObserveNthCommute SrcValue DstValue)
  (isvc : IsValueComplete) (* soundness is not needed. *)
  :
  CerticoqTranslationCorrect Ls Ld.
Proof using.
  eapply valuePredTranslateLe_suff in vto; eauto;[].
  clear vty.
  eapply certicoqTranslationCorrect_suff2; eauto.
Qed.

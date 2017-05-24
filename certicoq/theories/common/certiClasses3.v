(** This file is exprerimental, currently not in use.
Here, the ⊑ relation has computation baked in, which is useful if we
ever add cofixpoints, where arguments of constructors of coinductive types
may compute further.
For a variant that supports separate compilation/linking, see certiClassesLinkable
*)

Require Import Common.exceptionMonad.
Require Import Common.AstCommon.
Require Import Common.certiClasses.
Require Import Common.certiClasses2.
Require Import Coq.Unicode.Utf8.


Class BigStepOpSem (Term:Type) := bigStepEval:> @certiClasses.BigStepOpSem Term Term.


Class CerticoqLanguage (Term:Type)
  `{BigStepOpSem Term} `{GoodTerm Term} 
   `{QuestionHead Term} `{ObserveNthSubterm Term} 
:= 
{
}.


Section CompObsPreserving.

Context (Src Dst: Type)
  (* {SrcValue DstValue: Type} having a seperate type for values becomes awkward in this setup.
     If really needed, one can always use sum types to combine the term and value types.*)
          `{QuestionHead Src} `{ObserveNthSubterm Src}
   `{QuestionHead Dst} `{ObserveNthSubterm Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} `{GoodTerm Src}.

(* Because we may need to compute in subterms before obseving them, this definition
bakes in computations. *)
CoInductive compObsLe : Src -> Dst -> Prop :=
| sameObs : forall (s : Src) (d : Dst),
    (forall (sv:Src),
        s ⇓ sv
        -> (exists dv:Dst,
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe compObsLe (observeNthSubterm n sv) (observeNthSubterm n dv))))
    -> compObsLe s d.


Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Context `{CerticoqTranslation Src Dst}.
Definition compObsPreserving :=
   ∀ (s:Src),
    goodTerm s
    -> liftLe compObsLe (Some s) (exception_option (translate Src Dst s)).

End CompObsPreserving.

Class CerticoqTranslationCorrect {Src Dst : Type}
  `{CerticoqLanguage Src} 
  `{CerticoqLanguage Dst}
  `{CerticoqTranslation Src Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} 
  := 
{
  certiGoodPres : goodPreserving Src Dst;
  obsePres : compObsPreserving Src Dst;
}.


Global Arguments CerticoqTranslationCorrect
  {Src} {Dst} {H} {H0} {H1} {H2} H3  {H4} {H5} {H6} {H7} H8 {H9} {H10} {H11}.

Notation "s ⊑ t" := (compObsLe _ _ s t) (at level 65).

Section Compose.
Context (Src Inter Dst : Type)
   `{Ls: CerticoqLanguage Src} `{Li: CerticoqLanguage Inter}  `{Ld: CerticoqLanguage Dst}.

Lemma compObsLeTransitive  :
   forall   (s : Src) (i : Inter) (d : Dst),
  s ⊑ i
  -> i ⊑ d 
  -> s ⊑ d.
Proof.
  cofix.
  intros ? ? ? Ha Hb.
  inversion Ha as [ss is Hah Has]. subst. clear Ha.
  inversion Hb as [is ds Hbh Hbs]. subst. clear Hb.
  constructor; auto.
  intros ? Hevs.
  destruct (Hah _ Hevs) as [iv  Hci]. clear Hah.
  destruct Hci as [Hevi Hci].
  destruct Hci as [Hyesi Hsubi].
  destruct (Hbh _ Hevi) as [dv  Hcd]. clear Hbh.
  destruct Hcd as [Hevd Hcd].
  destruct Hcd as [Hyesd Hsubd].
  exists dv. split;[ assumption| split].
- clear Hsubi Hsubd.
  unfold yesPreserved in *. intros q.
  specialize (Hyesi q).
  specialize (Hyesd q).
  destruct (questionHead q sv); simpl in *;[| reflexivity]. 
  rewrite Hyesi in Hyesd. assumption.
- clear Hyesi Hyesd.
  intros n.
  specialize (Hsubi n).
  specialize (Hsubd n).
  destruct Hsubi;[| constructor ].
  inversion Hsubd. subst. clear Hsubd.
  constructor. eauto.
Qed.

Require Import SquiggleEq.LibTactics.
Context   {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}.
Global Instance composeCerticoqTranslationCorrect
(* we don't need a translation for the value type, although typically Src=SrcValue*)
  {Ht1: CerticoqTranslationCorrect Ls Li}
  {Ht2: CerticoqTranslationCorrect Li Ld}
    : CerticoqTranslationCorrect Ls Ld.
Proof.
  destruct Ht1, Ht2.
  constructor; [eapply composePreservesGood; eauto; fail |].
  intros ? Hgoods.
  specialize (obsePres0 _ Hgoods).
  inverts obsePres0 as Hle Heq.
  apply certiGoodPres0 in Hgoods.
  unfold composeTranslation, translate in *.
  destruct (t1 s); compute in Hgoods; try contradiction.
  compute in Heq. inverts Heq.
  specialize (obsePres1 _ Hgoods).
  inverts obsePres1 as Hlei Heqi.
  apply certiGoodPres1 in Hgoods.
  unfold composeTranslation, translate in *. simpl.
  destruct (t2 i); compute in Hgoods; try contradiction.
  simpl.
  constructor.
  inverts Heqi.
  eapply compObsLeTransitive; eauto.
Qed.

End Compose.



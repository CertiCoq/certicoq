(** This file is exprerimental, currently not in use.
*)

Require Import Common.exceptionMonad.
Require Import Common.AstCommon.
Require Import Common.certiClasses.
Require Import Common.certiClasses2.
Require Import Common.certiClasses3.
Require Import Common.certiClassesLinkable.
Require Import Coq.Unicode.Utf8.



Section CompObsPreserving.

Context (Src Dst: Type)
  (* {SrcValue DstValue: Type} having a seperate type for values becomes awkward in this setup.
     If really needed, one can always use sum types to combine the term and value types.*)
          `{QuestionHead Src} `{ObserveNthSubterm Src}
   `{QuestionHead Dst} `{ObserveNthSubterm Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} `{GoodTerm Src}
   `{MkApply Src}  `{MkApply Dst}.


(* here, the arguments of app may be compiled by a different compiler or manually produced. 
Instead of requiring
that dvArg be the result of compiling svArg, we merely need that svArg and dvArg are
observationally equal.*)
Fixpoint compObsLeLinkExtN `{GoodTerm Dst} (m:nat) (s:Src) (d:Dst) {struct m} : Prop :=
  match m with
  | 0 => True (* top item in the space of relations. we are trying to define the greatest fixed point *)
  | S m =>
    (forall (sv:Src),
        s ⇓ sv
        -> (exists dv:Dst,
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe  (compObsLeLinkExtN m) (observeNthSubterm n sv) (observeNthSubterm n dv))
              /\ (questionHead  Abs sv = true -> forall svArg dvArg, goodTerm svArg -> goodTerm dvArg ->
                  compObsLeLinkExtN m svArg dvArg -> (* negative occurrence in a coinductive defn*)
                  compObsLeLinkExtN m
                      (mkApp sv svArg)
                      (mkApp dv dvArg))
          ))
  end.

Definition compObsLeLinkExt `{GoodTerm Dst} (s:Src) (d:Dst) : Prop :=
  forall m, compObsLeLinkExtN m s d.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Context `{CerticoqTranslation Src Dst}.
Definition compObsPreservingLinkableExt `{GoodTerm Dst}:=
   ∀ (s:Src),
    goodTerm s 
    -> liftLe compObsLeLinkExt (Some s) (exception_option (translate Src Dst s)).

End CompObsPreserving.

Class CerticoqLinkableExtTranslationCorrect {Src Dst : Type}
  `{CerticoqLinkableLanguage Src} 
  `{CerticoqLinkableLanguage Dst}
  `{CerticoqTranslation Src Dst}
  := 
{
  certiGoodPresLinkDiff : goodPreserving Src Dst;
  obsePresLinkDiff : compObsPreservingLinkableExt Src Dst;
}.

Global Arguments CerticoqLinkableExtTranslationCorrect
  {Src} {Dst} {H} {H0} {H1} {H2} {H3}  H4 {H5} {H6} {H7} {H8} {H9} H10 {H11}.


Section ComposeLinkExt.
Context (Src Inter Dst : Type)
        `{Ls: CerticoqLinkableLanguage Src}
        `{Li: CerticoqLinkableLanguage Inter}
        `{Ld: CerticoqLinkableLanguage Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
  {Ht1: CerticoqLinkableExtTranslationCorrect Ls Li}
  {Ht2: CerticoqLinkableExtTranslationCorrect Li Ld}.

Section Nn.
  Variable n:nat.
Notation "s ⊑ t" := (compObsLeLinkExtN  _ _ n s t) (at level 65).

Lemma compObsLeLinkExtTransitive:
   forall   (s : Src) (i : Inter) (d : Dst),
  s ⊑ i
  -> i ⊑ d 
  -> s ⊑ d.
Proof.
  rename n into m.
  induction m as [| m Hind];[ trivial| ].
  intros ? ? ? Hsi Hid ? Hevs.
  simpl in Hsi.
  specialize (Hsi _ Hevs).
  destruct Hsi as [iv Hsi].
  repnd. rename Hsi0 into Hevi.
  simpl in Hid.
  specialize (Hid _ Hevi).
  destruct Hid as [dv Hsd].
  repnd.
  exists dv.
  dands; auto; [eauto using (@yesPreservedTransitive Src Inter Dst) | | ].
- intros ?. clear Hsd Hsi. 
  simpl.
  eapply liftLeTrans; eauto.
- clear Hsd2 Hsi2.
  intros Habs. rename Hsd into Hsubd.
  rename Hsi into Hsubi.
  intros ? ? Hgs Hgd Hobsd.
  specialize (fun d => Hsubi Habs _ d Hgs).
  destruct Ht1 as [GPsi OPsi].
  specialize (GPsi svArg Hgs).
  specialize (OPsi _ Hgs).
  (* 
Where to get the intermediate term ivArg needed to invoke Hsubi, the part
hat comes from app linkable correctness from Src to Inter? 
How can we cook that up?
The only way to get a Inter is to translate: The translations between
Src to Inter and Inter to Dst have been proved correct.
However, we get stuck later.
Note that in this file, the relation ⊑ does not depend on any translation.
 *)
  destruct (translate Src Inter svArg) as [| iArg ]; try contradiction.
  invertsn OPsi.
  specialize (Hsubi iArg GPsi (OPsi m)).
  eapply Hind;[apply Hsubi | ].
  apply Hsubd; auto.
  + admit. (* easy *)
  + 
  (* 
This is not provable. iArg can answer yes to all questions. 
If this goal were provable, then dvArg must also say no to all questions.
Nothing in the hypotheses suggest that. For intuition with numbers, and <= being the relation,
We can have svArg :=1, iArg := 100, dvArg:=50.
We have svArg <= iArg  and svArg <= dvArg, but we dont have iArg <= dvArg, or 100 <= 50.

Note that, by design, dvArg is not the translation svArg. We wanted the app arg to 
be arbitrary and come from arbitrary compilers or by hand.
*)
Abort.
End Nn.
End ComposeLinkExt.


(** Relating the extensional version in this file to the non-extensional version
in certiClassesLinkable.v *)

Section ExtImpliesNonExt.
Context (Src Dst : Type)
        `{Ls: CerticoqLinkableLanguage Src}
        `{Ld: CerticoqLinkableLanguage Dst}
        {t1 : CerticoqTranslation Src Dst}
        {Hgg : CerticoqLinkableTranslationCorrect Ls Ld}.

Section Nn.
  Variable n:nat.
  Notation "s ⊑ t" := (compObsLeLinkExtN  _ _ n s t) (at level 65).
  Notation "s ≲ t" := (compObsLeLinkN  _ _ n s t) (at level 65).

Lemma extImpliesNonExt (s:Src) (t:Dst) : s ⊑ t -> s ≲ t.
Proof using.
  revert s t.
  induction n as [| m Hind];[constructor |].
  intros ? ? Hlt. 
  clear n. rename m into n.
  simpl in Hlt.
  constructor.
  intros ? Hev.
  specialize (Hlt _ Hev). exrepnd.
  exists dv. dands; eauto using liftLeRimpl;[].
  clear Hlt3.
  intros Hq svArg Hg.
  specialize (Hlt0 Hq svArg).
  destruct Hgg.
  specialize (certiGoodPresLink svArg Hg).
  specialize (obsePresLink svArg Hg).
  destruct (translate Src Dst svArg) as [ | tsvArg];[contradiction | ].
  inverts obsePresLink. 
  simpl. constructor.
  apply Hind.
  apply Hlt0; eauto.
  Fail apply Hind.
  idtac.
  Fail apply H11.
Abort.
End Nn.
End ExtImpliesNonExt.
(** This file is exprerimental, currently not in use.
*)

Require Import Common.exceptionMonad.
Require Import Common.AstCommon.
Require Import Common.certiClasses.
Require Import Common.certiClasses2.
Require Import Coq.Unicode.Utf8.


Class BigStepOpSem (Term:Type) := bigStepEval:> @certiClasses.BigStepOpSem Term Term.

Class MkApply (Term:Type) := mkApp : Term -> Term -> Term.

Class CerticoqLanguage (Term:Type)
  `{BigStepOpSem Term} `{GoodTerm Term} 
   `{QuestionHead Term} `{ObserveNthSubterm Term} 
:= 
{
}.

Definition sameValues {Term:Type}
  `{BigStepOpSem Term} (a b : Term)
:= forall (v: Term), a ⇓ v <-> b ⇓ v.

Class CerticoqLinkableLanguage (Term:Type)
  `{BigStepOpSem Term} `{GoodTerm Term} 
  `{QuestionHead Term} `{ObserveNthSubterm Term}
  `{MkApply Term} 
:= 
{
}.

Definition mkAppEx {Term:Type}  {mka: MkApply Term} (f:Term) (arg : exception Term):
  exception Term:=
  match arg with
  | Ret arg => Ret (mkApp f arg)
  | _ => arg
  end.

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


Context   `{CerticoqTranslation Src Dst}  `{MkApply Src}  `{MkApply Dst}.


CoInductive compObsLeLink : Src -> Dst -> Prop :=
| sameObsLink : forall (s : Src) (d : Dst),
    (forall (sv:Src),
        s ⇓ sv
        -> (exists dv:Dst,
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe compObsLeLink (observeNthSubterm n sv) (observeNthSubterm n dv))
              /\ (questionHead  Abs sv = true -> forall svArg, goodTerm svArg ->
                   liftLe compObsLeLink
                      (Some (mkApp sv svArg))
                      (exception_option (mkAppEx dv (translate Src Dst svArg))))
          ))
    -> compObsLeLink s d.

Hint Constructors liftLe : certiclasses.

Inductive compObsLeLinkN : nat -> Src -> Dst -> Prop :=
| sameObsLinkS : forall m (s : Src) (d : Dst),
    (forall (sv:Src),
        s ⇓ sv
        -> (exists dv:Dst,
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe (compObsLeLinkN m) (observeNthSubterm n sv) (observeNthSubterm n dv))
              /\ (questionHead  Abs sv = true -> forall svArg, goodTerm svArg ->
                   liftLe (compObsLeLinkN m)
                      (Some (mkApp sv svArg))
                      (exception_option (mkAppEx dv (translate Src Dst svArg))))
          ))
    -> compObsLeLinkN (S m) s d
| sameObsLinkO : forall (s : Src) (d : Dst), compObsLeLinkN 0 s d.


Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
(** this part is generally easy and unconditional *)
Lemma fromCoInd s d:
  compObsLeLink s d -> forall m, compObsLeLinkN m s d.
Proof using.
  intros Hc m. revert Hc. revert d. revert s.
  induction m as [ | m Hind]; intros ? ? Hc;
    [ constructor; fail | ].
  destruct Hc as [? ? Hc].
  constructor.
  intros sv Hev. specialize (Hc sv Hev).
  destruct Hc as [dv Hc]. repnd.
  exists dv. dands; eauto with certiclasses.
Qed.

(* transparent, to pass productivity checks. replace in certiclasses2*)
Lemma  liftLeRimpl {S D: Type} (R1 R2: S -> D -> Prop) os od:
  Rimpl R1 R2 -> liftLe R1 os od -> liftLe R2 os od.
Proof.
  intros Hr Hl.
  inverts Hl; constructor.
  apply Hr. assumption.
Defined.

Lemma toCoInd {dstDet: deterministicBigStep Dst}s d:
  (forall m, compObsLeLinkN m s d) -> compObsLeLink s d.
Proof using.
  revert d. revert s.
  cofix.
  intros ? ? Hi.
  constructor.
  intros ? Hev. pose proof Hi as Hib.
  specialize (Hi 1); inversion Hi as [ ? ? ? Hc | ]; subst. clear Hi.
  specialize (Hc sv Hev).
  destruct Hc as [dv Hc]. repnd.
  exists dv.
  dands; auto.
  - clear Hc. intros n.
    apply liftLeRimpl with (R1:= fun a b => forall m, compObsLeLinkN m a b); eauto.
    
    specialize (Hc2 n). invertsna Hc2 H0c;[ | constructor].
    rename s0 into svn.
    rename d0 into dvn.
    constructor.
    intros m.
    specialize (Hib (S m)).
    invertsna Hib Hib.
    specialize (Hib sv Hev).
    destruct Hib as [dvv Hib]. repnd.
    specialize (dstDet _ _ _ Hib0 Hc0). subst. clear Hib0 Hib.
    specialize (Hib2 n).
    rewrite <- H0c1, <- H0c0 in Hib2.
    inverts Hib2. assumption.

  - clear Hc2. intros Hq ? Hg.
    specialize (Hc Hq _ Hg).
    apply liftLeRimpl with (R1:= fun a b => forall m, compObsLeLinkN m a b); eauto.
    invertsna Hc H0c.
    constructor.
    intros m.
    specialize (Hib (S m)).
    invertsna Hib Hib.
    specialize (Hib sv Hev).
    destruct Hib as [dvv Hib]. repnd.
    specialize (dstDet _ _ _ Hib0 Hc0). subst. clear Hib0 Hib2.
    specialize (Hib Hq _ Hg).
    rewrite  <- H0c0 in Hib.
    inverts Hib. assumption.
Qed.    
        
Definition compObsPreserving :=
   ∀ (s:Src),
    goodTerm s
    -> liftLe compObsLe (Some s) (exception_option (translate Src Dst s)).

Definition compObsPreservingLinkable :=
   ∀ (s:Src),
    goodTerm s 
    -> liftLe compObsLeLink (Some s) (exception_option (translate Src Dst s)).

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

Class CerticoqLinkableTranslationCorrect {Src Dst : Type}
  `{CerticoqLinkableLanguage Src} 
  `{CerticoqLinkableLanguage Dst}
  `{CerticoqTranslation Src Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} 
  := 
{
  certiGoodPresLink : goodPreserving Src Dst;
  obsePresLink : compObsPreservingLinkable Src Dst;
}.

Global Arguments CerticoqTranslationCorrect
  {Src} {Dst} {H} {H0} {H1} {H2} H3  {H4} {H5} {H6} {H7} H8 {H9} {H10} {H11}.
Notation "s ⊑ t" := (compObsLe _ _ s t) (at level 65).

Global Arguments CerticoqLinkableTranslationCorrect
  {Src} {Dst} {H} {H0} {H1} {H2} {H3}  H4 {H5} {H6} {H7} {H8} {H9} H10 {H11} {H12} {H13}.

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



Section ComposeLink.
Context (Src Inter Dst : Type)
        `{Ls: CerticoqLinkableLanguage Src}
        `{Li: CerticoqLinkableLanguage Inter}
        `{Ld: CerticoqLinkableLanguage Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}.

Notation "s ⊑ t" := (compObsLeLink _ _ s t) (at level 65).

Lemma compObsLeLinkTransitive
      {Hgpsi : goodPreserving Src Inter}
      {Hgpid : goodPreserving Inter Dst}:
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
  exists dv. split;[ assumption|].
  assert (forall (A B: Prop), A -> (A-> B) -> A/\B) as Hp by (intros; tauto).
  apply Hp;[|intros Hyessd; split]; clear Hp.
- clear Hsubi Hsubd.
  unfold yesPreserved in *. intros q.
  specialize (Hyesi q).
  specialize (Hyesd q).
  destruct (questionHead q sv); simpl in *;[| reflexivity]. 
  rewrite Hyesi in Hyesd. assumption.
- clear Hyesi Hyesd.
  intros n.
  apply proj1 in Hsubi.
  apply proj1 in Hsubd.
  specialize (Hsubi n).
  specialize (Hsubd n).
  destruct Hsubi;[| constructor ].
  inversion Hsubd. subst. clear Hsubd.
  constructor. eauto.
- intros Habs.
  apply proj2 in Hsubi.
  apply proj2 in Hsubd.
  intros ? Hgsv.
  specialize (Hsubi Habs svArg Hgsv).
  unfold yesPreserved in Hyesi.
  specialize (Hyesi Abs).
  rewrite Habs in Hyesi.
  simpl in Hyesi.
  specialize (Hsubd Hyesi).
  inverts Hsubi as Hsub Heq.
  apply Hgpsi in Hgsv.
  unfold composeTranslation, translate in *.
  destruct (t1 svArg) as [| ivArg];[inverts Heq|].
  simpl in *. inverts Heq.
  specialize (Hsubd ivArg Hgsv).
  inverts Hsubd as Hsubd Heq.
  destruct (t2 ivArg) as [|dvArg ];[inverts Heq|].
  simpl in *. inverts Heq.
  constructor. eauto.
Qed.

Global Instance composeCerticoqLinkableTranslationCorrect
(* we don't need a translation for the value type, although typically Src=SrcValue*)
  {Ht1: CerticoqLinkableTranslationCorrect Ls Li}
  {Ht2: CerticoqLinkableTranslationCorrect Li Ld}
    : CerticoqLinkableTranslationCorrect Ls Ld.
Proof.
  destruct Ht1, Ht2.
  constructor; [eapply composePreservesGood; eauto; fail |].
  intros ? Hgoods.
  specialize (obsePresLink0 _ Hgoods).
  inverts obsePresLink0 as Hle Heq.
  apply certiGoodPresLink0 in Hgoods.
  unfold composeTranslation, translate in *.
  destruct (t1 s); compute in Hgoods; try contradiction.
  compute in Heq. inverts Heq.
  specialize (obsePresLink1 _ Hgoods).
  inverts obsePresLink1 as Hlei Heqi.
  apply certiGoodPresLink1 in Hgoods.
  unfold composeTranslation, translate in *. simpl.
  destruct (t2 i); compute in Hgoods; try contradiction.
  simpl.
  constructor.
  inverts Heqi.
  eapply compObsLeLinkTransitive; eauto.
  Unshelve. eauto. eauto.
Qed.

Require Import Morphisms.

Global Instance  compObsLeLinkRespectsSameVal:
  Proper (eq ==> sameValues ==> iff) ((@compObsLeLink Src Inter _ _ _ _ _ _ _ _ _ _  )).
Proof using.
  intros s1 s2 Heqs d1 d2 Hsvd. subst. rename s2 into s.
  split.
- revert Hsvd s.  revert d1 d2.
  cofix.
  intros ? ? Hsvd ? Hs.
  constructor.
  inverts Hs.
  unfold sameValues in Hsvd.
  firstorder. (* no idea what it did *)
- revert Hsvd s.  revert d1 d2.
  cofix.
  intros ? ? Hsvd ? Hs.
  constructor.
  inverts Hs.
  unfold sameValues in Hsvd.
  firstorder.
Qed. 

(* A more general version of the above
Global Instance  compObsLeLinkRespectsSameVal2:
  Proper (sameValues ==> sameValues ==> iff) ((@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  )).
Proof using.
  intros s1 s2 Hsvs d1 d2 Hsvd. subst.
  split.
- revert  s1 s2 Hsvs d1 d2 Hsvd.
  cofix.
  intros ? ? Hsvs ? ? Hsvd Hs.
  constructor.
  inverts Hs.
  unfold sameValues in *.
  firstorder. (* no idea what it did *)
- revert Hsvd s.  revert d1 d2.
  cofix.
  intros ? ? Hsvd ? Hs.
  constructor.
  inverts Hs.
  unfold sameValues in Hsvd.
  firstorder.
Qed. 
 *)

Local Instance  compObsLeLinkRespectsEval:
  Proper (eq ==> bigStepEval  ==> Basics.impl) ((@compObsLeLink Src Inter _ _ _ _ _ _ _ _ _ _  )).
Proof using.
  intros s1 s2 Heqs d1 d2 Hsvd Hs1. subst.
  constructor.
  intros ? Heval.
  (* need that the second arg of bigStepeval is terminal *)
Abort.

End ComposeLink.
Require Import Common.exceptionMonad.
Require Import Common.AstCommon.
Require Import Common.certiClasses.
Require Import Common.certiClasses2.
Require Import Common.certiClasses3.
Require Import Coq.Unicode.Utf8.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
Require Import Morphisms.

Class MkApply (Term:Type) := mkApp : Term -> Term -> Term.

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
   `{BigStepOpSem Src} `{BigStepOpSem Dst} `{GoodTerm Src}
   `{CerticoqTranslation Src Dst}  `{MkApply Src}  `{MkApply Dst}.


CoInductive compObsLeLink : Src -> Dst -> Prop :=
| sameObsLink : forall (s : Src) (d : Dst),
    (forall (o:Opt) (sv:Src),
        s ⇓ sv
        -> (exists (dv : Dst),
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe compObsLeLink (observeNthSubterm n sv) (observeNthSubterm n dv))
              /\ (questionHead  Abs sv = true -> forall svArg, goodTerm svArg ->
                   liftLe compObsLeLink
                      (Some (mkApp sv svArg))
                      (exception_option (mkAppEx dv (translate Src Dst o svArg))))
          ))
    -> compObsLeLink s d.

Inductive compObsLeLinkN : nat -> Src -> Dst -> Prop :=
| sameObsLinkS : forall m (s : Src) (d : Dst),
    (forall (o:Opt) (sv:Src),
        s ⇓ sv
        -> (exists (dv:Dst),
              d ⇓ dv /\
              yesPreserved sv dv
              /\ (forall n:nat, liftLe (compObsLeLinkN m) (observeNthSubterm n sv) (observeNthSubterm n dv))
              /\ (questionHead  Abs sv = true -> forall svArg, goodTerm svArg ->
                   liftLe (compObsLeLinkN m)
                      (Some (mkApp sv svArg))
                      (exception_option (mkAppEx dv (translate Src Dst o svArg))))
          ))
    -> compObsLeLinkN (S m) s d
| sameObsLinkO : forall (s : Src) (d : Dst), compObsLeLinkN 0 s d.


(** this part is generally easy and unconditional *)
Lemma fromCoInd s d:
  compObsLeLink s d -> forall m, compObsLeLinkN m s d.
Proof using.
  intros Hc m. revert Hc. revert d. revert s.
  induction m as [ | m Hind]; intros ? ? Hc;
    [ constructor; fail | ].
  destruct Hc as [? ? Hc].
  constructor.
  intros o1 sv Hev. specialize (Hc o1 sv Hev).
  destruct Hc as [dv Hc]. repnd.
  exists dv. dands; eauto with certiclasses.
Qed.

Lemma toCoInd {dstDet: deterministicBigStep Dst}s d:
  (forall m, compObsLeLinkN m s d) -> compObsLeLink s d.
Proof using.
  revert d. revert s.
  cofix toCoInd.
  intros ? ? Hi.
  constructor.
  intros o ? Hev. pose proof Hi as Hib.
  specialize (Hi 1); inversion Hi as [ ? ? ? Hc | ]; subst. clear Hi.
  specialize (Hc o sv Hev).
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
    specialize (Hib o sv Hev).
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
    specialize (Hib o sv Hev).
    destruct Hib as [dvv Hib]. repnd.
    specialize (dstDet _ _ _ Hib0 Hc0). subst. clear Hib0 Hib2.
    specialize (Hib Hq _ Hg).
    rewrite  <- H0c0 in Hib.
    inverts Hib. assumption.
Qed.
        
Definition compObsPreservingLinkable :=
   ∀ (o: Opt) (s:Src),
    goodTerm s 
    -> liftLe compObsLeLink (Some s) (exception_option (translate Src Dst o s)).

End CompObsPreserving.

Class CerticoqLinkableTranslationCorrect {Src Dst : Type}
  `{CerticoqLinkableLanguage Src} 
  `{CerticoqLinkableLanguage Dst}
  `{CerticoqTranslation Src Dst}
  := 
{
  certiGoodPresLink : goodPreserving Src Dst;
  obsePresLink : compObsPreservingLinkable Src Dst;
}.


Global Arguments CerticoqLinkableTranslationCorrect
  {Src} {Dst} {H} {H0} {H1} {H2} {H3}  H4 {H5} {H6} {H7} {H8} {H9} H10 {H11}.

Notation "s ⊑ t" := (compObsLeLink _ _ s t) (at level 65).


Section ComposeLink.
Context (Src Inter Dst : Type)
        `{Ls: CerticoqLinkableLanguage Src}
        `{Li: CerticoqLinkableLanguage Inter}
        `{Ld: CerticoqLinkableLanguage Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}.


Lemma compObsLeLinkTransitive
      {Hgpsi : goodPreserving Src Inter}
      {Hgpid : goodPreserving Inter Dst}:
   forall   (s : Src) (i : Inter) (d : Dst),
  s ⊑ i
  -> i ⊑ d 
  -> s ⊑ d.
Proof.
  cofix compObsLeLinkTransitive.
  intros ? ? ? Ha Hb.
  inverts Ha as Hah.
  inverts Hb as Hbh.
  constructor; auto.
  intros o ? Hevs.
  destruct (Hah o _ Hevs) as [iv  Hci]. clear Hah.
  destruct Hci as [Hevi Hci].
  destruct Hci as [Hyesi Hsubi].
  destruct (Hbh o _ Hevi) as [dv  Hcd]. clear Hbh.
  destruct Hcd as [Hevd Hcd].
  destruct Hcd as [Hyesd Hsubd].
  exists dv. split;[ assumption|].
  assert (forall (A B: Prop), A -> (A-> B) -> A/\B) as Hp by (intros; tauto).
  apply Hp;[|intros Hyessd; split]; clear Hp;
    [eauto using (@yesPreservedTransitive Src Inter Dst) | | ];[|].
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
  unfold goodPreserving in *. 
  eapply Hgpsi with (o:=o) in Hgsv.
  unfold composeTranslation, translate in *.
  destruct (t1 o svArg) as [| ivArg];[inverts Heq|].
  simpl in *. inverts Heq.
  specialize (Hsubd ivArg Hgsv).
  inverts Hsubd as Hsubd Heq.
  destruct (t2 o ivArg) as [|dvArg ];[inverts Heq|].
  simpl in *. inverts Heq.
  constructor. eauto.
Qed.

Section obsLeN.
Variable n:nat.
Notation "s ⊑ t" := (compObsLeLinkN _ _  n s t) (at level 65).

(** same as as [compObsLeLinkTransitive] above *)
Lemma compObsLeLinkNTransitive
      {Hgpsi : goodPreserving Src Inter}
      {Hgpid : goodPreserving Inter Dst}:
   forall   (s : Src) (i : Inter) (d : Dst),
  s ⊑ i
  -> i ⊑ d 
  -> s ⊑ d.
Proof.
  induction n as [| m Hind];[ constructor |].
  intros ? ? ? Ha Hb.
  clear n. rename m into n.
  inverts Ha as Hah.
  inverts Hb as Hbh.
  constructor; auto.
  intros o ? Hevs.
  destruct (Hah o _ Hevs) as [iv  Hci]. clear Hah.
  destruct Hci as [Hevi Hci].
  destruct Hci as [Hyesi Hsubi].
  destruct (Hbh o _ Hevi) as [dv  Hcd]. clear Hbh.
  destruct Hcd as [Hevd Hcd].
  destruct Hcd as [Hyesd Hsubd].
  exists dv. split;[ assumption|].
  assert (forall (A B: Prop), A -> (A-> B) -> A/\B) as Hp by (intros; tauto).
  apply Hp;[|intros Hyessd; split]; clear Hp;
    [eauto using (@yesPreservedTransitive Src Inter Dst) | | ];[|].
- clear Hyesi Hyesd.
  intros m.
  apply proj1 in Hsubi.
  apply proj1 in Hsubd.
  specialize (Hsubi m).
  specialize (Hsubd m).
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
  unfold goodPreserving in *. 
  eapply Hgpsi with (o:=o) in Hgsv.
  unfold composeTranslation, translate in *.
  destruct (t1 o svArg) as [| ivArg];[inverts Heq|].
  simpl in *. inverts Heq.
  specialize (Hsubd ivArg Hgsv).
  inverts Hsubd as Hsubd Heq.
  destruct (t2 o ivArg) as [|dvArg ];[inverts Heq|].
  simpl in *. inverts Heq.
  constructor. eauto.
Qed.

End obsLeN.
Global Instance composeCerticoqLinkableTranslationCorrect
(* we don't need a translation for the value type, although typically Src=SrcValue*)
  {Ht1: CerticoqLinkableTranslationCorrect Ls Li}
  {Ht2: CerticoqLinkableTranslationCorrect Li Ld}
    : CerticoqLinkableTranslationCorrect Ls Ld.
Proof.
  destruct Ht1, Ht2.
  constructor; [eapply composePreservesGood; eauto; fail |].
  intros o ? Hgoods.
  specialize (obsePresLink0 o _ Hgoods).
  inverts obsePresLink0 as Hle Heq.
  unfold goodPreserving in *. 
  eapply certiGoodPresLink0 with (o:=o) in Hgoods.
  unfold composeTranslation, translate in *.
  destruct (t1 o s); compute in Hgoods; try contradiction.
  compute in Heq. inverts Heq.
  specialize (obsePresLink1 o _ Hgoods).
  inverts obsePresLink1 as Hlei Heqi.
  eapply certiGoodPresLink1 with (o:=o) in Hgoods.
  unfold composeTranslation, translate in *. simpl.
  destruct (t2 o i); compute in Hgoods; try contradiction.
  simpl.
  constructor.
  inverts Heqi.
  eapply compObsLeLinkTransitive; eauto.
  Unshelve. eauto. eauto.
Qed.

(* Outside this section, this definition should not depend at all on Src and Dst.*)
Definition leObsId : Inter -> Inter -> Prop :=  ((@compObsLeLink Inter Inter _ _ _ _ _ _ _ (fun o x => Ret x) _ _ )).

Definition eqObsId (a b : Inter) := leObsId a b /\ leObsId b a. 


Lemma sameValuesImpliesLeObsId a b: sameValues a b -> leObsId a b.
Proof using.
  revert a b. cofix sameValuesImpliesLeObsId.
  intros ? ? Hs. constructor. intros o sv Hsv.
  specialize (proj1 (Hs _) Hsv). intros Hsvb.
  exists sv. dands; auto; try reflexivity.
- intros. apply liftLeRimpl with (R1:= sameValues); auto.
  apply liftLeRefl. unfold Reflexive, sameValues. reflexivity.
- intros. simpl. constructor. apply sameValuesImpliesLeObsId.
  unfold Reflexive, sameValues. reflexivity.
Qed.

Lemma sameValuesImpliesEqObsId a b: sameValues a b -> eqObsId a b.
Proof using Dst H4 H5 H6 H7 H8 Inter Src t1 t2.
  intros Hs. split; apply sameValuesImpliesLeObsId; auto.
  unfold Reflexive, sameValues in *. firstorder.
Qed.


Local Instance compObsLeLinkRespectsEval:
  Proper (eq ==> bigStepEval  ==> Basics.impl) (@compObsLeLink Src Inter _ _ _ _ _ _ _ _ _ _ ).
Proof using.
  intros s1 s2 Heqs d1 d2 Hsvd Hs1. subst.
  constructor.
  intros ? Heval.
  (* need that the second arg of bigStepeval is terminal *)
Abort.

End ComposeLink.



Arguments eqObsId {Inter} {H4} {H5} {H6} {H7} {H8}.
Arguments leObsId {Inter} {H4} {H5} {H6} {H7} {H8}.

Section LinkObsProper.
Context {Src Dst : Type}
        `{Ls: CerticoqLinkableLanguage Src}
        `{Ld: CerticoqLinkableLanguage Dst}.
Lemma compObsLeLink_proper_Feq t1 t2:
  (forall o s, t1 o s =  t2 o s) -> forall a b,
  (@compObsLeLink Src Dst _ _ _ _ _ _ _ t1 _ _ ) a b 
  -> (@compObsLeLink Src Dst _ _ _ _ _ _ _ t2 _ _ ) a b.
Proof using.
  intros feq.
  cofix compObsLeLink_proper_Feq.
  intros ? ? Hl.
  constructor. invertsn Hl.
  intros o sv Hev. specialize (Hl o sv Hev). exrepnd.
  exists dv. dands; eauto using  liftLeRimpl;[].
  intros Hq sva Hga. specialize (Hl0 Hq sva Hga). unfold translate in *.
  rewrite <- feq. simpl in *.
  eauto using liftLeRimpl.
Qed.

(* proof same as above *)
Lemma compObsLeLinkN_proper_Feq t1 t2:
  (forall o s, t1 o s =  t2 o s) -> forall n a b,
  (@compObsLeLinkN Src Dst _ _ _ _ _ _ _ t1  _ _ n) a b 
  -> (@compObsLeLinkN Src Dst _ _ _ _ _ _ _ t2  _ _ n) a b.
Proof using.
  intros feq n.  induction n;[ constructor |].
  intros ? ? Hl.
  constructor. invertsn Hl.
  intros o sv Hev. specialize (Hl o sv Hev). exrepnd.
  exists dv. dands; eauto using  liftLeRimpl;[].
  intros Hq sva Hga. specialize (Hl0 Hq sva Hga). unfold translate in *.
  rewrite <- feq. simpl in *.
  eauto using liftLeRimpl.
Qed.

Context {t : CerticoqTranslation Src Dst}
        {tg: goodPreserving Src Dst}.


  
Lemma compObsLeLinkRespectsLe:
  Proper ((Basics.flip leObsId) ==> leObsId ==> Basics.impl) (@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  ).
Proof using tg.
  intros l1 l2 Heql r1 r2 Heqr Hc.
  unfold leObsId, Basics.flip in *.
  eapply compObsLeLinkTransitive with (t1:= fun o x => Ret x); eauto;
    [apply goodPreservingId| ].
  eapply compObsLeLinkTransitive with (t2:= fun o x => Ret x) in Hc; eauto; try assumption;
    [|apply goodPreservingId];[].
  eapply compObsLeLink_proper_Feq;[| exact Hc].
  intros o s. unfold composeTranslation, translate.
  destruct (t o s); reflexivity.
Qed.

Lemma compObsLeLinkNRespectsLe n:
  Proper ((Basics.flip leObsId) ==> leObsId ==> Basics.impl) (@compObsLeLinkN  Src Dst _ _ _ _ _ _ _ _ _ _ n ).
Proof using tg.
  intros l1 l2 Heql r1 r2 Heqr Hc.
  unfold leObsId, Basics.flip in *.
  apply fromCoInd with (m:=n)in Heql.
  apply fromCoInd with (m:=n)in Heqr.
  eapply compObsLeLinkNTransitive with (t1:= fun s x => Ret x); eauto;
    [apply goodPreservingId|].
  eapply compObsLeLinkNTransitive with (t2:= fun s x => Ret x) in Hc; eauto; try assumption;
    [|apply goodPreservingId];[].
  eapply compObsLeLinkN_proper_Feq;[| exact Hc].
  intros o s. unfold composeTranslation, translate. destruct (t o s); reflexivity.
Qed.

Global Instance compObsLeLinkRespectsEqObs:
  Proper (eqObsId ==> eqObsId ==> iff) (@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  ).
Proof using tg.
  intros  ? ? Hleq ? ? Hreq. unfold eqObsId in *. repnd.
  split; apply compObsLeLinkRespectsLe; auto.
Qed.

Global Instance compObsLeLinkNRespectsEqObs n :
  Proper (eqObsId ==> eqObsId ==> iff) (@compObsLeLinkN Src Dst _ _ _ _ _ _ _ _ _ _ n).
Proof using tg.
  intros  ? ? Hleq ? ? Hreq. unfold eqObsId in *. repnd.
  split; apply compObsLeLinkNRespectsLe; auto.
Qed.


Global Instance  compObsLeLinkRespectsSameVal:
  Proper (sameValues ==> sameValues ==> iff) (@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  ).
Proof using H5 tg.
  intros ? ? ? ? ? ?.
  apply compObsLeLinkRespectsEqObs.
  eapply sameValuesImpliesEqObsId; try eassumption.
  exact (fun o x => Ret x). 
  eapply sameValuesImpliesEqObsId; try eassumption.
  exact (fun o x => Ret x). 
Qed.

Global Instance  compObsLeLinkNRespectsSameVal n:
  Proper (sameValues ==> sameValues ==> iff) (@compObsLeLinkN Src Dst _ _ _ _ _ _ _ _ _ _ n).
Proof using H5 tg.
  intros ? ? ? ? ? ?.
  apply compObsLeLinkNRespectsEqObs; eapply sameValuesImpliesEqObsId; try eassumption;
  exact (fun o x => Ret x). 
Qed.

End LinkObsProper.

Section EqObsEquiv.
Context {Src Dst : Type}
        `{Ls: CerticoqLinkableLanguage Src}.

Global Instance compObsLeLinkSymm:
  Symmetric eqObsId.
Proof using.
  intros x y. unfold eqObsId. tauto.
Qed.

Global Instance sameValuesEquiv:
  Equivalence sameValues.
Proof using.
  constructor; unfold sameValues;
    intros x; firstorder.
Qed.

Global Instance compObsLeLinkRefl:
  Reflexive leObsId.
Proof using.
  intros x. apply sameValuesImpliesLeObsId. reflexivity.
Qed.

Global Instance compObsEqLinkRefl:
  Reflexive eqObsId.
Proof using.
  intros x. split; reflexivity.
Qed.

Global Instance compObsLeLinkEquiv:
  Equivalence eqObsId.
Proof using.
  constructor; eauto with typeclass_instances.
  intros ? ? ? H1eq  H2eq. unfold eqObsId, leObsId.
  split.
- eapply compObsLeLinkRespectsEqObs;[apply compObsEqLinkRefl| symmetry; eauto
                                       | unfold eqObsId in *; tauto].
- eapply compObsLeLinkRespectsEqObs; [apply compObsEqLinkRefl|  eauto
                                      | unfold eqObsId in *; tauto].
Unshelve.
  apply goodPreservingId.
  apply goodPreservingId.
Qed.

End EqObsEquiv.

Section LinkingIllustration.
Context {Src Dst : Type}
        `{Ls: CerticoqLinkableLanguage Src}
        `{Ld: CerticoqLinkableLanguage Dst}
        {comp1 : CerticoqTranslation Src Dst}
        {Ht1: CerticoqLinkableTranslationCorrect Ls Ld}.

(** Suppose [f] computes to a function (lambda) [fv] in the [Src] language *)
Variable (o:Opt).
Variable f:Src.
Variable fv:Src.
Hypothesis fcomputes: f ⇓ fv.
Hypothesis flam : questionHead Abs fv = true. (** [fv] may say yes to other questions as well *)

(** [f] compiles to [fd] *)
Variable fd:Dst.
Hypothesis compilef : translate Src Dst o f = Ret fd.

(** [fd] computes to [fdv] *)
Variable fdv:Dst.
Hypothesis compilefd : fd ⇓ fdv.

(** Now consider an argument [t] to [f] in Src. *)
Variable t:Src.

Notation "s ⊑ t" := (compObsLeLink _ _ s t) (at level 65).

(** Suppose we SEPARATELY [t] compile by the SAME compiler it to get [td] *)
Variable td:Dst.
Section SameCompiler.
Hypothesis compilet : translate Src Dst o t = Ret td.


(** The destination language has a notion of application. Consider the destination term: *)
Let fdtd := mkApp fdv td.


(** We would like [fdtd] be be observationally equal to [mkApp fv t], which is an easy
corrollary of the linkable correctness property: *)
Corollary fdtdCorrect {dd : deterministicBigStep Dst}
  : goodTerm f -> goodTerm t -> mkApp fv t  ⊑ mkApp fdv td.
Proof.
  intros Hgf Hgt.
  destruct Ht1.
  specialize (obsePresLink0 o f Hgf).
  rewrite compilef in obsePresLink0. simpl in *.
  invertsn obsePresLink0.
  invertsn obsePresLink0.
  specialize (obsePresLink0 o fv fcomputes).
  exrepnd. clear obsePresLink2 obsePresLink3.
  unfold deterministicBigStep in dd.
  apply dd with (v2:= fdv) in obsePresLink0;[ subst | assumption].
  specialize (obsePresLink1 flam t Hgt).
  rewrite compilet in obsePresLink1. simpl in obsePresLink1.
  invertsn obsePresLink1. assumption.
Qed.
End SameCompiler.

Definition appArgCongr : Prop :=
  forall (ff tt1 tt2: Dst),
    (* consider adding this:  goodTerm ff -> , which will need ⇓ to be goodpreserving*)
     goodTerm tt1
    -> goodTerm tt2
    -> leObsId tt1 tt2
    -> leObsId (mkApp ff tt1) (mkApp ff tt2).

Section ManualTargetArgTargetRel.
(** Now suppose, we use DIFFERENT compiler to compile [td]. First, we
list the needed properties for the other compiler [comp2] *)

Hypothesis mkAppCongrLe : appArgCongr.

Lemma mkAppCongr : forall (ff tt1 tt2: Dst),
    (* consider adding this:  goodTerm ff -> , which will need ⇓ to be goodpreserving*)
     goodTerm tt1
    -> goodTerm tt2
    -> eqObsId tt1 tt2
    -> eqObsId (mkApp ff tt1) (mkApp ff tt2).
Proof using mkAppCongrLe.
  intros ff ? ? H1g H2g ?.
  specialize (mkAppCongrLe ff).
  unfold eqObsId in *. repnd.
  eauto.
Qed.

#[global] Instance mkAppRW : Proper (eq ==> eqObsId ==> eqObsId) (@mkApp Dst _).
Proof using.
  intros ? ? ? ? ? ?. subst.
  apply mkAppCongr.
  (* need goodTerm *)
Abort.

Hypothesis compilet :  (@translate Src Dst comp1 o t) = Ret td.
(** Suppose that instead of td, we wish to use another term td', which we produced manually
or by magic. We also proved that it is a good term and is greater than td *)
Variable td':Dst.
Hypothesis td'good: goodTerm td'.
Hypothesis td'Le : leObsId td td'.

(** Again, consider the application term in the destination language, where the function
  and the arg are compiled by different compilers *)
Let fdtd := mkApp fdv td'.


(** Again, we would like [fdtd] be be observationally equal to [mkApp fv t], which is a
corrollary of the linkable correctness property: *)
Corollary fdtdCorrectDiff {dd : deterministicBigStep Dst}
  : goodTerm f -> goodTerm t -> mkApp fv t  ⊑ mkApp fdv td'.
Proof.
  intros Hgf Hgt.
  destruct Ht1.
  specialize (obsePresLink0 o f Hgf).
  rewrite compilef in obsePresLink0. simpl in *.
  invertsn obsePresLink0.
  invertsn obsePresLink0.
  specialize (obsePresLink0 o fv fcomputes).
  exrepnd. clear obsePresLink2 obsePresLink3.
  unfold deterministicBigStep in dd.
  apply dd with (v2:= fdv) in obsePresLink0;[ subst | assumption].
  specialize (obsePresLink1 flam t Hgt).
  pose proof certiGoodPresLink0 as Hgpb.
  specialize (certiGoodPresLink0 t o Hgt).
  rewrite compilet in *. simpl in *.
  invertsna obsePresLink1 Hinvf.
  apply (mkAppCongrLe fdv) in td'Le; eauto;[].
  eapply compObsLeLinkRespectsLe; [reflexivity | apply td'Le |].
  exact Hinvf.
  Unshelve. assumption.
Qed.

End ManualTargetArgTargetRel.

(** 
Similar to the above section, except that the manually produced target argument [td']
has to be proved to be related to the corresponding [Src] term [t] instead of the
compilation result [td]. This was requested by Andrew Appel.
*)
Section ManualTargetArgSrcRel.

  (** In this section, this is all we know about [td]. We dont anymore have the hypothesis
  that [td] was obtained from compiling [t] *)
  Hypothesis argRelated :  t ⊑ td.
  Hypothesis tdGood :  goodTerm td.

  Hypothesis mkAppCongrLe : appArgCongr.

Corollary fdtdCorrectDiff {dd : deterministicBigStep Dst}
  : goodTerm f -> goodTerm t -> mkApp fv t  ⊑ mkApp fdv td.
Proof.
  intros Hgf Hgt.
  destruct Ht1.
  specialize (obsePresLink0 o f Hgf).
  rewrite compilef in obsePresLink0. simpl in *.
  invertsn obsePresLink0.
  invertsn obsePresLink0.
  specialize (obsePresLink0 o fv fcomputes).
  exrepnd. clear obsePresLink2 obsePresLink3.
  unfold deterministicBigStep in dd.
  apply dd with (v2:= fdv) in obsePresLink0;[ subst | assumption].
  specialize (obsePresLink1 flam t Hgt).
  pose proof certiGoodPresLink0 as Hgpb.
  specialize (certiGoodPresLink0 t o Hgt).
  destruct Ht1.
  specialize (obsePresLink0 o t Hgt).
  destruct (@translate Src Dst comp1 o t) as [| tdc]; try contradiction.
  simpl in *.
  invertsna obsePresLink1 Hinvf.
  invertsna obsePresLink0 Hinvt.
  (** 
   [Hinvf] is what we get from using the correctness property of the compiler, instantiated
   for the function [f]. We have to somehow replace [tdc] by [td] there. 
   Recall that [tdc] is the result of compiling [td]. 

   The only way to use [mkAppCongr], which is congruence in [Dst],
   is to show that [tdc ⊑ td].
   We may, however, choose to have a different assumption instead of [mkAppCongr].
 *)
  
  eapply compObsLeLinkRespectsLe; [reflexivity | apply (mkAppCongrLe _ tdc _) | ]; auto.

(** 
This goal seems unprovable. We have both [t ⊑ tdc] and [t ⊑ td].
That says nothing about the ordering between [tdc] and [td]. 
*)
  
Abort.

End ManualTargetArgSrcRel.

End LinkingIllustration.

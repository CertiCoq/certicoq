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

(* Outside this section, this definition should not depend at all on Src and Dst.*)
Definition leObsId : Inter -> Inter -> Prop :=  ((@compObsLeLink Inter Inter _ _ _ _ _ _ _ (fun x => Ret x) _ _ )).

Definition eqObsId (a b : Inter) := leObsId a b /\ leObsId b a. 


Lemma sameValuesImpliesLeObsId a b: sameValues a b -> leObsId a b.
Proof using.
  revert a b. cofix.
  intros ? ? Hs. constructor. intros sv Hsv.
  specialize (proj1 (Hs _) Hsv). intros Hsvb.
  exists sv. dands; auto; try reflexivity.
- intros. apply liftLeRimpl with (R1:= sameValues); auto.
  apply liftLeRefl. unfold Reflexive, sameValues. reflexivity.
- intros. simpl. constructor. apply sameValuesImpliesLeObsId.
  unfold Reflexive, sameValues. reflexivity.
Qed.

Lemma sameValuesImpliesEqObsId a b: sameValues a b -> eqObsId a b.
Proof using.
  intros Hs. split; apply sameValuesImpliesLeObsId; auto.
  unfold Reflexive, sameValues in *. firstorder.
Qed.


Local Instance  compObsLeLinkRespectsEval:
  Proper (eq ==> bigStepEval  ==> Basics.impl) ((@compObsLeLink Src Inter _ _ _ _ _ _ _ _ _ _  )).
Proof using.
  intros s1 s2 Heqs d1 d2 Hsvd Hs1. subst.
  constructor.
  intros ? Heval.
  (* need that the second arg of bigStepeval is terminal *)
Abort.

End ComposeLink.


Lemma goodPreservingId {Src:Type} {Hg: GoodTerm Src}:
  @goodPreserving Src Src (fun x => Ret x) _ _.
Proof using.
  intros ? ?.
  simpl. assumption.
Qed.
Arguments eqObsId {Inter} {H4} {H5} {H6} {H7} {H8}.
Arguments leObsId {Inter} {H4} {H5} {H6} {H7} {H8}.

Section LinkObsProper.
Context {Src Dst : Type}
        `{Ls: CerticoqLinkableLanguage Src}
        `{Ld: CerticoqLinkableLanguage Dst}.
Lemma compObsLeLink_proper_Feq t1 t2:
  (forall s,  t1 s =  t2 s) -> forall a b,
  (@compObsLeLink Src Dst _ _ _ _ _ _ _ t1 _ _ ) a b 
  -> (@compObsLeLink Src Dst _ _ _ _ _ _ _ t2 _ _ ) a b.
Proof using.
  intros feq.
  cofix.
  intros ? ? Hl.
  constructor. invertsn Hl.
  intros sv Hev. specialize (Hl sv Hev). exrepnd.
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
  eapply compObsLeLinkTransitive with (t1:= fun x => Ret x); eauto;
    [apply goodPreservingId| ].
  eapply compObsLeLinkTransitive with (t2:= fun x => Ret x) in Hc; eauto; try assumption;
    [|apply goodPreservingId];[].
  eapply compObsLeLink_proper_Feq;[| exact Hc].
  intros. unfold composeTranslation, translate. destruct (t s); reflexivity.
Qed.
  
Global Instance compObsLeLinkRespectsEqObs:
  Proper (eqObsId ==> eqObsId ==> iff) (@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  ).
Proof using tg.
  intros  ? ? Hleq ? ? Hreq. unfold eqObsId in *. repnd.
  split; apply compObsLeLinkRespectsLe; auto.
Qed.


Local Instance  compObsLeLinkRespectsSameVal:
  Proper (sameValues ==> sameValues ==> iff) (@compObsLeLink Src Dst _ _ _ _ _ _ _ _ _ _  ).
Proof using H5 tg.
  intros ? ? ? ? ? ?.
  apply compObsLeLinkRespectsEqObs; apply sameValuesImpliesEqObsId; assumption.
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

Global Instance compObsLeLinkRefl:
  Reflexive leObsId.
Proof using.
  intros x. apply sameValuesImpliesLeObsId. unfold sameValues. reflexivity.
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
Variable f:Src.
Variable fv:Src.
Hypothesis fcomputes: f ⇓ fv.
Hypothesis flam : questionHead Abs fv = true. (** [fv] may say yes to other questions as well *)

(** [f] compiles to [fd] *)
Variable fd:Dst.
Hypothesis compilef : translate Src Dst f = Ret fd.

(** [fd] computes to [fdv] *)
Variable fdv:Dst.
Hypothesis compilefd : fd ⇓ fdv.

(** Now consider an argument [t] to [f] in Src. *)
Variable t:Src.

Notation "s ⊑ t" := (compObsLeLink _ _ s t) (at level 65).

(** Suppose we SEPARATELY [t] compile by the SAME compiler it to get [td] *)
Variable td:Dst.
Section SameCompiler.
Hypothesis compilet : translate Src Dst t = Ret td.


(** The destination language has a notion of application. Consider the destination term: *)
Let fdtd := mkApp fdv td.


(** We would like [fdtd] be be observationally equal to [mkApp fv t], which is an easy
corrollary of the linkable correctness property: *)
Corollary fdtdCorrect {dd : deterministicBigStep Dst}
  : goodTerm f -> goodTerm t -> mkApp fv t  ⊑ mkApp fdv td.
Proof.
  intros Hgf Hgt.
  destruct Ht1.
  specialize (obsePresLink0 f Hgf).
  rewrite compilef in obsePresLink0. simpl in *.
  invertsn obsePresLink0.
  invertsn obsePresLink0.
  specialize (obsePresLink0 fv fcomputes).
  exrepnd. clear obsePresLink2 obsePresLink3.
  unfold deterministicBigStep in dd.
  apply dd with (v2:= fdv) in obsePresLink0;[ subst | assumption].
  specialize (obsePresLink1 flam t Hgt).
  rewrite compilet in obsePresLink1. simpl in obsePresLink1.
  invertsn obsePresLink1. assumption.
Qed.
End SameCompiler.

Section DiffCompiler.
(** Now suppose, we use DIFFERENT compiler to compile [td]. First, we
list the needed properties for the other compiler [comp2] *)

Variable (comp2 : CerticoqTranslation Src Dst).

(** on good inputs, the compilers produce observationally equivalent outputs. *)
Hypothesis c2Equiv :
  forall s:Src, goodTerm s
           -> liftExc leObsId (@translate _ _ comp1 s) (@translate _ _ comp2 s).

Hypothesis mkAppCongrLe : forall (ff tt1 tt2: Dst),
    (* consider adding this:  goodTerm ff -> , which will need ⇓ to be goodpreserving*)
     goodTerm tt1
    -> goodTerm tt2
    -> leObsId tt1 tt2
    -> leObsId (mkApp ff tt1) (mkApp ff tt2).

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

Instance mkAppRW : Proper (eq ==> eqObsId ==> eqObsId) (@mkApp Dst _).
Proof using.
  intros ? ? ? ? ? ?. subst.
  apply mkAppCongr.
  (* need goodTerm *)
Abort.

Hypothesis compilet : @translate Src Dst comp2 t = Ret td.

(** Again, consider the application term in the destination language, where the function
  and the arg are compiled by different compilers *)
Let fdtd := mkApp fdv td.

Notation "s ⊑ t" := (@compObsLeLink _ _ _ _ _ _ _ _ _ comp1  _ _ s t) (at level 65).

(** Again, we would like [fdtd] be be observationally equal to [mkApp fv t], which is a
corrollary of the linkable correctness property: *)
Corollary fdtdCorrectDiff {dd : deterministicBigStep Dst} {fp2 : @goodPreserving Src Dst comp2 _ _}
  : goodTerm f -> goodTerm t -> mkApp fv t  ⊑ mkApp fdv td.
Proof.
  intros Hgf Hgt.
  destruct Ht1.
  specialize (obsePresLink0 f Hgf).
  rewrite compilef in obsePresLink0. simpl in *.
  invertsn obsePresLink0.
  invertsn obsePresLink0.
  specialize (obsePresLink0 fv fcomputes).
  exrepnd. clear obsePresLink2 obsePresLink3.
  unfold deterministicBigStep in dd.
  apply dd with (v2:= fdv) in obsePresLink0;[ subst | assumption].
  specialize (obsePresLink1 flam t Hgt).
  pose proof certiGoodPresLink0 as Hgpb.
  specialize (certiGoodPresLink0 t Hgt).
  specialize (c2Equiv t Hgt).
  destruct (@translate Src Dst comp1 t); try contradiction.
  specialize (fp2 t Hgt). rewrite compilet in fp2.
  simpl in obsePresLink1. rewrite compilet in c2Equiv. simpl in c2Equiv.
  apply mkAppCongrLe  with (ff:=fdv) in c2Equiv; eauto;[].
  invertsna obsePresLink1 Hinv.
  eapply compObsLeLinkRespectsLe; [reflexivity | apply c2Equiv |].
  exact Hinv.
  Unshelve. assumption.
Qed.

End DiffCompiler.
End LinkingIllustration.

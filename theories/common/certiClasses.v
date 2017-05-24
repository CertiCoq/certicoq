Require Import Common.exceptionMonad.
Require Import Common.AstCommon.
Require Import Coq.Unicode.Utf8.

CoInductive liftLe {S D: Type} (R: S -> D -> Prop): option S -> option D -> Prop :=
(* defining this using pattern matching confuses the strict positivity checker.
  Can this part be defined outside generically, using induction? *)
| liftSome: forall s d, R s d -> liftLe R (Some s) (Some d)
| liftNone: forall d, liftLe R None d.

Hint Constructors liftLe : certiclasses.

(** is this defined in the Coq standard library of ExtLib? *)
Definition Rimpl {S D: Type} (R1 R2: S -> D -> Prop) :=
  forall s d, R1 s d -> R2 s d.

Require Import SquiggleEq.LibTactics.
(** Could have used RImpl for the conclusion as well, Coq's hint search is not so good
 at unfolding definitions. *)
Lemma  liftLeRimpl {S D: Type} (R1 R2: S -> D -> Prop) os od:
  Rimpl R1 R2 -> liftLe R1 os od -> liftLe R2 os od.
Proof.
  intros Hr Hl.
  inverts Hl; constructor.
  apply Hr. assumption.
Defined.

Hint Resolve liftLeRimpl : certiclasses.

(* This operations picks out the "good" terms in the language.
 All bets are off about the terms that are not good *)
Class GoodTerm (Term: Type) := goodTerm : Term  -> Prop.

Generalizable Variables Src Dst Inter Term Value SrcValue DstValue InterValue.

(** A [Term] can contain an environment embedded in it. *)
Class BigStepOpSem (Term Value:Type) := bigStepEval: Term -> Value -> Prop.


Require Import String.

(* one can use ⇓ to refer to the big step eval relation *)
Notation "s ⇓ t" := (bigStepEval s t) (at level 70).

Definition sameValues {Term:Type}
  `{BigStepOpSem Term} (a b : Term)
:= forall (v: Value), a ⇓ v <-> b ⇓ v.

Inductive bigStepResult (Term Value:Type) :=
| Result : Value -> bigStepResult Term Value
| OutOfTime : Term -> bigStepResult Term Value
| Error : string -> option Term -> bigStepResult Term Value.

Class BigStepOpSemExec (Term Value:Type)
  := bigStepEvaln: nat -> Term -> bigStepResult Term Value.

Arguments Result {Term} {Value} v.
Arguments OutOfTime {Term} {Value} e.
Arguments Error {Term} {Value} s.

Require Import ExtLib.Structures.Monads.

(** for an example usage of this monad, see eval_n in L4_deBruijn/L4_5_to_L5.v *)
Global Instance Monad_bigStepResult (Term :Type): Monad (bigStepResult Term) :=
{ ret := @Result Term
; bind := fun _ _ r f => match r with
                             | Result v => f v
                             | OutOfTime t => OutOfTime t
                             | Error s ot => Error s ot
                           end
}.



Definition mapBigStepRes {T1 V1 T2 V2 : Type}
           (ft : T1 -> T2)
           (fv : V1 -> V2)
           (tr : bigStepResult T1 V1) : bigStepResult T2 V2 :=
  match tr with
  | Result v => Result (fv v)
  | OutOfTime t => OutOfTime (ft t)
  | Error s t => Error s (option_map ft t)
  end.


Definition injectOption {Term V:Type} (oa : option V) : bigStepResult Term V :=
  match oa with
  | Some v => Result v
  | None => Error "None" None
  end.               
  

Class BigStepOpSemExecCorrect {Term Value:Type}
      {bs: BigStepOpSem Term Value} (bse: BigStepOpSemExec Term Value) :=
  { (** weaken = to a custom equality, which can be instantiated, e.g. by alpha equality? *)
    bseSound: forall n e v, bigStepEvaln n e = Result v -> e ⇓ v;
    bseComplete: forall e v, e ⇓ v -> exists n, bigStepEvaln n e = Result v
  }.
      

Instance liftBigStepException `{BigStepOpSem Term Value} 
  : BigStepOpSem (exception Term) (exception Value) :=
λ (s : exception Term) (sv : exception Value),
match (s, sv) with
| (Ret s, Ret sv) => s ⇓ sv
| (_,_) => False
end.

Definition liftExc {T:Type} (R: T->T->Prop) (oa1 oa2 : exception T) :=
  match oa1, oa2 with
  | Ret a1, Ret a2 => R a1 a2
  | _,_ => False
  end.

Class CerticoqTranslation (Src Dst : Type) : Type
  := translate : Src -> exception Dst.

Class CerticoqTotalTranslation (Src Dst : Type) : Type
  := translateT : Src -> Dst.

Arguments translate  Src Dst {CerticoqTranslation} s.
Arguments translateT  Src Dst {CerticoqTotalTranslation} s.

Instance liftTotal `{CerticoqTotalTranslation Src Dst} : CerticoqTranslation Src Dst :=
  fun (x:Src) => Ret (translateT Src Dst x). 


Definition goodPreserving `{CerticoqTranslation Src Dst}
    `{GoodTerm Src} `{GoodTerm Dst} : Prop := 
  ∀ (s: Src), 
    goodTerm s 
    -> match translate Src Dst s with
      | Ret t => goodTerm t
      | Exc _ => False
      end.

Arguments goodPreserving Src Dst {H} {H0} {H1}.

Definition bigStepPreserving `{CerticoqTranslation Src Dst} 
  `{CerticoqTranslation SrcValue DstValue}
   `{BigStepOpSem Src SrcValue} `{BigStepOpSem Dst DstValue} `{GoodTerm Src}
  :=
   ∀ (s:Src) (sv: SrcValue), 
    goodTerm s 
    -> s ⇓ sv
    -> (translate Src Dst s) ⇓ (translate SrcValue DstValue sv).

Arguments bigStepPreserving Src Dst {H} {SrcValue} {DstValue} {H0} {H1} {H2} {H3}.

Require Import Common.exceptionMonad.

Global Instance composeTranslation `{CerticoqTranslation Src Inter} 
  `{CerticoqTranslation Inter Dst} :
  `{CerticoqTranslation Src Dst} :=
λ s, bind (translate Src Inter s) (translate Inter Dst).


Lemma composePreservesGood (Src Inter Dst: Type)
  {goodi: GoodTerm Inter}
  {goods: GoodTerm Src}
  {goodt: GoodTerm Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst} :
goodPreserving Src Inter
-> goodPreserving Inter Dst
-> goodPreserving Src Dst.
Proof.
  intros Hsi Hit s Hs.
  apply Hsi in Hs.
  unfold composeTranslation, bind.
  unfold translate in *.
  destruct (t1 s); [contradiction|].
  apply Hit in Hs.
  unfold translate in *.
  assumption.
Qed.


Section obsPreserving.
Context (Src Dst: Type) {SrcValue DstValue: Type}
          (VR: SrcValue -> DstValue -> Prop).
Notation "s ⊑ t" := (VR s t) (at level 65).

(* Similar to what Zoe suggested on Wed, Aug 17, 2016 at 8:57 AM *)
Definition obsPreserving 
  `{CerticoqTranslation Src Dst} 
   `{BigStepOpSem Src SrcValue} `{BigStepOpSem Dst DstValue} `{GoodTerm Src}
  :=
   ∀ (s:Src) (sv: SrcValue), 
    goodTerm s 
    -> (s ⇓ sv)
    -> ∃ (dv: DstValue), (translate Src Dst s) ⇓ (Ret dv) ∧ sv ⊑ dv.
End obsPreserving.

(* 
Notation "s =⊏  t" := (obsLe StrongObservation s t) (at level 65). 
*)

(*
Arguments CerticoqTranslationCorrect2 NonTrivObservation
  Src {SrcValue} {H} {H0} {H1} {H2} {H3} Dst {DstValue} {H4} {H5} {H6} {H7} {H8} {H9}.
Arguments CerticoqLanguage2 Term Value {H} {H0} {H1} {H2}.
Arguments obsPreserving Src Dst {H} {SrcValue} {H0} {DstValue} {H1} {H2} {H3} {H4} {H5} {H6}.
*)


Definition normalizes `{BigStepOpSem Term Value} (s:Term): Prop :=
  ∃ (sv : Value) , s ⇓ sv.


(* Todo : generalize over Coq.Init.Logic.eq. *)
Definition deterministicBigStep `{BigStepOpSem Term Value} :=
∀ (s :Term) (v1 v2 : Value), s ⇓ v1 -> s ⇓ v2 -> v1 = v2.

Arguments deterministicBigStep Term {Value} {H}.

Definition totalTranslation `{CerticoqTranslation Src Dst} : Prop :=
  ∀ (s:Src), 
match translate Src Dst s with
| Ret _ => True
| Exc _ => False
end.


Lemma deterministicBigStepLiftExc `{BigStepOpSem Term Value}:
  deterministicBigStep Term
  -> deterministicBigStep (exception Term).
Proof.
  intros Hd ? ? ? He1 He2.
  destruct s, v1, v2; compute in He1; compute in He2; try contradiction.
  f_equal.
  unfold deterministicBigStep in Hd.
  eapply Hd; eauto.
Qed.


(* ( * ) in Randy's email dated Tue, May 31, 2016 at 10:35 PM EST 
*) 

Definition bigStepReflecting `{CerticoqTranslation Src Dst}
  `{CerticoqTranslation SrcValue DstValue}  
   `{BigStepOpSem Src SrcValue} `{BigStepOpSem Dst DstValue} 
   (s:Src)
    : Prop :=
 ∀ (dv: DstValue), 
    (translate Src Dst s) ⇓ (Ret dv)
    -> ∃ (sv:SrcValue), s ⇓ sv ∧ Ret dv = translate SrcValue DstValue sv.


Section obsPreserving2.
Context (Src Dst : Type) {SrcValue DstValue : Type} (VR : SrcValue -> DstValue -> Prop).
Notation "s ⊑ t" := (VR s t) (at level 65).

(* Similar to the new +, except this one does not enforce preservation of non-termination *)
Definition obsReflecting `{CerticoqTranslation Src Dst}
   `{BigStepOpSem Src SrcValue} `{BigStepOpSem Dst DstValue} 
   (s:Src)
    : Prop :=
 ∀ (dv: DstValue), 
    (translate Src Dst s) ⇓ (Ret dv)
    -> ∃ (sv:SrcValue), s ⇓ sv ∧ sv ⊑ dv .
    
End obsPreserving2.

Arguments bigStepReflecting Src Dst {H} {SrcValue} {DstValue} {H0} {H1} {H2} s.


Lemma bigStepPreservingReflecting 
  `{CerticoqTranslation Src Dst}
  `{CerticoqTranslation SrcValue DstValue}
  `{GoodTerm Src}
  `{GoodTerm Dst}
  `{BigStepOpSem Src SrcValue}
  `{BigStepOpSem Dst DstValue}
  {_:bigStepPreserving Src Dst} :
  (deterministicBigStep Dst)
  -> ∀ (s:Src), 
    goodTerm s
    -> normalizes s
    -> bigStepReflecting Src Dst s.
Proof.
  intros Hd ? Hp Hn ? Ht.
  destruct Hn as [d  Hn].
  exists d. split;[assumption|].
  apply deterministicBigStepLiftExc in Hd.
  eauto.
(* info eauto : 
eapply Hd.
 exact Ht.
 apply preservesEval0.
  exact Hp.
  exact Hn.
*)
Qed.

Lemma obsPreservingReflecting 
  `{CerticoqTranslation Src Dst}
  `{GoodTerm Src}
  `{GoodTerm Dst}
  `{BigStepOpSem Src SrcValue}
  `{BigStepOpSem Dst DstValue}
  (RV : SrcValue → DstValue → Prop)
  {Ho:obsPreserving Src Dst RV} : (* * *)
  (deterministicBigStep Dst)
  -> ∀ (s:Src), 
    goodTerm s
    -> normalizes s
    -> obsReflecting Src Dst RV s. (* + *)
Proof.
  intros Hd ? Hp Hn ? Ht.
  destruct Hn as [sv  Hn].
  pose proof Hn as Hnb.
  eapply Ho in Hn;[| assumption].
  destruct Hn as [dvv Hn].
  destruct Hn as [Hnt  Hnr].
  apply deterministicBigStepLiftExc in Hd.
  specialize (Hd _ _ _ Hnt Ht).
  inversion Hd. subst. clear Hd.
  exists sv. split; assumption.
Qed.



Require Import SquiggleEq.UsefulTypes.
Require Import Template.Ast.

Global Instance EqDecInd : Deq inductive.
eapply @deqAsSumbool.
unfold DeqSumbool. intros.
unfold DecidableSumbool.
repeat decide equality.
Defined.

Lemma goodPreservingId {Src:Type} {Hg: GoodTerm Src}:
  @goodPreserving Src Src (fun x => Ret x) _ _.
Proof using.
  intros ? ?.
  simpl. assumption.
Qed.

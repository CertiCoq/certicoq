Require Import Common.exceptionMonad.

Require Import Common.AstCommon.


Class WellFormed (Term: Type) := wf : Term  -> Prop. 

Generalizable Variables Src Dst Inter Term Value SrcValue DstValue InterValue.

(** A [Term] can contain an environment embedded in it. 
Use this class when there is a separate type (and translation?) for values *)
Class BigStepHetero (Term Value:Type) := bigStepEval: Term -> Value -> Prop.

(** Use this class when values are just a subcollection of terms. *)
Class BigStepOpSem (Term:Type) := bigStepEvalSame:> BigStepHetero Term Term.

(* In either case, one can use ⇓ to refer to the big step eval relation *)

Notation "s ⇓ t" := (bigStepEval s t) (at level 70).



Require Import Coq.Unicode.Utf8.


Instance liftBigStepException `{BigStepHetero Term Value} 
  : BigStepHetero (exception Term) (exception Value) :=
λ (s : exception Term) (sv : exception Value),
match (s, sv) with
| (Ret s, Ret sv) => s ⇓ sv
| (_,_) => False
end.


Class CerticoqTranslation (Src Dst : Type) : Type
  := translate : Src -> exception Dst.

Class CerticoqTotalTranslation (Src Dst : Type) : Type
  := translateT : Src -> Dst.

Arguments translate  Src Dst {CerticoqTranslation} s.
Arguments translateT  Src Dst {CerticoqTotalTranslation} s.

Instance liftTotal `{CerticoqTotalTranslation Src Dst} : CerticoqTranslation Src Dst :=
  fun (x:Src) => Ret (translateT Src Dst x). 


Definition wfPreserving `{CerticoqTranslation Src Dst}
    `{WellFormed Src} `{WellFormed Dst} : Prop := 
  ∀ (s: Src), 
    wf s 
    -> match translate Src Dst s with
      | Ret t => wf t
      | Exc _ => False
      end.

Arguments wfPreserving Src Dst {H} {H0} {H1}.

(** A Certicoq language must have an associated bigstep operational semantics and 
  a well formedness predicate (possibly \_.True) *)
Class CerticoqLanguage `{BigStepHetero Term Value} `{WellFormed Term} := 
{
  (* Sensible, but not needed yet.
  wfPreserved : forall (s v : Term), 
    wf s
    -> s ⇓ v
    -> wf v
  *)
}.

(* can be used to get the Term type from an instance *)
Definition cTerm `{CerticoqLanguage Term Value} : Type := Term.
(* can be used to get the Value type from an instance *)
Definition cValue `{CerticoqLanguage Term Value} : Type := Term.

Arguments cTerm {Term} {Value} {H} {H0} _.
Arguments cValue {Term} {Value} {H} {H0} _.


Arguments CerticoqLanguage Term {Value} {H} {H0}.


Definition bigStepPreserving `{CerticoqTranslation Src Dst} 
  `{CerticoqTranslation SrcValue DstValue}
   `{BigStepHetero Src SrcValue} `{BigStepHetero Dst DstValue} `{WellFormed Src}
  :=
   ∀ (s:Src) (sv: SrcValue), 
    wf s 
    -> s ⇓ sv
    -> (translate Src Dst s) ⇓ (translate SrcValue DstValue sv).

Arguments bigStepPreserving Src Dst {H} {SrcValue} {DstValue} {H0} {H1} {H2} {H3}.


Class CerticoqTranslationCorrect 
  `{CerticoqLanguage Src SrcValue} `{CerticoqLanguage Dst DstValue}
  `{CerticoqTranslation Src Dst} `{CerticoqTranslation SrcValue DstValue} := 
{
  certiWfPres : wfPreserving Src Dst;
  certiBigStepPres : bigStepPreserving Src Dst; (* consider  [obsPreserving] below*)
}.

Arguments CerticoqTranslationCorrect 
  Src {SrcValue} {H} {H0} {H1} Dst {DstValue} {H2} {H3} {H4} {H5} {H6}.

Global Instance composeTranslation `{CerticoqTranslation Src Inter} 
  `{CerticoqTranslation Inter Dst} :
  `{CerticoqTranslation Src Dst} :=
λ s, bind (translate Src Inter s) (translate Inter Dst).


Lemma composePreservesWf (Src Inter Dst: Type)
  {wfi: WellFormed Inter}
  {wfs: WellFormed Src}
  {wft: WellFormed Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst} :
wfPreserving Src Inter
-> wfPreserving Inter Dst
-> wfPreserving Src Dst.
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


Instance composeCerticoqTranslationCorrect
  `{CerticoqLanguage Src SrcValue}
  `{CerticoqLanguage Inter InterValue}
  `{CerticoqLanguage Dst DstValue}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
  {t1v : CerticoqTranslation SrcValue InterValue}
  {t2v : CerticoqTranslation InterValue DstValue}
  {Ht1: CerticoqTranslationCorrect Src Inter}
  {Ht2: CerticoqTranslationCorrect Inter Dst}
    : CerticoqTranslationCorrect Src Dst.
Proof.
  destruct Ht1, Ht2.
  constructor;[eapply composePreservesWf; eauto|].
  intros ? ? Hwf Hev.
  apply certiBigStepPres0 in Hev;[| assumption].
  apply certiWfPres0 in Hwf.
  unfold composeTranslation, translate in *.
  destruct (t1 s), (t1v sv); compute in Hev; try contradiction.
  apply certiBigStepPres1 in Hev;[| assumption].
  exact Hev.
Qed.

(* We fix one type of observations of the head of a value. Typically,
these would be the tags of constructors of (co-)inductive types.
If a value is not a constructor applied to some args, e.g. a lambda,
the observation should be None.

This means, that \x.1 ~ \x.2 , which is unfortunate. It would be especially bad if,
although unlikely,
the IO monad had an operation that takes a function of type nat -> string, e.g. to
indicate the string to be sent at the nth tick.

Can ¬ (\x.1 ~ \x.2) still be implied using the existing assumptions in 
  [CerticoqTranslationCorrect2]?

Should we allow some computation when making observation, especially on subterms?
When we add cofix/coinductives/effects, this may become necessary.
*)

Definition Observation :Set := option (inductive * nat).

Class ObserveHead (Value:Type) := observeHead: Value -> Observation.

(* observe subterms for a constructor. return [] if the value is not a constructor. *)
Class ObserveSubterms (Value:Type) := observeSubterms: Value -> list Value.

Require Import List.
(* Coinductive, in case we add support for Coq's coinductive types lateron *)
CoInductive obsEqual
   `{ObserveHead SrcValue} `{ObserveSubterms SrcValue} 
   `{ObserveHead DstValue} `{ObserveSubterms DstValue} : SrcValue -> DstValue -> Prop :=
| sameObs : forall (s : SrcValue) (d : DstValue),
    observeHead s = observeHead d
    -> (let ls := (observeSubterms s) in
       let ld := (observeSubterms d) in
       length ls = length ld /\
       forall n:nat, obsEqual (nth n ls s)  (nth n ld d))
    -> obsEqual s d.

Notation "s ~ t" := (obsEqual s t) (at level 65).

(* Similar to what Zoe suggested on 	Wed, Aug 17, 2016 at 8:57 AM *)
Definition obsPreserving 
  `{CerticoqTranslation Src Dst} 
   `{BigStepHetero Src SrcValue} `{BigStepHetero Dst DstValue} `{WellFormed Src}
   `{ObserveHead SrcValue} `{ObserveSubterms SrcValue} 
   `{ObserveHead DstValue} `{ObserveSubterms DstValue}
  :=
   ∀ (s:Src) (sv: SrcValue), 
    wf s 
    -> (s ⇓ sv)
    -> ∃ (dv: DstValue), (translate Src Dst s) ⇓ (Ret dv) ∧  sv ~ dv.

Arguments obsPreserving Src Dst {H} {SrcValue} {H0} {DstValue} {H1} {H2} {H3} {H4} {H5} {H6}.

Class CerticoqLanguage2 `{BigStepHetero Term Value} `{WellFormed Term} 
   `{ObserveHead Value} `{ObserveSubterms Value} 
:= 
{
  (* Sensible, but not needed yet.
  wfPreserved : forall (s v : Term), 
    wf s
    -> s ⇓ v
    -> wf v
  *)
}.

(*
Arguments CerticoqLanguage2 Term {Value} {H} {H0} {H1} {H2}.

Class CerticoqTranslationCorrect2 Src SrcValue Dst DstValue S1 S2 S3 S4 D1 D2 D3 D4
  `{@CerticoqLanguage2 Src SrcValue S1 S2 S3 S4} 
  `{@CerticoqLanguage2 Dst DstValue D1 D2 D3 D4}
  `{CerticoqTranslation Src Dst} := 
{
  certiWfPres2 : wfPreserving Src Dst;
  obsePres : obsPreserving Src Dst;
}.
*)


(* later in this file, we make [Value] an implicit argument. Having it be explicit
  here cuts down a lot of verbosity (by using `, which doesn't work with @) 
  in some definitions below.
 *)
Arguments CerticoqLanguage2 Term Value {H} {H0} {H1} {H2}.

Class CerticoqTranslationCorrect2
  `{CerticoqLanguage2 Src SrcValue} 
  `{CerticoqLanguage2 Dst DstValue}
  `{CerticoqTranslation Src Dst} := 
{
  certiWfPres2 : wfPreserving Src Dst;
  obsePres : obsPreserving Src Dst;
}.

Arguments CerticoqTranslationCorrect2
  Src {SrcValue} {H} {H0} {H1} {H2} {H3} Dst {DstValue} {H4} {H5} {H6} {H7} {H8} {H9}.

(*
Does not have a any theory of heterigeneous relations. Niether does MathClasses.
Require Import Coq.Classes.RelationClasses.
*)


Lemma obsEqualTrns
   `{ObserveHead SrcValue} `{ObserveSubterms SrcValue} 
   `{ObserveHead InterValue} `{ObserveSubterms InterValue} 
   `{ObserveHead DstValue} `{ObserveSubterms DstValue} :
   forall   (s : SrcValue) (i : InterValue) (d : DstValue),
  s ~ i
  -> i ~ d 
  -> s ~ d.
Proof.
  cofix.
  intros ? ? ? Ha Hb.
  inversion Ha as [ss is Hah Has]. subst. clear Ha.
  inversion Hb as [is ds Hbh Hbs]. subst. clear Hb.
  constructor;[congruence|].
  simpl in *. destruct Has as [Hasl Has].
  destruct Hbs as [Hbsl Hbs].
  split; [congruence|].
  eauto.
(* info eauto : 
intro.
eapply obsEqualTrns.
 apply Has.
 apply Hbs.
*)
Qed.

Instance composeCerticoqTranslationCorrect2
  `{CerticoqLanguage2 Src SrcValue}
  `{CerticoqLanguage2 Inter InterValue}
  `{CerticoqLanguage2 Dst DstValue}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
(* we don't anymore need a translation for the value type, although typically Src=SrcValue*)
  {Ht1: CerticoqTranslationCorrect2 Src Inter}
  {Ht2: CerticoqTranslationCorrect2 Inter Dst}
    : CerticoqTranslationCorrect2 Src Dst.
Proof.
  destruct Ht1, Ht2.
  constructor;[eapply composePreservesWf; eauto; fail|].
  intros ? ? Hwf Hev.
  apply obsePres0 in Hev;[| assumption].
  apply certiWfPres3 in Hwf.
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
  eapply obsEqualTrns with (i:=iv); eauto.
Qed.



Instance  BigStepOpWEnv (Term:Set) (ev: (environ Term) -> Term -> Term -> Prop) :
  BigStepOpSem (Program Term) :=
fun p1 p2 => ev (env p1) (main p1) (main p2) /\ (env p1 = env p2).

Definition normalizes `{BigStepHetero Term Value} (s:Term): Prop :=
∃ (sv : Value) , s ⇓ sv.


(* Todo : generalize over Coq.Init.Logic.eq. *)
Definition deterministicBigStep `{BigStepHetero Term Value} :=
∀ (s :Term) (v1 v2 : Value), s ⇓ v1 -> s ⇓ v2 -> v1 = v2.

Arguments deterministicBigStep Term {Value} {H}.

Definition totalTranslation `{CerticoqTranslation Src Dst} : Prop :=
  ∀ (s:Src), 
match translate Src Dst s with
| Ret _ => True
| Exc _ => False
end.


Lemma deterministicBigStepLiftExc `{BigStepHetero Term Value}:
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
   `{BigStepHetero Src SrcValue} `{BigStepHetero Dst DstValue} (s:Src) : Prop :=
 ∀ (td: exception DstValue), 
    (translate Src Dst s) ⇓ td
    -> ∃ (d:SrcValue), s ⇓ d ∧ td = translate SrcValue DstValue d.


Arguments bigStepReflecting Src Dst {H} {SrcValue} {DstValue} {H0} {H1} {H2} s.


Lemma bigStepPreservingReflecting 
  `{CerticoqTranslation Src Dst}
  `{CerticoqTranslation SrcValue DstValue}
  `{CerticoqLanguage Src SrcValue}
  `{CerticoqLanguage Dst DstValue}
  {_:bigStepPreserving Src Dst} :
  (deterministicBigStep Dst)
  -> ∀ (s:Src), 
    wf s
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


Fixpoint FunctionType (L:list Type) (R:Type): Type :=
match L with
| nil => R
| cons H T => H -> (FunctionType T R)
end.

Fixpoint excFunction (L:list Type) (R:Type) (err: String.string) {struct L}: 
  (FunctionType (List.map exception L) (exception R)) :=
match L return (FunctionType (List.map exception L) (exception R)) with
| nil => Exc err
| cons H T => λ (he : exception H), (excFunction T R err)
end.


Fixpoint liftExeption (L:list Type) (R:Type) 
  (f: FunctionType L R) {struct L}: (FunctionType (List.map exception L) (exception R)) :=
match L 
  return (FunctionType L R -> FunctionType (List.map exception L) (exception R)) with
| nil => λ f, Ret f
| cons H T => fun ff he => 
    match he with
    | Exc err => excFunction T R err
    | Ret h =>  liftExeption T R (ff h)
    end
end f.


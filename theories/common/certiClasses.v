Require Import Common.exceptionMonad.

Require Import Common.AstCommon.


Class WellFormed (Term: Type) := wf : Term  -> Prop. 

Generalizable Variables Src Dst Inter Term.

(** A [Term] can contain an environment embedded in it. *)
Class BigStepOpSem (Term:Type) := bigStepEval: Term -> Term -> Prop.


Notation "s ⇓ t" := (bigStepEval s t) (at level 70).

Require Import Coq.Unicode.Utf8.


Instance liftBigStepException `{BigStepOpSem Term} : BigStepOpSem (exception Term):=
λ (s sv: exception Term),
match (s, sv) with
| (Ret s, Ret sv) => s ⇓ sv
| (_,_) => False
end.


Class CerticoqTranslation (Src Dst : Type)
  := translate : Src -> exception Dst.

Arguments translate  Src Dst {CerticoqTranslation} s.

Definition wfPreserving `{CerticoqTranslation Src Dst}
    `{WellFormed Src} `{WellFormed Dst} : Prop := 
  ∀ (s: Src), 
    wf s 
    -> match translate Src Dst s with
      | Ret t => wf t
      | Exc _ => False
      end.

Arguments wfPreserving Src Dst {H} {H0} {H1}.

Definition bigStepPreserving `{CerticoqTranslation Src Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} `{WellFormed Src}
  :=
   ∀ (s sv:Src), 
    wf s 
    -> s ⇓ sv
    -> (translate Src Dst s) ⇓ (translate Src Dst sv).

Arguments bigStepPreserving Src Dst {H} {H0} {H1} {H2}.

(* Sometimes, the translation of a value may not be a value. 
For example, in L3 to L4, the environment is translated as let bindings.
Thus, a value with a non-empty environment will be translated to a term
whose outermost operator is a let binding and is hence not a value.
This definition, which is inspired by CPS correct seems weaker, is not strong enough
to be sensible. For example it is possible that the translation of [s] and [sv] both
diverge. *)
Definition bigStepPreservingWeaker `{CerticoqTranslation Src Dst}
   `{BigStepOpSem Src} `{BigStepOpSem Dst} `{WellFormed Src}
  :=
   ∀ (s sv:Src) (tv : Dst), 
    wf s 
    -> s ⇓ sv
    -> ((translate Src Dst s) ⇓ (Ret tv) <-> (translate Src Dst sv) ⇓ (Ret tv)).

Arguments bigStepPreservingWeaker Src Dst {H} {H0} {H1} {H2}.


(** A Certicoq language must have an associated bigstep operational semantics and 
  a well formedness predicate (possibly \_.True) *)
Class CerticoqLanguage (Term : Type) `{BigStepOpSem Term} `{WellFormed Term} := 
{
  (* Sensible, but not needed yet.
  wfPreserved : forall (s v : Term), 
    wf s
    -> s ⇓ v
    -> wf v
  *)
}.

Arguments CerticoqLanguage Term {H} {H0}.

Class CerticoqTranslationCorrect 
  `{CerticoqLanguage Src} `{CerticoqLanguage Dst}
  `{CerticoqTranslation Src Dst} := 
{
  certiWfPres : wfPreserving Src Dst;
  certiBigStepPres : bigStepPreserving Src Dst; (* consider [bigStepPreservingWeaker] *)
}.

Arguments CerticoqTranslationCorrect Src {H} {H0} {H1} Dst {H2} {H3} {H4} {H5}.

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


Instance composeCerticoqTranslationCorrect (Src Inter Dst: Type)
  `{CerticoqLanguage Src}
  `{CerticoqLanguage Inter}
  `{CerticoqLanguage Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
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
  destruct (t1 s), (t1 sv); compute in Hev; try contradiction.
  apply certiBigStepPres1 in Hev;[| assumption].
  exact Hev.
Qed.


Instance  BigStepOpWEnv (Term:Set) (ev: (environ Term) -> Term -> Term -> Prop) :
  BigStepOpSem (Program Term) :=
fun p1 p2 => ev (env p1) (main p1) (main p2) /\ (env p1 = env p2).


(* A possible replacement for [CerticoqTranslationCorrect] 
Class CerticoqTranslationCorrect2 
  `{CerticoqLanguage Src} `{CerticoqLanguage Dst}
  `{CerticoqTranslation Src Dst} := 
{
  certiWfPres2 : wfPreserving Src Dst;
  certiBigStepPres2 : bigStepPreservingWeaker Src Dst;
}.

Arguments CerticoqTranslationCorrect2 Src {H} {H0} {H1} Dst {H2} {H3} {H4} {H5}.


Instance composeCerticoqTranslationCorrect2 (Src Inter Dst: Type)
  `{CerticoqLanguage Src}
  `{CerticoqLanguage Inter}
  `{CerticoqLanguage Dst}
  {t1 : CerticoqTranslation Src Inter}
  {t2 : CerticoqTranslation Inter Dst}
  {Ht1: CerticoqTranslationCorrect2 Src Inter}
  {Ht2: CerticoqTranslationCorrect2 Inter Dst}
    : CerticoqTranslationCorrect2 Src Dst.
Proof.
  destruct Ht1, Ht2.
  constructor;[eapply composePreservesWf; eauto|].
  intros ? ? ? Hwf Hev.
  specialize (fun ti => certiBigStepPres3 _ _ ti Hwf Hev).

*)


(* ( * ) in Randy's email dated Tue, May 31, 2016 at 10:35 PM EST 
*) 

Definition bigStepReflecting `{CerticoqTranslation Src Dst}  
   `{BigStepOpSem Src} `{BigStepOpSem Dst} (s:Src) : Prop :=
 ∀ (td: exception Dst), 
    (translate Src Dst s) ⇓ td
    -> ∃ (d:Src), s ⇓ d ∧ td = translate Src Dst d.


Arguments bigStepReflecting Src Dst {H} {H0} {H1} s.



Definition normalizes `{BigStepOpSem Term} (s:Term): Prop :=
∃ sv, s ⇓ sv.


(* Todo : generalize over Coq.Init.Logic.eq. *)
Definition deterministicBigStep `{BigStepOpSem Term} :=
∀ (s v1 v2:Term), s ⇓ v1 -> s ⇓ v2 -> v1 = v2.

Arguments deterministicBigStep Term {H}.

Definition totalTranslation `{CerticoqTranslation Src Dst} : Prop :=
  ∀ (s:Src), 
match translate Src Dst s with
| Ret _ => True
| Exc _ => False
end.


Lemma deterministicBigStepLiftExc `{BigStepOpSem Term}:
  deterministicBigStep Term
  -> deterministicBigStep (exception Term).
Proof.
  intros Hd ? ? ? He1 He2.
  destruct s, v1, v2; compute in He1; compute in He2; try contradiction.
  f_equal.
  unfold deterministicBigStep in Hd.
  eapply Hd; eauto.
Qed.

Lemma bigStepPreservingReflecting 
  `{CerticoqTranslation Src Dst}
  `{CerticoqLanguage Src}
  `{BigStepOpSem Dst}
  `{@bigStepPreserving Src Dst _ _ _ _ } :
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
  info_eauto.
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


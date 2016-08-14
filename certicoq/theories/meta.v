Require Import Common.exceptionMonad.

Require Import Common.AstCommon.

Set Implicit Arguments.

(** A [Term] can contain an environment embedded in it. *)
Class BigStepLanguage (Term: Type) := bigStepEval: Term -> Term -> Prop. 

Generalizable Variables Src Dst Term.

Notation "s ⇓ t" := (bigStepEval s t) (at level 70).

Require Import Coq.Unicode.Utf8.

Instance liftBigStepException `{BigStepLanguage Term} : BigStepLanguage (exception Term):=
λ (s sv: exception Term),
match (s, sv) with
| (Ret s, Ret sv) => s ⇓ sv
| (_,_) => False
end.


Definition normalizes `{BigStepLanguage Term} (s:Term): Prop :=
∃ sv, s ⇓ sv.


(* Todo : generalize over Coq.Init.Logic.eq. *)
Definition deterministicBigStep `{BigStepLanguage Term} :=
∀ (s v1 v2:Term), s ⇓ v1 -> s ⇓ v2 -> v1 = v2.

Arguments deterministicBigStep Term {H}.

Lemma deterministicBigStepLiftExc `{BigStepLanguage Term}:
  deterministicBigStep Term
  -> deterministicBigStep (exception Term).
Proof.
  intros Hd ? ? ? He1 He2.
  destruct s, v1, v2; compute in He1; compute in He2; try contradiction.
  f_equal.
  unfold deterministicBigStep in Hd.
  eapply Hd; eauto.
Qed.

(* TODO : BigStep semantics is not necessary to define a translation *)
Class Translation `{BigStepLanguage Src} `{BigStepLanguage Dst}
  := translate : Src -> exception Dst.

Definition totalTranslation `{Translation Src Dst} : Prop :=
  ∀ (s:Src), 
match translate s with
| Ret _ => True
| Exc _ => False
end.

Class BigStepPreserving `{Translation Src Dst} (precondition : Src -> Prop)
  :=
  preservesEval  : ∀ (s sv:Src), 
    precondition s 
    -> s ⇓ sv
    -> (translate s) ⇓ (translate sv)
. 

(* ( * ) in Randy's email dated Tue, May 31, 2016 at 10:35 PM EST 
*) 

Definition bigStepReflecting `{Translation Src Dst} (precondition : Src -> Prop) (s:Src) : Prop :=
 ∀ (td: exception Dst), 
    (translate s) ⇓ td
    -> ∃ (d:Src), s ⇓ d ∧ td = translate d. 


Arguments BigStepPreserving Src {H} Dst {H0} {H1} precondition.
Arguments bigStepReflecting Src {H} Dst {H0} {H1} precondition s.


Generalizable Variable precondition.

Lemma bigStepPreservingReflecting  `{BigStepPreserving Src Dst precondition}: 
  (deterministicBigStep Dst)
  -> ∀ (s:Src), 
    precondition s
    -> normalizes s
    -> bigStepReflecting Src Dst precondition s.
Proof.
  intros Hd ? Hp Hn ? Ht.
  destruct Hn as [d  Hn].
  exists d. split;[assumption|].
  apply deterministicBigStepLiftExc in Hd.
  eauto.
(*
(* info eauto : *)
eapply Hd.
 exact Ht.
 apply H2.
  exact Hp.
  exact Hn.
*)
Qed.

  


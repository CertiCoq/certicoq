Require Import ExtLib.Core.Type.

Global Instance type_Prop : type Prop :=
{ equal := iff
; proper := fun _ => True
}.

Global Instance typeOk_Prop : typeOk type_Prop.
Proof.
  constructor; compute; firstorder.
Qed.

(*
Set Implicit Arguments.
Set Strict Implicit.

Global Instance Logic_Prop : Logic Prop :=
{ Entails g p := List.fold_right Basics.impl p g
; Tr       := True
; Fa       := False
; And  p q := p /\ q
; Or   p q := p \/ q
; Impl p q := p -> q
}.

Global Instance LogicLaws_Prop : LogicLaws Logic_Prop.
constructor; try solve [ unfold Basics.impl; simpl in *; firstorder; try (induction G; simpl in *; firstorder) ].
induction G; simpl in *; intros; auto. contradiction.
destruct H. subst. red. clear. intros. induction G; simpl in *; auto.
red. auto.
red. eauto.
Qed.

Instance Quant_Prop : Quant Prop :=
{ All := fun V (P : V -> Prop) => forall x : V, P x
; Ex  := fun V (P : V -> Prop) => exists x : V, P x
}.

Instance QuantLaws_Prop : QuantLaws Quant_Prop _.
Proof.
  constructor.
  { induction G; simpl; intros; auto.
    intro. eapply IHG. eapply H. auto. }
  { induction G; simpl; intros; auto.
    intro. apply IHG. intro. eapply H. auto. }
Qed.

Existing Instance LogicLaws_Prop.
*)
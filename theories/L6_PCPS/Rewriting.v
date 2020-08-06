Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.funind.Recdef.
Require Import Coq.PArith.BinPos.
Require Import Lia.
From compcert.lib Require Import Maps.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Set Default Proof Mode "Ltac2".

Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.Eqdep.
Ltac inv_ex :=
  repeat progress match goal with
  | H : existT ?P ?T _ = existT ?P ?T _ |- _ => apply inj_pairT2 in H
  end.

Require Export CertiCoq.L6.Frame.

Set Implicit Arguments.

(* -------------------- Annotations -------------------- *)

Definition Rec {A} (rhs : A) : A := rhs.
Definition BottomUp {A} (rhs : A) : A := rhs.

(* -------------------- Erased values -------------------- *)

(* An erased value of type [A] is a value which can only be used to construct Props.
   We can represent erased values [x] in CPS with answer type Prop, as functions of
   the form [fun k => k x]: *)
Definition erased A := (A -> Prop) -> Prop.
Class e_ok {A} (x : erased A) := erased_ok : exists (y : A), x = (fun k => k y).
(* These two items are carried separately so that they can both be erased during extraction.
   Bundling them together in a dependent pair type would erase to a pair type [box × box] *)

(* Erasing a value *)
Definition erase {A} : A -> erased A := fun x k => k x.
Instance erase_ok {A} (x : A) : e_ok (erase x). Proof. exists x; reflexivity. Qed.

(* Erased values can always be used to construct other erased values *)
Definition e_map {A B} (f : A -> B) (x : erased A) : erased B := fun k => x (fun x => k (f x)).
Instance e_map_ok {A B} (f : A -> B) (x : erased A) `{H : e_ok _ x} : e_ok (e_map f x).
Proof. destruct H as [y Hy]; subst x; unfold e_map; now exists (f y). Qed.

Definition e_map_fuse {A B C} (f : B -> C) (g : A -> B) (x : erased A) :
  e_map f (e_map g x) = e_map (fun x => f (g x)) x.
Proof. reflexivity. Qed.

(* Only proofs can be unerased *)
Definition recover (x : erased Prop) : Prop := x (fun x => x).
Notation "'«' P '»'" := (recover P).

(* Remove all erased operators from a goal using e_ok hypotheses *)
Ltac unerase :=
  repeat match goal with
  | H : e_ok ?x |- _ => 
    let x' := fresh x in
    rename x into x';
    destruct H as [x H];
    subst x'
  end;
  unfold recover, e_map, erase in *.

Ltac2 unerase () := ltac1:(unerase).
Ltac2 Notation "unerase" := unerase ().

(* Example *)
Require Import Lia.
Require Extraction.
Module Example.

Fixpoint thingy (n : erased nat) `{Hn : e_ok _ n} (m p : nat) (Hmp : «e_map (fun n => n + m = p) n») {struct m} : nat.
Proof.
  destruct m as [|m] > [exact p|].
  specialize (thingy (e_map S n) _ m p); apply thingy; clear thingy.
  ltac1:(unerase; lia).
Defined.

Print thingy.
(* Since n and its proof are carried separately, both are erased entirely *)
Recursive Extraction thingy.
End Example.

(* -------------------- Fixpoint combinator -------------------- *)

(* Equations and Program Fixpoint use a fixpoint combinator which has the following type when
   specialized to a particular measure [measure]:
     [forall arg_pack, (forall arg_pack', measure arg_pack' < measure arg_pack -> P arg_pack') -> P arg_pack]
   This requires wrapping and unwrapping [arg_pack]s. Instead we'll make
     [forall (cost : erased nat), e_ok cost -> (forall cost', e_ok cost' -> cost' < cost -> Q cost') -> Q cost]
   which can achieve the same thing without arg packs by setting
     [Q := fun cost => arg1 -> ‥ -> arg_n -> cost = measure(arg1, ‥, arg_n) -> P (arg1, ‥, arg_n)].

   After a function has been defined this way, unfolding all fixpoint combinators will leave behind a
   primitive fixpoint of type
     [forall (cost : erased nat), e_ok cost -> Accessible cost -> arg1 -> ‥ -> arg_n -> cost = measure ‥ -> P ‥]
   that is structurally recursive on the accessibility proof [Accessible cost].

   Extraction will erase [cost : erased nat], [e_ok cost], [Accessible cost], and [cost = measure ‥],
   leaving a plain recursive function of type [arg1 -> ‥ -> arg_n -> P ‥]. *)
Require Import Coq.Arith.Wf_nat.
Section WellfoundedRecursion.

(* Modelled after https://coq.inria.fr/library/Coq.Init.Wf.html#Acc *)
Section AccS.

  Context (A : Type) (B : A -> Prop) (R : forall x, B x -> forall y, B y -> Prop).

  Inductive AccS (x : A) (Hx : B x) : Prop :=
    AccS_intro : (forall (y : A) (Hy : B y), R Hy Hx -> @AccS y Hy) -> AccS Hx.

  Definition well_foundedS := forall (x : A) (Hx : B x), AccS Hx.

  Section FixS.

    Context
      (Rwf : well_foundedS)
      (P : A -> Type)
      (F : forall (x : A) (Hx : B x), (forall (y : A) (Hy : B y), R Hy Hx -> P y) -> P x).

    Fixpoint FixS_F (x : A) (Hx : B x) (H : AccS Hx) {struct H} : P x :=
      F (fun (y : A) (Hy : B y) (Hyx : R Hy Hx) =>
          FixS_F (let 'AccS_intro H := H in H y Hy Hyx)).

    Definition FixS (x : A) (Hx : B x) : P x := FixS_F (Rwf Hx).

  End FixS.

End AccS.

Section FixEN.

Definition enat := erased nat.
Definition e_lt : forall x : enat, e_ok x -> forall y : enat, e_ok y -> Prop :=
  fun n Hn m Hm => «e_map (fun n => «e_map (fun m => n < m) m») n».

Lemma e_lt_wf : well_foundedS e_ok e_lt.
Proof.
  intros n Hn; unerase.
  induction n as [n IHn] using Wf_nat.lt_wf_ind.
  constructor; intros m Hm Hmn; unerase.
  now apply IHn.
Defined.

Definition FixEN :
  forall P : enat -> Type,
  (forall (x : enat) (Hx : e_ok x), (forall (y : enat) (Hy : e_ok y), e_lt Hy Hx -> P y) -> P x) ->
  forall x : enat, e_ok x -> P x
  := FixS e_lt_wf.

End FixEN.

End WellfoundedRecursion.

Extraction Inline FixEN FixS FixS_F.

Module FixENExample.

Definition plus : forall (cost : enat) `{e_ok _ cost}, forall n m : nat, «e_map (eq n) cost» -> nat.
Proof.
  apply (FixEN (fun cost => forall n m : nat, «e_map (eq n) cost» -> nat)).
  intros cost Hok rec n m Hcost.
  destruct n as [|n] > [exact m|].
  specialize rec with (n := n).
  specialize (rec (erase n) _).
  apply S, rec > [|exact m|]; unfold e_lt in *; ltac1:(unerase; lia).
Defined.

End FixENExample.

Print FixENExample.plus.
Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction FixENExample.plus.

(* -------------------- 1-hole contexts built from frames -------------------- *)

(* A 1-hole context made out of frames F *)
Inductive frames_t' {U : Set} {F : U -> U -> Set} : U -> U -> Set :=
| frames_nil : forall {A}, frames_t' A A
| frames_cons : forall {A B C}, F A B -> frames_t' B C -> frames_t' A C.
Arguments frames_t' {U} F _ _.
Notation "C '>::' f" := (frames_cons f C) (at level 50, left associativity).
Notation "<[]>" := (frames_nil).
Notation "<[ x ; .. ; z ]>" := (frames_cons z .. (frames_cons x frames_nil) ..).

(* The 1-hole contexts you usually want *)
Definition frames_t {U : Set} `{Frame U} : U -> U -> Set := frames_t' frame_t.

(* Context application *)
Reserved Notation "C '⟦' x '⟧'" (at level 50, no associativity).
Fixpoint framesD {U : Set} `{Frame U} {A B : U}
         (fs : frames_t A B) : univD A -> univD B :=
  match fs with
  | <[]> => fun x => x
  | fs >:: f => fun x => fs ⟦ frameD f x ⟧
  end
where "C '⟦' x '⟧'" := (framesD C x).

Lemma framesD_cons {U : Set} `{Frame U} {A B C : U}
      (fs : frames_t B C) (f : frame_t A B)
      (x : univD A)
  : (fs >:: f) ⟦ x ⟧ = fs ⟦ frameD f x ⟧.
Proof. reflexivity. Qed.

Fixpoint frames_lift {U : Set} {F : U -> U -> Set}
      (P : U -> Set) (Hf : forall {A B}, F A B -> P A -> P B)
      {A B} (fs : frames_t' F A B)
  : P A -> P B :=
  match fs with
  | <[]> => fun pa => pa
  | fs >:: f => fun pa => frames_lift P (@Hf) fs (Hf f pa)
  end.

(* Context composition *)
Reserved Notation "gs '>++' fs" (at level 50, left associativity).
Fixpoint frames_compose {U : Set} {F : U -> U -> Set} {A B C : U}
         (fs : frames_t' F A B) : frames_t' F B C -> frames_t' F A C :=
  match fs with
  | <[]> => fun gs => gs
  | fs >:: f => fun gs => gs >++ fs >:: f
  end
where "gs '>++' fs" := (frames_compose fs gs).

(* Laws: functor laws + injectivity *)

Lemma frames_id_law {U : Set} `{Frame U} {A} (x : univD A) : <[]> ⟦ x ⟧ = x.
Proof. auto. Qed.

Lemma frames_compose_law {U : Set} `{Frame U} {A B C} :
  forall (fs : frames_t B C) (gs : frames_t A B) (x : univD A),
  (fs >++ gs) ⟦ x ⟧ = fs ⟦ gs ⟦ x ⟧ ⟧.
Proof. intros fs gs; revert fs; induction gs; simpl; auto. Qed.

Class Frame_inj (U : Set) `{Frame U} :=
  frame_inj :
    forall {A B : U} (f : frame_t A B) (x y : univD A),
    frameD f x = frameD f y -> x = y.

Lemma frames_inj {U : Set} `{Frame U} `{Frame_inj U} {A B} (fs : frames_t A B) :
  forall (x y : univD A), fs ⟦ x ⟧ = fs ⟦ y ⟧ -> x = y.
Proof.
  induction fs; auto; cbn; intros x y Heq.
  apply IHfs, (frame_inj f) in Heq; auto.
Qed.

(* Misc. lemmas (mostly about how frames_t is similar to list) *)

Definition flip {U} (F : U -> U -> Set) : U -> U -> Set := fun A B => F B A.
Fixpoint frames_rev {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) : frames_t' (flip F) B A :=
  match fs with
  | <[]> => <[]>
  | fs >:: f => <[f]> >++ frames_rev fs
  end.
Fixpoint frames_revD {U : Set} `{Frame U} {A B : U}
         (fs : frames_t' (flip frame_t) B A) : univD A -> univD B :=
  match fs with
  | <[]> => fun x => x
  | fs >:: f => fun x => frameD f (frames_revD fs x)
  end.

Lemma frames_nil_comp {U : Set} {F : U -> U -> Set} {A B : U}
      (fs : frames_t' F A B)
  : <[]> >++ fs = fs.
Proof. induction fs > [reflexivity|cbn; now rewrite IHfs]. Qed.

Lemma frames_revD_comp {U : Set} `{HFrame : Frame U} {A B C : U}
      (fs : frames_t' (flip frame_t) B A) (gs : frames_t' (flip frame_t) C B)
      (x : univD A)
  : frames_revD (fs >++ gs) x = frames_revD gs (frames_revD fs x).
Proof. induction gs > [reflexivity|cbn; now rewrite IHgs]. Qed.

Lemma framesD_rev {U : Set} `{Frame U} {A B : U} (fs : frames_t A B) (x : univD A)
  : fs ⟦ x ⟧ = frames_revD (frames_rev fs) x.
Proof.
  induction fs > [reflexivity|cbn].
  now rewrite frames_revD_comp, <- IHfs.
Qed.

Lemma frames_rev_assoc {U : Set} {F : U -> U -> Set} {A B C D : U}
      (fs : frames_t' F A B) (gs : frames_t' F B C) (hs : frames_t' F C D)
  : hs >++ (gs >++ fs) = hs >++ gs >++ fs.
Proof. induction fs > [reflexivity|cbn; now rewrite IHfs]. Qed.

Lemma frames_rev_comp {U : Set} {F : U -> U -> Set} {A B C : U}
      (fs : frames_t' F A B) (gs : frames_t' F B C)
  : frames_rev (gs >++ fs) = frames_rev fs >++ frames_rev gs.
Proof.
  induction fs; cbn.
  - now rewrite frames_nil_comp.
  - now rewrite IHfs, frames_rev_assoc.
Qed.

Lemma frames_rev_rev {U : Set} `{Frame U} {A B : U} (fs : frames_t A B)
  : frames_rev (frames_rev fs) = fs.
Proof. induction fs > [reflexivity|cbn]. now rewrite frames_rev_comp, IHfs. Qed.

Fixpoint frames_any {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
         {A B} (fs : frames_t' F A B) : Prop :=
  match fs with
  | <[]> => False
  | fs >:: f => P f \/ frames_any (@P) fs
  end.

Lemma frames_any_app
      {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
      {A B C} (gs : frames_t' F B C) (fs : frames_t' F A B)
  : frames_any (@P) (gs >++ fs) <-> frames_any (@P) gs \/ frames_any (@P) fs.
Proof. induction fs > [cbn; ltac1:(tauto)|cbn]. rewrite IHfs; ltac1:(tauto). Qed.

Lemma frames_any_cons
      {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
      {A B C} (fs : frames_t' F B C) (f : F A B)
  : frames_any (@P) (fs >:: f) <-> frames_any (@P) fs \/ P f.
Proof. unfold frames_any; ltac1:(tauto). Qed.

Fixpoint frames_len {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) : nat :=
  match fs with
  | <[]> => O
  | fs >:: f => S (frames_len fs)
  end.

Lemma frames_len_compose {U : Set} {F : U -> U -> Set} {A B C}
      (fs : frames_t' F A B) (gs : frames_t' F B C) :
  frames_len (gs >++ fs) = frames_len fs + frames_len gs.
Proof. induction fs as [|A' AB B' f fs IHfs] > [reflexivity|cbn]. now rewrite IHfs. Qed.

(* Useful in situations where [destruct] struggles with dependencies *)
Lemma frames_split' {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) :
  (exists AB (g : F A AB) (gs : frames_t' F AB B), fs = gs >:: g) \/
  (A = B /\ JMeq fs (<[]> : frames_t' F A A) /\ frames_len fs = 0%nat).
Proof. destruct fs as [| A' AB B' f fs] > [now right|left; now do 3 eexists]. Qed.

(* Like frames_split', but peels off frames from the left instead of from the right *)
Lemma frames_split {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) :
  (exists AB (g : F AB B) (gs : frames_t' F A AB), fs = <[g]> >++ gs) \/ (frames_len fs = O).
Proof.
  induction fs as [| A' AB B' f fs IHfs] > [now right|left].
  destruct IHfs as [[AB' [g [gs Hgs]]] | Hnil].
  - subst. do 2 eexists; exists (gs >:: f); reflexivity.
  - destruct fs; simpl in Hnil; inversion Hnil. do 2 eexists; exists <[]>; reflexivity.
Qed.

(* Well-founded induction on the length of the context *)
Lemma frames_len_ind (U : Set) (F : U -> U -> Set)
      (P : forall {A B}, frames_t' F A B -> Prop)
      (Hlt : forall {A B} (fs : frames_t' F A B),
        (forall {C D} (gs : frames_t' F C D), frames_len gs < frames_len fs -> P gs) ->
        P fs)
      A B (fs : frames_t' F A B)
  : P fs.
Proof.
  remember (frames_len fs) as n eqn:Hlen.
  ltac1:(generalize dependent B; generalize dependent A).
  induction n as [n IHn] using lt_wf_ind; intros A B fs Hlen.
  apply Hlt; intros C D gs Hlt_gs; eapply IHn > [|reflexivity]; ltac1:(lia).
Qed.

(* [frames_t] is a snoc-list of frames; this is an induction principle for reasoning about
   them as if they were cons-lists. *)
Lemma frames_rev_ind (U : Set) (F : U -> U -> Set)
      (P : forall {A B}, frames_t' F A B -> Prop)
      (Hnil : forall {A}, P (<[]> : frames_t' F A A))
      (Hcons : forall {A B C} (f : F B C) (fs : frames_t' F A B), P fs -> P (<[f]> >++ fs))
      A B (fs : frames_t' F A B)
  : P fs.
Proof.
  induction fs as [A B fs IHfs] using frames_len_ind.
  destruct (frames_split fs) as [[AB [f [fs' Hfs']]] | Hfs_nil] > [subst fs|].
  - apply Hcons, IHfs; rewrite frames_len_compose; cbn; ltac1:(lia).
  - destruct fs > [|now cbn in Hfs_nil]; apply Hnil.
Qed.

(* -------------------- Rewriters -------------------- *)
Section Rewriters.

Context
  (* Types the rewriter will encounter + type of 1-hole contexts *)
  (U : Set) `{HFrame : Frame U}
  (* The type of trees being rewritten *)
  (Root : U).

(* State variables, parameters, and delayed computations *)
Section Strategies.

Context
  (D : Set) (I_D : forall (A : U), univD A -> D -> Prop)
  (R : Set) (I_R : forall (A : U), frames_t A Root -> R -> Prop)
  (S : Set) (I_S : forall (A : U), frames_t A Root -> univD A -> S -> Prop).

Definition Delay {A} (e : univD A) : Set := {d | I_D A e d}.
Definition Param {A} (C : erased (frames_t A Root)) : Set :=
  {r | «e_map (fun C => I_R C r) C»}.
Definition State {A} (C : erased (frames_t A Root)) (e : univD A) : Set :=
  {s | «e_map (fun C => I_S C e s) C»}.

Class Delayed := {
  delayD : forall {A} (e : univD A), Delay e -> univD A;
  delay_id : forall {A} (e : univD A), Delay e;
  delay_id_law : forall {A} (e : univD A), delayD (delay_id e) = e }.

Class Preserves_R :=
  preserve_R :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B),
    Param fs -> Param (e_map (fun fs => fs >:: f) fs).

Class Preserves_S_up :=
  preserve_S_up :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B) (x : univD A),
    State (e_map (fun fs => fs >:: f) fs) x -> State fs (frameD f x).

Class Preserves_S_dn :=
  preserve_S_dn :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B) (x : univD A),
    State fs (frameD f x) -> State (e_map (fun fs => fs >:: f) fs) x.

Extraction Inline delayD delay_id preserve_R preserve_S_up preserve_S_dn.

End Strategies.

(* Handy instances *)

(* Structures with no invariants *)

Definition I_D_plain (D : Set) (A : U) (_ : univD A) (_ : D) : Prop := True.
Definition id_Delay := @Delay unit (@I_D_plain unit).

Global Instance Delayed_id_Delay : Delayed (@I_D_plain unit).
Proof.
  ltac1:(unshelve econstructor).
  - intros A x _; exact x.
  - intros; exists tt; exact I.
  - reflexivity.
Defined.

Definition I_R_plain (R : Set) (A : U) (C : frames_t A Root) (_ : R) : Prop := True.
Definition I_S_plain (S : Set) (A : U) (C : frames_t A Root) (_ : univD A) (_ : S) : Prop := True.

Global Instance Preserves_R_plain (R : Set) : Preserves_R (@I_R_plain R).
Proof. unfold Preserves_R; intros; assumption. Defined.

Global Instance Preserves_S_up_plain (S : Set) : Preserves_S_up (@I_S_plain S).
Proof. unfold Preserves_S_up; intros; assumption. Defined.

Global Instance Preserves_S_dn_plain (S : Set) : Preserves_S_dn (@I_S_plain S).
Proof. unfold Preserves_S_dn; intros; assumption. Defined.

Extraction Inline Delayed_id_Delay Preserves_R_plain Preserves_S_up_plain Preserves_S_dn_plain.

(* Composing two parameters *)
Section R_prod.

Context
  (R1 R2 : Set)
  (I_R1 : forall A, frames_t A Root -> R1 -> Prop) 
  (I_R2 : forall A, frames_t A Root -> R2 -> Prop).

Definition I_R_prod A (C : frames_t A Root) : R1 * R2 -> Prop :=
  fun '(r1, r2) => I_R1 C r1 /\ I_R2 C r2.

Global Instance Preserves_R_prod
       `{H1 : @Preserves_R _ (@I_R1)}
       `{H2 : @Preserves_R _ (@I_R2)} :
  Preserves_R I_R_prod.
Proof.
  unfold I_R_prod; intros A B C C_ok f [[r1 r2] Hr12].
  assert (Hr1 : «e_map (fun C => I_R1 _ C r1) C»). { unerase; now destruct Hr12. }
  assert (Hr2 : «e_map (fun C => I_R2 _ C r2) C»). { unerase; now destruct Hr12. }
  pattern r1 in Hr1; pattern r2 in Hr2. apply exist in Hr1; apply exist in Hr2. clear Hr12 r1 r2.
  ltac1:(unshelve eapply preserve_R with (f := f) in Hr1); try assumption.
  ltac1:(unshelve eapply preserve_R with (f := f) in Hr2); try assumption.
  destruct Hr1 as [r1 Hr1], Hr2 as [r2 Hr2]; exists (r1, r2).
  unerase; auto.
Defined.

Extraction Inline Preserves_R_prod.

End R_prod.

(* Composing two states *)
Section S_prod.

Context
  (S1 S2 : Set)
  (I_S1 : forall A, frames_t A Root -> univD A -> S1 -> Prop) 
  (I_S2 : forall A, frames_t A Root -> univD A -> S2 -> Prop).

Definition I_S_prod A (C : frames_t A Root) (e : univD A) : S1 * S2 -> Prop :=
  fun '(s1, s2) => I_S1 C e s1 /\ I_S2 C e s2.

Global Instance Preserves_S_up_prod
         `{H1 : @Preserves_S_up _ (@I_S1)}
         `{H2 : @Preserves_S_up _ (@I_S2)} :
  Preserves_S_up I_S_prod.
Proof.
  unfold I_S_prod; intros A B C C_ok f x [[s1 s2] Hs12].
  assert (Hs1 : «e_map (fun C => I_S1 _ (C >:: f) x s1) C»). { unerase; now destruct Hs12. }
  assert (Hs2 : «e_map (fun C => I_S2 _ (C >:: f) x s2) C»). { unerase; now destruct Hs12. }
  pattern s1 in Hs1; pattern s2 in Hs2; apply exist in Hs1; apply exist in Hs2; clear Hs12 s1 s2.
  ltac1:(unshelve eapply preserve_S_up with (f := f) in Hs1); try assumption.
  ltac1:(unshelve eapply preserve_S_up with (f := f) in Hs2); try assumption.
  destruct Hs1 as [s1 Hs1], Hs2 as [s2 Hs2]; exists (s1, s2); unerase; auto.
Defined.

Global Instance Preserves_S_dn_prod
         `{H1 : @Preserves_S_dn _ (@I_S1)}
         `{H2 : @Preserves_S_dn _ (@I_S2)} :
  Preserves_S_dn I_S_prod.
Proof.
  unfold I_S_prod; intros A B C C_ok f x [[s1 s2] Hs12].
  assert (Hs1 : «e_map (fun C => I_S1 _ C (frameD f x) s1) C»). { unerase; now destruct Hs12. }
  assert (Hs2 : «e_map (fun C => I_S2 _ C (frameD f x) s2) C»). { unerase; now destruct Hs12. }
  pattern s1 in Hs1; pattern s2 in Hs2; apply exist in Hs1; apply exist in Hs2; clear Hs12 s1 s2.
  ltac1:(unshelve eapply preserve_S_dn with (f := f) in Hs1); try assumption.
  ltac1:(unshelve eapply preserve_S_dn with (f := f) in Hs2); try assumption.
  destruct Hs1 as [s1 Hs1], Hs2 as [s2 Hs2]; exists (s1, s2); unerase; auto.
Defined.

Extraction Inline Preserves_S_up_prod Preserves_S_dn_prod.

End S_prod.

Section FuelAndMetric.

Definition Fuel (fueled : bool) := if fueled then positive else True.

Definition is_empty (fueled : bool) : Fuel fueled -> bool :=
  match fueled with
  | true => fun fuel => match fuel with xH => true | _ => false end
  | false => fun 'I => false
  end.

Definition fuel_dec (fueled : bool) : Fuel fueled -> Fuel fueled :=
  match fueled with
  | true => fun fuel => Pos.pred fuel
  | false => fun fuel => fuel
  end.

Definition lots_of_fuel : positive := (1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1)%positive.

Extraction Inline is_empty fuel_dec lots_of_fuel.

Definition Metric (fueled : bool) :=
  if fueled then unit
  else forall A, frames_t A Root -> univD A -> nat.

Definition run_metric (fueled : bool) (metric : Metric fueled)
           (fuel : Fuel fueled) A (C : frames_t A Root) (e : univD A) : nat :=
  match fueled return Fuel fueled -> Metric fueled -> nat with
  | true => fun fuel 'tt => Pos.to_nat fuel
  | false => fun fuel metric => metric A C e
  end fuel metric.

End FuelAndMetric.

(* The type of the rewriter *)
Section Rewriter.

Context
  (* Fueled rewriters use [positive] as fuel parameter *)
  (fueled : bool)
  (Fuel := Fuel fueled)
  (metric : Metric fueled)
  (run_metric := run_metric fueled metric)
  (* One rewriting step *)
  (Rstep : relation (univD Root))
  (* Delayed computation, parameter, and state variable *)
  (D : Set) (I_D : forall (A : U), univD A -> D -> Prop)
  (R : Set) (I_R : forall (A : U), frames_t A Root -> R -> Prop)
  (S : Set) (I_S : forall (A : U), frames_t A Root -> univD A -> S -> Prop)
  `{HDelay : Delayed _ I_D}.

(* The result returned by a rewriter when called with context C and exp e *)
Record result A (C : erased (frames_t A Root)) (e : univD A) : Set := mk_result {
  resTree : univD A;
  resState : State I_S C resTree;
  resProof : «e_map (fun C => clos_refl_trans _ Rstep (C ⟦ e ⟧) (C ⟦ resTree ⟧)) C» }.

Definition rw_for (fuel : Fuel) A (C : erased (frames_t A Root)) (e : univD A) :=
  forall n `{e_ok _ n} (r : Param I_R C) (s : State I_S C e),
  «e_map (fun n => «e_map (fun C => n = run_metric fuel C e) C») n» ->
  result C e.

Definition rewriter' :=
  forall (fuel : Fuel) A (C : erased (frames_t A Root)) `{e_ok _ C} (e : univD A) (d : Delay I_D e),
  rw_for fuel C (delayD d).

Definition res_chain A (C : erased (frames_t A Root)) `{e_ok _ C} (e : univD A) (m : result C e)
           (k : forall e (s : State I_S C e), result C e) : result C e.
Proof.
  destruct m as [e' s' Hrel1]; cbn in k.
  specialize (k e' s'); destruct k as [e'' s'' Hrel2].
  econstructor > [exact s''|unerase; eapply rt_trans; eauto].
Defined.

Extraction Inline res_chain.

End Rewriter.

End Rewriters.

Require Import L6.Ensembles_util.
Require Import Libraries.Coqlib.
Require Import Coq.Numbers.BinNums Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles
        Coq.Relations.Relations Coq.Classes.Morphisms.

(** ** Usefull definitions and lemmas about functions. *)

Definition codomain {A B} (f : A -> B) : Ensemble B :=
  fun y => exists x, f x = y.

Definition image {A B} (f : A -> B) (S : Ensemble A) :=
  fun y => exists x, In _ S x /\ f x = y.

(** A function is injective in a subdomain *)
Definition injective_subdomain {A B} P (f : A -> B) :=
  forall x x', In _ P x -> In _ P x' -> f x = f x' -> x = x'.

Definition injective {A B} (f : A -> B) := injective_subdomain (Full_set _) f.

(** Extensional equality on a subdomain *)
Definition f_eq_subdomain {A B} S (f1 f2 : A -> B) :=
  forall x, In _ S x -> f1 x = f2 x.

(** Extensional equality *)
Definition f_eq  {A B} (f1 f2 : A -> B) : Prop :=  forall x, f1 x = f2 x.

(** Extend a function. Only works for positives to avoid parameterizing the definition with
  * the decidable equality proof. TODO: fix this *)
Definition extend (f: positive -> positive) (x x' : positive) : (positive -> positive) :=
  fun z => if peq z x then x' else f z.

Notation " f '{' x '~>' y '}' " := (extend f x y) (at level 10, no associativity)
                                   : fun_scope.

Open Scope fun_scope.


(** * Lemmas about [f_eq_subdomain] and [f_eq] *)

Instance equivalence_f_eq_subdomain {A B} S : Equivalence (@f_eq_subdomain A B S). 
Proof. 
  constructor; try now constructor.
  intros f1 f2 Heq x HS; rewrite Heq. reflexivity. eassumption.
  intros f1 f2 f3 Heq1 Heq2 x HS; rewrite Heq1. now eauto. eassumption.
Qed.

Instance equivalence_f_eq {A B} : Equivalence (@f_eq A B).
Proof. 
  constructor; congruence.
Qed.  

Instance f_eq_subdomain_Proper_Same_set {A B} :
  Proper (Same_set A ==> eq ==> eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Hseq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS;
  apply Hfeq; eapply Hseq; eassumption.
Qed.

Instance f_eq_subdomain_Proper_f_eq_l {A B} :
  Proper (eq ==> f_eq ==> eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Heq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS.
  now rewrite <- Heq1; eauto. now rewrite Heq1; eauto.
Qed.

Instance f_eq_subdomain_Proper_f_eq_r {A B} :
  Proper (eq ==> eq ==> f_eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Heq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS.
  now rewrite <- Heq2; eauto. now rewrite Heq2; eauto.
Qed.

Instance f_eq_Proper_f_eq_l {A B} :
  Proper (f_eq ==> eq ==> iff) (@f_eq A B).
Proof.
  intros  f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x.
  now rewrite <- Heq1; eauto. now rewrite Heq1; eauto.
Qed.

Instance f_eq_Proper_f_eq_r {A B} :
  Proper (eq ==> f_eq ==> iff) (@f_eq A B).
Proof.
  intros f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq.
  now rewrite <- Heq2; eauto. now rewrite Heq2; eauto.
Qed.

Lemma f_eq_subdomain_antimon {A B} S S' (f f' : A -> B) :
  Included _ S' S ->
  f_eq_subdomain S f f' ->
  f_eq_subdomain S' f f'.
Proof.
  intros Hinc Hfeq x Hin; eauto.
Qed.

(** * Lemmas about [image] *)

Instance image_Proper_Same_set {A B} : Proper (eq ==> Same_set A ==> Same_set B) image.
Proof.
  intros x1 x2 Heq1 s1 s2 Hseq; subst; split; intros x [y [Hin Heq]]; subst;
  eexists; split; eauto; apply Hseq; eauto.
Qed.

Instance image_Proper_f_eq {A B} : Proper (f_eq ==> eq ==> Same_set B) (@image A B).
Proof.
  intros x1 x2 Heq1 s1 s2 Hseq2; subst; split; intros x [y [Hin Heq]]; subst;
  eexists; split; eauto; rewrite Heq1; eauto; now (constructor; eauto).
Qed.

Lemma image_Union {A B} S1 S2 (g : A -> B) :
  Same_set _ (image g (Union _ S1 S2)) (Union _ (image g S1) (image g S2)).
Proof. 
  split; intros x Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    left. eexists; eauto.
    right. eexists; eauto.
  - inv Hi; destruct H as [x' [Hin Heq]]; subst;
    eexists; split; eauto.
Qed.

Lemma image_Singleton {A B} x (g : A -> B) :
  Same_set _ (image g (Singleton _ x)) (Singleton _ (g x)).
Proof. 
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    eauto.
  - destruct Hi as [x' [Hin Heq]]; subst. eexists; eauto.
Qed.

Lemma image_Empty_set {A B} (g : A -> B) :
  Same_set _ (image g (Empty_set _)) ((Empty_set _)).
Proof. 
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
  - inv Hi.
Qed.

Lemma image_f_eq_subdomain {A B} (f1 f2 : A -> B) S :
  f_eq_subdomain S f1 f2 ->
  Same_set _ (image f1 S) (image f2 S).
Proof.
  intros Heq; split; intros x [y [Hin Heq']]; subst; 
  (eexists; split; [ now eauto |]); now rewrite Heq.
Qed.

Lemma image_monotonic {A B} (f : A -> B) S S' :
  Included _ S S' ->
  Included _ (image f S) (image f S').
Proof.
  intros Hin x [y [Hin' Heq]]; subst. eexists; eauto.
Qed.

(** * Lemmas about [extend] *)

Instance extend_Proper : Proper (f_eq ==> Logic.eq ==> Logic.eq ==> f_eq) extend.
Proof. 
  intros f1 f2 Hfeq x1 x2 Heq1 x3 x4 Hfeq2; subst.
  intros x. unfold extend. destruct (peq x x2); eauto.
Qed.

Lemma extend_gss f x x' :
  f {x ~> x'} x = x'.
Proof. 
  unfold extend. rewrite peq_true. reflexivity.
Qed.

Lemma extend_gso f x x' y :
  y <> x ->
  f {x ~> x'} y = f y.
Proof. 
  intros Heq. unfold extend. rewrite peq_false; eauto.
Qed.

Lemma extend_same f x y :
  f x = x ->
  f {y ~> y} x = x. 
Proof.
  unfold extend. destruct (peq x y); eauto.
Qed.

Lemma f_eq_extend (f f' : positive -> positive) x y :
  f_eq f f' ->
  f_eq (f{x ~> y}) (f'{x ~> y}).
Proof. 
  intros Heq. 
  unfold extend. intros z. 
  destruct (peq z x); eauto.
Qed.

Lemma f_eq_extend_same (f : positive -> positive) x y :
  f x = y ->
  f_eq (f{x ~> y}) f.
Proof. 
  intros Heq x'.
    unfold extend. destruct (peq x' x); eauto.
    congruence. 
Qed.    

Lemma f_eq_subdomain_extend S (f f' : positive -> positive) x y :
  f_eq_subdomain S f f' ->
  f_eq_subdomain (Union _ (Singleton _ x) S) (f{x ~> y}) (f'{x ~> y}).
Proof. 
  intros Heq. 
  unfold extend. intros z Hin. 
  destruct (peq z x). now eauto.
  apply Heq. inv Hin; [| now eauto ]. inv H; congruence. 
Qed.

Lemma f_eq_subdomain_extend_not_In_S_l f1 S f2 x x'  : 
  ~ In _ S x ->
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain S (f1{x~>x'}) f2.
Proof.
  intros Hin Hfeq y HIn.
  rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma f_eq_subdomain_extend_not_In_S_r f1 S f2 x x'  : 
  ~ In _ S x ->
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain S f1 (f2{x~>x'}).
Proof.
  intros Hin Hfeq y HIn.
  rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma image_extend_not_In_S f x x' S :
  ~ In _ S x ->
  Same_set _ (image (f {x ~> x'} ) S) (image f S).
Proof.    
  intros Hnin.
  split; intros y [y' [Hin Heq]]. rewrite extend_gso in Heq.
  now eexists; eauto. intros Hc. subst. contradiction.
  eexists; split; eauto. rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma image_extend_In_S f x x' S :
  In _ S x ->
  Same_set _ (image (f {x ~> x'}) S)
           (Union _ (image f (Setminus _ S (Singleton _ x)))
                  (Singleton _ x')).
Proof.
  intros HinS. split. 
  - intros y [y' [Hin Heq]]; subst. 
    destruct (peq x y').
    + subst. rewrite extend_gss. eauto.
    + rewrite extend_gso; eauto. left.
      eexists; split; eauto. constructor; eauto.
      intros Hc; inv Hc; congruence.
  - intros y Hin.
    destruct (peq x' y); subst.
    + eexists; split; eauto. rewrite extend_gss; eauto.
    + inv Hin. 
      * destruct H as [y' [Hin Heq]]; subst. inv Hin.
        eexists; split. now eauto. rewrite extend_gso; eauto.
        intros Heq; subst. eauto.
      * inv H. congruence. 
Qed.

Lemma image_Setminus_extend f v v' S :
  Included _ (image (f {v ~> v'}) (Setminus _ S  (Singleton positive v)))
           (image f S).
Proof.
  rewrite image_extend_not_In_S.
  apply image_monotonic.
  now apply Setminus_Included.
  intros Hc. inv Hc. eapply H0; eauto.
Qed.

Lemma image_extend_Included f x x' S :
  Included _ (image (f {x ~> x'}) S) (Union _ (image f S) (Singleton _ x')).
Proof.  
  intros y [y' [Hin Heq]]. unfold extend in Heq.
  destruct (peq y' x); subst; [ now eauto |] .
  left. eexists; eauto.
Qed.

Lemma In_image {A B} S f x: 
  In A S x ->
  In B (image f S) (f x).
Proof. 
  intros; repeat eexists; eauto.
Qed.

Lemma Included_image_extend g S x x':
  ~ In _ S x ->
  Included _ (image g S)
           (image (g {x ~> x'}) (Union _ (Singleton _ x) S)).
Proof.
  intros H.
  eapply Included_trans.
  eapply image_extend_not_In_S. eassumption. eapply image_monotonic.
  now apply Included_Union_r.
Qed.

Hint Resolve In_image Included_image_extend : functions_BD.


(** * Lemmas about [injective_subdomain] and [injective] *)

Instance injective_subdomain_Proper_f_eq {A B} : Proper (eq ==> f_eq ==> iff)
                                                   (@injective_subdomain A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq; split; intros Hinj x y Hin1 Hin2 Heq; subst;
  eapply Hinj; eauto. now rewrite !Hfeq. now rewrite <- !Hfeq. 
Qed.

Instance injective_subdomain_Proper_Same_set {A B} : Proper (Same_set _ ==> eq ==> iff)
                                                   (@injective_subdomain A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq; split; intros Hinj x y Hin1 Hin2 Heq; subst;
  eapply Hinj; eauto; now apply Hseq.
Qed.

Instance injective_Proper {A B} : Proper (f_eq ==> iff)
                                         (@injective A B).
Proof.
  now apply injective_subdomain_Proper_f_eq. 
Qed.


Lemma injective_subdomain_antimon {A B} (σ : A -> B) S S' :
  injective_subdomain S σ ->
  Included _ S' S ->
  injective_subdomain S' σ .
Proof. 
  intros Hinj Hinc x y Hin Hin' Heq. eauto.
Qed.

Lemma injective_subdomain_Union {A B} (f : A -> B) S1 S2 :
  injective_subdomain S1 f ->
  injective_subdomain S2 f ->
  Disjoint  _ (image f S1) (image f S2) ->
  injective_subdomain (Union A S1 S2) f.
Proof.
  intros Hinj1 Hinj2 HD x1 x2 Hin1 Hin2 Heq.
  inv Hin1; inv Hin2.
  - eauto.
  - exfalso. eapply HD. constructor; eexists; eauto.
  - exfalso. eapply HD. constructor; eexists; eauto.
  - eauto.
Qed.

Lemma injective_subdomain_Singleton {A B} (f : A -> B) x :
  injective_subdomain (Singleton _ x) f.
Proof.
  intros x1 x2 Hin1 Hin2 Heq. inv Hin1. inv Hin2.
  reflexivity.
Qed.

Lemma injective_subdomain_Empty_set {A B} (f : A -> B) :
  injective_subdomain (Empty_set _) f.
Proof.
  intros x1 x2 Hin1 Hin2 Heq. inv Hin1.
Qed.

Lemma injective_subdomain_extend f x x' S :
  injective_subdomain S f ->
  ~ In _ (image f (Setminus _ S (Singleton _ x))) x' ->
  injective_subdomain (Union _ (Singleton _ x) S) (f {x~>x'}).
Proof.
  intros Hinj Hnin.
  intros y y' Hin1 Hin2.
  destruct (peq x y); subst.
  - rewrite extend_gss. intros Heq.
    destruct (peq y y'); [ now eauto | ].
    rewrite extend_gso in Heq; [| now eauto ]. 
    exfalso. eapply Hnin. eexists; split; [| now eauto ].
    inv Hin2. inv H. congruence.
    constructor; eauto. intros Hc; inv Hc; congruence.
  - rewrite extend_gso; [| now eauto ].
    destruct (peq x y'); subst.
    + rewrite extend_gss. intros Heq. subst.
      exfalso. apply Hnin. eexists.
      split; [| reflexivity ].
      inv Hin1. inv H; congruence. 
      constructor; eauto. intros Hc; inv Hc; congruence.
    + rewrite extend_gso; [| now eauto ].
      intros Heq. eapply Hinj; eauto.
      inv Hin1. inv H; congruence. eassumption.
      inv Hin2. inv H; congruence. eassumption.
Qed.

Lemma injective_subdomain_extend' f x x' S :
  injective_subdomain S f ->
  ~ In _ (image f (Setminus _ S (Singleton _ x))) x' ->
  injective_subdomain S (f {x~>x'}).
Proof.
  intros Hinj Hnin.
  intros y y' Hin1 Hin2.
  destruct (peq x y); subst.
  - rewrite extend_gss. intros Heq.
    destruct (peq y y'); [ now eauto | ].
    rewrite extend_gso in Heq; [| now eauto ]. 
    exfalso. eapply Hnin. eexists; split; [| now eauto ].
    constructor; eauto. intros Hc; eapply n. now inv Hc.
  - rewrite extend_gso; [| now eauto ].
    destruct (peq x y'); subst.
    + rewrite extend_gss. intros Heq. subst.
      exfalso. apply Hnin. eexists.
      split; [| reflexivity ].
      constructor; eauto. intros Hc; eapply n. now inv Hc.
    + rewrite extend_gso; [| now eauto ].
      intros Heq. eapply Hinj; eauto.
Qed.

Lemma injective_extend (f : positive -> positive) x y :
  injective f ->
  ~ In _ (codomain f) y ->
  injective (f{x ~> y}).
Proof.
  intros Hinj Hin x1 x2 __ _ Heq.
  unfold extend in *.
  edestruct (peq x1 x).
  - rewrite <- e in Heq.
    edestruct (peq x2 x1); [ now eauto |].
    exfalso. eapply Hin. eexists; eauto.
  - edestruct (peq x2 x).
    + exfalso. eapply Hin. eexists; eauto.
    + eapply Hinj; try now constructor; eauto.
      assumption.
Qed.

Lemma injective_subdomain_Union_not_In_image {A B} (f : A -> B) S1 S2 :
  injective_subdomain (Union _ S1 S2) f ->
  Disjoint _ S1 S2 ->
  Disjoint _ (image f S1) (image f S2).
Proof. 
  intros Hinj. constructor; intros x Hin. inv Hin. 
  destruct H0 as [y [Hin Heq]]. destruct H1 as [y' [Hin' Heq']].
  subst. eapply Hinj in Heq'; eauto. eapply H. subst; eauto.
Qed.
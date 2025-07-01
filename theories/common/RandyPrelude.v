(** Some basic lemmas that I couldn't find in the standard library
*** and other things shared by the whole development
**)
(* The Abstract Syntax file of Malecha's plugin is needed by all languages
** because of types like Sort, ...
*)

Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.DecBool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Common.exceptionMonad.
Require Import FunInd.
Require Import (*Coq.Arith.Div2*) (*Coq.Numbers.Natural.Peano.NPeano*) Coq.Program.Wf.
Require Import MetaCoq.Utils.bytestring.
Local Open Scope bs_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Infix "++" := String.append : bs_scope.
Bind Scope bs_scope with string.

(** named cases from Software Foundations **)
Section PP.
Local Open Scope bs_scope.

Definition digit_to_string (n:nat): string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end%nat.

Program Fixpoint nat_to_string (n:nat) {measure n}: string :=
  (match n <? 10 as x return n <? 10 = x -> string with
     | true => fun _ => digit_to_string n
     | false => fun pf =>
                  let m := Nat.div n 10 in
                  (nat_to_string m) ++ (digit_to_string (n - 10 * m))
   end eq_refl)%nat.
Next Obligation.
  apply (Nat.div_lt n 10%nat).
  destruct n. unfold Nat.ltb in *. simpl in *.
  discriminate. auto with arith.
  auto with arith.
Defined.
Next Obligation.
  revert a. apply measure_wf, lt_wf.
Defined.
End PP.


Definition
  andb_true_true (b1 b2:bool) (q:b1 && b2 = true) : b1 = true /\ b2 = true.
Proof.
  destruct b1; destruct b2; cbn in q.
  + split; reflexivity.
  + split. reflexivity. assumption.
  + split. assumption. reflexivity.
  + split. assumption. assumption.
Defined.

Definition
  true_true_andb (b1 b2:bool) (q1:b1 = true) (q2:b2 = true) : b1 && b2 = true.
Proof.
  destruct b1; destruct b2; [reflexivity | discriminate ..].
Qed.

(** snoc lists *)
Definition unit (A:Type) (a:A) : list A := cons a nil.
Definition snoc (A:Type) (l:list A) (a:A) : list A := l ++ unit a.
Notation "b ::: bs" := (snoc bs b)  (at level 100).

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Close Scope string_scope.

(** my stuff **)
Ltac inversion_Clear h := inversion h; subst; clear h.

Ltac SomeSubst :=
  repeat match goal with
           | [ H:(_ = Some _) |- _ ] => rewrite H
           | [ H:(Some _ = _) |- _ ] => rewrite H
         end.

Ltac dstrct1 h :=
  let xx := fresh "x"
  with jj := fresh "j"
  in destruct h as [xx jj].
Ltac dstrct2 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with jj := fresh "j"
  in destruct h as [xx [yy jj]].
Ltac dstrct3 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j"
  in destruct h as [xx [yy [zz jj]]].
Ltac dstrct4 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with ww := fresh "w"
  with jj := fresh "j" in
  destruct h as [xx [yy [zz [ww jj]]]].
Ltac dstrct5 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with ww := fresh "w"
  with uu := fresh "u"
  with jj := fresh "j" in
  destruct h as [xx [yy [zz [ww [uu jj]]]]].
Ltac dstrct6 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with ww := fresh "w"
  with uu := fresh "u"
  with aa := fresh "a"
  with jj := fresh "j" in
  destruct h as [xx [yy [zz [ww [uu [aa jj]]]]]].
Ltac dstrct7 h :=
  let xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with ww := fresh "w"
  with uu := fresh "u"
  with aa := fresh "a"
  with bb := fresh "b"
  with jj := fresh "j" in
  destruct h as [xx [yy [zz [ww [uu [aa [bb jj]]]]]]].
Ltac dstrctn h :=
  first [dstrct7 h | dstrct6 h | dstrct5 h | dstrct4 h |
         dstrct3 h | dstrct2 h | dstrct1 h].
Ltac is_inv h := dstrctn h; discriminate.
Ltac not_isn :=
  let hh := fresh "h" in intros hh; dstrctn hh; discriminate.
Ltac not_isApp := not_isn.
Ltac not_isLambda := not_isn.
Ltac not_isCase := not_isn.
Ltac not_isFix := not_isn.
Ltac not_isCast := not_isn.
Ltac not_isDummy := not_isn.
Ltac not_isProof := not_isn.
Ltac not_isInd := not_isn.
Ltac not_isWrong := not_isn.
Ltac not_isConstruct := not_isn.

Lemma Nat_eqb_rfl: forall n m, Nat.eqb n m = true -> n = m.
Proof.
  induction n; induction m; intros.
  - reflexivity.
  - cbn in H. discriminate.
  - cbn in H. discriminate.
  - cbn in H. erewrite IHn. reflexivity. assumption.
Qed.

Lemma rfl_Nat_eqb: forall n, Nat.eqb n n = true.
Proof.
  induction n; intros; cbn.
  - reflexivity.
  - assumption.
Qed.

Lemma triv_exists:
  forall (A B:Type) (C:A -> B) (a:A), exists (aa:A), C a = C aa.
  intros A B C a. exists a. reflexivity.
Qed.

Definition xor (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
  end.


(** turn decidable comparisons into Prop comparisons **)
Ltac Compare_Prop :=
  match goal with
    | [ H:(_ ?= _) = Eq |- _ ] =>
      let j := fresh "j" in
      assert (j := proj1 (Nat.compare_eq_iff _ _) H); clear H
    | [ H:(_ ?= _) = Lt |- _ ] =>
      let j := fresh "j" in
      assert (j := proj1 (Nat.compare_lt_iff _ _) H); clear H
    | [ H:(_ ?= _) = Gt |- _ ] =>
      let j := fresh "j" in
      assert (j := proj1 (Nat.compare_gt_iff _ _) H); clear H
    | [ H:(_ =? _) = true |- _ ] =>
      let j := fresh "j" in
      assert (j:= proj1 (Nat.eqb_eq _ _) H); clear H
    | [ H:(_ <=? _) = true |- _ ] =>
      let j := fresh "j" in
      assert (j:= proj1 (Nat.leb_le _ _) H); clear H
    | [ H:(_ <? _) = true |- _ ] =>
      let j := fresh "j" in
      assert (j:= proj1 (Nat.ltb_lt _ _) H); clear H
  end.

Ltac compare_Prop H := first [
                           let j := fresh "j" in
                           assert (j := proj1 (Nat.compare_eq_iff _ _) H)
                         | let j := fresh "j" in
                           assert (j := proj1 (Nat.compare_lt_iff _ _) H)
                         | let j := fresh "j" in
                           assert (j := proj1 (Nat.compare_gt_iff _ _) H)
                         | let j := fresh "j" in
                           assert (j:= proj1 (Nat.eqb_eq _ _) H)
                         | let j := fresh "j" in
                           assert (j:= proj1 (Nat.leb_le _ _) H)
                         | let j := fresh "j" in
                           assert (j:= proj1 (Nat.ltb_lt _ _) H) ].


Lemma match_cn_Eq:
  forall m n, m = n ->
              forall (A:Type) (a b c: A),
                match m ?= n with
                  | Datatypes.Eq => a
                  | Lt => b
                  | Gt => c
                end = a.
Proof.
  intros m n h A a b c.
  rewrite (proj2 (Nat.compare_eq_iff _ _) h). reflexivity.
Qed.

Lemma match_cn_Lt:
  forall m n, m < n ->
              forall  (A:Type) (a b c: A),
                match m ?= n with
                  | Datatypes.Eq => a
                  | Lt => b
                  | Gt => c
                end = b.
Proof.
  intros m n h A a b c.
  rewrite (proj2 (Nat.compare_lt_iff _ _) h). reflexivity.
Qed.

Lemma match_cn_Gt:
  forall m n, m > n ->
              forall (A:Type) (a b c: A),
                match m ?= n with
                  | Datatypes.Eq => a
                  | Lt => b
                  | Gt => c
                end = c.
Proof.
  intros m n h A a b c.
  rewrite (proj2 (Nat.compare_gt_iff _ _) h). reflexivity.
Qed.

Lemma compare_match_eq:
  forall n m, n = m ->
              forall {A} (x y z:A),
                match n ?= m with
                  | Datatypes.Eq => x
                  | Lt => y
                  | Gt => z end = x.
Proof.
  intros. rewrite H. rewrite (proj2 (Nat.compare_eq_iff _ _)); reflexivity.
Qed.


Ltac nreflexivity h := elim h; reflexivity.

Ltac myInjection h := injection h; intros; subst; clear h.

Lemma opt_notSome_None:
  forall (A:Type) (oa:option A), (forall a:A, oa <> Some a) -> oa = None.
  induction oa; intros.
  - assert (j:= H a). nreflexivity j.
  - reflexivity.
Qed.


Section Sec_list_eq_dec.
  Variable A:Type.
  Hypothesis eq_dec : forall (x y : A), x = y \/ x <> y.
  Lemma list_eq_dec : forall l l':list A, l = l' \/ l <> l'.
  Proof.
    induction l; destruct l'.
    - left. reflexivity.
    - right. intros h. discriminate.
    - right. intros h. discriminate.
    - destruct (eq_dec a a0); subst.
      + destruct (IHl l'). subst.
        * left. reflexivity.
        * right. intros h. injection h. contradiction.
      + right. intros h. injection h. contradiction.
  Qed.
End Sec_list_eq_dec.


(** well-founded induction and recursion on natural number measure **)
Lemma complete_nat_induct:
  forall (P:nat -> Prop)
         (ih:forall (n:nat), (forall (x:nat), x < n -> P x) -> P n),
  forall m, P m.
  intros P ih m. apply ih. induction m.
  + intros x j. lia.
  + intros x j. inversion j.
    * apply ih. assumption.
    * assert (k: x < m). lia. apply IHm. assumption.
Qed.

Lemma wf_ind:
  forall (A:Type) (f:A -> nat) (P:A -> Prop)
         (wfih:forall (t:A), (forall (x:A), f x < f t -> P x) -> P t),
  forall k, P k.
  intros A f P wfih k.
  eapply (complete_nat_induct (fun n:nat => forall (y:A), n = f y -> P y)).
  - intros. apply wfih. intros. eapply H. rewrite H0. apply H1. reflexivity.
  - reflexivity.
Qed.  

Definition wf_rec:
  forall (A:Type) (f:A -> nat) (P:A -> Type)
         (wfih:forall (t:A), (forall (x:A), f x < f t -> P x) -> P t),
  forall k, P k.
  intros A f P wfih k.
  eapply ((well_founded_induction_type lt_wf)
            (fun n:nat => forall (y:A), n = f y -> P y)).
  - intros. apply wfih. intros. eapply X. instantiate (1:= f x0). subst.
    assumption. reflexivity.
  - reflexivity.
Defined.


(** Want to unfold all occurrances of nm in context and goal
 *** don't know how  
Ltac Unfold nm :=
  repeat match goal with
        | [ H:(_ nm _) |- _ ] => unfold nm in H
        | [ |- _ nm _ ] => unfold nm
      end.
 ***)

(* when reduction stops *)
Definition no_step {A:Set} (R:A -> A -> Prop) (a:A) :=
  forall (b:A), ~ R a b.

Lemma neq_sym: forall (A:Type) (a b:A), a <> b -> b <> a.
  intuition auto.
Qed.

Function list_to_zero (n:nat) : list nat :=
  match n with
    | 0 => nil
    | S n => n :: (list_to_zero n)
  end.

Lemma In_list_to_zero:
  forall n m, In n (list_to_zero m) -> n < m.
Proof.
  induction m; intros.
  - cbn in *. contradiction.
  - destruct H.
    + subst; lia.
    + pose proof (IHm H). lia.
Qed.

Lemma list_to_zero_length:
  forall m, List.length (list_to_zero m) = m.
Proof.
  induction m. reflexivity.
  cbn. rewrite IHm. reflexivity.
Qed.

Definition list_to_1 (n:nat) : list nat :=
  match n with
  | 0 => nil
  | S 0 => nil
  | S n => n :: (list_to_zero n)
  end.

Lemma list_to_zero_S:
  forall n, list_to_zero (S n) = (cons n nil) ++ list_to_zero n.
Proof.
  induction n. reflexivity. cbn. reflexivity.
Qed.
  

Definition list_to_n (n:nat) : list nat := List.rev (list_to_zero n).

Lemma In_list_to_n:
  forall n m, In n (list_to_n m) -> n < m.
Proof.
  intros. apply In_list_to_zero. rewrite <- rev_involutive.
  apply (proj1 (in_rev _ _)). exact H.
Qed.

Lemma list_to_n_length:
  forall m, List.length (list_to_n m) = m.
Proof.
  intros. unfold list_to_n. rewrite length_rev. apply list_to_zero_length.
Qed.

Lemma list_to_n_S:
  forall n, list_to_n (S n) = (list_to_n n) ++ (cons n nil).
Proof.
  induction n; reflexivity.
Qed.
  
Fixpoint exnNth (A:Type) (xs:list A) (n:nat) : exception A :=
  match xs, n with
  | nil, _ =>
    raise ("(exnNth:" ++ nat_to_string (List.length xs) ++ ","
                      ++ nat_to_string n ++ ")")%bs
    | cons y ys, 0 => ret y
    | cons y ys, S m => exnNth ys m
  end.

Lemma bool_not_neq: forall (b1 b2:bool), (~ b1 <> b2) <-> b1 = b2.
  split; induction b1; induction b2; intuition auto.
Qed.

Lemma bool_neq_false: forall (b:bool), (b <> false) <-> b = true.
  split; induction b; intuition auto.
Qed.

Lemma bs_not_cons_bs:
  forall (B:Type) (b:B) (bs:list B), bs <> (b::bs).
  intros B b bs h.
  assert (j: List.length bs = List.length (b :: bs)). rewrite <- h; reflexivity.
  simpl in j. lia.
Qed.

Lemma deMorgan_impl: forall (A B:Prop), (A -> B) -> (~B -> ~A).
  intuition auto.
Qed.

Lemma orb3_true_elim:
  forall b1 b2 b3, b1 || b2 || b3 = true ->
                   {b1 = true} + {b2 = true} + {b3 = true}.
  intros b1 b2 b3 h.
  assert (j1: {b1 = true} + {b2 || b3 = true}).
  { apply orb_true_elim. rewrite orb_assoc. assumption. }
  destruct j1.
  - intuition auto.
  - assert (j2: {b2 = true} + {b3 = true}). apply (orb_true_elim _ _ e).
    destruct j2; intuition auto.
Qed.  

Lemma fold_left_bool_mono:
  forall (ds:list bool),
    fold_left (fun (b c:bool) => b || c) ds false = true ->
    fold_left (fun (b c:bool) => b || c) ds true = true.
  induction ds; intro h; intuition auto. induction a. 
  - exact h.
  - simpl. simpl in h. apply (IHds h).
Qed.

Lemma fold_left_bool_head:
  forall (A:Type) (P:A -> bool) (d:A) (ds:list A),
    fold_left (fun (b:bool) (t:A) => b || P t) (d::ds) false =
    fold_left (fun (b:bool) (t:A) => b || P t) ds (P d).
  simpl. intros. reflexivity.
Qed.

Lemma A_fold_left_bool_mono:
  forall (A:Type) (P:A -> bool) (ds:list A),
    fold_left (fun (b:bool) (t:A) => b || P t) (ds) false = true ->
    fold_left (fun (b:bool) (t:A) => b || P t) (ds) true = true.
  induction ds. simpl. reflexivity.
  simpl. intros h. case_eq (P a); intro j; rewrite j in h.
  - assumption.
  - apply (IHds h).
Qed.

Lemma append_nil_1:
  forall (A:Type) (ls ms:list A), (ls++ms) = nil -> ms = nil.
  induction ms; induction ls; intros h.
  - reflexivity.
  - reflexivity.
  - simpl in h. discriminate h.
  - simpl in h. discriminate h.
Qed.

Lemma nat_compare_EQ: forall n, Nat.compare n n = Eq.
  intro n. apply (proj2 (Nat.compare_eq_iff n n)). reflexivity.
Qed.
#[global] Hint Rewrite nat_compare_EQ : core.

Lemma notNone_Some:
  forall (A:Type) (o:option A), o <> None -> exists a, o = Some a.
  destruct o.
  - intros h. exists a. reflexivity.
  - intros h. destruct h. reflexivity.
Qed.

(** lemmas about [max] used in reasoning about wcbvEval, that has a
*** step counter (timer, or fuel)
**)
Lemma max_commutes: forall m n, max m n = max n m.
induction m; induction n; simpl; try reflexivity.
rewrite IHm. reflexivity.
Qed.

Lemma max_associates: forall l m n, max l (max m n) = max (max l m) n.
induction l; induction m; induction n; simpl; try reflexivity.
rewrite IHl. reflexivity.
Qed.

Lemma max_0: forall m, max m 0 = m.
induction m; simpl; reflexivity.
Qed.

Lemma max_fst: forall m n, max m n >= m.
induction m; induction n; simpl; intuition auto with arith.
Qed.

Lemma max_snd: forall m n, max m n >= n.
induction m; induction n; simpl; intuition auto with arith.
Qed.

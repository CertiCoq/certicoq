(** Some basic lemmas that I couldn't find in the standard library
*** and other things shared by the whole development
**)
(* The Abstract Syntax file of Malecha's plugin is needed by all languages
** because of types like Sort, ...
*)

(****)
Add LoadPath "../common" as Common.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.DecBool.
Require Import Coq.omega.Omega.
Require Import Common.exceptionMonad.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** named cases from Software Foundations **)
Require Coq.Strings.String. 
Open Scope string_scope.

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

Ltac nreflexivity h := elim h; reflexivity.

Ltac myInjection h := injection h; intros; subst.

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

  
(** well-founded induction on natural number measure **)
Lemma complete_nat_induct:
  forall (P:nat -> Prop)
         (ih:forall (n:nat), (forall (x:nat), x < n -> P x) -> P n),
  forall m, P m.
  intros P ih m. apply ih. induction m.
  + intros x j. omega.
  + intros x j. inversion j.
    * apply ih. assumption.
    * assert (k: x < m). omega. apply IHm. assumption.
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
intuition.
Qed.

Fixpoint list_to_zero (n:nat) : list nat :=
  match n with
    | 0 => nil
    | S n => n :: (list_to_zero n)
  end.

Fixpoint exnNth (A:Type) (xs:list A) (n:nat) : exception A :=
  match xs, n with
    | nil, _ => raise "exnNth; no hit"
    | cons x xs, 0 => ret x
    | cons x xs, S m => exnNth xs m
  end.

Lemma bool_not_neq: forall (b1 b2:bool), (~ b1 <> b2) <-> b1 = b2.
split; induction b1; induction b2; intuition.
Qed.

Lemma bool_neq_false: forall (b:bool), (b <> false) <-> b = true.
split; induction b; intuition.
Qed.

Lemma bs_not_cons_bs:
  forall (B:Type) (b:B) (bs:list B), bs <> (b::bs).
intros B b bs h.
assert (j: List.length bs = List.length (b :: bs)). rewrite <- h; reflexivity.
simpl in j. intuition.
Qed.

Lemma deMorgan_impl: forall (A B:Prop), (A -> B) -> (~B -> ~A).
intuition.
Qed.

Lemma orb3_true_elim:
  forall b1 b2 b3, b1 || b2 || b3 = true ->
                   {b1 = true} + {b2 = true} + {b3 = true}.
intros b1 b2 b3 h.
assert (j1: {b1 = true} + {b2 || b3 = true}).
{ apply orb_true_elim. rewrite orb_assoc. assumption. }
destruct j1.
- intuition.
- assert (j2: {b2 = true} + {b3 = true}). apply (orb_true_elim _ _ e).
  destruct j2; intuition.
Qed.  

Lemma fold_left_bool_mono:
  forall (ds:list bool),
       fold_left (fun (b c:bool) => b || c) ds false = true ->
       fold_left (fun (b c:bool) => b || c) ds true = true.
induction ds; intro h; intuition. induction a. 
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

Lemma nat_compare_EQ: forall n, nat_compare n n = Eq.
intro n. apply (proj2 (nat_compare_eq_iff n n)). reflexivity.
Qed.
Hint Rewrite nat_compare_EQ.

Lemma notNone_Some:
  forall (A:Type) (o:option A), o <> None -> exists a, o = Some a.
destruct o.
- intros h. exists a. reflexivity.
- intros h. destruct h. reflexivity.
Qed.


Lemma string_eq_character:
     forall (b c:ascii) (bs cs:string),
       (String b bs) = (String c cs) -> b = c /\ bs = cs.
intros b c bs cs h.
destruct (ascii_dec b c); injection h; intuition.
Qed.

Lemma string_neq_character:
     forall (b c:ascii) (bs cs:string),
       (String b bs) <> (String c cs) -> b <> c \/ bs <> cs.
intros b c bs cs.
destruct (ascii_dec b c).
- rewrite e. destruct (string_dec bs cs).
  + rewrite e0. intuition.
  + intuition.
- intuition.
Qed.

Definition ascii_eq_bool (a1 a2:ascii) : bool :=
  ifdec (ascii_dec a1 a2) true false.

Lemma ascii_eq_bool_eq:
  forall (a1 a2:ascii),
    ascii_eq_bool a1 a2 = true -> a1 = a2.
intros a1 a2 h. case (ascii_dec a1 a2). intuition.
intro ha.
assert (j:ascii_eq_bool a1 a2 = false).
apply (ifdec_right (ascii_dec a1 a2) ha true false).
rewrite h in j. discriminate.
Qed.

Lemma ascii_eq_bool_rfl:
  forall (a:ascii), ascii_eq_bool a a = true.
intro a. case (ascii_dec a a); intuition.
unfold ascii_eq_bool. rewrite ifdec_left; intuition.
Qed.

Lemma ascii_neq_bool_neq:
  forall (a1 a2:ascii),
    ascii_eq_bool a1 a2 = false -> a1 <> a2.
intros a1 a2 h j. subst. rewrite ascii_eq_bool_rfl in h. discriminate.
Qed.

Lemma ascii_eq_bool_neq:
  forall (a1 a2:ascii), a1 <> a2 -> ascii_eq_bool a1 a2 = false.
intros a1 a2 h. unfold ascii_eq_bool. rewrite ifdec_right; intuition.
Qed.

Definition string_eq_bool (a1 a2:string) : bool :=
  ifdec (string_dec a1 a2) true false.

Lemma string_eq_bool_rfl:
  forall (s:string), string_eq_bool s s = true.
induction s. reflexivity. unfold string_eq_bool. eapply ifdec_left.
intuition.
Qed.
Hint Resolve string_eq_bool_rfl.

Lemma string_eq_bool_eq:
  forall (s1 s2:string), string_eq_bool s1 s2 = true -> s1 = s2.
intros s1 s2 h. case (string_dec s1 s2). intuition.
intro hs.
assert (j:string_eq_bool s1 s2 = false).
apply (ifdec_right (string_dec s1 s2) hs true false).
rewrite h in j. discriminate.
Qed.

Lemma string_eq_bool_neq:
  forall (s1 s2:string), s1 <> s2 -> string_eq_bool s1 s2 = false.
intros s1 s2 h. unfold string_eq_bool. rewrite  ifdec_right; intuition.
Qed.

Lemma string_neq_bool_neq:
  forall (a1 a2:string),
    string_eq_bool a1 a2 = false -> a1 <> a2.
intros a1 a2 h j. subst. rewrite string_eq_bool_rfl in h. discriminate.
Qed.

Fixpoint string_compare (ss ts:string) : Prop :=
  match string_eq_bool ss ts with
    | true => True
    | false => False
  end.

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
induction m; induction n; simpl; intuition.
Qed.

Lemma max_snd: forall m n, max m n >= n.
induction m; induction n; simpl; intuition.
Qed.


Section PP.
Require Import Coq.Strings.String Coq.Arith.Div2 Coq.Numbers.Natural.Peano.NPeano Coq.Program.Wf.
Local Open Scope string_scope.

Definition digit_to_string (n:nat): string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end%nat.

Program Fixpoint nat_to_string (n:nat) {measure n}: string :=
  (match n <? 10 as x return n <? 10 = x -> string with
     | true => fun _ => digit_to_string n
     | false => fun pf =>
                  let m := NPeano.Nat.div n 10 in
                  (nat_to_string m) ++ (digit_to_string (n - 10 * m))
   end eq_refl)%nat.
Next Obligation.
  apply (NPeano.Nat.div_lt n 10%nat).
  destruct n. unfold NPeano.Nat.ltb in *. simpl in *.
  discriminate. auto with arith.
  auto with arith.
Defined.

End PP.


(***
Goal
  forall (A B:Type) (x:option A) (f:A -> B) (b:B),
    match x with
      | Some y => Some (f y)
      | None => None
    end = Some b -> b = f y.
***)
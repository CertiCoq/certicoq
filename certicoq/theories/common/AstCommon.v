
Add LoadPath "../../../template-coq-coq-8.5-coqOpam/theories" as Template.
Add LoadPath "../common" as Common.

Require Export Template.Ast.
Require Import PArith.BinPos.
Require Import Strings.String.
Require Import Arith.Peano_dec.
Require Import Logic.Eqdep_dec.

Require Import Common.RandyPrelude.


Lemma name_dec: forall (s1 s2:name), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2; try (solve [right; intros h; discriminate]).
- left; reflexivity.
- destruct (string_dec i i0).
  + subst. left. reflexivity.
  + right. injection. intuition.
Qed.

Lemma universe_dec: forall x y : universe, {x = y} + {x <> y}.
exact Coq.PArith.BinPos.Pos.eq_dec.
Qed.

Lemma sort_dec: forall (s1 s2:sort), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2;
try (solve [right; intros; discriminate]);
try (solve [left; reflexivity]).
destruct (universe_dec u u0).
- subst. left. reflexivity.
- right. intros h. injection h. intuition.
Qed.

Lemma cast_kind_dec: forall (c1 c2:cast_kind), {c1 = c2}+{c1 <> c2}.
induction c1; induction c2;
try (solve [right; intros; discriminate]);
try (solve [left; reflexivity]).
Qed.

Lemma inductive_dec: forall (s1 s2:inductive), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2.
destruct (string_dec s s0); destruct (eq_nat_dec n n0); subst;
try (solve [left; reflexivity]); 
right; intros h; elim n1; injection h; intuition.
Qed.

Lemma nat_list_dec : forall l1 l2 : list nat, {l1 = l2} + {l1 <> l2}.
Proof.
  induction l1; induction l2; try solve [left; reflexivity].
  right. congruence.
  right; congruence.
  destruct (eq_nat_dec a a0); subst.
  destruct (IHl1 l2); subst.
  left; reflexivity.
  right; congruence.
  right; congruence.
Qed.

Inductive Srt := SProp | SSet | SType.

Lemma Srt_dec: forall (s1 s2:Srt), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2;
try (solve [right; intros h; discriminate]);
try (solve [left; reflexivity]).
Qed.

(** lists of terms !!!! ***
Section term_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma Term_dec: 
  forall (s t:term), s = t \/ s <> t.
induction s; induction t; cross.
- destruct (eq_nat_dec n n0); [lft | rght].
- destruct (string_dec i i0); [lft | rght].
- destruct (eq_nat_dec n n0); [lft | rght].
- destruct (eq_nat_dec n n0); [lft | rght].
- destruct (sort_dec s s0); [lft | rght].
- destruct (cast_kind_dec c c0); destruct (IHs1 t1); destruct (IHs2 t2);
  [lft | rght ..]. 
- destruct (name_dec n n0);
    destruct (IHs1 t1); destruct (IHs2 t2); [lft | rght ..].
- destruct (name_dec n n0);
    destruct (IHs1 t1); destruct (IHs2 t2); [lft | rght ..]. 
- destruct (name_dec n n0);
    destruct (IHs1 t1); destruct (IHs2 t2); destruct (IHs3 t3); 
    [lft | rght ..]. 
- destruct (IHs t). destruct (IHt l0). destruct (H1 t2); [lft | rght ..].
- induction t; cross. destruct (string_dec s s0); [lft | rght].
- induction t; cross. destruct (inductive_dec i i0); [lft | rght].
- induction t; cross.
  destruct (inductive_dec i i0); destruct (eq_nat_dec n n0); [lft | rght .. ].
- induction t2; cross.
  destruct (eq_nat_dec n n0); destruct (H t2_1); destruct (H0 t2_2);
  destruct (H1 t2); [lft | rght .. ].
- induction t; cross.
  destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
- induction tt; cross. lft.
- induction tt; cross. destruct (H t1); destruct (H0 tt); [lft | rght .. ].
- induction ee; cross. lft.
- induction ee; cross.
  destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
  destruct (H t1); destruct (H0 t2); destruct (H1 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.
**************)
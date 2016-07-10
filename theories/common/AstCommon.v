
Add LoadPath "../common" as Common.

Require Export Template.Ast.
Require Import Coq.PArith.BinPos.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.

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

(** certiCoq representation of sorts **)
Inductive Srt := SProp | SSet | SType.

Lemma Srt_dec: forall (s1 s2:Srt), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2;
try (solve [right; intros h; discriminate]);
try (solve [left; reflexivity]).
Qed.

(** certiCoq representation of inductive types **)
(* a constructor; the string only for human readability *)
Record Cnstr := mkCnstr { CnstrNm:string; CnstrArity:nat }.
Definition defaultCnstr := {| CnstrNm:=""; CnstrArity:= 0 |}.
(* a type is a list of Cnstrs; string only for human readability *)
Record ityp := mkItyp { itypNm:string; itypCnstrs:list Cnstr }.
Definition defaultItyp := {| itypNm:=""; itypCnstrs:=nil |}.
(* a mutual type package is a list of ityps *)
Definition itypPack := list ityp.

Lemma Cnstr_dec: forall C1 C2:Cnstr, C1 = C2 \/ C1 <> C2.
Proof.
  destruct C1 as [Cn1 Ca1], C2 as [Cn2 Ca2],  (string_dec Cn1 Cn2),
  (eq_nat_dec Ca1 Ca2).
  - left. subst. reflexivity.
  - right. intros h. assert (j:= f_equal CnstrArity h).
    simpl in j. contradiction.
  - right. intros h. assert (j:= f_equal CnstrNm h).
    simpl in j. contradiction.
  - right. intros h. assert (j:= f_equal CnstrNm h).
    simpl in j. contradiction.
Qed.

Lemma ityp_dec: forall i j:ityp, i = j \/ i <> j.
Proof.
  destruct i as [iN iC], j as [jN jC]. destruct (string_dec iN jN);
  destruct (list_eq_dec Cnstr_dec iC jC); subst;
  try (left; reflexivity);
  right; intros h.
  - assert (j:= f_equal itypCnstrs h). simpl in j. contradiction.
  - assert (j:= f_equal itypNm h). simpl in j. contradiction.
  - assert (j:= f_equal itypNm h). simpl in j. contradiction.
Qed.  

(** environments and programs parameterized by a notion of term **)
Section trm_Sec.
Variable trm: Set.
Variable trm_dec: forall (s t:trm), s = t \/ s <> t.
  
Inductive envClass := 
| ecTrm (_:trm)
| ecTyp (_:nat) (_:itypPack)
| ecAx.

Lemma isAx_dec:
  forall (e:envClass), e = ecAx \/ e <> ecAx.
Proof.
  destruct e.
  - right. intros h. discriminate.
  - right. intros h. discriminate.
  - left. reflexivity.
Qed.

Lemma envClass_dec: forall e f:envClass, e = f \/ e <> f.
Proof.
  destruct e, f; try (right; intros h; discriminate).
  - destruct (trm_dec t t0).
    + left. subst. reflexivity.
    + right. intros h. injection h. intros. contradiction.
  - destruct (eq_nat_dec n n0), (Common.RandyPrelude.list_eq_dec ityp_dec i i0).
    + subst. left. reflexivity.
    + right. intros h. injection h. contradiction.
    + right. intros h. injection h. contradiction.
    + right. intros h. injection h. contradiction.
  - left. reflexivity.
Qed.

(** An environ is a list of definitions.
***  Currently ignoring Types and Axioms **)
Definition environ := list (string * envClass).
Record Program : Type := mkPgm { main:trm; env:environ }.

End trm_Sec.

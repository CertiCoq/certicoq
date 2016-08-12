Add LoadPath "../common" as Common.

Require Export Template.Ast.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.

Require Import Common.exceptionMonad.
Require Import Common.RandyPrelude.
Require Import Common.classes.

Open Scope list_scope.
Set Implicit Arguments.


Lemma name_dec: forall (s1 s2:name), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2; try (solve [right; intros h; discriminate]).
- left; reflexivity.
- destruct (string_dec i i0).
  + subst. left. reflexivity.
  + right. injection. intuition.
Defined.

Lemma universe_dec: forall x y : universe, {x = y} + {x <> y}.
exact Coq.PArith.BinPos.Pos.eq_dec.
Defined.

Lemma sort_dec: forall (s1 s2:sort), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2;
try (solve [right; intros; discriminate]);
try (solve [left; reflexivity]).
destruct (universe_dec u u0).
- subst. left. reflexivity.
- right. intros h. injection h. intuition.
Defined.

Lemma cast_kind_dec: forall (c1 c2:cast_kind), {c1 = c2}+{c1 <> c2}.
induction c1; induction c2;
try (solve [right; intros; discriminate]);
try (solve [left; reflexivity]).
Defined.

Lemma inductive_dec: forall (s1 s2:inductive), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2.
destruct (string_dec s s0); destruct (eq_nat_dec n n0); subst;
try (solve [left; reflexivity]); 
right; intros h; elim n1; injection h; intuition.
Defined.

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
Defined.

Require Import NArith.NArith.
Instance NEq: Eq N := { eq_dec := N.eq_dec }.
Instance EqPair A B `(Eq A) `(Eq B) : Eq (A * B).
Proof.
  constructor; intros [x y] [x' y'].
  destruct (eq_dec x x'). destruct (eq_dec y y').
  left; congruence.
  right; congruence.
  right; congruence.
Defined.

Instance InductiveEq: Eq inductive := { eq_dec := inductive_dec }.

(** certiCoq representation of sorts **)
Inductive Srt := SProp | SSet | SType.

Lemma Srt_dec: forall (s1 s2:Srt), {s1 = s2}+{s1 <> s2}.
induction s1; induction s2;
try (solve [right; intros h; discriminate]);
try (solve [left; reflexivity]).
Defined.


(** certiCoq representation of inductive types **)
(* a constructor; the string only for human readability *)
Record Cnstr := mkCnstr { CnstrNm:string; CnstrArity:nat }.

(* a type is a list of Cnstrs; string only for human readability *)
Record ityp := mkItyp { itypNm:string; itypCnstrs:list Cnstr }.

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

(** Hack: we code axioms in the environment as ecTyp with itypPack = nil **)
Inductive envClass := 
| ecTrm (_:trm)
| ecTyp (_:nat) (_:itypPack).

Definition ecAx : envClass := ecTyp 0 nil.

(** for debugging **)
Definition print_ec (ec:envClass) : string :=
  match ec with
    | ecTrm _ => "(ecTrm)"
    | ecTyp _ (cons _ _) => "(ecTyp)"
    | ecTyp _ nil => "(ecAx)"
  end.

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
Qed.

Lemma isAx_dec:
  forall (e:envClass), e = ecAx \/ e <> ecAx.
Proof.
  unfold ecAx. intros.
  apply envClass_dec.
Qed.

(** An environ is a list of definitions. **)
Definition environ := list (string * envClass).
Record Program : Type := mkPgm { main:trm; env:environ }.

(** for debugging **)
Fixpoint print_environ (e:environ) : string :=
  match e with
    | nil => "(envnil)"
    | cons (str, ec) ecs => "(envcons " ++ str ++ (print_ec ec) ++ ")" ++
                                        (print_environ ecs)
  end.

(** environments are finite functions **)
Inductive fresh (nm:string) : environ -> Prop :=
| fcons: forall s p ec,
         fresh nm p -> nm <> s -> fresh nm ((s,ec)::p)
| fnil: fresh nm nil.
Hint Constructors fresh.

Lemma fresh_dec: forall nm p, (fresh nm p) \/ ~(fresh nm p).
induction p.
- left. auto.
- destruct a. destruct IHp. destruct (string_dec nm s).
 + subst. right. intros h. inversion_Clear h. nreflexivity H4.
 + left. constructor; auto.
 + right. intros h. elim H. inversion_Clear h. assumption.
Qed.

Lemma fresh_tl: forall nm p, fresh nm p -> fresh nm (tl p).
induction 1.
- simpl. assumption.
- auto.
Qed.

Lemma fresh_strengthen:
  forall rs qs nm, fresh nm (rs++qs) -> fresh nm qs.
induction rs; intros qs nm h.
- assumption.
- inversion h. subst. auto.
Qed.

Lemma fresh_not_head:
  forall nm t p nmtp, fresh nm nmtp -> nmtp = ((nm,t)::p) -> False.
induction 1; intros h.
- inversion h. subst. auto.
- discriminate h.
Qed.


(** looking a name up in an environment **)
(** Hack: we code axioms in the environment as ecTyp with itypPack = nil **)
Inductive Lookup: string -> environ -> envClass -> Prop :=
| LHit: forall s p t, Lookup s ((s,t)::p) t
| LMiss: forall s1 s2 p t ec,
           s2 <> s1 -> Lookup s2 p ec -> Lookup s2 ((s1,t)::p) ec.
Hint Constructors Lookup.
Definition LookupDfn s p t := Lookup s p (ecTrm t).
Definition LookupTyp s p n i := Lookup s p (ecTyp n i) /\ i <> nil.
Definition LookupAx s p := Lookup s p ecAx.

(** equivalent lookup functions **)
Function lookup (nm:string) (p:environ) : option envClass :=
  match p with
   | nil => None
   | cons (s,ec) p => if (string_eq_bool nm s) then Some ec
                      else lookup nm p
  end.

Definition lookupDfn (nm:string) (p:environ) : exception trm :=
  match lookup nm p with
    | Some (ecTrm t) => ret t
    | _ => raise ("lookupDfn; fails on " ++ nm)
  end.

Definition lookupTyp (nm:string) (p:environ) : exception (nat * itypPack) :=
  match lookup nm p with
    | Some (ecTyp n ((cons _ _) as t)) => Ret (n, t)
    | _ => raise ("lookupTyp; fails on " ++ nm)
  end.

Lemma Lookup_lookup:
  forall nm p t, Lookup nm p t -> lookup nm p = Some t.
induction 1; intros; subst.
- simpl. rewrite (string_eq_bool_rfl s). reflexivity.
- simpl. rewrite (string_eq_bool_neq H). destruct t; assumption.
Qed.

Lemma lookup_Lookup:
  forall nm p t, lookup nm p = Some t -> Lookup nm p t.
induction p; intros t h. inversion h.
destruct a. destruct (string_dec nm s); simpl in h.
- subst. rewrite (string_eq_bool_rfl s) in h. 
  injection h. intros; subst. apply LHit.
- apply LMiss. assumption. apply IHp. 
  rewrite (string_eq_bool_neq n) in h. assumption.
Qed.

Lemma not_lookup_not_Lookup:
 forall (nm:string) (p:environ) (ec:envClass),
   ~(lookup nm p = Some ec) <-> ~(Lookup nm p ec).
split; eapply deMorgan_impl.
- apply (Lookup_lookup).
- apply (lookup_Lookup).
Qed.

Lemma LookupDfn_lookupDfn:
  forall nm p t, Lookup nm p t ->
                 forall te, t = (ecTrm te) -> lookupDfn nm p = Ret te.
  induction 1; intros; subst; unfold lookupDfn, lookup.
- rewrite (string_eq_bool_rfl s). reflexivity.
- rewrite (string_eq_bool_neq H). 
  destruct t; apply IHLookup; reflexivity.
Qed.

Lemma lookupDfn_LookupDfn:
  forall nm p t, lookupDfn nm p = Ret t -> Lookup nm p (ecTrm t).
Proof.
  intros nm p t. intros. apply lookup_Lookup.
  unfold lookupDfn in H. 
  case_eq (lookup nm p); intros; rewrite H0 in H.
  - destruct e.
    + myInjection H. reflexivity.
    + discriminate.
  - discriminate.
Qed.

Lemma Lookup_dec:
  forall s p, (exists t, Lookup s p t) \/ (forall t, ~ Lookup s p t).
Proof.
  induction p; intros.
  - right. intros t h. inversion h.
  - destruct IHp; destruct a; destruct (string_dec s s0); subst.
    + left. destruct H. exists e. apply LHit.
    + left. destruct H. exists x. apply LMiss; assumption.
    + destruct e.
      * left. exists (ecTrm t). apply LHit.
      * left. exists (ecTyp n i). apply LHit. 
    + right. intros t h. inversion_Clear h. 
      * elim n. reflexivity.
      * elim (H t). assumption.
Qed.

Lemma Lookup_fresh_neq:
  forall nm2 p t, Lookup nm2 p t -> forall nm1, fresh nm1 p -> nm1 <> nm2.
induction 1; intros.
- inversion H. assumption.
- apply IHLookup. apply (fresh_tl H1).
Qed.

Lemma fresh_Lookup_fails:
  forall nm p ec, fresh nm p -> ~(Lookup nm p ec).
induction 1; intro h; inversion h; subst; auto.
Qed.

Lemma fresh_lookup_None: forall nm p, fresh nm p <-> lookup nm p = None.
split. 
- induction 1; simpl; try reflexivity.
  + rewrite string_eq_bool_neq; assumption.
- induction p; auto.
  + destruct a. destruct (string_dec nm s). 
    * subst. simpl. rewrite string_eq_bool_rfl. discriminate.
    * simpl. rewrite string_eq_bool_neq; try assumption. intros h.
      apply fcons; intuition.
Qed.

Lemma Lookup_single_valued:
  forall (nm:string) (p:environ) (t r:envClass),
    Lookup nm p t -> Lookup nm p r -> t = r.
Proof.
  intros nm p t r h1 h2. 
  assert (j1:= Lookup_lookup h1).
  assert (j2:= Lookup_lookup h2).
  rewrite j1 in j2. myInjection j2. reflexivity. 
Qed.

Lemma LookupDfn_single_valued:
  forall (nm:string) (p:environ) (t r:trm),
    LookupDfn nm p t -> LookupDfn nm p r -> t = r.
Proof.
  unfold LookupDfn. intros nm p t r h1 h2.
  injection (Lookup_single_valued h1 h2). intuition.
Qed.

Lemma Lookup_weaken:
  forall s p t, Lookup s p t -> 
      forall nm ec, fresh nm p -> Lookup s ((nm, ec) :: p) t.
intros s p t h1 nm ec h2.
assert (j1:= Lookup_fresh_neq h1 h2). apply LMiss. apply neq_sym. assumption.
assumption.
Qed.

Lemma Lookup_strengthen:
  forall (nm1:string) pp t, Lookup nm1 pp t -> 
       forall nm2 ec p, pp = (nm2,ec)::p -> nm1 <> nm2 -> Lookup nm1 p t.
intros nm1 pp t h nm2 ecx px j1 j2. subst. assert (k:= Lookup_lookup h).
simpl in k. rewrite (string_eq_bool_neq j2) in k.
apply lookup_Lookup. assumption.
Qed.

(** find an ityp in an itypPack **)
Definition getInd (ipkg:itypPack) (inum:nat) : exception ityp :=
  exnNth ipkg inum.

(** find a Cnstr in an ityp **)
Definition getCnstr (ip:ityp) (cnum:nat) : exception Cnstr :=
  exnNth (itypCnstrs ip) cnum.


(** total constructor arity (including parameters) is only computed
 ***  n the fly during translation from L2 to L3 **)
Definition cnstrArity (p:environ) (i:inductive) (cndx:nat) : exception nat :=
  match i with
    | mkInd nm tndx =>
      match lookupTyp nm p with
        | Exc str => raise ("cnstrArity; lookupTyp fails: " ++ str)
        | Ret (npars, itypkg) =>
          match getInd itypkg tndx with
            | Exc str => raise ("cnstrArity; getInd fails: " ++ str)
            | Ret ity => match getCnstr ity cndx with
                           | Exc str =>
                             raise ("cnstrArity; getCnstr fails: " ++ str)
                           | Ret itp => ret (npars + (CnstrArity itp))
                         end
          end
       end
  end.

End trm_Sec.

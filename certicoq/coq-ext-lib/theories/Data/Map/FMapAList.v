Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section keyed.
  Variable K : Type.
  Variable R : K -> K -> Prop.
  Variable RD_K : RelDec R.

  Variable V : Type.

  Definition alist : Type := list (K * V).

  Definition alist_remove (k : K) (m : alist) : alist :=
    List.filter (fun x => negb (k ?[ R ] (fst x))) m.

  Definition alist_add (k : K) (v : V) (m : alist) : alist :=
    (k, v) :: alist_remove k m.

  Fixpoint alist_find (k : K) (m : alist) : option V :=
    match m with
      | nil => None
      | (k',v) :: ms =>
        if k ?[ R ] k' then
          Some v
        else
          alist_find k ms
    end.

  Section fold.
    Import MonadNotation.
    Local Open Scope monad_scope.

    Variables T : Type.
    Variable f : K -> V -> T -> T.

    Fixpoint fold_alist (acc : T) (map : alist) : T :=
      match map with
        | nil => acc
        | (k,v) :: m =>
          let acc := f k v acc in
          fold_alist acc m
      end.
  End fold.

  Definition alist_union (m1 m2 : alist) : alist :=
    fold_alist alist_add m2 m1.

  Global Instance Map_alist : Map K V alist :=
  { empty  := nil
  ; add    := @alist_add
  ; remove := alist_remove
  ; lookup := alist_find
  ; union  := @alist_union
  }.

  Section proofs.
    Hypothesis RDC_K : RelDec_Correct RD_K.
    Require Import RelationClasses.

    Hypothesis Refl : Reflexive R.
    Hypothesis Sym : Symmetric R.
    Hypothesis Trans : Transitive R.

    Definition mapsto_alist (m : alist) k v : Prop :=
      alist_find k m = Some v.

    Lemma mapsto_alist_cons : forall k v m k' v',
                                mapsto_alist ((k',v') :: m) k v <->
                                (   (mapsto_alist m k v /\ ~R k k')
                                 \/ (R k k' /\ v = v')).
    Proof.
      unfold mapsto_alist; intuition; simpl in *.
      { consider (k ?[ R ] k'); intros.
        { right. inversion H0; auto. }
        { left. auto. } }
      { consider (k ?[ R ] k'); intros; intuition. }
      { consider (k ?[ R ] k'); intros; intuition. congruence. }
    Qed.

    Theorem mapsto_lookup_alist : forall (k : K) (v : V) (m : list (K * V)),
                                   lookup k m = Some v <-> mapsto_alist m k v.
    Proof.
      reflexivity.
    Qed.

    Theorem mapsto_remove_eq_alist : forall (m : list (K * V)) (k : K) (v : V),
                                       ~mapsto_alist (remove k m) k v.
    Proof.
      unfold mapsto_alist, remove, alist_remove; simpl. intros.
      induction m; simpl; auto.
      { congruence. }
      { destruct a; simpl in *.
        consider (k ?[ R ] k0); auto; intros.
        simpl. consider (k ?[ R ] k0); auto. }
    Qed.

    Theorem mapsto_remove_neq_alist : forall (m : list (K * V)) (k : K),
                                      forall k', ~ R k k' -> forall v', (mapsto_alist m k' v' <-> mapsto_alist (remove k m) k' v').
    Proof.
      unfold mapsto_alist, add; simpl. intros.
      induction m; simpl in *.
      { intuition. }
      { destruct a. simpl in *.
        consider (k' ?[ R ] k0); intros.
        { consider (k ?[ R ] k0); intros.
          { exfalso. eauto. }
          { simpl. consider (k' ?[ R ] k0); intros.
            { intuition. }
            { exfalso; auto. } } }
        { rewrite IHm.
          consider (k ?[ R ] k0); simpl; intros.
          { intuition. }
          { consider (k' ?[ R ] k0); intros.
            { exfalso; auto. }
            { intuition. } } } }
    Qed.

    Theorem mapsto_add_eq_alist : forall (m : list (K * V)) (k : K) (v : V),
                                 mapsto_alist (add k v m) k v.
    Proof.
      unfold mapsto_alist, add, alist_add; simpl. intros.
      consider (k ?[ R ] k); auto.
      intro. exfalso. apply H. reflexivity.
    Qed.

    Theorem mapsto_add_neq_alist : forall (m : list (K * V)) (k : K) (v : V),
                                     forall k', ~ R k k' -> forall v', (mapsto_alist m k' v' <-> mapsto_alist (add k v m) k' v').
    Proof.
      unfold mapsto_alist, add; simpl. intros.
      consider (k' ?[ R ] k); try solve [ intros; exfalso; auto ].
      intros. eapply mapsto_remove_neq_alist in H. eapply H.
    Qed.

    Global Instance MapLaws_alist : MapOk R Map_alist.
    Proof.
      refine {| mapsto := fun k v m => mapsto_alist m k v |};
      eauto using mapsto_lookup_alist, mapsto_add_eq_alist, mapsto_add_neq_alist.
      { intros; intro. inversion H. }
    Qed.

  End proofs.

  Global Instance Foldable_alist : Foldable alist (K * V) :=
    fun _ f b => fold_alist (fun k v => f (k,v)) b.

End keyed.

Global Instance Functor_alist K : Functor (alist K) :=
{ fmap := fun T U f => map (fun x => (fst x, f (snd x))) }.

(** Performance Test **)
(*
Module TEST.
  Definition m := alist nat nat.
  Instance Map_m : Map nat (alist nat).
    apply Map_alist. eauto with typeclass_instances.
  Defined.

  Definition z : m :=
    (fix fill n acc : m :=
      let acc := add n n acc in
      match n with
        | 0 => acc
        | S n => fill n acc
      end) 500 empty.

  Time Eval compute in
    let z := z in
    (fix find_all n : unit :=
      let _ := lookup n z in
      match n with
        | 0 => tt
        | S n => find_all n
      end) 500.
End TEST.
*)
Require Import Coq.Lists.List.
Require Import Relations RelationClasses.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section hlist.
  Context {iT : Type}.
  Variable F : iT -> Type.

  Inductive hlist : list iT -> Type :=
  | Hnil  : hlist nil
  | Hcons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | l :: _ => F l
                               end with
      | Hnil => tt
      | Hcons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | Hnil => tt
      | Hcons _ _ _ x => x
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
          | nil => fun _ => Hnil
          | a :: b => fun h => Hcons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.

  Fixpoint hlist_app ll lr (h : hlist ll) : hlist lr -> hlist (ll ++ lr) :=
    match h in hlist ll return hlist lr -> hlist (ll ++ lr) with
      | Hnil => fun x => x
      | Hcons _ _ hd tl => fun r => Hcons hd (hlist_app tl r)
    end.

  Lemma app_ass_trans : forall {T} (a b c : list T), (a ++ b) ++ c = a ++ b ++ c.
  Proof.
    induction a; simpl.
    reflexivity.
    intros. f_equal. apply IHa.
  Defined.

  Lemma app_nil_r_trans : forall {T} (a : list T), a ++ nil = a.
  Proof.
    induction a; simpl.
    reflexivity.
    f_equal. apply IHa.
  Defined.

  Lemma hlist_app_nil_r
  : forall ls (h : hlist ls),
      hlist_app h Hnil = match eq_sym (app_nil_r_trans ls) in _ = t return hlist t with
                           | eq_refl => h
                         end.
  Proof.
    induction h; simpl; intros; auto.
    rewrite IHh at 1.
    unfold eq_trans. unfold f_equal. unfold eq_sym.
    clear. revert h.
    generalize dependent (app_nil_r_trans ls). 
    destruct e. reflexivity.
  Qed.

  Fixpoint hlist_rev' ls ls' (h : hlist ls) : hlist ls' -> hlist (rev ls ++ ls') :=
    match h in hlist ls return hlist ls' -> hlist (rev ls ++ ls') with
      | Hnil => fun h => h
      | Hcons l ls0 x h' => fun hacc =>
        match app_ass_trans (rev ls0) (l :: nil) ls' in _ = t return hlist t -> hlist _ with
          | eq_refl => fun x => x
        end (@hlist_rev' _ (l :: ls') h' (Hcons x hacc))
    end.

  Definition hlist_rev ls (h : hlist ls) : hlist (rev ls) :=
    match app_nil_r_trans (rev ls) in _ = t return hlist t with
      | eq_refl => hlist_rev' h Hnil
    end.

  Lemma hlist_rev_nil : hlist_rev Hnil = Hnil.
  Proof.
    reflexivity.
  Qed.

  (** TODO: I need hlist_rev_cons **)


  Section equiv.
    Variable eqv : forall x, relation (F x).

    Inductive equiv_hlist : forall ls, hlist ls -> hlist ls -> Prop :=
    | hlist_eqv_nil : equiv_hlist Hnil Hnil
    | hlist_eqv_cons : forall l ls x y h1 h2, eqv x y -> equiv_hlist h1 h2 ->
      @equiv_hlist (l :: ls) (Hcons x h1) (Hcons y h2).

    Global Instance Reflexive_equiv_hlist (R : forall t, Reflexive (@eqv t)) ls
    : Reflexive (@equiv_hlist ls).
    Proof.
      red. induction x; constructor; auto. reflexivity.
    Qed.

    Global Instance Symmetric_equiv_hlist (R : forall t, Symmetric (@eqv t)) ls
    : Symmetric (@equiv_hlist ls).
    Proof.
      red. induction 1.
      { constructor. }
      { constructor. symmetry. assumption. auto. }
    Qed.

    Global Instance Transitive_equiv_hlist (R : forall t, Transitive (@eqv t)) ls
    : Transitive (@equiv_hlist ls).
    Proof.
      red. induction 1.
      { intro; assumption. }
      { rewrite (hlist_eta z).
        refine
          (fun H' =>
             match H' in @equiv_hlist ls X Y
                   return
                   match ls as ls return hlist ls -> hlist ls -> Prop with
                     | nil => fun _ _ : hlist nil => True
                     | l :: ls => fun (X Y : hlist (l :: ls)) =>
                                    forall Z x xs,
                                      eqv (hlist_hd Z) (hlist_hd X) ->
                                      equiv_hlist xs (hlist_tl X) ->
                                      (forall z : hlist ls,
                                         equiv_hlist (hlist_tl X) z ->
                                         equiv_hlist (hlist_tl Z) z) ->
                                      @equiv_hlist (l :: ls) Z Y
                   end X Y
             with
               | hlist_eqv_nil => I
               | hlist_eqv_cons l ls x y h1 h2 pf pf' => _
             end (Hcons x h1) x _ H H0 (@IHequiv_hlist)).
        intros. rewrite (hlist_eta Z).
        constructor. simpl in *. etransitivity. eassumption. eassumption.
        eapply H3. simpl in *. eassumption. }
    Qed.

  End equiv.

  Lemma hlist_nil_eta : forall (h : hlist nil), h = Hnil.
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Lemma hlist_cons_eta : forall a b (h : hlist (a :: b)),
    h = Hcons (hlist_hd h) (hlist_tl h).
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Section injection.
    Variable rd : RelDec (@eq iT).
    Variable rdc : RelDec_Correct rd.

    Global Instance Injection_hlist_cons ls t (a : F t) (b : hlist ls) c d
    : Injective (Hcons a b = Hcons c d) :=
      { result := a = c /\ b = d }.
    Proof.
      abstract (inversion 1; eapply inj_pair2 in H2; eapply inj_pair2 in H1; auto).
    Defined.

    Theorem equiv_eq_eq : forall ls (x y : hlist ls),
                            equiv_hlist (fun x => @eq _) x y <-> x = y.
    Proof.
      induction x; simpl; intros.
      { split. inversion 1. rewrite hlist_nil_eta. reflexivity.
        intros; subst; constructor. }
      { split.
        { inversion 1; subst.
          apply inj_pair2 in H2.
          apply inj_pair2 in H5.
          apply inj_pair2 in H4. subst. f_equal. eapply IHx. eauto. }
        { intros; subst. constructor; auto.
          reflexivity. } }
    Qed.
  End injection.

  Fixpoint hlist_get ls a (m : member a ls) : hlist ls -> F a :=
    match m in member _ ls return hlist ls -> F a with
      | MZ _ => hlist_hd
      | MN _ _ r => fun hl => hlist_get r (hlist_tl hl)
    end.

  Fixpoint hlist_nth_error {ls} (hs : hlist ls) (n : nat)
    : option (match nth_error ls n with
                | None => unit
                | Some x => F x
              end) :=
    match hs in hlist ls return option (match nth_error ls n with
                                          | None => unit
                                          | Some x => F x
                                        end)
      with
      | Hnil => None
      | Hcons l ls h hs =>
        match n as n return option (match nth_error (l :: ls) n with
                                      | None => unit
                                      | Some x => F x
                                    end)
          with
          | 0 => Some h
          | S n => hlist_nth_error hs n
        end
    end.

  Fixpoint hlist_nth ls (h : hlist ls) (n : nat) :
    match nth_error ls n with
      | None => unit
      | Some t => F t
    end :=
    match h in hlist ls , n as n
      return match nth_error ls n with
               | None => unit
               | Some t => F t
             end
      with
      | Hnil , 0 => tt
      | Hnil , S _ => tt
      | Hcons _ _ x _ , 0 => x
      | Hcons _ _ _ h , S n => hlist_nth h n
    end.

  Fixpoint nth_error_hlist_nth ls (n : nat)
  : option (hlist ls -> match nth_error ls n with
                          | None => Empty_set
                          | Some x => F x
                        end) :=
    match ls as ls
          return option (hlist ls -> match nth_error ls n with
                                       | None => Empty_set
                                       | Some x => F x
                                     end)
    with
      | nil => None
      | l :: ls =>
        match n as n
              return option (hlist (l :: ls) -> match nth_error (l :: ls) n with
                                                  | None => Empty_set
                                                  | Some x => F x
                                                end)
        with
          | 0 => Some hlist_hd
          | S n =>
            match nth_error_hlist_nth ls n with
              | None => None
              | Some f => Some (fun h => f (hlist_tl h))
            end
        end
    end.

  Definition cast1 T l
  : forall (l' : list T) n v,
      nth_error l n = Some v -> Some v = nth_error (l ++ l') n.
  Proof.
    induction l. intros. 
    { exfalso. destruct n; inversion H. }
    { destruct n; simpl; intros; auto. }
  Defined.

  Definition cast2 T l
  : forall (l' : list T) n,
      nth_error l n = None ->
      nth_error l' (n - length l) = nth_error (l ++ l') n.
  Proof.
    induction l; simpl.
    { destruct n; simpl; auto. }
    { destruct n; simpl; auto.
      inversion 1. }
  Defined.

  Theorem hlist_nth_hlist_app
  : forall l l' (h : hlist l) (h' : hlist l') n,
    hlist_nth (hlist_app h h') n =
    match nth_error l n as k
      return nth_error l n = k ->
      match nth_error (l ++ l') n with
        | None => unit
        | Some t => F t
      end
      with
      | Some _ => fun pf =>
        match cast1 _ _ _ pf in _ = z ,
          eq_sym pf in _ = w
          return match w with
                   | None => unit
                   | Some t => F t
                 end ->
          match z with
            | None => unit
            | Some t => F t
          end
          with
          | eq_refl , eq_refl => fun x => x
        end (hlist_nth h n)
      | None => fun pf =>
        match cast2 _ _ _ pf in _ = z
          return match z with
                   | Some t => F t
                   | None => unit
                 end
          with
          | eq_refl => hlist_nth h' (n - length l)
        end
    end eq_refl.
  Proof.
    induction h; simpl; intros.
    { destruct n; simpl in *; reflexivity. }
    { destruct n; simpl.
      { reflexivity. }
      { rewrite IHh. reflexivity. } }
  Qed.

  Section type.
    Variable eqv : forall x, type (F x).

    Global Instance type_hlist (ls : list iT): type (hlist ls) :=
    { equal := @equiv_hlist (fun x => @equal _ (eqv x)) ls
    ; proper :=
      (fix recur ls (h : hlist ls) : Prop :=
        match h with
          | Hnil => True
          | Hcons _ _ x y => proper x /\ recur _ y
        end) ls
    }.

    Variable eqvOk : forall x, typeOk (eqv x).

    Global Instance typeOk_hlist (ls : list iT): typeOk (type_hlist ls).
    Proof.
      constructor.
      { induction ls; intros.
        { rewrite (hlist_eta x) in *. rewrite (hlist_eta y) in *.
          clear. compute; auto. }
        { rewrite (hlist_eta x) in *. rewrite (hlist_eta y) in *.
          simpl in H. inversion H; clear H; subst.
          inv_all; repeat match goal with
                            | [ H : exists x, _ |- _ ] => destruct H
                          end; subst. simpl.
          eapply IHls in H7. eapply only_proper in H3; auto.
          destruct x3. destruct x4. destruct x2. destruct x1.
          intuition. } }
      { intro. induction ls; simpl.
        { rewrite (hlist_eta x); intros; constructor. }
        { rewrite (hlist_eta x); intros; intuition; constructor.
          eapply preflexive; eauto with typeclass_instances.
          eapply IHls; eauto. } }
      { red. induction 1.
        { constructor. }
        { constructor. symmetry. assumption. assumption. } }
      { red. induction 1.
        { auto. }
        { intro H1.
          etransitivity; [ | eassumption ].
          constructor; eauto. } }
    Qed.

    Global Instance proper_hlist_app l l' : proper (@hlist_app l l').
    Proof.
      do 6 red. induction 1; simpl; auto.
      { intros. constructor; eauto.
        eapply IHequiv_hlist. exact H1. }
    Qed.

    Lemma hlist_app_assoc : forall ls ls' ls''
                                 (a : hlist ls) (b : hlist ls') (c : hlist ls''),
      hlist_app (hlist_app a b) c =
      match eq_sym (app_ass_trans ls ls' ls'') in _ = t return hlist t with
        | eq_refl => hlist_app a (hlist_app b c)
      end.
    Proof.
      intros ls ls' ls''.
      generalize (eq_sym (app_assoc_reverse ls ls' ls'')).
      induction ls; simpl; intros.
      { rewrite (hlist_eta a); simpl.
        reflexivity. }
      { rewrite (hlist_eta a0). simpl.
        inversion H.
        erewrite (IHls H1).
        unfold f_equal. unfold eq_trans. unfold eq_sym.
        generalize (app_ass_trans ls ls' ls'').
        rewrite <- H1.
        clear. intro.
        generalize dependent (hlist_app (hlist_tl a0) (hlist_app b c)).
        destruct e. reflexivity. }
    Qed.

    Lemma hlist_app_assoc' : forall ls ls' ls''
                                 (a : hlist ls) (b : hlist ls') (c : hlist ls''),
      hlist_app a (hlist_app b c) =
      match app_ass_trans ls ls' ls'' in _ = t return hlist t with
        | eq_refl => hlist_app (hlist_app a b) c
      end.
    Proof.
      intros ls ls' ls''.
      generalize (app_assoc_reverse ls ls' ls'').
      induction ls; simpl; intros.
      { rewrite (hlist_eta a); simpl. reflexivity. }
      { rewrite (hlist_eta a0). simpl.
        inversion H.
        erewrite (IHls H1).
        unfold eq_trans, f_equal.
        generalize (app_ass_trans ls ls' ls'').
        rewrite <- H1. clear; intro.
        generalize dependent (hlist_app (hlist_app (hlist_tl a0) b) c).
        destruct e. reflexivity. }
    Qed.

    Fixpoint hlist_split ls ls' : hlist (ls ++ ls') -> hlist ls * hlist ls' :=
      match ls as ls return hlist (ls ++ ls') -> hlist ls * hlist ls' with
        | nil => fun h => (Hnil, h)
        | l :: ls => fun h =>
                       let (a,b) := @hlist_split ls ls' (hlist_tl h) in
                       (Hcons (hlist_hd h) a, b)
      end.

    Lemma hlist_app_hlist_split : forall ls' ls (h : hlist (ls ++ ls')),
      hlist_app (fst (hlist_split ls ls' h)) (snd (hlist_split ls ls' h)) = h.
    Proof.
      induction ls; simpl; intros; auto.
      rewrite (hlist_eta h); simpl.
      specialize (IHls (hlist_tl h)).
      destruct (hlist_split ls ls' (hlist_tl h)); simpl in *; auto.
      f_equal. auto.
    Qed.

    Lemma hlist_split_hlist_app : forall ls' ls (h : hlist ls) (h' : hlist ls'),
      hlist_split _ _ (hlist_app h h') = (h,h').
    Proof.
      induction ls; simpl; intros.
      { rewrite (hlist_eta h); simpl; auto. }
      { rewrite (hlist_eta h); simpl.
        rewrite IHls. reflexivity. }
    Qed.

  End type.

End hlist.

Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.

Section hlist_map.
  Variable A : Type.
  Variable F : A -> Type.
  Variable G : A -> Type.
  Variable ff : forall x, F x -> G x.

  Fixpoint hlist_map (ls : list A) (hl : hlist F ls) {struct hl} : hlist G ls :=
    match hl in @hlist _ _ ls return hlist G ls with
      | Hnil => Hnil
      | Hcons _ _ hd tl =>
        Hcons (ff hd) (hlist_map tl)
    end.
End hlist_map.

Arguments hlist_map {_ _ _} _ {_} _.

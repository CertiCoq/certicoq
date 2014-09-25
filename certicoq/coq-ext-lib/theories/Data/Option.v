Require Import ExtLib.Core.Type.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.FunctorLaws.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v =>
    match v with
      | None => d
      | Some x => f x d
    end.

Global Instance Traversable_option : Traversable option :=
{| mapT := fun F _ _ _ f o =>
  match o with
    | None => pure None
    | Some o => ap (pure (@Some _)) (f o)
  end
|}.

Global Instance Applicative_option : Applicative option :=
{| pure := Some
 ; ap := fun _ _ f x =>
           match f , x with
             | Some f , Some x => Some (f x)
             | _ , _ => None
           end
|}.

Global Instance Functor_option : Functor option :=
{| fmap := fun _ _ f x => match x with
                            | None => None
                            | Some x => Some (f x)
                          end |}.

Section type.
  Variable T : Type.
  Variable tT : type T.

  Definition eqv_option rT (a b : option T) :=
    match a , b with
      | None , None => True
      | Some a , Some b => rT a b
      | _ , _ => False
    end.

  Global Instance type_option : type (option T) :=
  { equal := eqv_option equal
  ; proper := fun x => match x with
                         | None => True
                         | Some y => proper y
                       end }.

  Variable tTOk : typeOk tT.

  Global Instance typeOk_option : typeOk type_option.
  Proof.
    constructor.
    { destruct x; destruct y; simpl; auto; try contradiction; intros.
      unfold proper in *. simpl in *.
      destruct tTOk.
      eapply only_proper in H. intuition. }
    { red. destruct x; simpl; auto. intro. eapply preflexive; [ | eapply H ]. eapply equiv_prefl; auto. }
    { red. destruct x; destruct y; simpl; auto. intros.
      destruct tTOk. apply equiv_sym. auto. }
    { red. destruct x; destruct y; destruct z; intros; try contradiction; auto.
      simpl in *. destruct tTOk.
      etransitivity; eauto. }
  Qed.

  Global Instance proper_Some : proper (@Some T).
  Proof. compute; auto. Qed.

  Global Instance proper_None : proper (@None T).
  Proof. compute; auto. Qed.

End type.

Global Instance FunctorLaws_option : FunctorLaws Functor_option type_option.
Proof.
  constructor.
  { simpl. red. destruct x; destruct y; simpl; auto.
    red in H0. intros. etransitivity. eapply H0. 2: eauto.
    eapply proper_left; eauto. }
  { red; simpl. red; simpl. red; simpl; intros.
    destruct x; destruct y; simpl in *; auto.
    unfold compose. eauto using equal_app. }
  { red; simpl. red; simpl. red; simpl; intros.
    destruct x0; destruct y0; eauto.
    red in H2. simpl. eauto using equal_app. }
Qed.

Global Instance Injective_Some (T : Type) (a b : T) : Injective (Some a = Some b) :=
{ result := a = b }.
abstract (inversion 1; auto).
Defined.

Require EquivDec.

Global Instance EqDec_option (T : Type) (EDT : EquivDec.EqDec T (@eq T)) : EquivDec.EqDec (option T) (@eq _).
Proof.
  red. unfold Equivalence.equiv, RelationClasses.complement. intros.
  change (x = y -> False) with (x <> y).
  decide equality. apply EDT.
Qed.

Section OptionEq.
  Variable T : Type.
  Variable EDT : RelDec (@eq T).

  (** Specialization for equality **)
  Global Instance RelDec_eq_option : RelDec (@eq (option T)) :=
  { rel_dec := fun x y =>
    match x , y with
      | None , None => true
      | Some x , Some y => eq_dec x y
      | _ , _ => false
    end }.

  Variable EDCT : RelDec_Correct EDT.

  Global Instance RelDec_Correct_eq_option : RelDec_Correct RelDec_eq_option.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros; try congruence;
      f_equal; try match goal with
                     | [ H : context [ eq_dec ?X ?Y ] |- _ ] =>
                       consider (eq_dec X Y)
                     | [ |- context [ eq_dec ?X ?Y ] ] =>
                       consider (eq_dec X Y)
                   end; auto; congruence.
  Qed.

End OptionEq.

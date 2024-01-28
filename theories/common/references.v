Require Import Coq.Classes.RelationClasses.
Require Import Relation_Definitions.
From Coq.Strings Require Import String Ascii.
From Coq.Bool Require Import Bool.
From compcert Require Import Maps.
(** Type of references, abstracting the global reference types of Coq.

  In Coq, they will be implemented as positives or bignums, as physical
  equality cannot be leveraged in the system.

  In the extracted compiler, they can remain as
  Globnames.global_references, or to optimize a little more, a
  hashconsed version of it that can be used for fast success _and_
  failure tests.

  Not only the string representation needs to change, the environment
  representation as a list (reference * declaration) needs to be moved
  to a Map datastructure. We have efficient maps of strings implemented
  here.
*)

Class Eqb (A : Type) :=
  { eqb : A -> A -> bool }.

(* TODO improve *)
#[global] Instance ascii_eq : Eqb ascii :=
  { eqb s s' := if ascii_dec s s' then true else false }.

(* TODO improve *)
#[global] Instance string_eq : Eqb string :=
  { eqb s s' := if string_dec s s' then true else false }.

Definition reforder {A} (f : A -> A -> comparison) :=
  fun x y => f x y = Lt.

Class ReferenceType (A : Type) :=
  { reference_eq :> Eqb A;
    reference_compare : A -> A -> comparison ;
    reference_of_string : string -> A ;
    string_of_reference : A -> string ;
    reference_order := fun x y => reference_compare x y = Lt ;
    reference_order_strict :> StrictOrder reference_order }.

Definition bool_compare (b b' : bool) :=
  match b, b' with
  | true, true => Eq
  | true, false => Gt
  | false, true => Lt
  | false, false => Eq
  end.

Local Notation " 'comp' c '?=' f " :=
  (match c with
   | Eq => f
   | x => x
   end) (at level 10, f at level 200).

Definition ascii_compare (a a' : ascii) :=
  let 'Ascii a b c d e f g h := a in
  let 'Ascii a' b' c' d' e' f' g' h' := a' in
  comp (bool_compare a a') ?=
  comp (bool_compare b b') ?=
  comp (bool_compare c c') ?=
  comp (bool_compare d d') ?=
  comp (bool_compare e e') ?=
  comp (bool_compare f f') ?=
  comp (bool_compare g g') ?=
  bool_compare h h'.

Fixpoint string_compare (s s' : string) :=
  match s, s' with
  | EmptyString, EmptyString => Eq
  | EmptyString, _ => Lt
  | _, EmptyString => Gt
  | String a s, String a' s' =>
    comp (ascii_compare a a') ?= string_compare s s'
  end.

Require Import NArith.BinNat.

Definition ascii_compare_N (a a' : ascii) : comparison :=
  N.compare (N_of_ascii a) (N_of_ascii a').

Lemma ascii_compare_N_view (a a' : ascii) : ascii_compare a a' = ascii_compare_N a a'.
Proof.
  unfold ascii_compare_N.
  case N.compare_spec.
  + intros. apply (f_equal ascii_of_N) in H.
    rewrite !ascii_N_embedding in H. rewrite H.
    destruct a';
      repeat (match reverse goal with
                [ b : bool |- _ ] => destruct b
              end); simpl; reflexivity.
Admitted.

#[global] Instance ascii_reftype : ReferenceType ascii.
Proof.
  refine {| reference_compare := ascii_compare |}.
  intro. exact Space. intro c. exact (String c EmptyString).
  esplit. repeat red.
  intros.
  induction x; simpl in *.
  repeat (match goal with
            [ b : bool |- _ ] => destruct b; simpl in *
          end); try discriminate.
  red. intros.
  rewrite !ascii_compare_N_view in *.
  unfold ascii_compare_N in *.
  rewrite N.compare_lt_iff in *. N.order.
Defined.
  
#[global] Instance string_reftype : ReferenceType string.
Proof.
  refine {| reference_compare := string_compare |}.
  exact id. exact id.
  esplit. repeat red.
  intros.
  induction x; simpl in *. discriminate.
  destruct ascii_compare eqn:Heq. auto.
  assert (HIrr:=irreflexivity (R:=reference_order (A:=ascii))).
  specialize (HIrr a). red in HIrr. auto.
  discriminate.

  red. intros.
Admitted.


Require Import Plus.
Require Export BinPosDef.

(** String maps by translation to positive. 
  Bijection string <-> positive taken from Iris (BSD license) *)
Require Import List.
Import ListNotations.
Module StringPos.
  Definition t := string.
  Close Scope nat_scope.
  Local Open Scope list_scope.
  (** * Encoding and decoding *)
  (** In order to reuse or existing implementation of radix-2 search trees over
      positive binary naturals [positive], we define an injection [string_to_pos]
      from [string] into [positive]. *)
  Fixpoint digits_to_pos (βs : list bool) : positive :=
    match βs with
    | nil => xH
    | false :: βs => (digits_to_pos βs)~0
    | true :: βs => (digits_to_pos βs)~1
    end%positive.
  Definition ascii_to_digits (a : Ascii.ascii) : list bool :=
    match a with
    | Ascii.Ascii β1 β2 β3 β4 β5 β6 β7 β8 => [β1;β2;β3;β4;β5;β6;β7;β8]
    end.
  Local Open Scope positive_scope.
  Fixpoint Papp (p1 p2 : positive) : positive :=
    match p2 with
    | xH => p1
    | p2~0 => (Papp p1 p2)~0
    | p2~1 => (Papp p1 p2)~1
    end.
  Infix "++" := Papp : positive_scope.
  Fixpoint string_to_pos (s : string) : positive :=
    match s with
    | EmptyString => xH
    | String a s => string_to_pos s ++ digits_to_pos (ascii_to_digits a)
    end%positive.
  Fixpoint digits_of_pos (p : positive) : list bool :=
    match p with
    | xH => []
    | p~0 => false :: digits_of_pos p
    | p~1 => true :: digits_of_pos p
    end%positive.
  Fixpoint ascii_of_digits (βs : list bool) : ascii :=
    match βs with
    | [] => zero
    | β :: βs => Ascii.shift β (ascii_of_digits βs)
    end.
  Fixpoint string_of_digits (βs : list bool) : string :=
    match βs with
    | β1 :: β2 :: β3 :: β4 :: β5 :: β6 :: β7 :: β8 :: βs =>
      String (ascii_of_digits [β1;β2;β3;β4;β5;β6;β7;β8]) (string_of_digits βs)
    | _ => EmptyString
    end.
  Definition string_of_pos (p : positive) : string :=
    string_of_digits (digits_of_pos p).
  Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
  Proof.
    unfold string_of_pos.
    induction s as [|[[][][][][][][][]]]; f_equal; simpl; now try rewrite IHs.    
  Qed.

  Definition index := string_to_pos.
  
  Lemma index_inj: forall (x y: string), index x = index y -> x = y.
  Proof.
    intros.
    unfold index in *.
    apply (f_equal string_of_pos) in H.
    now rewrite !string_of_to_pos in H.
  Qed.

  Lemma eq: forall (x y: string), {x = y} + {x <> y}.
  Proof.
    apply string_dec.
  Qed.

End StringPos.

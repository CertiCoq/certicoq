(** This file gives some equational properties for manipulating matches.
 **)

Set Implicit Arguments.
Set Strict Implicit.

Lemma eq_Arr_eq
: forall T (a b : T) (pf : a = b) (F G : T -> Type) val x,
    match pf in _ = x return F x -> G x with
      | eq_refl => val
    end x =
    match pf in _ = x return G x with
      | eq_refl => val match eq_sym pf in _ = x return F x with
                         | eq_refl => x
                       end
    end.
Proof.
  destruct pf. reflexivity.
Qed.

Lemma eq_sym_eq
: forall T (a b : T) (pf : a = b) (F : T -> Type) val,
    match eq_sym pf in _ = x return F x with
      | eq_refl => val
    end =
    match pf in _ = x return F x -> F a with
      | eq_refl => fun x => x
    end val.
Proof.
  destruct pf. reflexivity.
Qed.

Lemma eq_Const_eq
: forall T (a b : T) (pf : a = b) (R : Type) val,
    match pf in _ = x return R with
      | eq_refl => val
    end = val.
Proof.
  destruct pf. reflexivity.
Qed.

Lemma eq_option_eq
: forall T (a b : T) (pf : a = b) (F : _ -> Type) val,
    match pf in _ = x return option (F x) with
      | eq_refl => val
    end = match val with
            | None => None
            | Some val => Some match pf in _ = x return F x with
                                 | eq_refl => val
                               end
          end.
Proof.
  destruct pf. destruct val; reflexivity.
Qed.
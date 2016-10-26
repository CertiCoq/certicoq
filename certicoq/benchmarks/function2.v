Require Import Recdef.
Require Import ZArith.

Definition blowup (n: Z) := Z.to_nat (2^n).

(*
Function bad (n: Z) {measure blowup n} : Z := Z0.

Time Eval cbn in bad 17.
Time Eval cbv in bad 17.

*)

(*
Lemma pow_pos:
 forall i, (0 <= i)%Z -> (0 < 2 ^ i)%Z.
Proof.
intros.
destruct i; simpl.
reflexivity.
unfold Z.pow_pos.
apply Pos.iter_invariant.
intros.
rewrite Z.mul_comm.
apply Z.mul_pos_pos; auto.
reflexivity.
reflexivity.
compute in H.
elimtype False; auto.
Qed.
*)

Lemma zero_le_Zpos_minus_1: forall i, (0 <= Z.pos i - 1)%Z.
Proof.
intros.
destruct i; intro H; inversion H.
Qed.

Lemma f_proof:    forall (p : positive),
  blowup (Z.pos p - 1) < blowup (Z.pos p).
Admitted.
(*
Proof.
intros. 
unfold blowup.
apply Z2Nat.inj_lt; try (apply Z.lt_le_incl; apply pow_pos).
apply zero_le_Zpos_minus_1.
compute; intro H; inversion H.
replace (Z.pos p) with (Z.pos p - 1 + 1)%Z at 2.
rewrite Z.pow_add_r.
rewrite <- (Z.mul_1_r (2 ^ (Z.pos p - 1))) at 1.
change (2^1)%Z with 2%Z.
apply Zmult_gt_0_lt_compat_l.
apply Z.lt_gt.
apply pow_pos.
apply zero_le_Zpos_minus_1.
reflexivity.
apply zero_le_Zpos_minus_1.
intro H; inversion H.
apply Z.sub_simpl_r.
Qed.*)

Function f (n: Z) {measure blowup n} : Z := 
  match n with Zpos _ => f(n-1) | _ => Z0 end.
Proof. intros; apply f_proof. Defined.

Time Eval lazy in f 17.
Time Eval cbv in f 17.

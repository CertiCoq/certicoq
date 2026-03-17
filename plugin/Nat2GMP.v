From MetaRocq Require Import Show.
From CertiRocq.Plugin Require Import CertiRocq.
From Corelib Require Import Nat BinNums PrimInt63 PrimString.
From Stdlib Require Import ZArith.

(* CertiRocq Register [ *)
(*   Corelib.Init.Nat.pred => "z_nat_pred" with tinfo, *)
(*   Corelib.Init.Nat.add => "z_add" with tinfo *)
(* ] Include [ ]. *)

Definition test_gmp :=
  let a := GMP.succ in
  msg_info (show (GMP.nat_case_dummy GMP.zero (fun _ => GMP.one) (fun _ => GMP.one))).

CertiRocq Eval -unsafe-erasure -time -debug test_gmp.

CertiRocq Extract Inductive To Constants [
  nat => [ [ GMP.zero GMP.succ | GMP.nat_case_dummy ] ] ].

(* Definition test_Z (x : Z) := *)
(*   if BinInt.Z.eqb x 10%Z then true else false. *)

Definition testzi :=
  let a := GMP.succ in
  let a := GMP.zero in
  let a A v x y := @GMP.nat_case_dummy A v x y in
  let g := Uint63Axioms.to_Z 10%uint63 in
  g.

CertiRocq Show IR -unsafe-erasure -debug testzi.
CertiRocq Eval -unsafe-erasure -debug testzi.

Require Import String.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Require Import Common.RandyPrelude.

Require Import Common.Common.

Definition NVar : Type := (positive * Ast.name).

Global Instance deqnname : Deq name.
Proof.
  apply @deqAsSumbool.
  intros ? ?.
  apply name_dec.
Defined.

(*
Global Instance deqnvar : Deq NVar.
Proof.
  eauto with typeclass_instances.
  apply deq_prod.
Defined.
*)

Require Import SquiggleEq.varInterface.

Global Instance varClassNVar : VarClass NVar bool :=
fun p => varClass (fst p).

Global Instance freshVarsNVar : FreshVars NVar bool:=
fun (n:nat) 
  (c : option bool) (avoid original : list NVar)
=>
  let vars := freshVars n c (map fst avoid) (map fst original) in
  map (fun p => (p, nAnon)) vars.


Lemma freshVarsPosCorrect:
forall (n : nat) (oc : option bool) (avoid original : list NVar),
let lf := freshVarsNVar n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : bool, oc = Some c -> forall v : NVar, In v lf -> varClassNVar v = c).
Proof.
Admitted.

Global Instance vartypePos : VarType NVar bool.
  apply Build_VarType.
  exact freshVarsPosCorrect.
Defined.

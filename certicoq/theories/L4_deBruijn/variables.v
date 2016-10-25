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

(* Move *)
Definition listPad {T} (def:T) (l: list T) (n: nat) : list T :=
l++(repeat def (n-length l)).

Global Instance freshVarsNVar : FreshVars NVar bool:=
fun (n:nat) 
  (c : option bool) (avoid suggested : list NVar)
=>
  let vars := freshVars n c (map fst avoid) (map fst suggested) in
  let names := listPad nAnon (map snd suggested) n in
  combine vars names.



Lemma freshVarsPosCorrect:
forall (n : nat) (oc : option bool) (avoid original : list NVar),
let lf := freshVarsNVar n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : bool, oc = Some c -> forall v : NVar, In v lf -> varClassNVar v = c).
Proof.
  simpl. intros ? ? ? ?.
Admitted.

Global Instance vartypePos : VarType NVar bool.
  apply Build_VarType.
  exact freshVarsPosCorrect.
Defined.

Require Import L4.varInterface.
Global Instance NVUpdateName : UpdateName NVar :=
  fun p => let (v,name) := p in (fst v, name).


Definition name2string (n:Ast.name): string :=
match n with
| nAnon => "_"
| nNamed s => s
end.

Require Import  ExtLib.Data.String.



Definition NVar2string (v: NVar): string :=
let name := (name2string (snd v)) in
if ((varClass v):bool)
  then name
  else (name++(nat2string10 (Pos.to_nat (fst v)))).


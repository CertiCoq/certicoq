Require Import String.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.varImplDummyPair.

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Require Import Common.RandyPrelude.

Require Import Common.Common.

Definition NVar : Set := (positive * Ast.name).

Global Instance deqnname : Deq name.
Proof.
  apply @deqAsSumbool.
  intros ? ?.
  apply name_dec.
Defined.


Require Import SquiggleEq.varInterface.

Global Instance varClassNVar : VarClass NVar bool :=
  varImplDummyPair.varClassNVar.


Global Instance freshVarsNVar : FreshVars NVar bool:=
  varImplDummyPair.freshVarsNVar nAnon.


Global Instance vartypePos : VarType NVar bool :=
  varImplDummyPair.vartypePos nAnon.

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


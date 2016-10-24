Require Import String.

Require Import Coq.Arith.Arith Coq.NArith.BinNat.

Require Import Common.RandyPrelude.

Require Import Common.Common.

(* T need NOT be isomorphic to [positive * Ast.name]. 
In particular, for efficiency,
we may provide an instance where names are discarded *)
Class MakeNamedVar (T:Type)
  := mkNVar : positive -> Ast.name -> T.

Class NVarGetId (T:Type)
  := getId :  T -> positive.

Class CertiVarType (T :Type) {mn : MakeNamedVar T}
  {mn : NVarGetId T} :=
{
  getIdCorr : forall p n, getId (mkNVar p n) = p
}.

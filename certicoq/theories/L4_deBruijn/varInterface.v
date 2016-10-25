Require Import String.

Require Import Coq.Arith.Arith Coq.NArith.BinNat.

Require Import Common.RandyPrelude.

Require Import Common.Common.

(* [mkNVar] need NOT be an injection from [positive * Ast.name] to [T]. 
In particular, for efficiency,
we may provide an instance where names are discarded *)
Class MakeNamedVar (T:Type)
  := mkNVar : positive -> Ast.name -> T.

Class NVarGetId (T:Type)
  := getId :  T -> positive.

(* We can have the following, but cannot have the property analogous 
  to getIdCorr below. Having that will force  [mkNVar] to not discard
  names.

Class NVarGetName (T:Type)
  := getName :  T -> Ast.name.
*)

Class CertiVarType (T :Type) {mn : MakeNamedVar T}
  {mn : NVarGetId T} :=
{
  getIdCorr : forall p n, getId (mkNVar p n) = p
}.

Class UpdateName (T:Type)
  := updateName : T * Ast.name -> T.

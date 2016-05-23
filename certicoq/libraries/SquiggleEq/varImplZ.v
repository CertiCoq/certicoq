Require Import export.
Require Import UsefulTypes.

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Global Instance deqpos : Deq positive.
Proof.
  apply @deqAsSumbool.
  intros ? ?. unfold DecidableSumbool.
  decide equality.
Qed.

Definition varClassP (p:positive) : bool :=
match p with
| xO _ => true (* p is even *)
| _  => false
end.

Fixpoint maxl (d: positive) (p: list positive) : positive :=
match p with
| [] => d
| h::tl  => maxl (Pos.max h d) tl
end.

Fixpoint seq (start : positive) (len : nat) {struct len} : list positive :=
match len with
| 0 => []
| S len0 => start :: seq (Pos.succ start) len0
end.


Definition freshVarsPosAux (n:nat) 
  (c : bool) (avoid original : list positive) : list positive :=
let maxn := maxl xH avoid in
let f := (if c then xO else xI) in
List.map f (seq (Pos.succ maxn) n).

Definition freshVarsPos (n:nat) 
  (c : option bool) (avoid original : list positive) : list positive :=
let c : bool :=
  match c with
  |Some c => c
  |None => true
  end in
  freshVarsPosAux n c avoid original.

Lemma freshVarsPosCorrect:
forall (n : nat) (oc : option bool) (avoid original : list positive),
let lf := freshVarsPos n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : bool, oc = Some c -> forall v : positive, In v lf -> varClassP v = c).
Proof.
Admitted.

Global Instance vartypePos : @VarType positive bool deqpos.
  apply Build_VarType with (varClass:=varClassP) (freshVars := freshVarsPos).
  exact freshVarsPosCorrect.
Defined.

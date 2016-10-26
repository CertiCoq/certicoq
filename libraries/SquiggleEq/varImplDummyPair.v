Require Import SquiggleEq.varInterface.
Require Import SquiggleEq.UsefulTypes.

Section VarPair.

Context {Var T2 vc} {deqnvar : Deq Var} {varcl freshv} 
{varclass: @VarType Var vc deqnvar varcl freshv} {deqt2 : Deq T2} (def: T2).


Definition NVar : Type := (Var * T2).



Instance varClassNVar : VarClass NVar vc :=
fun p => varClass (fst p).


Require  Import SquiggleEq.list.
Require  Import Coq.Lists.List.

Instance freshVarsNVar : FreshVars NVar vc:=
fun (n:nat) 
  (c : option vc) (avoid suggested : list NVar)
=>
  let vars := freshVars n c (map fst avoid) (map fst suggested) in
  let names := listPad def (map snd suggested) n in
  combine vars names.

Require Import SquiggleEq.tactics.


Lemma freshVarsPosCorrect:
forall (n : nat) (oc : option vc) (avoid original : list NVar),
let lf := freshVarsNVar n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : vc, oc = Some c -> forall v : NVar, In v lf -> varClassNVar v = c).
Proof.
  simpl. intros ? ? ? ?. unfold freshVarsNVar.
  addFreshVarsSpec. repnd.
  dands.
- apply (nodup_map fst).
  rewrite <- combine_map_fst2; auto.
  rewrite HfreshVars0. apply listPad_length.
- intros Hl. apply (disjoint_map fst).
  rewrite <- combine_map_fst2; auto.
  rewrite HfreshVars0. apply listPad_length.
- unfold  freshVarsNVar. setoid_rewrite combine_length.
  rewrite HfreshVars0.
  apply Min.min_l. apply listPad_length.
- intros ? ? ? Hin. destruct v.
  apply in_combine in Hin. apply proj1 in Hin.
  eapply HfreshVars in Hin; eauto.
Qed.

Instance vartypePos : VarType NVar vc.
  apply Build_VarType.
  exact freshVarsPosCorrect.
Defined.

End VarPair.

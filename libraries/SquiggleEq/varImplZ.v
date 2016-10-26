Require Import UsefulTypes.

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Global Instance deqpos : Deq positive.
Proof.
  unfold Deq.
  intros ? ?.
  exists (Pos.eqb a b).
  split.
  - intros. apply Peqb_true_eq. assumption.
  - intros. subst. apply Pos.eqb_refl.
Defined.

Require Import varInterface.

Global Instance varClassP : VarClass positive bool :=
fun p =>
match p with
| xO _ => true (* p is even *)
| _  => false
end.


Require Import list.
Section Temp.
Local Notation seq := (seq Pos.succ).


  Lemma in_seq len start n :
    In n (seq start len) <-> ((Pos.to_nat start) <= Pos.to_nat  n < (Pos.to_nat start) +len).
  Proof.
   revert start. induction len; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst. intuition auto with arith.
      rewrite Pos2Nat.inj_succ in H.
      omega.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H);
       rewrite Pos2Nat.inj_succ in *; intuition.
       apply Pos2Nat.inj_iff in H0. auto.
  Qed.

  Lemma in_seql len start n :
    In n (seq start len) -> (start <= n)%positive.
  Proof using.
    intros Hin.
    apply in_seq in Hin. apply proj1 in Hin.
    lia.
  Qed.

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_).
  rewrite Pos2Nat.inj_succ in *.
   apply (Lt.lt_irrefl _ H).
  Qed.
Lemma seq_maxlp : forall a v avoid n,
 LIn a (seq (maxlp avoid 1) n)
 -> LIn v avoid
 -> (v <= a)%positive.
Proof using.
  intros ? ? ? ? Hin1 Hina.
  apply in_seql in Hin1. subst.
  pose proof (maxlp_le v avoid xH (or_intror Hina)).
  lia.
Qed.


(*
  Lemma in_seqN len start n :
    In n (seq start len) <-> (N.pos start <=  N.pos n < N.pos start + N.of_nat len)%N.
  Proof.
   revert start. induction len; simpl; intros.
   -  split;[easy|].
     intros (H,H'). omega. apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst. intuition auto with arith.
      rewrite Pos2Nat.inj_succ in H.
      omega.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H);
       rewrite Pos2Nat.inj_succ in *; intuition.
       apply Pos2Nat.inj_iff in H0. auto.
  Qed.
*)



Definition freshVarsPosAux (n:nat) 
  (c : bool) (avoid original : list positive) : list positive :=
let maxn := maxlp avoid  xH in
let f := (if c then xO else xI) in
List.map f (seq (maxn) n).

End Temp.


Global Instance freshVarsPos : FreshVars positive bool:=
fun (n:nat) 
  (c : option bool) (avoid original : list positive)
=>
let c : bool :=
  match c with
  |Some c => c
  |None => true
  end in
  freshVarsPosAux n c avoid original.

Require Import tactics.


Lemma freshVarsPosCorrect:
forall (n : nat) (oc : option bool) (avoid original : list positive),
let lf := freshVarsPos n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : bool, oc = Some c -> forall v : positive, In v lf -> varClassP v = c).
Proof.
  intros.
  split;[split;[|split]|]; subst lf; simpl; unfold freshVarsPos,freshVarsPosAux.
- apply NoDupInjectiveMap;[|apply seq_NoDup].
  destruct oc; [destruct b|]; unfold injective_fun; intros;
  cpx; inversion H; auto.
- intros ? Hin Hinc.
  apply in_map_iff in Hin. exrepnd.
  pose proof (seq_maxlp _ t avoid _ Hin1 Hinc) as Hin.
  subst. destruct oc as [c | ]; try lia.
  destruct c; lia.
- rewrite map_length. rewrite seq_length. refl. 
- intros ? ?. subst. intros ? Hin. simpl.
  apply in_map_iff in Hin.
  exrepnd.
  subst.
  unfold varClassP.
  destruct c; refl.
Qed.

Global Instance vartypePos : VarType positive bool.
  apply Build_VarType.
  exact freshVarsPosCorrect.
Defined.

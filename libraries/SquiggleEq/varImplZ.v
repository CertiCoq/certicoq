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

(* Copied from https://github.com/coq/coq/blob/7ee82cd2dfd8cb226c35c3094423e56c75010377/theories/Lists/List.v *)
 Lemma seq_length : forall len start, length (seq start len) = len.
  Proof.
    induction len; simpl; auto.
  Qed.



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

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_).
  rewrite Pos2Nat.inj_succ in *.
   apply (Lt.lt_irrefl _ H).
  Qed.

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

Require Import tactics.

(* Move *)
Lemma NoDupInjectiveMap {A B : Type} (f:A->B) :
injective_fun f
-> forall l, NoDup l -> NoDup (map f l).
Proof.
  intros Hin. induction l; [simpl; cpx |].
  intros Hnd. inversion Hnd.
  simpl. constructor; cpx.
  intros Hl.
  apply in_map_iff in Hl. subst.
  exrepnd.
  apply Hin in Hl1.
  subst. contradiction.
Qed.
  
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
- admit.
- rewrite map_length. rewrite seq_length. refl. 
- intros ? ?. subst. intros ? Hin. simpl.
  apply in_map_iff in Hin.
  exrepnd.
  subst.
  unfold varClassP.
  destruct c; refl.
Admitted.

Global Instance vartypePos : @VarType positive bool deqpos.
  apply Build_VarType with (varClass:=varClassP) (freshVars := freshVarsPos).
  exact freshVarsPosCorrect.
Defined.

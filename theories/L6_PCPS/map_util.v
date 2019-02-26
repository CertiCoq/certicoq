From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
Require Import L6.Ensembles_util L6.set_util L6.functions
        compcert.lib.Maps.

Module M := Maps.PTree. 

Open Scope Ensembles_scope.

Definition key_set {A : Type} (map : M.t A) :=
  [ set x : positive | match M.get x map with
                           | Some x => True
                           | None => False
                         end ]. 
  
Definition sub_map {A : Type} (map1 map2 : M.t A) :=
  forall x v, M.get x map1 = Some v ->
         M.get x map2 = Some v.

Fixpoint xfilter {A : Type} (pred : positive -> A -> bool) (m : M.t A) 
         (i : positive) {struct m} : M.t A :=
  match m with
  | M.Leaf => M.Leaf
  | M.Node l o r =>
    let o' :=
        match o with
        | Some x => if pred (M.prev i) x then o else None
        | None => None
        end
    in
    M.Node' (xfilter pred l (i~0)%positive) o' (xfilter pred r (i~1)%positive)
  end.

Lemma xgfilter (A: Type) (pred : positive -> A -> bool) (m : M.t A) 
      (i j : positive) : 
  M.get i (xfilter pred m j) =
  match M.get i m with
  | Some x => if pred (M.prev (M.prev_append i j)) x then Some x else None
  | None => None
  end.
Proof.
  revert i j. induction m; intros i j; simpl.
  - rewrite !M.gleaf. reflexivity.
  - rewrite M.gnode'.
    destruct i; simpl.
    + rewrite IHm2. reflexivity.
    + rewrite IHm1. reflexivity.
    + destruct o; reflexivity.
Qed.

Definition filter  {A : Type} (pred : positive -> A -> bool) (m : M.t A) : M.t A :=
  xfilter pred m 1.

Lemma gfilter (A: Type) (pred : positive -> A -> bool) (m : M.t A) 
      (i : positive) : 
  M.get i (filter pred m) =
  match M.get i m with
  | Some x => if pred i x then Some x else None
  | None => None
  end.
Proof.
  unfold filter. rewrite xgfilter. simpl. 
  rewrite <- M.prev_append_prev. simpl. 
  rewrite Maps.PTree.prev_involutive. reflexivity. 
Qed.


Instance ToMSet_key_set {A} (rho : M.t A) : ToMSet (key_set rho).
Proof. 
  eexists (@mset (FromList (map fst (M.elements rho))) _).
  rewrite <- mset_eq, FromList_map_image_FromList.
  split; intros x Hin.
  - unfold In, key_set in *.
    destruct (M.get x rho) eqn:Hget. 
    eexists (x, a). split; eauto.
    eapply M.elements_correct. eassumption. 

    exfalso; eauto.
  - destruct Hin as [[z a] [Hin Hget]]; subst.
    unfold In, FromList in Hin. eapply M.elements_complete in Hin.
    simpl. unfold key_set, In. now rewrite Hin.
Qed. 



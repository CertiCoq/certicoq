Require Import Arith BinNat String List Omega Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Export cpstrans.

(*** deBruijn operations for Var: shifting and substitution ***)

(* optimised shift *)
Fixpoint ushift_cps (n:N) (k:N) (e:cps): cps :=
  match e with
    | Halt_c v => Halt_c (ushift_val n k v)
    | Ret_c v1 v2 => Ret_c (ushift_val n k v1) (ushift_val n k v2)
    | Call_c v1 v2 v3 =>
        Call_c (ushift_val n k v1) (ushift_val n k v2) (ushift_val n k v3)
    | Match_c v bs =>
        Match_c (ushift_val n k v) (ushift_branches n k bs)
  end
with ushift_val (n:N) (k:N) (v:val_c): val_c :=
  match v with
    | Var_c i => Var_c (if lt_dec i k then i else i+n)
    | KVar_c i => KVar_c i
    | Lam_c e' => Lam_c (ushift_cps n (1 + k) e')
    | Cont_c e' => Cont_c (ushift_cps n k e')
    | Con_c d vs => Con_c d (ushift_vals n k vs)
    | Fix_c cs i => Fix_c (ushift_fnlst n (fnlst_length cs + k) cs) i
  end
with ushift_vals n k (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (ushift_val n k v) (ushift_vals n k vs)
       end
with ushift_fnlst n k (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (ushift_cps n (1+k) f) (ushift_fnlst n k fs)
       end
with ushift_branches n k (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (ushift_cps n (j+k) c) (ushift_branches n k bs)
       end.

Lemma ushift_zero :
  (forall e d, ushift_cps 0 d e = e) /\ 
  (forall v d, ushift_val 0 d v = v) /\
  (forall vs d, ushift_vals 0 d vs = vs) /\
  (forall bs d, ushift_branches 0 d bs = bs) /\
  (forall cs d, ushift_fnlst 0 d cs = cs).
Proof.
  apply my_cps_ind; simpl; intros; fold ushift_vals; fold ushift_branches; 
  fold ushift_fnlst; try congruence.
  - if_split. rewrite N.add_0_r; auto.
Qed.
Definition cps_ushift_0 := proj1 ushift_zero.
Definition val_ushift_0 := proj1 (proj2 ushift_zero).
Definition vals_ushift_0 := proj1 (proj2 (proj2 ushift_zero)).
Definition branches_ushift_0 := proj1 (proj2 (proj2 (proj2 ushift_zero))).
Definition fnlst_ushift_0 := proj2 (proj2 (proj2 (proj2 ushift_zero))).

Lemma ushift_fnlst_length n k l :
  fnlst_length (ushift_fnlst n k l) = fnlst_length l.
Proof.
  induction l as [ |a l IHl]; simpl; rewrite ?IHl; auto.
Qed.

Lemma ushift_twice :
  (forall c i j m n, i <= j -> j <= i + m ->
     ushift_cps n j (ushift_cps m i c) = ushift_cps (m+n) i c) /\
  (forall v i j m n, i <= j -> j <= i + m ->
     ushift_val n j (ushift_val m i v) = ushift_val (m+n) i v) /\
  (forall vs i j m n, i <= j -> j <= i + m ->
     ushift_vals n j (ushift_vals m i vs) = ushift_vals (m+n) i vs) /\
  (forall bs i j m n, i <= j -> j <= i + m ->
     ushift_branches n j (ushift_branches m i bs) =
     ushift_branches (m+n) i bs) /\
  (forall fs i j m n, i <= j -> j <= i + m ->
     ushift_fnlst n j (ushift_fnlst m i fs) = ushift_fnlst (m+n) i fs).
Proof.
  Opaque N.add.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto; fail).
  - repeat if_split; auto.
    replace (n + (m + n0)) with (n + m + n0); try lia; auto.
  - rewrite H; try lia. reflexivity.
  - rewrite ushift_fnlst_length, H; try lia. reflexivity.
  - rewrite H, H0; try lia. reflexivity. 
  - rewrite H, H0; try lia. reflexivity.
Qed.
Definition cps_ushift_twice := proj1 ushift_twice.
Definition val_ushift_twice := proj1 (proj2 ushift_twice).
Definition vals_ushift_twice := proj1 (proj2 (proj2 ushift_twice)).
Definition cpsbranches_ushift_twice :=
  proj1 (proj2 (proj2 (proj2 ushift_twice))).
Definition fnlst_ushift_twice := proj2 (proj2 (proj2 (proj2 ushift_twice))).


(* unoptimised shift *)
Fixpoint ushft_cps (k:N) (e:cps): cps :=
  match e with
    | Halt_c v => Halt_c (ushft_val k v)
    | Ret_c v1 v2 => Ret_c (ushft_val k v1) (ushft_val k v2)
    | Call_c v1 v2 v3 =>
        Call_c (ushft_val k v1) (ushft_val k v2) (ushft_val k v3)
    | Match_c v bs =>
        Match_c (ushft_val k v) (ushft_branches k bs)
  end
with ushft_val (k:N) (v:val_c): val_c :=
  match v with
    | Var_c i => Var_c (if lt_dec i k then i else i+1)
    | KVar_c i => KVar_c i
    | Lam_c e' => Lam_c (ushft_cps (1 + k) e')
    | Cont_c e' => Cont_c (ushft_cps k e')
    | Con_c d vs => Con_c d (ushft_vals k vs)
    | Fix_c cs i => Fix_c (ushft_fnlst (fnlst_length cs + k) cs) i
  end
with ushft_vals k (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (ushft_val k v) (ushft_vals k vs)
       end
with ushft_fnlst k (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs => flcons (ushft_cps (1+k) f) (ushft_fnlst k fs)
       end
with ushft_branches k (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (ushft_cps (j+k) c) (ushft_branches k bs)
       end.

(** u-shifting is a no-op for u-closed cps **)
Lemma ushft_uwf_noop:
  (forall (e:cps) n, cps_uwf n e -> forall k, n < k ->
                    ushft_cps k e = e) /\
  (forall (v:val_c) n, val_uwf n v -> forall k, n < k ->
                      ushft_val k v = v) /\
  (forall (v:vals_c) n, vals_uwf n v -> forall k, n < k ->
                       ushft_vals k v = v) /\
  (forall (v:branches_c) n, cpsbranches_uwf n v -> forall k, n < k ->
                        ushft_branches k v = v) /\
  (forall (v:fnlst) n, fnlst_uwf n v -> forall k, n < k ->
                        ushft_fnlst k v = v).
Proof.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (solve [inversion H0; subst; erewrite H; eauto]);
  try (solve [inversion H1; subst; erewrite H, H0; eauto]).
  - inversion H2; subst; erewrite H, H0, H1; eauto.
  - if_split. inversion H; subst. lia.
  - erewrite H. reflexivity. inversion H0. subst. eassumption. lia.
  - erewrite H; try eassumption; try reflexivity.
    + inversion H0; subst. apply H4.
    + lia.
  - erewrite H, H0; try eassumption; try reflexivity.
    + inversion H1. subst. eassumption.
    + inversion H1. subst. eassumption.
    + lia.
  - erewrite H, H0; try eassumption; try reflexivity.
    + inversion H1. subst. eassumption.
    + inversion H1. subst. eassumption.
    + lia.
Qed.


(** for u-closed cps, ushft and ushift are the same **)
Lemma uwf_ushft_ushift' :
  (forall m e, cps_uwf m e ->
    forall k n, m <= k -> ushift_cps n k e = ushft_cps k e) /\
  (forall m v, val_uwf m v -> 
    forall k n, m <= k -> ushift_val n k v = ushft_val k v) /\
  (forall m vs, vals_uwf m vs ->
    forall k n, m <= k ->  ushift_vals n k vs = ushft_vals k vs) /\ 
  (forall m bs, cpsbranches_uwf m bs -> 
    forall k n, m <= k -> ushift_branches n k bs =
                           ushft_branches k bs) /\
  (forall m cs, fnlst_uwf m cs ->
    forall k n, m <= k -> ushift_fnlst n k cs = ushft_fnlst k cs).
Proof.
  apply my_uwf_ind; simpl; intros; try reflexivity;
  try (rewrite H, ?H0, ?H1; try lia; reflexivity).
  - if_split.
Qed.
Definition uwf_cps_ushift_ushft := proj1 uwf_ushft_ushift'.
Definition uwf_val_ushift_ushft := proj1 (proj2 uwf_ushft_ushift').
Definition uwf_vals_ushift_ushft := proj1 (proj2 (proj2 uwf_ushft_ushift')).
Definition uwf_cpsbranches_ushift_ushft :=
  proj1 (proj2 (proj2 (proj2 uwf_ushft_ushift'))).
Definition uwf_fnlst_ushift_ushft :=
  proj2 (proj2 (proj2 (proj2 uwf_ushft_ushift'))).

Lemma ucl_cps_ushift_ushft:
  forall e, cps_uwf 0 e -> forall n k, ushift_cps n k e = ushft_cps k e.
Proof.
  intros. erewrite uwf_cps_ushift_ushft. reflexivity. eassumption. lia.
Qed.

Lemma cps_ushift_ushft':
  (forall c n k, ushift_cps (1 + n) k c = ushft_cps k (ushift_cps n k c)) /\
  (forall v n k, ushift_val (1 + n) k v = ushft_val k (ushift_val n k v)) /\
  (forall vs n k,
     ushift_vals (1 + n) k vs = ushft_vals k (ushift_vals n k vs)) /\ 
  (forall bs n k, ushift_branches (1 + n) k bs = 
                  ushft_branches k (ushift_branches n k bs)) /\
  (forall cs n k, ushift_fnlst (1 + n) k cs =
                  ushft_fnlst k (ushift_fnlst n k cs)).
Proof.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (solve [rewrite H, ?H0, ?H1; reflexivity]).
  - repeat if_split. replace (n + (1 + n0)) with (n + n0 + 1); try lia.
    reflexivity.
  - now rewrite ushift_fnlst_length, H.
Qed.
Definition cps_ushift_ushft := proj1 cps_ushift_ushft'.
Definition val_ushift_ushft := proj1 (proj2 cps_ushift_ushft').
Definition vals_ushift_ushft := proj1 (proj2 (proj2 cps_ushift_ushft')).
Definition cpsbranches_ushift_ushft :=
  proj1 (proj2 (proj2 (proj2 cps_ushift_ushft'))).
Definition fnlst_ushift_ushft :=
  proj2 (proj2 (proj2 (proj2 cps_ushift_ushft'))).


(** Substitution of a value for a user-level variable.  Notice this has
    has no effect on [KVar_c] and that the index does not change going
    under a [Cont_c]. *)
(* optimised substitution for user vars *)
Fixpoint usubst_cps (v:val_c) (k:N) (e:cps): cps :=
  match e with
    | Halt_c v' => Halt_c (usubst_val v k v')
    | Ret_c v1 v2 => Ret_c (usubst_val v k v1) (usubst_val v k v2)
    | Call_c v1 v2 v3 =>
      Call_c (usubst_val v k v1) (usubst_val v k v2) (usubst_val v k v3)
    | Match_c v' bs =>
      Match_c (usubst_val v k v') (usubst_branches v k bs)
  end
with usubst_val (v:val_c) (k:N) (v':val_c): val_c :=
  match v' with
    | Var_c i => if lt_dec i k then Var_c i
                 else if eq_dec i k then ushift_val k 0 v
                      else Var_c (i - 1)
    | KVar_c i => KVar_c i
    | Lam_c e => Lam_c (usubst_cps v (1 + k) e)
    | Cont_c e => Cont_c (usubst_cps v k e)
    | Con_c d vs => Con_c d (usubst_vals v k vs)
    | Fix_c cs i => Fix_c (usubst_fnlst v (fnlst_length cs + k) cs) i
  end
with usubst_vals (u:val_c) (k:N) (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (usubst_val u k v) (usubst_vals u k vs)
       end
with usubst_fnlst (v:val_c) (k:N) (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (usubst_cps v (1+k) f) (usubst_fnlst v k fs)
       end
with usubst_branches (v:val_c) (k:N) (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (usubst_cps v (j+k) c) (usubst_branches v k bs)
       end.


(* unoptimised substitution for user vars *)
Fixpoint usbst_cps (v:val_c) (k:N) (e:cps): cps :=
  match e with
    | Halt_c v' => Halt_c (usbst_val v k v')
    | Ret_c v1 v2 => Ret_c (usbst_val v k v1) (usbst_val v k v2)
    | Call_c v1 v2 v3 =>
      Call_c (usbst_val v k v1) (usbst_val v k v2) (usbst_val v k v3)
    | Match_c v' bs =>
      Match_c (usbst_val v k v') (usbst_branches v k bs)
  end
with usbst_val (v:val_c) (k:N) (v':val_c): val_c :=
  match v' with
    | Var_c i => if lt_dec i k then Var_c i
                 else if eq_dec i k then v
                      else Var_c (i - 1)
    | KVar_c i => KVar_c i
    | Lam_c e =>    (* JGM: should this be ushft of v? *)
      Lam_c (usbst_cps (ushft_val 0 v) (1 + k) e)
    | Cont_c e => Cont_c (usbst_cps v k e) 
    | Con_c d vs => Con_c d (usbst_vals v k vs)
    | Fix_c cs i => Fix_c (usbst_fnlst v (fnlst_length cs + k) cs) i
  end
with usbst_vals (u:val_c) (k:N) (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (usbst_val u k v) (usbst_vals u k vs)
       end
with usbst_fnlst (v:val_c) (k:N) (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (usbst_cps v (1+k) f) (usbst_fnlst v k fs)
       end
with usbst_branches (v:val_c) (k:N) (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (usbst_cps (ushft_val 0 v) (j+k) c)
                    (usbst_branches (ushft_val 0 v) k bs)
       end.

(** Re-use the notation for user var substitution. *)
Class Substitute (v:Type) (t:Type) := { substitute: v -> N -> t -> t }.
Notation "M { j := N }" := (substitute N j M)
                      (at level 10, right associativity).
Instance UCPSSubstitute: Substitute val_c cps := { substitute := usubst_cps }.
Instance UValSubstitute: Substitute val_c val_c :=
  { substitute := usubst_val }.
Instance UValsSubstitute: Substitute val_c vals_c :=
  { substitute := usubst_vals }.
Instance UBranchSubstitute: Substitute val_c branches_c :=
  {substitute := usubst_branches}.
Instance UFNListSubstitute: Substitute val_c fnlst :=
  {substitute := usubst_fnlst}.

Class USbstitute (v:Type) (t:Type) := { usbstitute: v -> N -> t -> t }.
Notation "M { j ::= N }" :=
  (usbstitute N j M) (at level 10, right associativity).
Instance UCPSSbstitute: USbstitute val_c cps :=
  { usbstitute := usbst_cps }.
Instance UValSbstitute: USbstitute val_c val_c :=
  { usbstitute := usbst_val }.
Instance UValsSbstitute: USbstitute val_c vals_c :=
  { usbstitute := usbst_vals }.
Instance UBranchesSbstitute: USbstitute val_c branches_c :=
  {usbstitute := usbst_branches}.
Instance UFNListSbstitute: USbstitute val_c fnlst :=
  {usbstitute := usbst_fnlst}.


Function usubst_list (c:cps) (vs:vals_c): cps :=
  match vs with
    | vcnil => c
    | vccons v vs => usubst_list (c{0:=v}) vs
  end.
Function usbst_list (c:cps) (vs:vals_c): cps :=
  match vs with
    | vcnil => c
    | vccons v vs => usbst_list (c{0::=v}) vs
  end.


(** lemmas about unoptimised substitution **)

Lemma usbst_eq: forall u k, (Var_c k){k ::= u} = u.
Proof. 
  intros. simpl. repeat if_split. 
Qed.
Hint Rewrite usbst_eq.


Lemma usbst_gt: forall u i k, i < k -> (Var_c k){i ::= u} = Var_c (k - 1).
Proof.
  intros; simpl. repeat if_split.
Qed.


Lemma usbst_lt: forall u i k, k < i -> (Var_c k){i ::= u} = Var_c k.
Proof.
  intros; simpl. if_split. 
Qed.


Require Import Arith BinNat String List Omega Coq.Program.Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Export CPS.cpstrans.

(*** deBruijn operations for KVar: shifting and substitution ***)

(** unoptimised shift of KVar: leaves Var unchanged **)
Fixpoint kshft_cps (k:N) (e:cps): cps :=
  match e with
    | Halt_c v => Halt_c (kshft_val k v)
    | Ret_c v1 v2 => Ret_c (kshft_val k v1) (kshft_val k v2)
    | Call_c v1 v2 v3 =>
        Call_c (kshft_val k v1) (kshft_val k v2) (kshft_val k v3)
    | Match_c v bs =>
        Match_c (kshft_val k v) (kshft_branches k bs)
  end
with kshft_val (k:N) (v:val_c): val_c :=
  match v with
    | KVar_c i => KVar_c (if lt_dec i k then i else i+1)
    | Var_c i => Var_c i
    | Lam_c e' => Lam_c (kshft_cps (1 + k) e')
    | Cont_c e' => Cont_c (kshft_cps (1 + k) e')
    | Con_c d vs => Con_c d (kshft_vals k vs)
    | Fix_c cs i => Fix_c (kshft_fnlst k cs) i
  end
with kshft_vals k (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (kshft_val k v) (kshft_vals k vs)
       end
with kshft_fnlst k (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs => flcons (kshft_cps (1 + k) f) (kshft_fnlst k fs)
       end
with kshft_branches k (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (kshft_cps k c) (kshft_branches k bs)
       end.

(** k-shfting is a no-op for k-closed cps **)
Lemma kshft_kwf_noop':
  (forall (e:cps) n, cps_kwf n e -> forall k, n < k ->
                    kshft_cps k e = e) /\
  (forall (v:val_c) n, val_kwf n v -> forall k, n < k ->
                      kshft_val k v = v) /\
  (forall (v:vals_c) n, vals_kwf n v -> forall k, n < k ->
                       kshft_vals k v = v) /\
  (forall (v:branches_c) n, cpsbranches_kwf n v -> forall k, n < k ->
                        kshft_branches k v = v) /\
  (forall (v:fnlst) n, fnlst_kwf n v -> forall k, n < k ->
                        kshft_fnlst k v = v).
Proof.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (solve [inversion H0; subst; erewrite H; eauto]);
  try (solve [inversion H1; subst; erewrite H, H0; eauto]).
  - inversion H2; subst; erewrite H, H0, H1; eauto.
  - if_split. inversion H; subst. lia.
  - erewrite H. reflexivity. inversion H0. subst. eassumption. lia.
  - erewrite H. reflexivity. inversion H0. subst. eassumption. lia.
  - erewrite H, H0; try eassumption; try reflexivity.
    + inversion H1. subst. eassumption.
    + inversion H1. subst. eassumption.
    + lia.
Qed.
Definition cps_kshft_kwf_noop := proj1 kshft_kwf_noop'.

Lemma kshft_kshft:
  (forall (c:cps) i k, i < k+1 ->
     kshft_cps (k+1) (kshft_cps i c) = kshft_cps i (kshft_cps k c)) /\
  (forall (v:val_c) i k, i < k+1 ->
     kshft_val (k+1) (kshft_val i v) = kshft_val i (kshft_val k v)) /\
  (forall (vs:vals_c) i k, i < k+1 ->
     kshft_vals (k+1) (kshft_vals i vs) = kshft_vals i (kshft_vals k vs)) /\
  (forall (bs:branches_c) i k, i < k+1 ->
     kshft_branches (k+1) (kshft_branches i bs) =
          kshft_branches i (kshft_branches k bs)) /\ 
  (forall (cs:fnlst) i k,  i < k+1 ->
     kshft_fnlst (k+1) (kshft_fnlst i cs) =
          kshft_fnlst i (kshft_fnlst k cs)).
Proof.
  apply my_cps_ind; intros; try reflexivity;
  try (solve [simpl; rewrite H; try reflexivity; try lia]);
  try (solve [simpl; rewrite H, H0; try reflexivity; try lia]);
  try (solve [simpl; rewrite H, H0, H1; try reflexivity; try lia]).
  - simpl. repeat if_split.
  - simpl. replace (1 + (k + 1)) with (k+1+1); try lia. 
    rewrite H; try lia. replace (k + 1) with (1 + k); try lia.
    reflexivity.
  - simpl. rewrite Nplus_assoc. rewrite H; try lia. reflexivity.
  - simpl. rewrite Nplus_assoc. rewrite H, H0; try lia. reflexivity.
Qed.
Definition cps_kshft_kshft := proj1 kshft_kshft.
Definition val_kshft_kshft := proj1 (proj2 kshft_kshft).
Definition vals_kshft_kshft := proj1 (proj2 (proj2 kshft_kshft)).
Definition cpsbranches_kshft_kshft :=
  proj1 (proj2 (proj2 (proj2 kshft_kshft))).
Definition fnlst_kshft_kshft := proj2 (proj2 (proj2 (proj2 kshft_kshft))).


(*** optimised shift of KVar: leaves Var unchanged ***)
Fixpoint kshift_cps (n:N) (k:N) (e:cps): cps :=
  match e with
    | Halt_c v => Halt_c (kshift_val n k v)
    | Ret_c v1 v2 => Ret_c (kshift_val n k v1) (kshift_val n k v2)
    | Call_c v1 v2 v3 =>
        Call_c (kshift_val n k v1) (kshift_val n k v2) (kshift_val n k v3)
    | Match_c v bs =>
        Match_c (kshift_val n k v) (kshift_branches n k bs)
  end
with kshift_val (n:N) (k:N) (v:val_c): val_c :=
  match v with
    | KVar_c i => KVar_c (if lt_dec i k then i else i+n)
    | Var_c i => Var_c i
    | Lam_c e' => Lam_c (kshift_cps n (1 + k) e')
    | Cont_c e' => Cont_c (kshift_cps n (1 + k) e')
    | Con_c d vs => Con_c d (kshift_vals n k vs)
    | Fix_c cs i => Fix_c (kshift_fnlst n k cs) i
  end
with kshift_vals n k (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (kshift_val n k v) (kshift_vals n k vs)
       end
with kshift_fnlst n k (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (kshift_cps n (1+k) f) (kshift_fnlst n k fs)
       end
with kshift_branches n k (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (kshift_cps n k c) (kshift_branches n k bs)
       end.

Lemma kshift_zero :
  (forall e d, kshift_cps 0 d e = e) /\ 
  (forall v d, kshift_val 0 d v = v) /\
  (forall vs d, kshift_vals 0 d vs = vs) /\
  (forall bs d, kshift_branches 0 d bs = bs) /\
  (forall cs d, kshift_fnlst 0 d cs = cs).
Proof.
  apply my_cps_ind; simpl; intros; fold kshift_vals; fold kshift_branches; 
  fold kshift_fnlst; try congruence.
  - if_split. rewrite N.add_0_r; auto.
Qed.
Definition cps_kshift_0 := proj1 kshift_zero.
Definition val_kshift_0 := proj1 (proj2 kshift_zero).
Definition vals_kshift_0 := proj1 (proj2 (proj2 kshift_zero)).
Definition branches_kshift_0 := proj1 (proj2 (proj2 (proj2 kshift_zero))).
Definition fnlst_kshift_0 := proj2 (proj2 (proj2 (proj2 kshift_zero))).

Lemma kshift_twice :
  (forall c i j m n, i <= j -> j <= i + m ->
     kshift_cps n j (kshift_cps m i c) = kshift_cps (m+n) i c) /\
  (forall v i j m n, i <= j -> j <= i + m ->
     kshift_val n j (kshift_val m i v) = kshift_val (m+n) i v) /\
  (forall vs i j m n, i <= j -> j <= i + m ->
     kshift_vals n j (kshift_vals m i vs) = kshift_vals (m+n) i vs) /\
  (forall bs i j m n, i <= j -> j <= i + m ->
     kshift_branches n j (kshift_branches m i bs) =
     kshift_branches (m+n) i bs) /\
  (forall fs i j m n, i <= j -> j <= i + m ->
     kshift_fnlst n j (kshift_fnlst m i fs) = kshift_fnlst (m+n) i fs).
Proof.
  Opaque N.add.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto; fail).
  - repeat if_split; auto.
    replace (n + (m + n0)) with (n + m + n0); try lia; auto.
  - rewrite H; try lia. reflexivity.
  - rewrite H; try lia. reflexivity. 
  - rewrite H, H0; try lia. reflexivity. 
Qed.
Definition cps_kshift_twice := proj1 kshift_twice.
Definition val_kshift_twice := proj1 (proj2 kshift_twice).
Definition vals_kshift_twice := proj1 (proj2 (proj2 kshift_twice)).
Definition cpsbranches_kshift_twice :=
  proj1 (proj2 (proj2 (proj2 kshift_twice))).
Definition fnlst_kshift_twice := proj2 (proj2 (proj2 (proj2 kshift_twice))).

(** for k-closed cps, kshft and kshift are the same **)
Lemma kwf_kshft_kshift' :
  (forall m e, cps_kwf m e ->
    forall k n, m <= k -> kshift_cps n k e = kshft_cps k e) /\
  (forall m v, val_kwf m v -> 
    forall k n, m <= k -> kshift_val n k v = kshft_val k v) /\
  (forall m vs, vals_kwf m vs ->
    forall k n, m <= k ->  kshift_vals n k vs = kshft_vals k vs) /\ 
  (forall m bs, cpsbranches_kwf m bs -> 
    forall k n, m <= k -> kshift_branches n k bs =
                           kshft_branches k bs) /\
  (forall m cs, fnlst_kwf m cs ->
    forall k n, m <= k -> kshift_fnlst n k cs = kshft_fnlst k cs).
Proof.
  apply my_kwf_ind; simpl; intros; try reflexivity;
  try (rewrite H; try lia; reflexivity);
  try (rewrite H, H0; try lia; reflexivity);
  try (rewrite H, H0, H1; try lia; reflexivity). 
  - if_split.
Qed.
Definition kwf_cps_kshift_kshft := proj1 kwf_kshft_kshift'.
Definition kwf_val_kshift_kshft := proj1 (proj2 kwf_kshft_kshift').
Definition kwf_vals_kshift_kshft := proj1 (proj2 (proj2 kwf_kshft_kshift')).
Definition kwf_cpsbranches_kshift_kshft :=
  proj1 (proj2 (proj2 (proj2 kwf_kshft_kshift'))).
Definition kwf_fnlst_kshift_kshft :=
  proj2 (proj2 (proj2 (proj2 kwf_kshft_kshift'))).

Lemma kcl_cps_kshift_ushft:
  forall e, cps_kwf 0 e -> forall n k, kshift_cps n k e = kshft_cps k e.
Proof.
  intros. erewrite kwf_cps_kshift_kshft. reflexivity. eassumption. lia.
Qed.

(** k-shifting is a no-op for k-closed cps **)
Lemma kshift_kwf_noop:
  (forall (e:cps) n, cps_kwf n e -> forall m k, n < k ->
                    kshift_cps m k e = e) /\
  (forall (v:val_c) n, val_kwf n v -> forall m k, n < k ->
                      kshift_val m k v = v) /\
  (forall (v:vals_c) n, vals_kwf n v -> forall m k, n < k ->
                       kshift_vals m k v = v) /\
  (forall (v:branches_c) n, cpsbranches_kwf n v -> forall m k, n < k ->
                        kshift_branches m k v = v) /\
  (forall (v:fnlst) n, fnlst_kwf n v -> forall m k, n < k ->
                        kshift_fnlst m k v = v).
Proof.
  apply my_cps_ind; simpl; intros; try reflexivity;
  try (solve [inversion H0; subst; erewrite H; eauto]);
  try (solve [inversion H1; subst; erewrite H, H0; eauto]).
  - inversion H2; subst; erewrite H, H0, H1; eauto.
  - if_split. inversion H; subst. lia.
  - erewrite H. reflexivity. inversion H0. subst. eassumption. lia.
  - erewrite H. reflexivity. inversion H0. subst. eassumption. lia.
  - erewrite H, H0; try eassumption; try reflexivity.
    + inversion H1. subst. eassumption.
    + inversion H1. subst. eassumption.
    + lia.
Qed.


(** k-substitution.
    Substitution of a value for a continuation variable.  This has no
    effect on [Var_c], and the k-index changes when going under
    either a [Cont_c] or a [Lam_c].

    Since (eval_cps e) is k-closed, no shifting is required for 
    _evaluation_.  Shifting is required for reduction.
**)
(* no shifting: only for evaluation of k-closed terms *)
Fixpoint nsksbst_cps (v:val_c) (k:N) (e:cps): cps :=
  match e with
    | Halt_c v' => Halt_c (nsksbst_val v k v')
    | Ret_c v1 v2 => Ret_c (nsksbst_val v k v1) (nsksbst_val v k v2)
    | Call_c v1 v2 v3 =>
      Call_c (nsksbst_val v k v1) (nsksbst_val v k v2) (nsksbst_val v k v3)
    | Match_c v' bs =>
      Match_c (nsksbst_val v k v') (nsksbst_branches v k bs)
  end
with nsksbst_val (v:val_c) (k:N) (v':val_c): val_c :=
  match v' with
    | KVar_c i => if lt_dec i k then KVar_c i
                 else if eq_dec i k then v
                      else KVar_c (i - 1)
    | Var_c i => Var_c i
    | Lam_c e => Lam_c (nsksbst_cps v (1 + k) e)
    | Cont_c e => Cont_c (nsksbst_cps v (1 + k) e) 
    | Con_c d vs => Con_c d (nsksbst_vals v k vs)
    | Fix_c cs i => Fix_c (nsksbst_fnlst v k cs) i
  end
with nsksbst_vals (u:val_c) (k:N) (vs:vals_c): vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (nsksbst_val u k v) (nsksbst_vals u k vs)
       end
with nsksbst_fnlst (v:val_c) (k:N) (fls:fnlst): fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (nsksbst_cps v (1+k) f) (nsksbst_fnlst v k fs)
       end
with nsksbst_branches (v:val_c) (k:N) (bs:branches_c): branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (nsksbst_cps v k c) (nsksbst_branches v k bs)
       end.

(* unoptimised, for possibly open terms *)
Fixpoint ksbst_cps (v:val_c) (k:N) (e:cps) {struct e}: cps :=
  match e with
    | Halt_c v' => Halt_c (ksbst_val v k v')
    | Ret_c v1 v2 => Ret_c (ksbst_val v k v1) (ksbst_val v k v2)
    | Call_c v1 v2 v3 =>
      Call_c (ksbst_val v k v1) (ksbst_val v k v2) (ksbst_val v k v3)
    | Match_c v' bs =>
      Match_c (ksbst_val v k v') (ksbst_branches v k bs)
  end
with ksbst_val (v:val_c) (k:N) (v':val_c) {struct v'}: val_c :=
  match v' with
    | KVar_c i => if lt_dec i k then KVar_c i
                 else if eq_dec i k then v
                      else KVar_c (i - 1)
    | Var_c i => Var_c i
    | Lam_c e =>    (* JGM: should this be ushft of v? *)
          Lam_c (ksbst_cps (kshft_val 0 v) (1 + k) e)
    | Cont_c e => Cont_c (ksbst_cps (kshft_val 0 v) (1 + k) e)
    | Con_c d vs => Con_c d (ksbst_vals v k vs)
    | Fix_c cs i => Fix_c (ksbst_fnlst v k cs) i
  end
with ksbst_vals (u:val_c) (k:N) (vs:vals_c) {struct vs} : vals_c :=
       match vs with
         | vcnil => vcnil
         | vccons v vs => vccons (ksbst_val u k v) (ksbst_vals u k vs)
       end
with ksbst_fnlst (v:val_c) (k:N) (fls:fnlst) {struct fls}: fnlst :=
       match fls with
         | flnil => flnil
         | flcons f fs =>
           flcons (ksbst_cps (kshft_val 0 v) (1+k) f) (ksbst_fnlst v k fs)
       end
with ksbst_branches (v:val_c) (k:N) (bs:branches_c) {struct bs}: branches_c :=
       match bs with
         | brnil_c => brnil_c
         | brcons_c d j c bs =>
           brcons_c d j (ksbst_cps v k c)
                    (ksbst_branches (kshft_val 0 v) k bs)
       end.

(* unoptimised, for possibly open terms: later *)


(** Use square brackets for continuation substitution. *)
Class KSbstitute (v:Type) (t:Type) := { ksbstitute: v -> N -> t -> t }.
Notation "M [ j ::= N ]" :=
  (ksbstitute N j M) (at level 10, right associativity).
Instance KCPSSbstitute: KSbstitute val_c cps :=
  { ksbstitute := ksbst_cps }.
Instance KValSbstitute: KSbstitute val_c val_c :=
  { ksbstitute := ksbst_val }.
Instance KValsSbstitute: KSbstitute val_c vals_c :=
  { ksbstitute := ksbst_vals }.
Instance KBranchesSbstitute: KSbstitute val_c branches_c :=
  { ksbstitute := ksbst_branches}.
Instance KFNListSbstitute: KSbstitute val_c fnlst :=
  { ksbstitute := ksbst_fnlst}.

Class nsKSbstitute (v:Type) (t:Type) := { nsksbstitute: v -> N -> t -> t }.
Notation "M [ j ;= N ]" :=
  (nsksbstitute N j M) (at level 10, right associativity).
Instance nsKCPSSbstitute: nsKSbstitute val_c cps :=
  { nsksbstitute := nsksbst_cps }.
Instance nsKValSbstitute: nsKSbstitute val_c val_c :=
  { nsksbstitute := nsksbst_val }.
Instance nsKValsSbstitute: nsKSbstitute val_c vals_c :=
  { nsksbstitute := nsksbst_vals }.
Instance nsKBranchesSbstitute: nsKSbstitute val_c branches_c :=
  { nsksbstitute := nsksbst_branches}.
Instance nsKFNListSbstitute: nsKSbstitute val_c fnlst :=
  { nsksbstitute := nsksbst_fnlst}.

Lemma vsbst_eq: forall u k, (KVar_c k)[k ::= u] = u.
Proof. 
  intros. simpl. repeat if_split. 
Qed.
Hint Rewrite vsbst_eq.

Lemma vsbst_gt: forall u i k, i < k -> (KVar_c k)[i ::= u] = KVar_c (k - 1).
Proof.
  intros; simpl. repeat if_split.
Qed.

Lemma vsbst_lt: forall u i k, k < i -> (KVar_c k)[i ::= u] = KVar_c k.
Proof.
  intros; simpl. if_split. 
Qed.

(*************** ?????
Lemma kshft_ksbst:
    (forall (e:cps) j i u, j < i + 1 ->
     kshft_cps i (e[j ::= u]) = (kshft_cps (i + 1) e)[j ::= kshft_val i u]) /\
    (forall (v:val_c) j i u, j < i + 1 ->
     kshft_val i (v[j ::= u]) = (kshft_val (i + 1) v)[j ::= kshft_val i u]) /\
    (forall (v:vals_c) j i u, j < i + 1 ->
     kshft_vals i (v[j ::= u]) = 
     (kshft_vals (i + 1) v)[j ::= kshft_val i u]) /\
    (forall (b:branches_c) j i u, j < i + 1 ->
     kshft_branches i (b[j ::= u]) = 
     (kshft_branches (i + 1) b)[j ::= kshft_val i u]) /\
    (forall (b:fnlst) j i u, j < i + 1 ->
     kshft_fnlst i (b[j ::= u]) = 
     (kshft_fnlst (i + 1) b)[j ::= kshft_val i u]).
Proof.
  apply my_cps_ind; simpl; intros; intros; try reflexivity;
  try (solve [simpl; rewrite H; try lia; reflexivity]);
  try (solve [simpl; rewrite H, H0; try lia; reflexivity]);
  try (solve [simpl; rewrite H, H0, H1; try lia; reflexivity]).
  - repeat if_split.
    + destruct (lt_dec n (i + 1)); try lia.
    + destruct (lt_dec n (i + 1)); try lia.
    + destruct (lt_dec n (i + 1)); try lia.
    + replace (n - 1 + 1) with (n + 1 - 1); try lia. reflexivity.
  - rewrite H; try lia. 
    replace (1 + (i + 1)) with (1 + i + 1); try lia. 
    replace (1 + i) with (i + 1); try lia. 
    rewrite val_kshft_kshft. reflexivity. lia.
  - rewrite <- val_kshft_kshft; try lia.
    rewrite H; try lia. replace (1 + (i + 1)) with (1 + i + 1); try lia. 
    replace (1 + i) with (i + 1); try lia. reflexivity.
  - apply f_equal2.
    + rewrite H; try lia. reflexivity.
    + rewrite H0; try lia. rewrite <- val_kshft_kshft; try lia. 
      admit.
  - apply f_equal2.
    + rewrite H; try lia.
      replace (1+i) with (i+1); try lia. rewrite val_kshft_kshft; try lia.
      replace (1 + (i + 1)) with (i + 1 + 1); try lia. reflexivity.
    + rewrite H0; try lia. reflexivity.
Admitted.

rewrite val_kshft_kshft. reflexivity.
    rewrite H0. rewrite <- val_kshft_kshft.
    rewrite H, H0; try lia.
    rewrite <- val_kshft_kshft at 1. rewrite <- val_kshft_kshft.
    rewrite <- val_kshft_kshft . rewrite <- val_kshft_kshft .


  - destruct (lt_dec n (i + 1)); destruct (lt_dec n i); try reflexivity.
    + assert (h:n = i). lia. subst. admit.
    + lia.
  - rewrite H; try lia. 
    replace (1 + (i + 1)) with (1 + i + 1); try lia. 
    replace (1 + i) with (i + 1); try lia. reflexivity.
  - apply f_equal2. 
    + rewrite <- val_kshft_kshft. rewrite H; try lia. 
      replace (n + (i + 1)) with (n + i + 1); try lia. reflexivity.

Check val_kshft_kshft. admit.
    + rewrite H0; try lia. rewrite <- val_kshft_kshft.
    replace (n + (i + 1)) with (n + i + 1); try lia.
    apply f_equal2. 
    + rewrite val_kshft_kshft.
    + rewrite <- H.
    + apply f_equal2; try reflexivity.
      replace (1 + (i + 1)) with (1 + i + 1); try lia.
      replace (1 + i) with (i + 1); try lia.  admit.
(***
  - apply f_equal2. 
    + apply f_equal2. reflexivity. rewrite H; try lia. admit.
    + rewrite H0; try lia. reflexivity.
***)
  - apply f_equal2.
    + rewrite H; try lia. replace (2 + i) with (i+1+1); try lia.
      rewrite (val_kshft_kshft u 0 (i+1)); try lia. admit.
    + rewrite H0; try lia. reflexivity.
Admitted.


***************)
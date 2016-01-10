Require Import Arith BinNat String List Omega Coq.Program.Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Export L4.expression.

(***************************************)
(*** CPS expressions and translation ***)
(***************************************)

(** We distinguish values from computations in the syntax.  In
    addition, we have two separate deBruijn name spaces -- one for
    user-level variables that come from the source expression (and
    remain the same after being translated) and one for continuation
    variables which are introduced as part of the CPS translation.

    So for instance, [Var_c] refers to a user-level variable, whereas
    [KVar_c] refers to a continuation variable.

    The construct [Cont_c] is a one-argument lambda that abstracts a
    [KVar_c].

    The construct [Lam_c] is a two-argument lambda that abstracts a
    [KVar_c] and a [Var_c].  So for instance, the expression: 
    [Lam_c (Ret_c (KVar_c 0) (Var_c 0))] is closed and corresponds to 
    [fun k x => k x].
*)
Inductive cps: Type :=
| Halt_c: val_c -> cps
| Ret_c: val_c (* result *) -> val_c (* cont *) -> cps
| Call_c: val_c (* fn *) -> val_c (* cont *) -> val_c (* arg *) -> cps
| Match_c: val_c -> branches_c -> cps
with val_c: Type :=
| Var_c: N -> val_c
| KVar_c: N -> val_c
| Lam_c: cps (* abstract cont first, then arg *) -> val_c
| Cont_c: cps (* abstracts arg *) -> val_c
| Con_c: dcon -> vals_c -> val_c
(* each of the Fix expressions abstracts
 (a) a user-level variable corresponding to the fixpoint record,
 (b) a user-level variable corresponding to the function
     argument, and
 (c) a continuation variable.
*)                                  
| Fix_c: fnlst -> N -> val_c
with fnlst: Type :=
| flnil: fnlst
| flcons: cps -> fnlst -> fnlst
with vals_c: Type :=
| vcnil: vals_c
| vccons: val_c -> vals_c -> vals_c
with branches_c: Type :=
| brnil_c: branches_c
| brcons_c: dcon -> N -> cps -> branches_c -> branches_c.
Hint Constructors cps val_c vals_c branches_c fnlst.
Scheme cps_ind2 := Induction for cps Sort Prop
with val_c_ind2 := Induction for val_c Sort Prop
with vals_c_ind2 := Induction for vals_c Sort Prop
with branches_c_ind2 := Induction for branches_c Sort Prop
with fnlst_ind2 := Induction for fnlst Sort Prop.
Combined Scheme my_cps_ind from cps_ind2, val_c_ind2,
      vals_c_ind2, branches_c_ind2, fnlst_ind2.

Fixpoint vals_c_length (vs:vals_c) : N :=
  match vs with
    | vcnil => N0
    | vccons _ us => 1 + (vals_c_length us)
  end.
Fixpoint branches_c_length (vs:branches_c) : N :=
  match vs with
    | brnil_c => N0
    | brcons_c _ _ _ us => 1 + (branches_c_length us)
  end.
Fixpoint fnlst_length (vs:fnlst) : N :=
  match vs with
    | flnil => N0
    | flcons _ us => 1 + (fnlst_length us)
  end.


(** [cps_kwf j c] (resp. [val_kwf j v]) holds when [c] (resp. [v]) has no 
    no free continuation variable greater than or equal to [j]. *)
Inductive cps_kwf: N -> (* cont *) cps -> Prop :=
| halt_kwf: forall j v, val_kwf j v -> cps_kwf j (Halt_c v)
| ret_kwf: forall j v1 v2,
             val_kwf j v1 -> val_kwf j v2 ->
             cps_kwf j (Ret_c v1 v2)
| call_kwf: forall j v1 v2 v3, 
              val_kwf j v1 -> val_kwf j v2 -> val_kwf j v3 -> 
              cps_kwf j (Call_c v1 v2 v3)
| match_kwf: forall j v bs,
               val_kwf j v -> cpsbranches_kwf j bs ->
               cps_kwf j (Match_c v bs)
with val_kwf: N -> val_c -> Prop :=
| var_kwf: forall j k, val_kwf j (Var_c k)
| kvar_kwf: forall j k, k < j -> val_kwf j (KVar_c k)
| lam_kwf: forall j c, cps_kwf (1 + j) c -> val_kwf j (Lam_c c)
| cont_kwf: forall j c, cps_kwf (1 + j) c -> val_kwf j (Cont_c c)
| con_kwf: forall j d vs, vals_kwf j vs -> val_kwf j (Con_c d vs)
| fix_kwf: forall j k cs, fnlst_kwf j cs -> val_kwf j (Fix_c cs k)
with vals_kwf: N -> vals_c -> Prop :=
| nil_c_kwf: forall j, vals_kwf j vcnil
| cons_c_kwf: forall j v vs, val_kwf j v -> vals_kwf j vs ->
                               vals_kwf j (vccons v vs)
with cpsbranches_kwf: N -> branches_c -> Prop :=
| nil_b_kwf: forall j, cpsbranches_kwf j brnil_c
| cons_b_kwf: forall j d n c bs, cps_kwf j c ->
              cpsbranches_kwf j bs ->
              cpsbranches_kwf j (brcons_c d n c bs)
with fnlst_kwf: N -> fnlst -> Prop :=
| nil_fn_kwf: forall j, fnlst_kwf j flnil
| cons_fn_kwf: forall j c cs,
                 cps_kwf (1 + j) c -> fnlst_kwf j cs ->
                 fnlst_kwf j (flcons c cs).
Hint Constructors cps_kwf val_kwf vals_kwf cpsbranches_kwf fnlst_kwf.
Scheme cps_kwf_ind2 := Induction for cps_kwf Sort Prop
with val_kwf_ind2 := Induction for val_kwf Sort Prop
with vals_kwf_ind2 := Induction for vals_kwf Sort Prop
with cpsbranches_kwf_ind2 := Induction for cpsbranches_kwf Sort Prop
with fnlst_kind2 := Induction for fnlst_kwf Sort Prop.
Combined Scheme my_kwf_ind from cps_kwf_ind2, val_kwf_ind2,
      vals_kwf_ind2, cpsbranches_kwf_ind2, fnlst_kind2.


(** [cps_uwf i c] (resp. [val_uwf i v]) holds when [c] (resp. [v]) has 
    no free user variable greater than or equal to [i]. *)
Inductive cps_uwf: N (* user *) -> cps -> Prop :=
| halt_uwf: forall i v, val_uwf i v -> cps_uwf i (Halt_c v)
| ret_uwf: forall i v1 v2,
             val_uwf i v1 -> val_uwf i v2 ->
             cps_uwf i (Ret_c v1 v2)
| call_uwf: forall i v1 v2 v3, 
              val_uwf i v1 -> val_uwf i v2 -> val_uwf i v3 -> 
              cps_uwf i (Call_c v1 v2 v3)
| match_uwf: forall i v bs,
               val_uwf i v -> cpsbranches_uwf i bs ->
               cps_uwf i (Match_c v bs)
with val_uwf: N -> val_c -> Prop :=
| var_uwf: forall i k, k < i -> val_uwf i (Var_c k)
| kvar_uwf: forall i k, val_uwf i (KVar_c k)
| lam_uwf: forall i c, cps_uwf (1 + i) c -> val_uwf i (Lam_c c)
| cont_uwf: forall i c, cps_uwf i c -> val_uwf i (Cont_c c)
| con_uwf: forall i d vs, vals_uwf i vs -> val_uwf i (Con_c d vs)
| fix_uwf: forall i cs k, fnlst_uwf (fnlst_length cs + i) cs -> val_uwf i (Fix_c cs k)
with vals_uwf: N -> vals_c -> Prop :=
| nil_c_uwf: forall i, vals_uwf i vcnil
| cons_c_uwf: forall i v vs, val_uwf i v -> vals_uwf i vs ->
                               vals_uwf i (vccons v vs)
with cpsbranches_uwf: N -> branches_c -> Prop :=
| nil_b_uwf: forall i, cpsbranches_uwf i brnil_c
| cons_b_uwf: forall i d n c bs, cps_uwf (n+i) c ->
              cpsbranches_uwf i bs ->
              cpsbranches_uwf i (brcons_c d n c bs)
with fnlst_uwf: N -> fnlst -> Prop :=
| nil_fn_uwf: forall i, fnlst_uwf i flnil
| cons_fn_uwf: forall i c cs,
                 cps_uwf (1 + i) c -> fnlst_uwf i cs ->
                 fnlst_uwf i (flcons c cs).
Hint Constructors cps_uwf val_uwf vals_uwf cpsbranches_uwf fnlst_uwf.
Scheme cps_uwf_ind2 := Induction for cps_uwf Sort Prop
with val_uwf_ind2 := Induction for val_uwf Sort Prop
with vals_uwf_ind2 := Induction for vals_uwf Sort Prop
with cpsbranches_uwf_ind2 := Induction for cpsbranches_uwf Sort Prop
with ufn_list_ind2 := Induction for fnlst_uwf Sort Prop.
Combined Scheme my_uwf_ind from cps_uwf_ind2, val_uwf_ind2,
      vals_uwf_ind2, cpsbranches_uwf_ind2, ufn_list_ind2.


(** [cps_wf i j c] (resp. [val_wf i j v]) holds when [c] (resp. [v]) has no 
    free user variable greater than or equal to [i], and no free 
    continuation variable greater than or equal to [j]. *)
Inductive cps_wf: N (* user *) -> N -> (* cont *) cps -> Prop :=
| halt_wf: forall i j v, val_wf i j v -> cps_wf i j (Halt_c v)
| ret_wf: forall i j v1 v2,
             val_wf i j v1 -> val_wf i j v2 ->
             cps_wf i j (Ret_c v1 v2)
| call_wf: forall i j v1 v2 v3, 
              val_wf i j v1 -> val_wf i j v2 -> val_wf i j v3 -> 
              cps_wf i j (Call_c v1 v2 v3)
| match_wf: forall i j v bs,
               val_wf i j v -> cpsbranches_wf i j bs ->
               cps_wf i j (Match_c v bs)
with val_wf: N -> N -> val_c -> Prop :=
| var_wf: forall i j k, k < i -> val_wf i j (Var_c k)
| kvar_wf: forall i j k, k < j -> val_wf i j (KVar_c k)
| lam_wf: forall i j c, cps_wf (1 + i) (1 + j) c -> val_wf i j (Lam_c c)
| cont_wf: forall i j c, cps_wf i (1 + j) c -> val_wf i j (Cont_c c)
| con_wf: forall i j d vs, vals_wf i j vs -> val_wf i j (Con_c d vs)
| fix_wf: forall i j cs k, fnlst_wf (fnlst_length cs + i) j cs -> val_wf i j (Fix_c cs k)
with vals_wf: N -> N -> vals_c -> Prop :=
| nil_c_wf: forall i j, vals_wf i j vcnil
| cons_c_wf: forall i j v vs, val_wf i j v -> vals_wf i j vs ->
                               vals_wf i j (vccons v vs)
with cpsbranches_wf: N -> N -> branches_c -> Prop :=
| nil_b_wf: forall i j, cpsbranches_wf i j brnil_c
| cons_b_wf: forall i j d n c bs, cps_wf (n+i) j c ->
              cpsbranches_wf i j bs -> 
              cpsbranches_wf i j (brcons_c d n c bs)
with fnlst_wf: N -> N -> fnlst -> Prop :=
| nil_fn_wf: forall i j, fnlst_wf i j flnil
| cons_fn_wf: forall i j c cs,
                 cps_wf (1 + i) (1 + j) c -> fnlst_wf i j cs ->
                 fnlst_wf i j (flcons c cs).
Hint Constructors cps_wf val_wf vals_wf cpsbranches_wf fnlst_wf.
Scheme cps_wf_ind2 := Induction for cps_wf Sort Prop
with val_wf_ind2 := Induction for val_wf Sort Prop
with vals_wf_ind2 := Induction for vals_wf Sort Prop
with cpsbranches_wf_ind2 := Induction for cpsbranches_wf Sort Prop
with fnlst_ind3 := Induction for fnlst_wf Sort Prop.
Combined Scheme my_wf_ind from cps_wf_ind2, val_wf_ind2,
      vals_wf_ind2, cpsbranches_wf_ind2, fnlst_ind3.

(** wf implies kwf **)
Lemma cps_wf_kwf':
  (forall i j e, cps_wf i j e -> cps_kwf j e) /\
  (forall i j v, val_wf i j v -> val_kwf j v) /\
  (forall i j vs, vals_wf i j vs -> vals_kwf j vs) /\ 
  (forall i j bs, cpsbranches_wf i j bs -> cpsbranches_kwf j bs) /\
  (forall i j cs, fnlst_wf i j cs -> fnlst_kwf j cs).
Proof.
  apply my_wf_ind; intros; auto.
Qed.
Definition cps_wf_kwf := proj1 cps_wf_kwf'.
Definition val_wf_kwf := proj1 (proj2 cps_wf_kwf').
Definition vals_wf_kwf := proj1 (proj2 (proj2 cps_wf_kwf')).
Definition cpsbranches_wf_kwf := proj1 (proj2 (proj2 (proj2 cps_wf_kwf'))).
Definition fnlst_wf_kwf := proj2 (proj2 (proj2 (proj2 cps_wf_kwf'))).

(** wf implies uwf **)
Lemma cps_wf_uwf':
  (forall i j e, cps_wf i j e -> cps_uwf i e) /\
  (forall i j v, val_wf i j v -> val_uwf i v) /\
  (forall i j vs, vals_wf i j vs -> vals_uwf i vs) /\ 
  (forall i j bs, cpsbranches_wf i j bs -> cpsbranches_uwf i bs) /\
  (forall i j cs, fnlst_wf i j cs -> fnlst_uwf i cs).
Proof.
  apply my_wf_ind; intros; auto.
Qed.
Definition cps_wf_uwf := proj1 cps_wf_uwf'.
Definition val_wf_uwf := proj1 (proj2 cps_wf_uwf').
Definition vals_wf_uwf := proj1 (proj2 (proj2 cps_wf_uwf')).
Definition cpsbranches_wf_uwf := proj1 (proj2 (proj2 (proj2 cps_wf_uwf'))).
Definition fnlst_wf_uwf := proj2 (proj2 (proj2 (proj2 cps_wf_uwf'))).

(** Weakening holds on well-formedness of CPS terms. *)
Lemma cps_weaken' :
  (forall i j e, cps_wf i j e -> forall k l, cps_wf (k + i) (l + j) e) /\
  (forall i j v, val_wf i j v -> forall k l, val_wf (k + i) (l + j) v) /\
  (forall i j vs, vals_wf i j vs -> forall k l, vals_wf (k + i) (l + j) vs) /\ 
  (forall i j bs, cpsbranches_wf i j bs ->
                  forall k l, cpsbranches_wf (k + i) (l + j) bs) /\
  (forall i j cs, fnlst_wf i j cs ->
                  forall k l, fnlst_wf (k + i) (l + j) cs).
Proof.
  apply my_wf_ind; simpl; intros; eauto; constructor; try lia; auto.
  - specialize (H k l).
    replace (1 + (k + i)) with (k + (1 + i)); try lia.
    replace (1 + (l + j)) with (l + (1 + j)); try lia. assumption.
  - specialize (H k l). replace (1 + (l + j)) with (l + (1 + j)); [auto|lia].
  - specialize (H k0 l).
    now replace (fnlst_length cs + (k0 + i)) with
      (k0 + (fnlst_length cs + i)); try lia.
  - specialize (H k l).
    replace (1 + (l + j)) with (l + (1 + j)); try lia.
    replace (n + (k + i)) with (k + (n + i)); [auto | lia].
  - replace (1 + (k + i)) with (k + (1 + i)); try lia.
    replace (1 + (l + j)) with (l + (1 + j)); try lia. apply H.
Qed.
Definition cps_weaken := proj1 cps_weaken'.
Definition val_weaken := proj1 (proj2 cps_weaken').
Definition vals_weaken := proj1 (proj2 (proj2 cps_weaken')).
Definition cpsbranches_weaken := proj1 (proj2 (proj2 (proj2 cps_weaken'))).
Definition fnlst_weaken := proj2 (proj2 (proj2 (proj2 cps_weaken'))).

Lemma cps_closed_weaken: forall i j c, cps_wf 0 0 c -> cps_wf i j c.
  intros. generalize (cps_weaken _ _ _ H i j) ;
          repeat rewrite N.add_0_r; auto.
Qed.
Lemma val_closed_weaken: forall i j v, val_wf 0 0 v -> val_wf i j v.
  intros. generalize (val_weaken _ _ _ H i j) ;
          repeat rewrite N.add_0_r; auto.
Qed.
Lemma vals_closed_weaken: forall i j vs, vals_wf 0 0 vs -> vals_wf i j vs.
  intros. generalize (vals_weaken _ _ _ H i j) ;
          repeat rewrite N.add_0_r; auto.
Qed.
Lemma cpsbranches_closed_weaken :
  forall i j bs, cpsbranches_wf 0 0 bs -> cpsbranches_wf i j bs.
  intros. generalize (cpsbranches_weaken _ _ _ H i j) ;
          repeat rewrite N.add_0_r; auto.
Qed.
Lemma fnlst_closed_weaken :
  forall i j cs, fnlst_wf 0 0 cs -> fnlst_wf i j cs.
  intros. generalize (fnlst_weaken _ _ _ H i j).
  repeat rewrite N.add_0_r; auto.
Qed.
Hint Resolve cps_closed_weaken val_closed_weaken vals_closed_weaken
     cpsbranches_closed_weaken fnlst_closed_weaken.

(** k-weakening holds on kwf CPS terms. *)
Lemma cps_kweaken' :
  (forall j e, cps_kwf j e -> forall l, cps_kwf (l + j) e) /\
  (forall j v, val_kwf j v -> forall l, val_kwf (l + j) v) /\
  (forall j vs, vals_kwf j vs -> forall l, vals_kwf (l + j) vs) /\ 
  (forall j bs, cpsbranches_kwf j bs ->
                  forall l, cpsbranches_kwf (l + j) bs) /\
  (forall j cs, fnlst_kwf j cs ->
                  forall l, fnlst_kwf (l + j) cs).
Proof.
  apply my_kwf_ind; simpl; intros; eauto; constructor; try lia; auto;
  repeat (replace (1 + (l + j)) with (l + (1 + j)); try lia; apply H).
Qed.
Definition cps_kweaken := proj1 cps_kweaken'.
Definition val_kweaken := proj1 (proj2 cps_kweaken').
Definition vals_kweaken := proj1 (proj2 (proj2 cps_kweaken')).
Definition cpsbranches_kweaken := proj1 (proj2 (proj2 (proj2 cps_kweaken'))).
Definition fnlst_kweaken := proj2 (proj2 (proj2 (proj2 cps_kweaken'))).

(** u-weakening holds on uwf CPS terms. *)
Lemma cps_uweaken' :
  (forall j e, cps_uwf j e -> forall l, cps_uwf (l + j) e) /\
  (forall j v, val_uwf j v -> forall l, val_uwf (l + j) v) /\
  (forall j vs, vals_uwf j vs -> forall l, vals_uwf (l + j) vs) /\ 
  (forall j bs, cpsbranches_uwf j bs ->
                  forall l, cpsbranches_uwf (l + j) bs) /\
  (forall j cs, fnlst_uwf j cs ->
                  forall l, fnlst_uwf (l + j) cs).
Proof.
  apply my_uwf_ind; simpl; intros; eauto; constructor; try lia; auto;
  repeat (replace (1 + (l + i)) with (l + (1 + i)); try lia; apply H).
  - replace (fnlst_length cs + (l + i)) with (l + (fnlst_length cs + i)); try lia.
    apply H.
  - replace (n + (l + i)) with (l + (n + i)); try lia. apply H.
Qed.
Definition cps_uweaken := proj1 cps_uweaken'.
Definition val_uweaken := proj1 (proj2 cps_uweaken').
Definition vals_uweaken := proj1 (proj2 (proj2 cps_uweaken')).
Definition cpsbranches_uweaken := proj1 (proj2 (proj2 (proj2 cps_uweaken'))).
Definition fnlst_uweaken := proj2 (proj2 (proj2 (proj2 cps_uweaken'))).


(**************************)
(** * The CPS Translation *)
(**************************)

Fixpoint list_to_indices (es:exps): vals_c :=
  match es with
    | enil => vcnil
    | econs _ es => vccons (KVar_c (exps_length es)) (list_to_indices es)
  end.

Lemma list_to_indices_wf :
  forall es i j, vals_wf i (j + (exps_length es)) (list_to_indices es).
Proof.
  Opaque N.of_nat.
  induction es; simpl; intros; auto.
  repeat constructor. lia. 
  replace (j + (1 + exps_length es)) with ((1+j) + (exps_length es));
    auto; lia.
Qed.

(** The inner, naive CBV CPS translation.  This introduces a lot of 
    administrative reductions, but simple things first.  Importantly,
    things that are already values are treated a little specially.  
    This ensures a substitution property 
    [cps_cvt(e{x:=v}) = (cps_cvt e){x:=(cps_vt_val v)}].
 *)
Function cps_cvt (e:exp) {struct e} : val_c :=
  match e with
    | App_e e1 e2 =>
      (* cont \k.(ret [e1] (cont \v1.(ret [e2] (cont \v2.call v1 k v2)))) *)
      Cont_c (Ret_c (cps_cvt e1)
                    (Cont_c (Ret_c (cps_cvt e2)
                                   (Cont_c (Call_c (KVar_c 1)
                                                   (KVar_c 2) (KVar_c 0))))))
    | Con_e d es => Cont_c (cps_cvts es (Ret_c (KVar_c (exps_length es))
                                               (Con_c d (list_to_indices es))))
(***
      match are_valuesb es with
        | false => Cont_c (cps_cvts es
                                    (Ret_c (KVar_c (exps_length es))
                                           (Con_c d (list_to_indices es))))
        | true => Cont_c (Ret_c (KVar_c 0) (Con_c d (cps_cvt_vals es)))
      end
***)
    | Match_e e bs => 
      Cont_c (Ret_c (cps_cvt e)
                    (Cont_c (Match_c (KVar_c 0) (cps_cvt_branches bs))))
    | Let_e e2 e1 =>
      (* translate as if it were App_e (Lam_e e1) e2 *)
      Cont_c (Ret_c (cps_cvt e2)
                    (Cont_c (Call_c (Lam_c (Ret_c (cps_cvt e1) (KVar_c 0)))
                                    (KVar_c 1) (KVar_c 0))))
    | Var_e i => Cont_c (Ret_c (KVar_c 0) (Var_c i))
    | Lam_e e => Cont_c (Ret_c (KVar_c 0)
                               (Lam_c (Ret_c (cps_cvt e) (KVar_c 0))))
    | Fix_e es k => Cont_c (Ret_c (KVar_c 0) (Fix_c (cps_cvt_fnlst es) k))
  end
with cps_cvts (es:exps) (c:cps) : cps :=
    match es with
      | enil => c
      | econs e es => Ret_c (cps_cvt e) (Cont_c (cps_cvts es c))
    end
(** (es:exps) (d:dcon) {struct es} : cps :=
       match es with
         | enil => Ret_c (KVar_c (exps_length es))
                         (Con_c d (list_to_indices es))
         | econs e es => Ret_c (cps_cvt e) (Cont_c (cps_cvts es d))
       end
**)
with cps_cvt_branches (bs:branches_e) {struct bs}: branches_c :=
       match bs with
         | brnil_e => brnil_c
         | brcons_e d n e bs => brcons_c d n (Ret_c (cps_cvt e) (KVar_c 1))
                                         (cps_cvt_branches bs)
       end
with cps_cvt_fnlst (es:efnlst) {struct es}: fnlst :=
       match es with
         | eflnil => flnil
         | eflcons e es => flcons (Ret_c (cps_cvt e) (KVar_c 0))
                                (cps_cvt_fnlst es)
       end.

Fixpoint cps_cvt_val (e:exp) : val_c := 
  match e with
      | Var_e n => Var_c n
      | Lam_e e => Lam_c (Ret_c (cps_cvt e) (KVar_c 0))
      | Con_e d es => Con_c d (cps_cvt_vals es)
      | Fix_e es k => Fix_c (cps_cvt_fnlst es) k
      | _ => Var_c 5 (* impossible *)
  end
with cps_cvt_vals (es:exps) : vals_c :=
  match es with
    | enil => vcnil
    | econs e es => vccons (cps_cvt_val e) (cps_cvt_vals es)
  end.


(** The top-level CPS translation. We use [cont \x.Halt x] as the initial
    continuation. *)
Definition cps_cvt_prog (e:exp): cps := 
   Ret_c (cps_cvt e) (Cont_c (Halt_c (KVar_c 0))).

(* cps_cvt produces no free KVars *)
Lemma val_kwf_Con_d_independent:
  forall (d1 d2:dcon) (es:exps) j, exps_length es < j ->
       val_kwf j (Con_c d1 (list_to_indices es)) ->
       val_kwf j (Con_c d2 (list_to_indices es)).
Proof.
  induction es; intros j h.
  - repeat constructor.
  - intros h1. constructor. inversion h1. subst. exact H1.
Qed.

(****
Lemma val_kwf_Cont_d_independent:
  forall (es:exps) j (d1 d2:dcon), exps_length es < j ->
       val_kwf j (Cont_c (cps_cvts es d1)) ->
       val_kwf j (Cont_c (cps_cvts es d2)).
Proof.
  induction es; intros j d1 d2 h.
  - repeat constructor. lia.
  - simpl. intros h1. repeat constructor; inversion h1; subst.
    + inversion H1. subst. assumption. 
    + inversion H1. subst. inversion H4. subst.
      assert (h2:exps_length es < 1 + j). simpl in h. lia.
      specialize (IHes _ d1 d2 h2 H4). inversion IHes. subst. assumption.
Qed.
****)

(***
Goal forall es, are_values es ->
     forall d j, cps_kwf j (cps_cvts es d) -> vals_kwf j (cps_cvt_vals es).
Proof.
  induction 1; intros; simpl in *.
  + constructor.
  + constructor. inversion H1; subst.
    * admit.
    * eapply IHare_values.
***)

(****
Lemma cps_cvt_kclosed:
  (forall e, val_kwf 0 (cps_cvt e)) /\
  (forall (es:exps) (d:dcon),
     cps_kwf 1 (cps_cvts es (Ret_c (KVar_c (exps_length es))
                                   (Con_c d (list_to_indices es))))) /\
  (forall (es:efnlst), fnlst_kwf 0 (cps_cvt_fnlst es)) /\
  (forall brs, cpsbranches_kwf 2 (cps_cvt_branches brs)).
Proof.
  apply my_exp_ind; intros; try (solve [repeat constructor]).
  - repeat constructor. repeat (apply val_kweaken). assumption.
  - repeat constructor.
    + repeat (apply val_kweaken). assumption.
    + repeat (apply val_kweaken). assumption.
  - simpl. repeat constructor. apply H.
  - repeat constructor. 
    + apply val_kweaken. assumption.
    + replace (1 + (1 + 0)) with 2; try lia. assumption.
  - repeat constructor.
    + apply val_kweaken. assumption.
    + repeat (apply val_kweaken). assumption.
  - repeat constructor. apply fnlst_kweaken. assumption.
  - repeat constructor. apply val_kweaken. assumption.
  - simpl. constructor.
    + replace 1 with (1 + 0); try lia. apply val_kweaken. assumption. 
    + constructor.


 simpl. apply cps_kweaken.

 apply H0.
  - constructor; try assumption. constructor. 
    + apply val_kweaken. assumption.
    + constructor. lia.
  - constructor; try assumption. constructor; try assumption.
    + replace 2 with (2 + 0); try lia. apply val_kweaken. assumption.
    + constructor. lia.
Qed.
***)

(***
Lemma cps_cvt_uclosed:
  (forall e, exp_wf 0 e -> val_uwf 0 (cps_cvt e)) /\
  (forall es, exps_wf 0 es -> vals_uwf 0 (cps_cvt_vals es)) /\
  (forall es, efnlst_wf 0 es -> fnlst_uwf 0 (cps_cvt_fnlst es)) /\
  (forall bs, branches_wf 0 bs -> cpsbranches_uwf 0 (cps_cvt_branches bs)).
Proof.
  apply my_exp_ind; simpl; intros;
  try (solve [repeat (try econstructor); try vm_compute]).
  - inversion H. lia.
  - repeat econstructor. inversion H0. subst. apply val_uweaken.
    apply H.
***)

Lemma cps_cvt_uclosed:
  (forall i e, exp_wf i e -> forall j, i < j -> val_uwf j (cps_cvt e)) /\
  (forall i es, exps_wf i es -> forall j, i < j ->
        vals_uwf j (cps_cvt_vals es)) /\
  (forall i es, efnlst_wf i es -> forall j, i < j -> 
         fnlst_uwf j (cps_cvt_fnlst es)) /\
  (forall i bs, branches_wf i bs -> forall j, i < j ->
         cpsbranches_uwf j (cps_cvt_branches bs)).
Proof.
  apply my_exp_wf_ind; simpl; intros;
  try (solve [repeat (try econstructor); try vm_compute]).
  - repeat econstructor. lia.
  - repeat econstructor. apply H. lia.
  - repeat econstructor.
    + apply H. assumption.
    + apply H0. assumption.
  - repeat econstructor. admit.
  - repeat econstructor.
    + apply H. assumption.
    + apply H0. assumption.
  - repeat econstructor.
     + apply H. assumption.
     + apply H0. lia.
  - repeat econstructor. apply H. admit.
  - repeat econstructor.
    + admit.
    + apply H0. assumption.
  - repeat econstructor.
    + apply val_uweaken. apply H. assumption.
    + apply H0. assumption.
  - repeat econstructor.
    + apply val_uweaken. apply H. admit.
    + apply H0. assumption.
Admitted.
(***********
  (forall i e, exp_uwf i e -> i = 0 -> val_kwf 0 (cps_cvt e)) /\
  (forall i v, val_uwf i v -> i = 0 -> val_kwf 0 (cps_cvt_val v)).
  (forall (es:exps) (d:dcon), cps_kwf 1 (cps_cvts es d)) /\
  (forall (es:efnlst), fnlst_kwf 0 (cps_cvt_fnlst es)) /\
  (forall brs, cpsbranches_kwf 2 (cps_cvt_branches brs)).
Proof.
  apply my_exp_ind; intros; try (solve [repeat constructor]).
********)
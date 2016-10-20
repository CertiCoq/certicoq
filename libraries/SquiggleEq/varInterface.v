(* MathClasses or Extlib may habe a much richer theory and implementation *)
Require Import Coq.Classes.DecidableClass.

Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.

Require Import list.

(* get rid of it eventually *)
Notation subsetv := subset (only parsing).

(** There can be different classes of variables, e.g. one for types, and one for terms.
As another example, during CPS conversion, it is handy to have a different class for continuation variables.
Substitution may need to rename bound variables,
and we prove that variable class is preserved by substitution. See
[alphaeq.ssubst_allvars_varclass_nb]
*)
Class VarClass (T ClassType : Type) :=
  varClass : T -> ClassType.

Class FreshVars (T ClassType : Type) := 
  freshVars : forall (n:nat)  (c : option ClassType) 
    (avoid : list T) (original : list T), list T.

Class VarType (T:Type) (ClassType : Type)  `{Deq T} 
  `{VarClass T ClassType} `{FreshVars T ClassType}:= {
(** We can generate fresh variables w.r.t. variables of any class. 
   [original] is a mechanism to pass extra information to [freshVars]. 
  For example, we often want the fresh replacement names to be close to original names.
  In such cases, [length original=n]. The correctness properties of [freshVars] ignore this input *)

(* Is it important to pick a more efficient variant of [nat]? This not a concern after extraction.
Even inside Coq the output is a list which will be built one element at a time. So [nat] should not
be the bottleneck*)

  freshCorrect: forall  (n:nat) (oc: option ClassType)  (avoid : list T) (original : list T), 
    let lf:= (freshVars  n oc avoid original) in
      (no_repeats lf 
      /\ disjoint lf avoid
      /\ length lf = n)
      /\ (forall c, oc = Some c -> forall v, In v lf -> varClass v = c); 
}.


Ltac addFreshVarsSpec :=
let tac n vc lva lvs :=
  let H := fresh "HfreshVars" in
  pose proof (freshCorrect n vc lva lvs) as H; simpl in H in
match goal with
[ |- context [freshVars ?n ?vc ?lva ?lvs]] => tac n vc lva lvs
|[ H: context [freshVars ?n ?vc ?lva ?lvs] |- _] => tac n vc lva lvs
end.

Require Import list.

Section Vars.
Context {NVar VClass : Type} `{VarType NVar VClass}.

Theorem eq_var_dec: forall x y : NVar, {x = y} + {x <> y}.
Proof.
  intros. apply decideP; auto.
Defined.

Lemma in_nvar_list_dec: forall (x : NVar) l, LIn x l [+] ! LIn x l.
Proof.
 induction l; simpl; sp. try (complete (right; sp)).
  destruct (eq_var_dec a x); subst; sp.
  right; sp.
Defined.


Theorem deq_nvar: Deq NVar.
Proof.
  eauto.
Defined.
Hint Immediate deq_nvar.


(** boolean membership of variable in a list of variables *)
Definition memvar := @memberb NVar _.

Lemma assert_memvar :
  forall v vars,
    assert (memvar v vars) <=> LIn v vars.
Proof.
  unfold memvar; intros.
  apply assert_memberb.
Qed.

Lemma memvar_app :
  forall v vs1 vs2,
    memvar v (vs1 ++ vs2) = memvar v vs1 || memvar v vs2.
Proof.
  unfold memvar; sp.
  apply memberb_app.
Qed.

Definition beq_var (a b : NVar):= decide (a=b).


Theorem beq_var_refl : forall X,
  true = beq_var X X.
Proof.
  intros. unfold beq_var. autorewrite with SquiggleEq.
  refl.
Qed.

Theorem not_eq_beq_var_false : forall i1 i2,
  i1 <> i2 -> beq_var i1 i2 = false.
Proof.
 intros. unfold beq_var. unfold decide.
 apply Decidable_sound_alt. auto.
Qed.

(* Move *)
Lemma bool_eq_as_true : forall b1 b2,
b1=b2 <-> (b1=true <-> b2 = true).
Proof.
  intros ? ?.
  destruct b1; destruct b2; try tauto; try congruence.
  split; try split; try discriminate; try tauto.
  intros. symmetry. tauto.
Qed.

Theorem beq_var_sym: forall i1 i2,
  beq_var i1 i2 = beq_var i2 i1.
Proof.
 intros.
 apply bool_eq_as_true.
 unfold beq_var.
 repeat rewrite Decidable_spec.
 split; intros; auto.
Qed.

Lemma memvar_singleton :
  forall a b,
    memvar a [b] = beq_var a b.
Proof.
  sp.
  unfold memvar; simpl. rewrite decide_decideP.
  destruct (decideP (b=a)); subst; sp.
  apply beq_var_refl.
  symmetry; apply not_eq_beq_var_false; sp.
Qed.


(** removes the elements of l1 from l2 *)
Definition remove_nvars (l1 l2 : list NVar) :=
 @diff NVar _ l1 l2.

Definition remove_nvar (l : list NVar) (v : NVar) :=
 remove_nvars [v] l.

Lemma null_remove_nvars :
  forall l1 l2,
    null (remove_nvars l1 l2) <=> forall x, LIn x l2 -> LIn x l1.
Proof.
  unfold remove_nvars.
  apply null_diff.
Qed.

Lemma in_remove_nvars :
  forall x l1 l2,
    LIn x (remove_nvars l1 l2) <=> (LIn x l2 # ! LIn x l1).
Proof.
  intros; apply in_diff.
Qed.

Lemma in_remove_nvar :
  forall x v l,
    LIn x (remove_nvar l v) <=> (LIn x l # x <> v).
Proof.
  intros; unfold remove_nvar; trw in_remove_nvars; simpl; split; sp.
Qed.

Lemma remove_nvar_nil : forall v, remove_nvar [] v = [].
Proof.
  sp.
Qed.

Lemma remove_nvars_unchanged :
  forall l1 l2,
    disjoint l2 l1 <=> remove_nvars l1 l2 = l2.
Proof.
  unfold remove_nvars.
  apply disjoint_iff_diff.
Qed.

Lemma remove_nvars_nil_l : forall l, remove_nvars [] l = l.
Proof.
  unfold remove_nvars; simpl; auto.
Qed.

Hint Rewrite remove_nvars_nil_l.

(* same as remove_nvars_nil_l *)
Lemma remove_var_nil : forall l, remove_nvars [] l = l.
Proof.
  sp; autorewrite with core.
Qed.

Lemma remove_nvars_nil_r : forall l, remove_nvars l [] = [].
Proof.
  unfold remove_nvars. apply diff_nil.
Qed.

Hint Rewrite remove_nvars_nil_r.

Lemma remove_nvars_app_r :
  forall l1 l2 l3,
    remove_nvars l1 (l2 ++ l3) = remove_nvars l1 l2 ++ remove_nvars l1 l3.
Proof.
  unfold remove_nvars.
  apply diff_app_r.
Qed.

Lemma remove_nvars_app_l :
  forall l1 l2 l3,
     remove_nvars l1 (remove_nvars l2 l3) = remove_nvars (l1 ++ l2) l3.
Proof.
  unfold remove_nvars.
  apply diff_app_l.
Qed.

Lemma remove_nvars_flat_map :
  forall T,
  forall f : T -> list NVar,
  forall l : list T,
  forall vars : list NVar,
   remove_nvars vars (flat_map f l) =
   flat_map (compose (fun vs => remove_nvars vars vs) f) l.
Proof.
  induction l; simpl; sp.
  apply remove_nvars_nil_r.
  rewrite remove_nvars_app_r.
  rewrite IHl.
  unfold compose.
  auto.
Qed.

Lemma remove_nvars_comm :
  forall l1 l2 l3,
    remove_nvars l1 (remove_nvars l2 l3) = remove_nvars l2 (remove_nvars l1 l3).
Proof.
  unfold remove_nvars; apply diff_comm.
Qed.

Lemma remove_nvars_dup :
  forall l1 l2 x l3,
    LIn x l1 -> remove_nvars (l1 ++ l2) l3 = remove_nvars (l1 ++ x :: l2) l3.
Proof.
  unfold remove_nvars; intros.
  apply diff_dup2; auto.
Qed.

Lemma remove_nvars_move :
  forall l1 l2 l3 x,
    remove_nvars (l1 ++ x :: l2) l3 = remove_nvars (x :: l1 ++ l2) l3.
Proof.
  unfold remove_nvars; intros.
  apply diff_move; auto.
Qed.

Lemma remove_nvars_cons :
  forall v l1 l2,
    remove_nvars (v :: l1) l2 = remove_nvars l1 (@remove NVar _ v l2).
Proof.
  unfold remove_nvars; simpl; auto.
Qed.

Lemma remove_nvars_cons_l_weak :
  forall v vs vars,
    !LIn v vars
    -> remove_nvars (v :: vs) vars
       = remove_nvars vs vars.
Proof.
  intros; unfold remove_nvars.
  rewrite diff_cons_r_ni; auto.
Qed.

Lemma remove_nvars_cons_r :
  forall l v vars,
    remove_nvars l (v :: vars)
    = if memvar v l then remove_nvars l vars
      else v :: remove_nvars l vars.
Proof.
  intros; unfold remove_nvars.
  rewrite diff_cons_r; auto.
Qed.

Lemma remove_nvar_cons :
  forall v x xs,
    remove_nvar (x :: xs) v
    = if beq_var v x then remove_nvar xs v
      else x :: remove_nvar xs v.
Proof.
  unfold remove_nvar; sp.
Qed.

Lemma disjoint_remove_nvars_l :
  forall l1 l2 l3,
    disjoint (remove_nvars l1 l2) l3 <=> disjoint l2 (remove_nvars l1 l3).
Proof.
  unfold remove_nvars; intros.
  apply disjoint_diff_l.
Qed.

Lemma remove_nvars_eq :
  forall l,
    remove_nvars l l = [].
Proof.
  unfold remove_nvars; sp.
  rw <- null_iff_nil.
  apply null_diff; sp.
Qed.


(** equals variable sets *)
Definition eq_vars := @eqsetb NVar _.

Notation eqset := eq_set (only parsing).
Notation eqsetv := eq_set (only parsing).


Lemma assert_eq_vars :
  forall vs1 vs2,
    assert (eq_vars vs1 vs2) <=> forall x, LIn x vs1 <=> LIn x vs2.
Proof.
  sp; unfold eq_vars.
  trw assert_eqsetb; sp.
Qed.

Lemma eqsetv_remove_nvar :
  forall vars1 vars2 v,
    eqsetv vars1 vars2
    -> eqsetv (remove_nvar vars1 v) (remove_nvar vars2 v).
Proof.
  introv.
  rewrite eqsetv_prop.
  rewrite eqsetv_prop in *; sp.
  allrw in_remove_nvar.
  allrw; sp.
Qed.

Lemma eqsetv_cons_l_iff :
  forall v vs1 vs2,
    eq_set (v :: vs1) vs2
    <=> (LIn v vs2 # eqsetv (remove_nvar vs1 v) (remove_nvar vs2 v)).
Proof.
  sp. do 2 (rewrite eqsetv_prop).
  split; intro i; sp; allrw in_remove_nvar; allsimpl.
  rw <- i; sp.
  split; sp.
  rw <- i; sp.
  apply_in_hyp p; sp; subst; sp.
  split; sp; subst; sp.
  destruct (eq_var_dec v x); subst; sp.
  gen_some x; allrw in_remove_nvar.
  discover; sp. firstorder.
  destruct (eq_var_dec v x); subst; sp.
  gen_some x; allrw in_remove_nvar.
  discover; sp; firstorder.
Qed.


(** 
Fixpoint insert (v : nat) (vars : list NVar) : list NVar :=
  match vars with
    | [] => [nvar v]
    | (nvar x) :: xs =>
        if lt_dec x v then nvar x :: insert v xs
        else if eq_nat_dec x v then vars
             else (nvar v) :: vars
  end.

Lemma insert_in :
  forall v vars,
    LIn (nvar v) (insert v vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  destruct (lt_dec n v); simpl; sp.
  destruct (eq_nat_dec n v); subst; simpl; sp.
Qed.

insertion of a nat in a list of variables in an ordered way 
Ltac invs2 :=
  match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; try subst; GC
    | [ H : nvar _ = nvar _ |- _ ] => inversion H; try subst; GC
  end.

Lemma in_insert :
  forall v x vars,
    LIn (nvar v) (insert x vars)
    <=> (v = x [+] LIn (nvar v) vars).
Proof.
  induction vars; simpl; sp.
  split; sp; invs2; sp.
  destruct a.
  destruct (eq_nat_dec n x); subst; allsimpl.
  destruct (lt_dec x x); sp; try omega; allsimpl.
  split; sp.
  destruct (lt_dec n x); sp; try omega; allsimpl.
  trewrite IHvars; split; sp.
  split; sp; invs2; sp.
Qed.

Lemma remove_nvar_insert :
  forall vars n,
    remove_nvar (insert n vars) (nvar n)
    = remove_nvar vars (nvar n).
Proof.
  induction vars; simpl; sp.
  rewrite remove_nvar_nil.
  rewrite remove_nvar_cons.
  rewrite remove_nvar_nil.
  rewrite <- beq_var_refl; sp.
  destruct a.
  destruct (lt_dec n0 n).
  rewrite remove_nvar_cons.
  destruct (eq_nat_dec n n0); subst; try omega.
  rewrite not_eq_beq_var_false; sp.
  rewrite remove_nvar_cons.
  rewrite not_eq_beq_var_false; sp.
  rewrite IHvars; sp.
  inversion H; subst; sp.
  inversion H; subst; sp.
  destruct (eq_nat_dec n0 n); subst; sp.
  repeat (rewrite remove_nvar_cons).
  rewrite <- beq_var_refl; sp.
Qed.

Fixpoint sort (vars : list NVar) : list NVar :=
  match vars with
    | [] => []
    | (nvar x) :: xs => insert x (sort xs)
  end.

Inductive issorted : list NVar -> Type :=
  | issorted_nil : issorted []
  | issorted_cons :
    forall v vs,
      (forall x, LIn x vs -> le_var v x)
      -> issorted vs
      -> issorted (v :: vs).

Hint Constructors issorted.
*)
Lemma eqsetv_refl {A} :
  forall (vs : list A), eqsetv vs vs.
Proof.
  sp.
Qed.

Hint Immediate eqsetv_refl.

(*
Lemma sort_eqsetv :
  forall vars,
    eqsetv vars (sort vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  trw eqsetv_cons_l_iff; sp.
  apply insert_in.
  rewrite remove_nvar_insert.
  apply eqsetv_remove_nvar; sp.
Qed.

Lemma sort_issorted :
  forall vars,
    issorted (sort vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  induction IHvars; simpl; sp.
  constructor; simpl; sp.
  destruct v.
  destruct (lt_dec n0 n).
  constructor; simpl; sp.
  destruct x; unfold le_var.
  allrw in_insert; sp; subst; try omega.
  apply_in_hyp p.
  unfold le_var in p; sp.
  destruct (eq_nat_dec n0 n); subst; sp.
  constructor; simpl; sp; subst.
  unfold le_var; omega.
  apply_in_hyp p; destruct x; allunfold le_var; omega.
Qed.

Fixpoint fresh_var_aux (v : nat) (vars : list NVar) : nat :=
  match vars with
    | [] => v
    | (nvar x) :: xs =>
      if lt_dec v x then v
      else if eq_nat_dec v x
           then fresh_var_aux (S v) xs
           else fresh_var_aux v xs
  end.

Lemma fresh_var_aux_le :
  forall vars v,
    v <= fresh_var_aux v vars.
Proof.
  induction vars; simpl; sp.
  destruct a.
  destruct (lt_dec v n); sp.
  destruct (eq_nat_dec v n); subst; auto.
  generalize (IHvars (S n)); sp; omega.
Qed.

Lemma fresh_var_aux_sorted_not_in :
  forall vars,
    issorted vars
    -> forall n, ! LIn (nvar (fresh_var_aux n vars)) vars.
Proof.
  intros vars H.
  induction H; simpl; sp.
  destruct v.
  destruct (lt_dec n n0).
  invs2; omega.
  destruct (eq_nat_dec n n0); subst.
  generalize (fresh_var_aux_le vs (S n0)); sp.
  invs2; omega.
  assert (n0 < n) by omega; clear n1 n2.
  generalize (fresh_var_aux_le vs n); sp.
  invs2; sp; omega.
  destruct v.
  destruct (lt_dec n n0).
  apply_in_hyp p.
  unfold le_var in p; omega.
  destruct (eq_nat_dec n n0); subst.
  allapply IHissorted; sp.
  allapply IHissorted; sp.
Qed.

Definition fresh_var (vars : list NVar) : NVar :=
  nvar (fresh_var_aux 0 (sort vars)).

Lemma fresh_var_not_in :
  forall vars,
    ! LIn (fresh_var vars) vars.
Proof.
  unfold fresh_var; introv X.
  generalize (sort_eqsetv vars); introv H.
  rewrite  eqsetv_prop  in H.
  trw_h H  X.
  apply fresh_var_aux_sorted_not_in in X. sp.
  apply sort_issorted.
Qed.

Lemma ex_fresh_var :
  forall vars, {v : NVar $ !LIn v vars}.
Proof.
  introv.
  exists (fresh_var vars); apply fresh_var_not_in.
Qed.

Lemma fresh_var_aux_0 :
  forall vars,
    ! LIn (nvar 0) vars
    -> issorted vars
    -> fresh_var_aux 0 vars = 0.
Proof.
  intros nin H iss; induction iss; simpl; sp.
  destruct v; allsimpl.
  allapply not_or; sp.
  destruct (lt_dec 0 n); sp.
  destruct n; allsimpl; sp;
  try omega;
  try (provefalse; apply H; auto).
Qed.

Lemma fresh_var_nvarx :
  forall vars,
    ! LIn nvarx vars
    -> fresh_var vars = nvarx.
Proof.
  unfold fresh_var; sp.
  rewrite fresh_var_aux_0; sp.
  generalize (sort_eqsetv vars); sp.
  rewrite (@eqsetv_prop NVar) in *.
  apply_in_hyp p; sp.
  apply sort_issorted.
Qed.

Lemma fresh_var_nil :
  fresh_var [] = nvarx.
Proof.
  sp.
Qed.

Hint Immediate fresh_var_nil.

Fixpoint fresh_distinct_vars (n:nat) (lv_avoid : list NVar) : (list NVar) :=
  match n with
    | O => []
    | S m =>
      let newvar := fresh_var lv_avoid in
      newvar :: (fresh_distinct_vars m (newvar :: lv_avoid))
  end.

Lemma fresh_distinct_vars_spec :
  forall n lv,
    let op := fresh_distinct_vars n lv in
    (no_repeats op) # (disjoint  op lv) # length(op)=n.
Proof. induction n as [ | n Hind]; introv. 
  simpl; split; sp. 
  allsimpl. pose proof (Hind ((fresh_var lv :: lv))) as Hind1; clear Hind.
  repnd. split; [| split]. 
  - constructor; auto. apply disjoint_sym in Hind2. apply Hind2. left. auto. 
  - apply disjoint_cons_l. split;[ | (apply fresh_var_not_in)]. 
    apply disjoint_cons_r in Hind2. repnd; auto. 
  - rewrite Hind1; reflexivity. 
Qed. 

(**another form of above which can be applied to remembered ops*)
Lemma fresh_distinct_vars_spec1 : forall n lv op, 
    (op = fresh_distinct_vars n lv) 
    -> (no_repeats op) # (disjoint  op lv) # length(op)=n.
Proof. intros. subst. apply fresh_distinct_vars_spec. 
Qed.
(* end hide *)

(** Another key requirement for a sensible formalization of variables
  is to have an unbounded supply of fresh variables. Hence,
  we prove the following lemma. 
  % The notation \coqdocnotation{\{\_:\_ $\times$ \_\}} denotes sigma types
  (\coqexternalref{sigT}
  {http://coq.inria.fr/V8.1/stdlib/Coq.Init.Specif}{\coqdocinductive{sigT}})%
  To those who are unfamiliar
  with constructive logic, the following lemma might just
  say that that for any [n] and [lv], there exists a list [lvn] 
  of length [n] of distinct variables  such that the members of [lvn]
  are disjoint from the members of [lv].

  However, because of the propositions as types principle%\footnote{we are not using Prop.}%,
  We are actually defining a function [fresh_vars] that takes a number
  [n] and a list [lv] of variables and returns a 4-tuple.
  The first member of that tuple is [lvn], a list of variables with
  the above mentioned properties. The next three members are proofs
  of the desired properties of [lvn].

 An important use [free_vars] of it will be in defining
 the substitution function.

*)
*)

Lemma fresh_vars :
  forall (n: nat) (lv : list NVar),
    {lvn : (list NVar) & no_repeats lvn # disjoint lvn lv # length lvn = n}.
Proof.
  intros. exists (freshVars n None lv []). 
  addFreshVarsSpec. tauto.
Defined.


(* begin hide *)


(*
Definition list_vars (vars : list NVar) : list nat :=
  map (fun x => match x with nvar n => n end) vars.

Definition fresh_var (vars : list NVar) : NVar :=
  let nats := list_vars vars in
  if nullb nats then nvar 0
  else let n := maxl nats in nvar (S n).

Lemma list_vars_eq :
  forall vars : list NVar,
    exists nats, vars = map nvar nats.
Proof.
  induction vars; simpl; sp.
  exists (nil : list nat); simpl; auto.
  destruct a.
  exists (n :: nats); simpl.
  rewrite <- H; auto.
 Qed.

Lemma list_vars_eq2 :
  forall nats : list nat,
    list_vars (map (fun n => nvar n) nats) = nats.
Proof.
  induction nats; simpl; sp.
  rewrite IHnats; auto.
 Qed.

Lemma fresh_var_in :
  forall vars,
    ! LIn (fresh_var vars) vars.
Proof.
  unfold fresh_var; intros.
  assert (exists nats, vars = map (fun n => nvar n) nats)
    by apply list_vars_eq; sp.
  rewrite H in H0.
  rewrite in_map_iff in H0; sp.
  rewrite list_vars_eq2 in H0.
  remember (nullb nats); symmetry in Heqb; destruct b; inversion H0; subst; GC.
  rewrite fold_assert in Heqb.
  rewrite assert_nullb in Heqb.
  rewrite null_iff_nil in Heqb; subst; allsimpl; sp.
  apply maxl_prop in H1; omega.
Qed.
*)

Definition sub_vars := @subsetb NVar _.

(* get rid of it eventually *)
Notation subsetv := subset (only parsing).

Lemma assert_sub_vars :
  forall vs1 vs2,
    assert (sub_vars vs1 vs2) <=> forall x, LIn x vs1 -> LIn x vs2.
Proof.
  sp; unfold sub_vars.
  trw assert_subsetb; sp.
Qed.

Lemma subsetv_eq {A}:
  forall (vs1 vs2 : list A),
    subsetv vs1 vs2 <=> subset vs1 vs2.
Proof.
  refl.
Qed.

Lemma subsetv_refl {A}:
  forall (vs : list A),
    subsetv vs vs.
Proof.
  sp.
Qed.

Hint Immediate subsetv_refl.

Lemma subsetv_prop {A}:
  forall (vs1 vs2 : list A),
    subsetv vs1 vs2 <=> forall x, LIn x vs1 -> LIn x vs2.
Proof.
  sp; trw subsetv_eq; unfold subset; split; sp.
Qed.

Tactic Notation "prove_subsetv" ident(h) :=
  let v := fresh "v" in
  let x := fresh "x" in
    rewrite subsetv_prop in h;
  rewrite subsetv_prop;
  intros v x;
  apply h in x.

Ltac provesv :=
  match goal with
    | [ H : subsetv ?v ?vs1 |- subsetv ?v ?vs2 ] =>
        let v := fresh "v" in
        let x := fresh "x" in
        let y := fresh "y" in
          rewrite subsetv_prop in H;
        rewrite subsetv_prop;
        intros v x;
        applydup H in x as y
  end.

Lemma subsetv_app_weak_l {A}:
  forall (vs1 vs2 vs3 : list A), subsetv vs1 vs2 -> subsetv vs1 (vs2 ++ vs3).
Proof.
  intros.
  unfold subset; sp; discover; allrw in_app_iff; sp.
Qed.

Lemma subsetv_singleton_l {A}:
  forall v vs,
    @subsetv A [v] vs <=> LIn v vs.
Proof.
  intros; unfold subset; simpl; split; sp; subst; sp.
Qed.

Lemma subsetv_singleton_r {A}:
  forall v vs, @subsetv A vs [v] <=> (forall x, LIn x vs -> x = v).
Proof.
  intros; rewrite subsetv_prop; simpl; split; sp; apply_in_hyp p; sp.
Qed.

Lemma subsetv_comm_r {A} :
  forall vs vs1 vs2,
    @subsetv A vs (vs1 ++ vs2) <=> subsetv vs (vs2 ++ vs1).
Proof.
  introv. unfold  subset.  split; introv Hyp Hin;
  apply Hyp in Hin; alltrewrite in_app_iff; sp; auto.
Qed.

Notation subsetv_flat_map := subset_flat_map.

Lemma subsetv_remove_nvars :
  forall vs1 vs2 vs3,
    subsetv (remove_nvars vs1 vs2) vs3
    <=>
    subsetv vs2 (vs3 ++ vs1).
Proof.
  sp; repeat (trw subsetv_eq); unfold remove_nvars.
  trw subset_diff; sp.
Qed.

Lemma null_remove_nvars_subsetv :
  forall vs1 vs2,
    null (remove_nvars vs1 vs2) <=> subsetv vs2 vs1.
Proof.
  unfold remove_nvars; sp.
  unfold subset.
  trw null_diff_subset; split; sp.
Qed.

Notation subsetv_cons_l := subset_cons_l (only parsing).
Notation subsetv_cons_r := subset_cons1 (only parsing).


Notation  subsetv_nil_l := subset_nil_l (only parsing).
Hint Immediate subsetv_nil_l.

Lemma subsetv_nil_l_iff {A}:
  forall s, @subsetv A [] s <=> True.
Proof.
  sp; rewrite subsetv_eq; split; sp; auto.
Qed.

Hint Rewrite (fun A => @subsetv_nil_l_iff A).

Notation  subsetv_snoc_weak := subset_snoc_r (only parsing).

Notation subsetv_app_l := subset_app (only parsing).

Lemma subsetv_app_remove_nvars_r :
  forall vs1 vs2 vs,
    subsetv vs (vs1 ++ remove_nvars vs1 vs2) <=> subsetv vs (vs1 ++ vs2).
Proof.
  sp; unfold subset; split; sp.
  apply_in_hyp p; alltrewrite in_app_iff; sp.
  alltrewrite in_remove_nvars; sp.
  apply_in_hyp p; alltrewrite in_app_iff; sp.
  alltrewrite in_remove_nvars; sp.
  destruct (in_nvar_list_dec x vs1); sp.
Qed.

Lemma subsetv_swap_r {A}:
  forall (vs1 vs2 vs : list A),
    subsetv vs (vs1 ++ vs2) <=> subsetv vs (vs2 ++ vs1).
Proof.
  sp; unfold subset; split; sp; alltrewrite in_app_iff;
  apply_in_hyp p; allrw in_app_iff; sp.
Qed.

Notation subsetv_trans := subset_trans (only parsing).


Theorem subsetv_app_trivial_l {A}:
  forall vs1 vs2, @subsetv A vs1 (vs1++vs2).
Proof.
  intros. apply subsetv_prop. intros.
  apply in_app_iff; sp.
Qed.

Theorem subsetv_app_trivial_r {A}:
  forall vs1 vs2, @subsetv A vs2 (vs1++vs2).
Proof.
  intros. apply subsetv_prop. intros.
  apply in_app_iff; sp.
Qed.

Lemma memvar_singleton_diff_r :
  forall x z, x <> z -> memvar x [z] = false.
Proof.
  sp.
  rw not_of_assert.
  rw assert_memvar; simpl; sp.
Qed.


Lemma remove_nvar_comm :
  forall vs a b,
    remove_nvar (remove_nvar vs a) b
    = remove_nvar (remove_nvar vs b) a.
Proof.
  sp.
  unfold remove_nvar.
  rewrite remove_nvars_comm; sp.
Qed.


(* Some tactics *)

Tactic Notation "simpl_vlist" :=
       repeat (progress (try (allrewrite remove_var_nil);
                         try (allapply app_eq_nil);repnd;
                         try (allrewrite app_nil_r);
                         try (allrewrite null_iff_nil))).

Lemma dmemvar :
  forall (v: NVar) lv,  (LIn v lv) + (notT (LIn v lv)).
Proof.
  apply (in_deq NVar deq_nvar).
Qed.

Theorem assert_memvar_false:
  forall (v : NVar) (vars : list NVar),
    memvar v vars = false <=> ! LIn v vars.
Proof.
  intros.
  rw <- assert_memvar.
  rw <- not_of_assert; sp.
Qed.

Lemma memvar_dmemvar : forall T v lv (ct cf:T) ,
  (if (memvar v lv)  then ct else cf) = (if (dmemvar v lv)  then ct else cf).
  intros. cases_if as  Hb; auto; cases_if as Hd ; auto; subst.
  apply assert_memvar in Hb. sp.
  apply assert_memvar_false in Hb.
  sp; try contradiction.
Qed.

Lemma eq_vars_nil {A}: forall (lv: list A), eqsetv [] lv -> lv=[].
Proof.
  introv Heq. rewrite eqsetv_prop in Heq.
  destruct lv;sp;[].
  pose proof (Heq a).
  allsimpl.
  discover; sp. tauto.
Qed.

Lemma eqsetv_nil {A}: forall (lva lvb : list A),
  lva=[] -> eq_set lva lvb -> lvb=[].
Proof.
  introv  Ha Heq.
  rw Ha in Heq.
  apply eq_vars_nil in Heq. auto.
Qed.

Ltac inj0_step :=
  match goal with
    | [ H : (_, _) = (_, _)     |- _ ] => apply pair_inj in H; repd; subst; GC
    | [ H : S _ = S _           |- _ ] => apply S_inj    in H; repd; subst; GC
    | [ H : S _ < S _           |- _ ] => apply S_lt_inj in H; repd; subst; GC
    | [ H : snoc _ _ = snoc _ _ |- _ ] => apply snoc_inj in H; repd; subst; GC
  end.

Ltac inj0 := repeat inj0_step.

(*
Ltac inj :=
  repeat match goal with
             [ H : _ |- _ ] =>
             (apply pair_inj in H
              || apply S_inj in H
              || apply S_lt_inj in H
              || apply snoc_inj in H);
               repd; subst; GC
         end; try (complete sp).
*)

Ltac inj := inj0; try (complete auto); try (complete sp).

Ltac cpx :=
  repeat match goal with
           (* false hypothesis *)
           | [ H : [] = snoc _ _ |- _ ] =>
             complete (apply nil_snoc_false in H; sp)
           | [ H : snoc _ _ = [] |- _ ] =>
             complete (symmetry in H; apply nil_snoc_false in H; sp)

           (* simplifications *)
           | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; GC

           | [ H : 0 = length _ |- _ ] =>
             symmetry in H; trw_h length0 H; subst
           | [ H : length _ = 0 |- _ ] =>
             trw_h length0 H; subst

           | [ H : 1 = length _ |- _ ] =>
             symmetry in H; trw_h length1 H; exrepd; subst
           | [ H : length _ = 1 |- _ ] =>
             trw_h length1 H; exrepd; subst

           | [ H : [_] = snoc _ _ |- _ ] =>
             symmetry in H; trw_h snoc1 H; repd; subst
           | [ H : snoc _ _ = [_] |- _ ] =>
             trw_h snoc1 H; repd; subst

           | [ H : context[length (snoc _ _)] |- _ ] =>
             rewrite length_snoc in H
         end;
  inj;
  try (complete (allsimpl; sp)).

Lemma eqsetv_remove_nvars :
  forall la lb ra rb,
    eqsetv la lb
    -> eqsetv ra rb
    -> eqsetv (remove_nvars la ra) (remove_nvars lb rb).
Proof.
  unfold eq_set, subset. setoid_rewrite in_remove_nvars.
  firstorder.
Qed.

Lemma eqsetv_app {A}:
  forall (la lb ra rb : list A),
    eqsetv la lb
    -> eqsetv ra rb
    -> eqsetv (app la ra) (app lb rb).
Proof.
  introv Ha Hb.
  unfold eq_set, subset. setoid_rewrite in_app_iff.
  firstorder.
Qed.

Hint Resolve eqsetv_trans eq_vars_sym eqsetv_refl eqsetv_remove_nvar eqsetv_remove_nvars eqsetv_app: eqsetv.

Definition dec_disjointv := dec_disjoint deq_nvar.

Lemma disjoint_remove_nvars: forall lva lvb,
  disjoint (remove_nvars lva lvb) lva.
Proof.
  introv Hin Hc.
  apply in_remove_nvars in Hin.
  sp.
Qed.

Lemma disjoint_remove_nvars2: forall lva lvb lvc,
  disjoint lvb lva 
  -> disjoint (remove_nvars lvc lvb) lva.
Proof.
  introv Hin Hc.
  apply in_remove_nvars in Hc.
  exrepnd.
  introv Hinc. disjoint_lin_contra.
Qed.

Ltac sp3 :=
  (repeat match goal with
  | [ H: _ <=> _ |- _ ] => destruct H end); spc.


Lemma subsetv_cons_r_weak_if_not_in {A}:
  forall vs1 v vs2,
    @subsetv A vs1 (v :: vs2)
    -> !LIn v vs1
    -> subsetv vs1 vs2.
Proof.
  introv sv ni. unfold subset.
  introv i.
  applydup sv in i as j.
  allsimpl; sp; subst; sp.
Qed.


Lemma eq_var_iff :
  forall v : NVar, v = v <=> True.
Proof. sp. Qed.

Lemma subsetv_eqsetv {A}:
  forall s1 s2 s3,
    subsetv s1 s2 -> eqsetv s1 s3 -> @subsetv A s3 s2.
Proof.
  introv s e.
  unfold eq_set in *.
  unfold subset in *.
  firstorder.
Qed.

Lemma subsetv_not_in {A}:
  forall vs1 vs2 v, @subsetv A vs2 vs1 -> !LIn v vs1 -> !LIn v vs2.
Proof.
  introv sv ni1 ni2.
  rewrite subsetv_prop in sv.
  discover; sp.
Qed.

Lemma not_over_not_lin_nvar :
  forall (v : NVar) l t,
    !(LIn v l # t) <=> (!LIn v l [+] !t).
Proof.
  introv; split; intro k; repnd; sp.
  generalize (in_deq NVar deq_nvar v l); intro o; sp;
  (* part below not needed for univ := prop *)
  right; intro j;
  apply k; sp.
Qed.



Definition remove_nvars_nop :=
(fun l1 l2 => proj1 (remove_nvars_unchanged l1 l2)).

(* Move *)
Definition listHead {A} (l:list A)(p: 0<length l) : A.
Proof.
  destruct l; simpl in p.
- apply False_rect. inversion p.
- exact a. 
Defined.


Definition listHeadIn {A} (l:list A)(p: 0<length l) : LIn (listHead l p) l.
Proof.
  unfold listHead.
  destruct l; simpl; auto.
  inversion p.
Qed.


Definition fresh_var (lx : list NVar) : NVar.
Proof.
  pose proof (freshCorrect 1 None lx []) as Hfr. simpl in Hfr.
  apply  proj1, proj2, proj2 in Hfr.
  apply (listHead (freshVars 1 None lx [])).
  rewrite Hfr. constructor.
Defined.

Lemma fresh_var_not_in :
  forall vars,
    ! LIn (fresh_var vars) vars.
Proof.
  intros ?.
  unfold fresh_var.
  addFreshVarsSpec.
  repnd.
  apply HfreshVars2.
  apply listHeadIn.
Qed.

Lemma memvar_fresh_var : forall x (lx : list NVar),
beq_var x (fresh_var (x::lx)) = false.
Proof.
  intros.
  pose proof (fresh_var_not_in (x::lx)) as Hf.
  apply not_eq_beq_var_false.
  simpl in *. tauto.
Qed.

Definition nvarx : NVar := fresh_var [].
Definition nvary : NVar := fresh_var [nvarx].
Definition nvarz : NVar := fresh_var [nvarx, nvary].

Lemma fresh_var_not_eq : forall lv v, 
  LIn v lv
  -> ~(v = (fresh_var lv)).
Proof.
  intros.
  pose proof (fresh_var_not_in lv).
  intros Hc.
  subst. tauto. 
Qed.

Lemma nvarx_nvary : nvarx <> nvary.
Proof using.
  allunfold nvary.
  apply fresh_var_not_eq.
  sp.
Qed.

(* Move, try to delete*)
Lemma beq_var_true :
  forall (i1 i2 : NVar),
    true = beq_var i1 i2 -> i1 = i2.
Proof.
  intros ? ? Hs. unfold  beq_var in Hs.
  symmetry in Hs. apply DecidableClass.Decidable_sound in Hs.
  auto.
Qed.



(* Move, try to delete*)
Lemma beq_var_false :
  forall (i1 i2 : NVar),
    false = beq_var i1 i2 -> i1 <> i2.
Proof using.
  sp. symmetry in H3. 
  apply DecidableClass.Decidable_complete_alt in H3.
  auto.
Qed.

Theorem beq_var_false_not_eq : forall i1 i2,
  beq_var i1 i2 = false -> i1 <> i2.
Proof using.
 intros. symmetry in H3.
 apply beq_var_false. auto.
Qed.

Definition varsOfClass (lv:list NVar) (vc : VClass) : Prop :=
  lforall (fun v => varClass v = vc) lv.

Lemma varsOfClassFreshDisjoint : forall (vca vcb : VClass),
vca <> vcb
-> forall lv, 
    varsOfClass lv vca
   -> forall n lva lvs, disjoint (freshVars n (Some vcb) lva lvs) lv.
Proof.
  intros ? ? Hn ? Hvc ? ? ?.
  addFreshVarsSpec.
  repnd.
  intros ? Hin.
  eapply HfreshVars in Hin;[| refl].
  intro Hc.
  apply Hvc in Hc.
  congruence.
Qed.


Definition freshReplacements (blv lva : list NVar) :=
  (freshVars (length blv) (option_map varClass (head blv)) lva blv).

Lemma freshVars0 : forall vc lva lvs, freshVars 0 vc lva lvs = [].
Proof.
  intros.
  addFreshVarsSpec.
  repnd.
  destruct (freshVars 0 vc lva lvs);[| inverts HfreshVars0].
  refl.
Qed.

(* for auto rewriting *)
Lemma freshVarsLen : forall n vc lva lvs, length (freshVars n vc lva lvs) = n.
Proof.
  intros.
  addFreshVarsSpec.
  tauto.
Qed.

Lemma freshRepsLen : forall lva lvs, length (freshReplacements lvs lva) = length lvs.
Proof.
  intros.
  apply freshVarsLen.
Qed.


Lemma  varsOfClassApp : forall (lv1 lv2 :list NVar) (vc : VClass),
varsOfClass (lv1++lv2) vc
<-> ((varsOfClass lv1 vc) # (varsOfClass lv2 vc)).
Proof using.
  clear H1 H2.
  unfold varsOfClass, lforall.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma  varsOfClassNil : forall (vc : VClass),
varsOfClass [] vc.
Proof using.
  unfold varsOfClass, lforall. simpl. tauto.
Qed.

Lemma freshReplacementsSameClass : forall (blv lva : list NVar) vc, 
  varsOfClass blv vc -> varsOfClass (freshReplacements blv lva) vc.
Proof using H H2.
  intros ? ? ? Hvc.
  unfold freshReplacements.
  addFreshVarsSpec.
  repnd.
  destruct blv as [|v blv]; simpl in *;[rewrite freshVars0; apply varsOfClassNil |].
  simpl.
  intros ? Hin. apply HfreshVars; eauto.
  f_equal. apply Hvc.
  simpl. auto.
Qed.

Require Import Morphisms.
Global Instance varsOfClassProper : Proper (eq_set ==> eq ==> iff ) (varsOfClass).
Proof using.
  intros ? ? Heq ? ? ?. unfold varsOfClass. rewrite Heq. subst. refl.
Qed.

Hint Rewrite @remove_nvars_nil_l @remove_nvars_nil_r : SquiggleEq.

Lemma remove_nvars_cons_r2:
  forall  (l : list NVar) (v : NVar) (vars : list NVar),
  remove_nvars l (v :: vars) = (remove_nvars l [v]) ++ (remove_nvars l vars).
Proof using.
  intros. rewrite remove_nvars_cons_r.
  rewrite cons_as_app.
  rewrite remove_nvars_cons_r.
  cases_if; simpl; autorewrite with SquiggleEq; auto.
Qed.

(* for rewriting selectively *)
Lemma remove_nvars_nops
     : forall l1 l2 :  NVar, disjoint [l2] [l1] -> remove_nvars [l1] [l2] = [l2].
Proof using.
  intros. apply remove_nvars_nop. assumption.
Qed.

Lemma varsOfClassSubset : forall  (la lb : list NVar), 
  subset la lb -> forall c, varsOfClass lb c -> varsOfClass la c.
Proof using.
  intros ? ? Hs ?.
  apply lforall_subset.
  assumption.
Qed.

Hint Rewrite @memvar_singleton @memvar_fresh_var : SquiggleEq.

Hint Rewrite <- @beq_var_refl : SquiggleEq.


Lemma remove_nvars_cons_r_same:
  forall  (v : NVar) (vars : list NVar),
  remove_nvars [v] (v :: vars) =
   remove_nvars [v] vars.
Proof using.
  intros.
  rewrite remove_nvars_cons_r.
  autorewrite with SquiggleEq.
  refl.
Qed.

Lemma memvar_nil_r :  forall a, memvar a [] = false.
Proof.
  intros.
  apply assert_memvar_false.
  auto.
Qed.

Definition freshVar  (o : VClass) (lx : list NVar) : NVar.
Proof.
  pose proof (freshCorrect 1 (Some o) lx nil) as Hfr. simpl in Hfr.
  apply  proj1, proj2, proj2 in Hfr.
  apply (listHead (freshVars 1 (Some o) lx nil)).
  rewrite Hfr. constructor.
Defined.


End Vars.



(* this is closer to the way things worked, and hence useful in reviving old proofs*)
Ltac addFreshVarsSpec2 vn pp :=
unfold freshReplacements in *;
let tac n vc lva lvs :=
  (pose proof (freshCorrect n vc lva lvs) as pp; simpl in pp;
  apply proj1 in pp;
  remember (freshVars n vc lva lvs) as vn) in
match goal with
[ |- context [freshVars ?n ?vc ?lva ?lvs]] => tac n vc lva lvs
|[ H: context [freshVars ?n ?vc ?lva ?lvs] |- _] => tac n vc lva lvs
end.



Ltac remove_nvars_r_simpl :=
repeat match goal with
[ |- context[remove_nvars _ (?h::?tl)]] =>
    notNil tl; setoid_rewrite (@remove_nvars_cons_r2 _ _ _ h tl)  
|[ H: context[remove_nvars _ (?h::?tl)] |- _ ] =>
    notNil tl; setoid_rewrite (@remove_nvars_cons_r2 _ _ _ h tl) in H  
end.

Hint Rewrite <- @beq_var_refl : SquiggleEq.

Hint Rewrite @memvar_singleton @memvar_fresh_var : SquiggleEq.

(* Remove : neve add anything to core DB *)
Hint Immediate @deq_nvar.
Hint Rewrite @remove_nvars_nil_l @remove_nvars_nil_r : SquiggleEq.

(* Hint Constructors issorted. *)
Hint Immediate eqsetv_refl.
Hint Immediate subsetv_refl.
(* Hint Immediate fresh_var_nil. *)
Hint Immediate subset_nil_l.
Hint Rewrite  @subsetv_nil_l_iff.
Hint Resolve eqsetv_trans eq_vars_sym eqsetv_refl eqsetv_remove_nvar eqsetv_remove_nvars eqsetv_app: eqsetv.

Tactic Notation "prove_subsetv" ident(h) :=
  let v := fresh "v" in
  let x := fresh "x" in
    rewrite subsetv_prop in h;
  rewrite subsetv_prop;
  intros v x;
  apply h in x.
Ltac provesv :=
  match goal with
    | [ H : subset ?v ?vs1 |- subset ?v ?vs2 ] =>
        let v := fresh "v" in
        let x := fresh "x" in
        let y := fresh "y" in
          rewrite subsetv_prop in H;
        rewrite subsetv_prop;
        intros v x;
        applydup H in x as y
  end.


Ltac inj0_step :=
  match goal with
    | [ H : (_, _) = (_, _)     |- _ ] => apply pair_inj in H; repd; subst; GC
    | [ H : S _ = S _           |- _ ] => apply S_inj    in H; repd; subst; GC
    | [ H : S _ < S _           |- _ ] => apply S_lt_inj in H; repd; subst; GC
    | [ H : snoc _ _ = snoc _ _ |- _ ] => apply snoc_inj in H; repd; subst; GC
  end.

Ltac inj0 := repeat inj0_step.

(*
Ltac inj :=
  repeat match goal with
             [ H : _ |- _ ] =>
             (apply pair_inj in H
              || apply S_inj in H
              || apply S_lt_inj in H
              || apply snoc_inj in H);
               repd; subst; GC
         end; try (complete sp).
*)

Ltac inj := inj0; try (complete auto); try (complete sp).

Ltac cpx :=
  repeat match goal with
           (* false hypothesis *)
           | [ H : [] = snoc _ _ |- _ ] =>
             complete (apply nil_snoc_false in H; sp)
           | [ H : snoc _ _ = [] |- _ ] =>
             complete (symmetry in H; apply nil_snoc_false in H; sp)

           (* simplifications *)
           | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; GC

           | [ H : 0 = length _ |- _ ] =>
             symmetry in H; trw_h length0 H; subst
           | [ H : length _ = 0 |- _ ] =>
             trw_h length0 H; subst

           | [ H : 1 = length _ |- _ ] =>
             symmetry in H; trw_h length1 H; exrepd; subst
           | [ H : length _ = 1 |- _ ] =>
             trw_h length1 H; exrepd; subst

           | [ H : [_] = snoc _ _ |- _ ] =>
             symmetry in H; trw_h snoc1 H; repd; subst
           | [ H : snoc _ _ = [_] |- _ ] =>
             trw_h snoc1 H; repd; subst

           | [ H : context[length (snoc _ _)] |- _ ] =>
             rewrite length_snoc in H
         end;
  inj;
  try (complete (allsimpl; sp)).
  
  Ltac sp3 :=
  (repeat match goal with
  | [ H: _ <=> _ |- _ ] => destruct H end); spc. 


Hint Immediate nvarx_nvary : slow.

Hint Rewrite (@freshVars0) : SquiggleEq.

Hint Immediate varsOfClassNil : SquiggleEq.


Hint Rewrite (@freshVarsLen) : SquiggleEq.

Hint Rewrite (@freshRepsLen) : SquiggleEq.

Hint Rewrite (fun T D l1 l2 => @remove_nvars_app_r T D l1 l1 l2) : SquiggleEq.
Hint Rewrite @remove_nvars_app_r : SquiggleEq2.

Hint Rewrite @remove_nvars_cons_r_same @remove_nvars_eq: SquiggleEq.


Tactic Notation "simpl_vlist" :=
       repeat (progress (try (allrewrite remove_var_nil);
                         try (allapply app_eq_nil);repnd;
                         try (allrewrite app_nil_r);
                         try (allrewrite null_iff_nil))).
                         
Notation beq_var_eq := beq_var_true.

Hint Rewrite remove_nvars_cons_r_same : SquiggleEq.

Hint Resolve varsOfClassSubset : subset.


Section Vars2Class.
Context {NVar : Type} `{VarType NVar bool}.


Lemma varsOfClassFreshDisjointBool : forall n lva lvs lv, 
    varsOfClass lv true
    -> disjoint (freshVars n (Some false) lva lvs) lv.
Proof.
  intros. eapply varsOfClassFreshDisjoint; eauto.
  discriminate.
Qed.

Lemma beq_deq : forall T (v1 v2 : NVar) (ct cf:T) ,
  (if (beq_var v1 v2)  then ct else cf) = (if (decideP (v1=v2))  then ct else cf).
Proof.
  intros.
  Local Transparent beq_var.
   apply decide_decideP.
  Local Opaque beq_var.
Qed.

End Vars2Class.

  Hint Resolve @varsOfClassSubset : subset.

Hint Rewrite @memvar_nil_r : SquiggleEq.


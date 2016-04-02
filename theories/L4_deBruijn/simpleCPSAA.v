
(** coqide -R /path/to/SquiggleLazyEq SquiggleLazyEq 
https://github.com/aa755/SquiggleLazyEq (branch ssubst)

*)

(** CPS conversion for a language with nominal style variable bindings.
We use the 
SquiggleLazyEq library for generically defined substitution, 
alpha equality (and soon, a contextual computational equivalence)
and several proofs about them.
*)

Require Import Arith BinNat String List Omega 
  Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.


Require Import Morphisms.
Lemma N_plus_minus:
  forall n:N, n > 0 -> (n - 1 + 1) = (n + 1 - 1).
Proof using.
  intros.
  induction n using N.peano_ind; intros; lia.
Qed.

Lemma N_plus_minus_eq:
  forall n:N, (n + 1 - 1) = n.
Proof using.
  induction n using N.peano_ind; intros; lia.
Qed.

Lemma N_i_plus_1:
  forall i:N, (i + 1) = (1 + i).
  induction i using N.peano_ind; intros; lia.
Qed.
Lemma N_i11:
  forall i, (i + 1 + 1) = (1 + i + 1).
Proof using.
  induction i using N.peano_ind; intros; lia.
Qed.

(* MathClasses or Extlib may habe a much richer theory and implementation *)
Require Import Coq.Classes.DecidableClass.
Require Import SquiggleLazyEq.alphaeq.
Require Import SquiggleLazyEq.UsefulTypes.

Instance NEqDec : Deq N.
Proof using.
  intros x y. exists (N.eqb x y). apply N.eqb_eq.
Defined.


(*
Instance NatEq : Eq nat := { eq_dec := eq_nat_dec }.

Definition lt_dec (x y:N) : {x < y} + { x >= y}.
  refine (match x <? y as z return (x <? y) = z -> {x < y} + {x >= y} with
            | true => fun H => left _ (proj1 (N.ltb_lt x y) H)
            | false => fun H => right _
          end eq_refl).
  intro. unfold N.ltb in *. rewrite H0 in H. discriminate.
Defined.
*)

(**************************)
(** * Source Expressions. *)
(**************************)


Definition dcon := N.


Section VarsOf2Class.

Context {NVar} {deqnvar : Deq NVar} {vartype: @VarType NVar bool (* 2 species of vars*) _}.

Notation USERVAR := true (only parsing).
Notation CPSVAR := false (only parsing).

Definition branch {s} : Type := (dcon * (@BTerm NVar s))%type.

(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Definition find_branch {s} (d:N) (m:nat) (matcht :list (@branch s)) : 
    option BTerm 
  := 
  let obr :=
  find 
    (fun a : (@branch s) => decide ((d,m) = (fst a, num_bvars (snd a)))) matcht in
  option_map snd obr.

Inductive CoqCanonicalOp : Set :=
 | NLambda
 | NFix (nMut : nat) (** number of functions that are mutually defined*)
 | NDCon (dc : dcon) (nargs : nat).

Definition CoqOpBindingsCan (c : CoqCanonicalOp) 
    : list nat :=
  match c with
  | NLambda    => [1]
  | NFix nMut => repeat nMut 1
  | NDCon _ nargs    => repeat nargs 0
  end.

Inductive CoqNonCanonicalOp : Set :=
 | NApply
 | NProj (selector :nat) (** which one to project out*)
 | NLet
 | NMatch (dconAndNumArgs : list (dcon * nat))
 (** each member of the list corresponds to a branch. 
    it says how many variables are bound in that branch*) .

Definition CoqOpBindingsNCan (nc : CoqNonCanonicalOp) : list nat :=
  match nc with
  | NApply     => [0,0]
  | NProj _ => [0]
  | NLet => [0,1]
  | NMatch numargsInBranches => 0::(List.map snd numargsInBranches)
  end.

Definition decc: forall x y : CoqCanonicalOp,
{x = y} + {x <> y}.
Proof using.
   repeat(decide equality).
Defined.

Definition decnc:
forall
  x y : CoqNonCanonicalOp, {x = y} + {x <> y}.
Proof using.
  repeat(decide equality).
Defined.
Require Import SquiggleLazyEq.alphaeq.



Definition CoqL4GenericTermSig : GenericTermSig :=
{| 
  CanonicalOp := CoqCanonicalOp;
  NonCanonicalOp := CoqNonCanonicalOp;
  OpBindingsCan := CoqOpBindingsCan;
  OpBindingsNCan := CoqOpBindingsNCan;
  canonical_dec := decc;
  ncanonical_dec := decnc
|}.


Notation BTerm := (@BTerm NVar CoqL4GenericTermSig).
Notation NTerm := (@NTerm NVar CoqL4GenericTermSig).
Notation oterm := (@oterm NVar CoqL4GenericTermSig).
Notation Can := (@Can CoqL4GenericTermSig).
Notation NCan := (@NCan CoqL4GenericTermSig).
Definition Lam_e (v : NVar) (b : NTerm) : NTerm :=
  oterm (Can NLambda) [bterm [v] b].

Definition Let_e (v : NVar) (e1 e2 : NTerm) : NTerm :=
  oterm (NCan NLet) [(bterm [] e1);(bterm [v] e2)].

Definition App_e (f a : NTerm) :=
  oterm (NCan NApply) [bterm [] f , bterm [] a].

Definition Con_e (dc : dcon) (args : list NTerm) : NTerm :=
  oterm (Can (NDCon dc (length args))) (List.map (bterm []) args).

Definition Proj_e (arg : NTerm) (selector : nat)  : NTerm :=
  oterm (NCan (NProj selector)) [bterm [] arg].

(** fix (\xf. (\x..,,)) *)
Definition Fix_e (xf : NVar) (args : list NTerm) : NTerm :=
  oterm (Can (NFix (length args))) (List.map (bterm [xf]) args).

Definition Match_e (discriminee : NTerm) (brs : list branch) : NTerm :=
  oterm (NCan (NMatch (List.map (fun b => (fst b, num_bvars (snd b))) brs))) 
        ((bterm [] discriminee)::(List.map snd brs)).

(* A few notes on the source:  

   [Let_e e1 [bterm [v] e2] ] corresponds to (let v := e1 in e2)

   [Fix_e xf [e1;e2;...;en]] produces an n-tuple of functions.  Each expression
   is treated as binding xf, which is the n-tuple of functions.

   So this is similar to saying something like:

    let rec f1 = \x1.e1
        and f2 = \x2.e2
        ...
        and fn = \xn.en
    in
      (f1,f2,...,fn)

   When [e] evaluates to [Fix_e xf [e1;e2;...;en]], then [Proj_e e i] evaluates
   to [ei{xf := Fix_e[e1;e2;...;en]}].  That is, we unwind the recursion when
   you project something out of the tuple.

   For [Match_e] each [branch] binds [n] variables, corresponding to the
   arguments to the data constructor.  
*)


(** A tactic for simplifying numeric tests. *)
Ltac if_split := 
  match goal with
    | [ |- context[if ?e then _ else _] ] => destruct e ; simpl ; try lia ; auto ; try subst
  end.

Ltac if_splitH H := 
  match type of H with
    context[if ?e then _ else _] => destruct e
  end.


Class Substitute (v:Type) (t:Type) := { substitute : v -> NVar -> t -> t }.


(** Notation for substitution. *)
Notation "M { j := N }" := (substitute N j M) (at level 10, right associativity).

Instance ExpSubstitute : Substitute NTerm NTerm :=
  { substitute := fun rep x t => subst t x rep}.




(** Big-step evaluation for [exp]. *)
Inductive eval : NTerm -> NTerm -> Prop :=
(** note that e could be an ill-formed term *)
| eval_Lam_e : forall (x: NVar) e, eval (Lam_e x e) (Lam_e x e)
| eval_App_e : forall e1 e1' x e2 v2 v,
                 eval e1 (Lam_e x e1') ->
                 eval e2 v2 ->
                 eval (e1'{x := v2}) v -> 
                 eval (App_e e1 e2) v
(**AA: do we need to go inside constructors for weak-head evaluation? *)
| eval_Con_e : forall d es vs, 
    length es = length vs
    -> (forall e v, (LIn (e,v) (combine es vs)) -> eval e v)
    -> eval (Con_e d es) (Con_e d vs)
| eval_Let_e : forall (x:NVar) e1 v1 e2 v2,
                 eval e1 v1 ->
                 eval (e2{x:=v1}) v2 ->
                 eval (Let_e x e1 e2) v2
| eval_Match_e : forall e bs d vs e' v,
                   eval e (Con_e d vs) ->
                   find_branch d ((List.length vs)) bs = Some e' ->
                   eval (apply_bterm e' vs) v ->
                   eval (Match_e e bs) v
| eval_Fix_e : forall xf es, eval (Fix_e xf es) (Fix_e xf es)
| eval_Proj_e : forall xf e es n xl bl,
                  eval e (Fix_e xf es) ->
                  select n es = Some (Lam_e xl bl) ->
                  eval (Proj_e e n) ((Lam_e xl bl){xf:=Fix_e xf es}).

(** will be used in [eval_reduces_fvars] and cps_cvt_corr *)
Lemma subset_step_app: forall x e1' v2,
  subset (free_vars (e1' {x := v2})) (free_vars (App_e (Lam_e x e1') v2)).
Proof using.
  intros. simpl. autorewrite with list core. unfold subst.
  rewrite eqsetv_free_vars_disjoint.
  intros ? Hc.
  rewrite in_app_iff in *.
  simpl in Hc.
  dorn Hc;[left; firstorder|right].
  rewrite memvar_dmemvar in Hc.
  if_splitH Hc; simpl in Hc; autorewrite with list in *;firstorder.
Qed.

Local Opaque ssubst.
Lemma eval_reduces_fvars :
  forall e v, eval e v ->  subset (free_vars v) (free_vars e).
Proof using.
  intros ? ? He. unfold closed. induction He; try auto;
  simpl in *;autorewrite with core list in *.
  (**Apply case*)
  -
    unfold subset.
    pose proof (subset_step_app x e1' v2) as H.
    pose proof (subset_trans _ _ _ _ IHHe3 H).
    clear H IHHe3. eapply subset_trans; eauto.
    simpl. autorewrite with list core.
    apply subsetvAppLR; firstorder.

  - rename H into Hl. rename H0 into H1i. rename H1 into H2i.
    change es  with (fst (es, vs)).
    change vs  with (snd (es, vs)) at 1.
    apply combine_split in Hl.
    rewrite <- Hl.
    rewrite fst_split_as_map, snd_split_as_map.
    repeat rewrite flat_map_map.
    repeat rw flat_map_empty.
    unfold subset. setoid_rewrite in_flat_map. 
    unfold compose. simpl.
    intros ? Hin. exrepnd. eexists. split;[apply Hin1|].
    autorewrite with list core in *.
    firstorder.

  (**Let case; same as the Apply case*)
  - simpl in IHHe2. intros ? Hc.
    apply_clear IHHe2 in Hc. unfold subst in Hc.
    rewrite eqsetv_free_vars_disjoint in Hc.
    simpl in Hc.
    rewrite in_app_iff in *.
    apply or_comm.
    simpl in Hc.
    dorn Hc;[left; firstorder|right].
    rewrite memvar_dmemvar in Hc.
    if_splitH Hc; simpl in Hc; autorewrite with list in *;firstorder.

(* match case *)
  - intros ? Hf. apply_clear IHHe2 in Hf.
    destruct e' as [lv nt].
    unfold apply_bterm in Hf. simpl in Hf.
    rewrite eqsetv_free_vars_disjoint in Hf.
    revert H. unfold find_branch. destFind; intro Hdf; [| discriminate].
    repnd.
    destruct bss as [xxx brbt]. simpl in Hdf. subst.
    simpl in Heqsnl.
    apply andb_true_iff, proj2,beq_nat_true in Heqsnl.
    unfold compose in Heqsnl0. simpl in *. destruct brbt as [lvv ntt].
    inverts Hdf. unfold num_bvars in Heqsnl. simpl in Heqsnl.
    rewrite dom_sub_combine in Hf;[| auto]. clear Heqsn.
    rewrite in_app_iff in *.
    apply or_comm.
    dorn Hf;[left|right].
    + apply in_flat_map.
      exists (bterm lv nt). repnd. split;[| assumption].
      apply in_map_iff. eexists; eauto.
    + apply IHHe1. apply in_sub_free_vars in Hf. exrepnd.
      apply in_flat_map. exists (bterm [] t).
      split;[| assumption]. apply in_map.
      apply in_sub_keep_first in Hf0. apply proj1 in Hf0.
      apply sub_find_some in Hf0. apply in_combine_r in Hf0.
      assumption.

- intros ? Hf. unfold subst.
  apply_clear IHHe. unfold subst in Hf.
  rewrite eqsetv_free_vars_disjoint in Hf.
  rewrite flat_map_map. simpl in Hf.
  rewrite in_app_iff in *.
  dorn Hf. 
  + unfold compose. repnd.
    apply select_in in H. apply in_flat_map. eexists; split; eauto.
  + rewrite memvar_dmemvar in Hf. 
    if_splitH Hf; simpl in Hf; autorewrite with list in *;[|firstorder].
    rewrite flat_map_map in Hf. assumption.
Qed.

(** Evaluation preserves closedness.*)
Corollary eval_preserves_closed :
  forall e v, eval e v ->  closed e -> closed v.
Proof using.
  intros ? ?  He. unfold closed. intro Hc.
  apply eval_reduces_fvars  in He.
  rewrite Hc in He.
  apply subsetv_nil_r in He. assumption.
Qed.

(** Characterize values *)
Inductive is_value : NTerm -> Prop :=
| var_is_value : forall i, is_value (vterm i)
| lam_is_value : forall x e, is_value (Lam_e x e)
| con_is_value : forall d es, (forall s, In s es -> is_value s) -> is_value (Con_e d es)
(** Unlike in Nuprl, fix is a value.*)
| fix_is_value : forall xf es, is_value (Fix_e xf es).

(** Show that evaluation always yields a value. *)
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v).
Proof using.
  intros ? ? He ; induction He ; simpl ; intros ; 
  auto ; try constructor ; auto;[|].
  - change vs  with (snd (es, vs)).
    rename H into Hl.
    apply combine_split in Hl.
    rewrite <- Hl.
    rewrite  snd_split_as_map.
    intros ? Hin.
    apply in_map_iff in Hin.
    exrepnd. simpl in *. subst.
    eauto.
  - unfold subst.
    Local Transparent ssubst. unfold Lam_e. unfold ssubst. simpl.
    cases_ifd Hd; simpl;[constructor|].
    unfold freshReplacements. simpl in *.
    addFreshVarsSpec2 lvn Hfr.
    repnd. simpl in *. dlist_len_name lvn a. simpl. constructor. 
Qed.

Ltac ntwfauto := 
simpl substitute in *;alphaeq.ntwfauto.

Lemma eval_preseves_wf :
  forall e v, eval e v ->  nt_wf e -> nt_wf v.
Proof using.
  intros ? ? He. induction He; intro Hn; try auto.
- ntwfauto. apply IHHe3. ntwfauto.
- ntwfauto;[|simpl].
  + rewrite list_nil_btwf.
    rewrite list_nil_btwf in Hntwf. revert Hntwf.
    change vs  with (snd (es, vs)).
    change es  with (fst (es, vs)) at 1.
    rename H into Hl.
    apply combine_split in Hl.
    rewrite <- Hl.
    rewrite  snd_split_as_map.
    rewrite  fst_split_as_map.
    intros ? ? Hin1.
    apply in_map_iff in Hin1. exrepnd.
    simpl in *. subst.
    eapply H1;eauto.
    apply Hntwf. apply in_map_iff; eauto.
  + rewrite map_map. unfold compose, num_bvars. simpl.
    apply repeat_map_len.
- ntwfauto. apply IHHe2. ntwfauto.
- ntwfauto. apply IHHe2. destruct e'. simpl in *.
  ntwfauto.
  + rewrite list_nil_btwf in Hntwf0.
    apply in_combine_r in Hsub. auto.
  + revert H. unfold find_branch. destFind;intros Hyp; [| discriminate].
    simpl in *. inverts Hyp.
    repnd. rewrite <- (bt_wf_iff l), <- H0.
    apply Hntwf. apply in_map. auto.
- ntwfauto. 
  subst.
  apply select_in in H.
  apply (in_map (bterm [xf])) in H.
  apply Hntwf in H.
  ntwfauto.
Qed.

Ltac rwsimpl He1 :=
  repeat progress (autorewrite with list core SquiggleLazyEq in He1; simpl in He1).

Ltac rwsimplAll :=
  repeat progress (autorewrite with list core SquiggleLazyEq in *; simpl in *).

Ltac rwsimplC :=
  repeat progress (autorewrite with list core SquiggleLazyEq; simpl).

Hint Rewrite @flat_map_bterm_nil_allvars : SquiggleLazyEq.

(* c := USERVAR in the intended use case. But this property holds more generally *)
Lemma eval_preseves_varclass :
  forall c e v, 
    eval e v 
    ->  varsOfClass (all_vars e) c 
    -> varsOfClass (all_vars v) c.
Proof using.
  intros ? ? ? He. induction He; intro Hn; try auto.
(* beta reduction *)
- apply_clear IHHe3.
  apply ssubst_allvars_varclass_nb.
  unfold App_e, Lam_e in *.
  rwsimplAll. tauto.

(* reduction inside constructors *)
- unfold Con_e in *. rwsimplAll.
  revert Hn.
  change es  with (fst (es, vs)).
  change vs  with (snd (es, vs)) at 2.
  rename H into Hl.
  apply combine_split in Hl.
  rewrite <- Hl.
  rewrite fst_split_as_map,snd_split_as_map.
  repeat rewrite flat_map_map.
  unfold compose. simpl.
  unfold varsOfClass, lforall.
  setoid_rewrite in_flat_map.
  intros Hyp ? Hin.
  exrepnd.
  rwsimpl Hin0.
  eapply H1; eauto.
  intros ? Hin.
  eapply Hyp.
  eexists; eauto.

(* Let reduction, same proof as beta reduction *)
- unfold Let_e in *.
  apply_clear IHHe2.
  apply ssubst_allvars_varclass_nb.
  rwsimplAll. tauto.

(* pattern matching (zeta?) reduction *)
- unfold Match_e, Con_e in *. clear He1 He2.
  apply_clear IHHe2.
  apply ssubst_allvars_varclass_nb.
  rwsimplAll.
  revert H.
  unfold find_branch. destFind; intros Hyp; [| discriminate].
  repnd.
  simpl in *. inverts Hyp.
  destruct bss as [cc btt].
  destruct btt as [lv nt].
  simpl in *.
  apply andb_true_iff, proj2,beq_nat_true in Heqsnl.
  unfold num_bvars in Heqsnl. simpl in *.
  rewrite dom_range_combine;[| auto].
  split;[|tauto].
  eapply varsOfClassSubset;[| apply Hn].
  intros ? Hin.
  rewrite flat_map_map.
  apply in_flat_map. eexists.
  split;[apply Heqsnl0|].
  unfold compose.
  simpl.
  rewrite allvars_bterm.
  apply in_app_iff. tauto.

- remember (Lam_e xl bl) as r. clear Heqr.
  unfold Fix_e, Proj_e in *.
  apply ssubst_allvars_varclass_nb.
  apply select_in in H.
  rwsimplAll.
  split;[| tauto].
  repnd.
  eapply varsOfClassSubset;[| apply IHHe; auto].
  intros ? Hin.
  rewrite flat_map_map.
  apply in_flat_map. eexists.
  split;[apply H|].
  unfold compose.
  simpl.
  rewrite allvars_bterm.
  apply in_app_iff. tauto.
Qed.

(**********************)
(** * CPS expressions *)
(**********************)


Inductive CPSCanonicalOp : Set :=
 | CLambda 
 | CKLambda
 | CFix (nMut : nat) (** number of functions that are mutually defined*)
 | CDCon (dc : dcon) (nargs : nat).

Definition CPSOpBindingsCan (c : CPSCanonicalOp) 
    : list nat :=
  match c with
  | CLambda    => [2] (* user lambda, also binds a continuation *)
  | CKLambda    => [1] (* continuation lambda  *)
  | CFix nMut => repeat nMut 1
  | CDCon _ nargs    => repeat nargs 0
  end.

Inductive CPSNonCanonicalOp : Set :=
 | CHalt 
 | CRet (** application of a continuation lambda ([CKLambda]) *)
 | CCall (** a bit like apply in source language *)
 | CProj (selector :nat) (** which one to project out*)
 | CMatch (dconAndNumArgs : list (dcon * nat))
 (** each member of the list corresponds to a branch. 
    it says how many variables are bound in that branch*).

Definition CPSOpBindingsNCan (nc : CPSNonCanonicalOp) : list nat :=
  match nc with
  | CHalt => [0]
  | CRet => [0,0]
  | CCall => [0,0,0]
  | CProj _ => [0,0]
  | CMatch numargsInBranches => 0::(List.map snd numargsInBranches)
  end.

Definition cdecc: forall x y : CPSCanonicalOp,
{x = y} + {x <> y}.
Proof using.
  repeat(decide equality).
Defined.

Definition cdecnc:
forall
  x y : CPSNonCanonicalOp, {x = y} + {x <> y}.
Proof using.
  repeat(decide equality).
Defined.

Definition CPSGenericTermSig : GenericTermSig :=
{| 
  CanonicalOp := CPSCanonicalOp;
  NonCanonicalOp := CPSNonCanonicalOp;
  OpBindingsCan := CPSOpBindingsCan;
  OpBindingsNCan := CPSOpBindingsNCan;
  canonical_dec := cdecc;
  ncanonical_dec := cdecnc
|}.


Notation CBTerm := (@terms.BTerm NVar CPSGenericTermSig).
Notation CTerm := (@terms.NTerm NVar CPSGenericTermSig).
Notation coterm := (@terms.oterm NVar CPSGenericTermSig).
Notation CCan := (@opid.Can CPSGenericTermSig).
Notation CNCan := (@opid.NCan CPSGenericTermSig).

Definition Lam_c (v vk : NVar) (b : CTerm) : CTerm :=
  coterm (CCan CLambda) [bterm [v; vk] b].

Definition KLam_c (v : NVar) (b : CTerm) : CTerm :=
  coterm (CCan CKLambda) [bterm [v] b].

Definition Ret_c (f a : CTerm) :=
  coterm (CNCan CRet) [bterm [] f , bterm [] a].

Definition Halt_c (v : CTerm) :=
  coterm (CNCan CHalt) [bterm [] v].

Definition Call_c (f k a : CTerm) :=
  coterm (CNCan CCall) [bterm [] f , bterm [] k , bterm [] a].

Definition Con_c (dc : dcon) (args : list CTerm) : CTerm :=
  coterm (CCan (CDCon dc (length args))) (List.map (bterm []) args).

Definition Proj_c (arg: CTerm) (selector : nat) (cont: CTerm)  : CTerm :=
  coterm (CNCan (CProj selector)) [bterm [] arg, bterm [] cont].

(** do we need a continuation variable as well? *)
Definition Fix_c (xf : NVar) (args : list CTerm) : CTerm :=
  coterm (CCan (CFix (length args))) (List.map (bterm [xf]) args).

Definition Fix_c' (lbt : list CBTerm) : CTerm :=
  coterm (CCan (CFix (length lbt))) lbt.

Definition Match_c (discriminee : CTerm) (brs : list branch) : CTerm :=
  coterm (CNCan (CMatch (List.map (fun b => (fst b, num_bvars (snd b))) brs))) 
         ((bterm [] discriminee)::(List.map snd brs)).

Instance CExpSubstitute : Substitute CTerm CTerm :=
  { substitute := fun rep x t => subst t x rep}.

(** OPTIMISED Big-step evaluation for CPS expressions.
    Notice that only computations
    are evaluated -- values are inert so to speak. *)
Inductive eval_c : CTerm -> CTerm -> Prop :=
| eval_Halt_c : forall v, eval_c (Halt_c v) v
| eval_Ret_c : forall x c v v',
                 eval_c (c {x := v}) v' -> 
                 eval_c (Ret_c (KLam_c x c) v) v'

| eval_Call_c : forall xk x c v1 v2 v',
                  eval_c (ssubst c [(x,v2);(xk,v1)]) v' -> 
                  eval_c (Call_c ((Lam_c x xk c)) v1 v2) v'
| eval_Match_c : forall d vs bs c v',
                   find_branch d (List.length vs) bs = Some c ->
                   eval_c (apply_bterm c vs) v' -> 
                   eval_c (Match_c (Con_c d vs) bs) v'
| eval_Proj_c : forall lbt i k v' xf xl xlk b,
                  select i lbt = Some (bterm [xf] (Lam_c xl xlk b)) -> 
                  eval_c (Ret_c k ((Lam_c xl xlk b){xf:=Fix_c' lbt})) v' ->
                  eval_c (Proj_c (Fix_c' lbt) i k) v'.
Hint Constructors eval_c.

(** Useful for rewriting. *)
Lemma eval_ret :
  forall x c v v', eval_c (Ret_c (KLam_c x c) v) v' 
  <-> eval_c (c{x := v}) v'.
Proof using.
  intros. split ; intro. inversion H. subst ; auto. constructor ; auto.
Qed.

(** Useful for rewriting. *)
Lemma eval_call : forall xk x c v1 v2 v',
   eval_c (Call_c (Lam_c x xk c) v1 v2) v'
  <-> eval_c (ssubst c [(x,v2);(xk,v1)]) v'.
Proof using.
  intros ; split ; intro; inversion H ; subst ; auto.
Qed.

(*
(** Useful for rewriting. *)
Lemma eval_match :
  forall d vs bs v' c,
    find_branch d (N.of_nat (List.length vs)) bs = Some c -> 
    (eval_c (Match_c (Con_c d vs) bs) v' <-> (eval_c (usubst_list c vs) v')).
Proof using..
  intros ; split ; intro. inversion H0 ; subst. rewrite H in H5. injection H5 ;
    intros ; subst. auto.
  econstructor ; eauto.
Qed.

(** Useful for rewriting. *)
Lemma eval_proj :
  forall cs i c k v',
    nthopt (N.to_nat i) cs = Some c ->
    (eval_c (Proj_c (Fix_c cs) i k) v' <->
     eval_c (Ret_c k ((Lam_c c){0:=Fix_c cs})) v').
Proof using..
  intros ; split ; intro. inversion H0 ; subst.
  rewrite H in H5. injection H5 ; intros ; subst.
  auto. econstructor ; eauto.
Qed.

*)


(**************************)
(** * The CPS Translation *)
(**************************)

(** Computable test as to whether a source expression is already a
    value (a.k.a., atomic).  *)

Definition isNilb {A:Type} (l: list A) : bool :=
match l with
| [] => true
| _ => false
end.

Fixpoint is_valueb (e:NTerm) : bool :=
  match e with
    | vterm _ => true
    | terms.oterm c lb => 
      match c with
      | opid.Can c => 
          match c with
          (* expensive test. need memoization *)
          | NDCon _ _ => ball (List.map (is_valueb ∘ get_nt) lb)
          | _ => true
          end
      | opid.NCan _ => false
      end
   end.

(* assuming nt_wf, we can make it iff *)
Lemma is_valueb_corr :
  (forall e, is_value e -> is_valueb e = true).
Proof using.
  intros ? H.
  induction H; auto. simpl. rewrite map_map.
  unfold compose. simpl. 
  rewrite ball_map_true. auto.
Qed.

Definition contVars (n:nat) : list NVar :=
  freshVars n (Some CPSVAR) [] [].

Definition contVar : NVar :=
  nth 0 (freshVars 1 (Some CPSVAR) [] []) nvarx.
   
(** The inner, naive CBV CPS translation.  This introduces a lot of 
    administrative reductions, but simple things first.  Importantly,
    things that are already values are treated a little specially.  
    This ensures a substitution property 
    [cps_cvt(e{x:=v}) = (cps_cvt e){x:=(cps_vt_val v)}].
 *)
 
Section CPS_CVT.
(** recursive call *)
  Variable cps_cvt : NTerm -> CTerm (*val_c *).
  
      (* cont \k.(ret [e1] (cont \v1.(ret [e2] (cont \v2.call v1 k v2)))) *)
  Definition cps_cvt_apply  (ce1 : CTerm) (e2: NTerm) : CTerm :=
      let kvars := contVars 3 in 
      let k := nth 0 kvars nvarx in  
      let k1 := nth 1 kvars nvarx in  
      let k2 := nth 2 kvars nvarx in  
       KLam_c k 
        (Ret_c ce1 (* e1 may not already be a lambda *)
               (KLam_c k1 (Ret_c (cps_cvt e2)
                                  (KLam_c k2 (Call_c (vterm k1) (vterm k) (vterm k2)))))).


  Definition cps_cvt_lambda (x : NVar) (b: NTerm) : CTerm :=
          let kv := contVar in
             (Lam_c x kv (Ret_c (cps_cvt b) (vterm kv))).

  (** the KLam_c was manually added. unlike now, Fix_c previously implicitly bound a var*)
  Definition cps_cvt_fn_list'  (es: list BTerm) : list CBTerm :=
    map (fun b => 
            let e := get_nt b in
            let vars := get_vars b in
            let kv := contVar in 
                    bterm vars (KLam_c kv (Ret_c (cps_cvt e) (vterm kv))) ) es.

  Fixpoint cps_cvt_val' (e:NTerm) : CTerm :=
    match e with
      | vterm n => vterm n
      | terms.oterm (opid.Can NLambda) [bterm [x] b] => 
          cps_cvt_lambda x b
      | terms.oterm (opid.Can (NDCon d l)) lb => 
          let fb := (fun b => 
                      bterm []
                            (cps_cvt_val' (get_nt b))) in
            coterm (CCan (CDCon d l)) (List.map fb lb)
      | terms.oterm (opid.Can (NFix nargs)) lb =>
          terms.oterm (CCan (CFix nargs))
             (cps_cvt_fn_list' lb)
      | _ => coterm (CCan CLambda) (map ((bterm []) ∘ vterm)  (free_vars e))
          (* ill-formed term, which will not arise from the prev. phase.
            This choice, which is also ill-formed,
            is just to ensure that the free variables are same as
            that of the the input *)
    end.

  Fixpoint cps_cvts' (vs: list NVar )(es:list BTerm) (c:CTerm) :  CTerm :=
    match es with
      | nil => c
      | (bterm _ e)::es =>
        match vs with
        | [] => Ret_c (cps_cvt e) (KLam_c nvarx (cps_cvts' [] es c)) (* impossible *)
        | kvh :: kvt => Ret_c (cps_cvt e) (KLam_c kvh (cps_cvts' kvt es c))
        end
    end.


  Definition cps_cvt_branch'  (kv : NVar) (bt: BTerm) : CBTerm :=
    match bt with
    | bterm vars nt =>
        (bterm vars (Ret_c (cps_cvt nt) (vterm kv)))
    end.

 Definition cps_cvt_branches'  (kv : NVar) : (list BTerm) -> list CBTerm :=
  List.map (cps_cvt_branch' kv).

End CPS_CVT.

  Definition val_outer ce :=
    let kv := contVar in 
      KLam_c kv (Ret_c (vterm kv) ce).

Fixpoint cps_cvt (e:NTerm) {struct e}: CTerm :=
  if is_valueb e 
  then val_outer (cps_cvt_val' cps_cvt e) 
     (*val_outer seems unnecessary eta expansion; not needed when consideing beta equiv?*)
    else
  match e with
    | terms.oterm (opid.NCan NApply) [bterm [] e1; bterm [] e2] => 
        cps_cvt_apply cps_cvt (cps_cvt e1) e2
    | terms.oterm (opid.Can (NDCon d nargs)) es => 
        let kvars := contVars (S (length es)) in
        let k := hd nvarx kvars  in
        let tlkv := tail kvars  in
        KLam_c k (cps_cvts' cps_cvt tlkv es (Ret_c (vterm k)
                                                          (Con_c d (map vterm tlkv))))
    | terms.oterm (opid.NCan (NMatch brl)) ((bterm [] discriminee)::brr) => 
      let kvars := contVars 2 in 
      let k := nth 0 kvars nvarx in
      let kd := nth 1 kvars nvarx in
      let brrc :=  (bterm [] (vterm kd))::(cps_cvt_branches' cps_cvt k brr) in
      KLam_c k (Ret_c (cps_cvt discriminee)
                      (KLam_c kd 
                              (coterm (CNCan (CMatch brl)) brrc)))


      (* translate as if it were App_e (Lam_e x e2) e1. See [cps_cvt_let_as_app_lam] below.
         Unlike the general cas of App, here the function is already a value *)
    | terms.oterm (opid.NCan NLet) [bterm [] e1, bterm [x] e2] => 
      let cpsLam := (val_outer (cps_cvt_lambda cps_cvt x e2)) in
        cps_cvt_apply cps_cvt cpsLam e1

    | terms.oterm (opid.NCan (NProj i)) [bterm [] e] =>
      let kvars := contVars  2 in 
      let k := nth 0 kvars nvarx in  
      let ke := nth 1 kvars nvarx in  
        KLam_c k (Ret_c (cps_cvt e) 
                        (KLam_c ke (Proj_c (vterm ke) i (vterm k))))
    | _ => coterm (CCan CLambda) (map ((bterm []) ∘ vterm)  (free_vars e))
          (* ill-formed term, which will not arise from the prev. phase.
            This choice, which is also ill-formed,
            is just to ensure that the free variables are same as
            that of the the input *)
  end.


Definition cps_cvt_val (e:NTerm) : CTerm :=
  cps_cvt_val' cps_cvt e.
(*
Definition cps_cvts := cps_cvts' cps_cvt.
Definition cps_cvt_vals := List.map cps_cvt_val.
Definition cps_cvt_branch := cps_cvt_branch' cps_cvt.
Definition cps_cvt_branches := cps_cvt_branches' cps_cvt.
Definition cps_cvt_fn_list := cps_cvt_fn_list' cps_cvt.
*)

(** The top-level CPS translation.  We use [cont \x.Halt x] as the initial
    continuation. *)
Definition cps_cvt_prog (e:NTerm) := Ret_c (cps_cvt e) (KLam_c nvarx (Halt_c (vterm nvarx))).

(*
(** An optimized translation -- this is more what we want, but still has 
    administrative reductions in it, and is harder to prove so I'm forgoing
    it for now.  *)
Fixpoint opt_cps_cvt (e:exp) (k: val_c) : cps := 
  match e with
    | Var_e n => Ret_c k (Var_c n)  
    | Lam_e e => Ret_c k (Lam_c (opt_cps_cvt e (KVar_c 0))) 
    | App_e e1 e2 =>
      opt_cps_cvt e1
        (Cont_c 
          (opt_cps_cvt e2
            (Cont_c
              (Call_c (KVar_c 1 (*e1*)) (kshift_val 2 0 k) (KVar_c 0 (*e2*))))))          
  end.

Definition opt_cps_cvt_prog (e:exp) := opt_cps_cvt e (Cont_c (Halt_c (KVar_c 0))).
*)

(** Some simple tests.  These were invaluable for debugging :-) *)
(*
Example e1 : exp := Lam_e (Var_e 0).  (* identity *)
Eval vm_compute in cps_cvt_prog e1.
Eval vm_compute in cps_to_string (cps_cvt_prog e1).
Eval vm_compute in eval_c_n 3 (cps_cvt_prog e1).
Eval vm_compute in ans_to_string (eval_c_n 100 (cps_cvt_prog e1)).
Example e2 : exp := App_e e1 e1.  (* (fun x => x) (fun x => x) *)
Eval vm_compute in cps_cvt_prog e2.
Eval vm_compute in cps_to_string (cps_cvt_prog e2).
Eval vm_compute in eval_c_n 100 (cps_cvt_prog e2).
Eval vm_compute in ans_to_string (eval_c_n 100 (cps_cvt_prog e2)).
Example e3 : exp := Con_e 42 nil.
Eval vm_compute in cps_cvt_prog e3.
Eval vm_compute in cps_to_string (cps_cvt_prog e3).
Example e4 : exp := Con_e 1 (e3::e3::nil).
Eval vm_compute in cps_cvt_prog e4.
Eval vm_compute in cps_to_string (cps_cvt_prog e4).
Example e5 : exp := Con_e 55 ((App_e e1 e3)::((Con_e 33 nil)::nil)).
Eval vm_compute in cps_cvt_prog e5.
Eval vm_compute in cps_to_string (cps_cvt_prog e5).
Eval vm_compute in eval_c_n 100 (cps_cvt_prog e5).
Eval vm_compute in ans_to_string (eval_c_n 100 (cps_cvt_prog e5)).
Example e6 : exp := Lam_e (Match_e (Var_e 0) [(55,1,Var_e 0); (44,0,Con_e 44 nil); (33,2,Var_e 1)]).
Eval vm_compute in cps_to_string (cps_cvt_prog e6).
Example e7 : exp := Let_e (Con_e 44 nil) (App_e e1 (Var_e 0)).
Eval vm_compute in eval_c_n 100 (cps_cvt_prog e7).
Example e8 : exp := Let_e e1 (Let_e (Con_e 44 nil) (App_e (Var_e 1) (Var_e 0))).
Eval vm_compute in eval_c_n 100 (cps_cvt_prog e8).
Example e9 : exp := Let_e e1 (Let_e (App_e (Var_e 0) (Con_e 44 nil)) (App_e (Var_e 1) (Var_e 0))).
Eval vm_compute in eval_c_n 100 (cps_cvt_prog e9).
*)
Import List.
Local Open Scope list_scope.

Lemma cps_cvt_let_as_app_lam : forall e1 x e2,
  cps_cvt (Let_e x e1 e2)
  = cps_cvt (App_e (Lam_e x e2) e1).
Proof using.
  intros. reflexivity.
Qed.

Lemma cps_val_outer :
  forall (v:NTerm), 
  is_valueb v = true -> 
  (cps_cvt v) = 
    val_outer (cps_cvt_val' cps_cvt v).
Proof using.
  simpl. intros ? Hisv.
  Local Opaque is_valueb cps_cvt_val'.
  destruct v; simpl; rewrite Hisv; refl.
  Local Transparent is_valueb cps_cvt_val'.
Qed.

(* TODO : pick a more specific name *)
Lemma cps_val :
  forall (v:NTerm), 
  let k := contVar in
  is_value v -> 
  (cps_cvt v) = 
    KLam_c k (Ret_c (vterm k) (cps_cvt_val' cps_cvt v)).
Proof using.
  simpl. intros ? Hisv.
  apply cps_val_outer.
  apply is_valueb_corr. eauto.
Qed.



Lemma ssubstRet_c : forall sub a b, 
   ssubst (Ret_c a b) sub = Ret_c (ssubst a sub) (ssubst b sub).
Proof using. refl. Qed.

Lemma ssubstKlam_c : forall sub x b, 
  sub_range_sat sub closed
  -> disjoint [x] (dom_sub sub)
  -> ssubst (KLam_c x b) sub = KLam_c x (ssubst b sub).
Proof using.
  intros.
  change_to_ssubst_aux8.
  simpl. rewrite sub_filter_disjoint1;[| disjoint_reasoningv].
  reflexivity.
Qed.

Lemma substKlam_cTrivial : forall x (b t : CTerm),
  closed t
  -> ssubst (KLam_c x b) [(x,t)] = KLam_c x b.
Proof using.
  intros ? ? ? H.
  change_to_ssubst_aux8;[ |simpl; rewrite H; disjoint_reasoningv; tauto].
  simpl. autorewrite with SquiggleLazyEq.
  simpl.
  reflexivity.
Qed.



Local Opaque remove_nvars.
Lemma substKlam_cTrivial2 : forall x xx (b t : CTerm),
  closed t
  -> closed (KLam_c x b)
  -> ssubst (KLam_c x b) [(xx,t)] = KLam_c x b.
Proof using.
  intros ? ? ? ? H Hb.
  change_to_ssubst_aux8;[ |simpl; rewrite H; disjoint_reasoningv; tauto].
  simpl. rewrite decide_decideP.
  destruct (decideP (x = xx)).
  - simpl. rewrite ssubst_aux_nil.
    reflexivity.
  - unfold KLam_c. do 3 f_equal.
    apply ssubst_aux_trivial_cl.
    intros ? ? Hin. in_reasoning. inverts Hin.
    split; [assumption|].
    unfold closed in Hb. simpl in Hb.
    autorewrite with core list in Hb.
    rw nil_remove_nvars_iff in Hb.
    firstorder.
Qed.

Local Opaque memvar.
Lemma substLam_cTrivial2 : forall x xk xx (b t : CTerm),
  closed t
  -> closed (Lam_c x xk b)
  -> ssubst (Lam_c x xk b) [(xx,t)] = Lam_c x xk b.
Proof using.
  intros ? ? ? ? ? H Hb.
  change_to_ssubst_aux8;[ |simpl; rewrite H; disjoint_reasoningv; tauto].
  simpl. rewrite memvar_dmemvar.
  cases_if.
  - simpl. rewrite ssubst_aux_nil.
    reflexivity.
  - unfold Lam_c. do 3 f_equal.
    apply ssubst_aux_trivial_cl.
    intros ? ? Hin. in_reasoning. inverts Hin.
    split; [assumption|].
    unfold closed in Hb. simpl in Hb.
    autorewrite with core list in Hb.
    rw nil_remove_nvars_iff in Hb.
    firstorder.
Qed.

Lemma ssubstCall_c : forall sub a b d, 
  ssubst (Call_c a b d) sub = Call_c (ssubst a sub) (ssubst b sub) (ssubst d sub).
Proof using. refl. Qed.

Definition onlyUserVars (t: NTerm) : Prop :=
  varsOfClass (all_vars t) USERVAR.

Lemma userVarsContVars : forall lv,
varsOfClass lv USERVAR
-> forall n, no_repeats (contVars n) /\ disjoint (contVars n) lv /\ Datatypes.length (contVars n) = n.
Proof using.
  intros. unfold contVars.
  addFreshVarsSpec.
  dands; try tauto.
  apply varsOfClassFreshDisjointBool.
  assumption.
Qed.

Lemma userVarsContVar : forall lv,
varsOfClass lv USERVAR
-> disjoint [contVar] lv.
Proof using.
  intros.
  unfold contVar.
  addFreshVarsSpec2 lvn Hfr.
  repnd.
  dlist_len_name lvn v.
  simpl.
  rewrite Heqlvn.
  apply varsOfClassFreshDisjointBool.
  assumption.
Qed.

Section CPS_CVT_INDUCTION.
(*cps_cvt and cps_cvt_val' depend on each other in a complex way. 
proving something about one of them needs a similar property about the other.
These definitions reduce duplication.*)

(* some property about cps_cvt and cps_cvt_val *)
Variable P : NTerm -> (NTerm -> CTerm) -> Prop.

Definition cps_cvt_val_step : Prop := forall e:NTerm,
  (forall es:NTerm , (size es) < size e  -> P es cps_cvt)
  -> P e (cps_cvt_val' cps_cvt).

Definition cps_cvt_val_step2 : Prop := forall e:NTerm,
  (forall es:NTerm , (size es) < size e  -> P es cps_cvt)
  -> is_valueb e = true
  -> P e (cps_cvt_val' cps_cvt).

(** because Let_e is like App_e of Lam_e  w.r.t.  CPS conversion, proving the 
App_e case separately enables its reuse in the Let_e case.
In that strategy, the proof must by induction on size (NTerm_better_ind3), and NOT structural subtermness *)
Definition cps_cvt_apply_step : Prop := forall e1 e2 :NTerm,
  (forall es:NTerm , (S (size es)) < (size (App_e e1 e2))  -> P es cps_cvt)
  -> P (App_e e1 e2) cps_cvt.

End CPS_CVT_INDUCTION.

(* get rid of it. must not depend on the return value on ill formed cases.
cps_cvt_val will  never be called for non-values. So add is_value as a hypothesis*)
Local Lemma cps_cvt_val_aux_fvars_aux : forall o lbt,
  (forall es, 
    (size es) < size (oterm o lbt)
    -> nt_wf es 
    -> varsOfClass (all_vars es) USERVAR
    -> eq_set (free_vars (cps_cvt  es)) (free_vars es))
-> nt_wf (oterm o lbt)
-> varsOfClass (all_vars (oterm o lbt)) USERVAR
-> eq_set (flat_map free_vars_bterm (cps_cvt_fn_list' cps_cvt lbt))
          (flat_map free_vars_bterm lbt).
Proof using.
  intros ? ? Hyp  Hwf Hvc.
  unfold cps_cvt_fn_list'. rewrite flat_map_map.
  apply eqset_flat_maps.
  intros bt Hin.
  destruct bt as [lvb nt]. unfold compose.
  simpl.
  autorewrite with list SquiggleLazyEq.
  rewrite remove_nvars_app_r, remove_nvars_eq.
  autorewrite with list in *.
  varsOfClassSimpl.
  rewrite Hyp; [
    | eapply size_subterm3; eauto
    | ntwfauto
    | tauto
      ].
  apply proj2, userVarsContVar in Hin.
  rewrite (remove_nvars_nop [contVar]);[| disjoint_reasoningv].
  refl.
Qed.

Local Ltac 
illFormedCase :=
 (try reflexivity; try (simpl;rewrite flat_map_vterm; reflexivity)).


Definition cps_preserves_fvars (e : NTerm) (cps_cvt : NTerm -> CTerm) := 
    nt_wf e 
    -> varsOfClass (all_vars e) USERVAR
    -> eq_set (free_vars (cps_cvt e)) (free_vars e).

Lemma cps_cvt_val_aux_fvars : 
  cps_cvt_val_step cps_preserves_fvars.
Proof using.
  simpl. unfold cps_preserves_fvars. intros ? Hyp.
  nterm_ind e as [v | o lbt Hind] Case;[eauto|].
  intros Hwf Hs. simpl in Hs.
  destruct o;[| illFormedCase].
  destruct c;[clear Hind| clear Hind|]; inverts Hwf as Hbt Hnb;
    simpl in Hnb.
(* lambda case *)
- simpl.
  dnumvbars Hnb bt.
  erewrite <- cps_cvt_val_aux_fvars_aux; eauto.
  simpl. autorewrite with list. rewrite remove_nvars_comm. reflexivity.

(* Fix_e case *)
- simpl.
  eapply cps_cvt_val_aux_fvars_aux; eauto.
  
(* Con_e case *)
- simpl.
  rewrite flat_map_map.
  apply eqset_flat_maps.
  intros ? Hin.
  unfold compose. destruct x. simpl.
  apply map_eq_repeat_implies with (v:= (bterm l n)) in Hnb;[| assumption].
  unfold num_bvars in Hnb. simpl in Hnb.
  dlist_len_name l vv.
  apply properEqsetvRemove; eauto.
  rewrite Hind; eauto; [|ntwfauto; fail|].
  + intros.  apply Hyp; eauto. eapply lt_trans; eauto.
    eapply size_subterm3; eauto.
  + varsOfClassSimpl. tauto.
Qed.

Ltac addContVarsSpec  m H vn:=
  let Hfr := fresh H "nr" in
  pose proof H as Hfr;
  apply userVarsContVars with (n:=m) in Hfr;
  let vf := fresh "lvcvf" in
  remember (contVars m) as vf;
  let Hdis := fresh "Hcvdis" in
  let Hlen := fresh "Hcvlen" in
  pose proof Hfr as  Hdis;
  pose proof Hfr as  Hlen;
  apply proj2, proj2 in Hlen;
  apply proj2, proj1 in Hdis;
  apply proj1 in Hfr;
  simpl in Hlen;
  dlist_len_name vf vn.


(** will be used for both the [App_e] ane [Let_e] case *)
Lemma cps_cvt_apply_fvars : 
cps_cvt_apply_step cps_preserves_fvars.
Proof using.
  intros ? ? Hind Hwf Hs.
  simpl. autorewrite with  SquiggleLazyEq list.
  unfold App_e in Hs.
  repeat progress (autorewrite with list allvarsSimpl in Hs; 
    simpl in Hs).
  addContVarsSpec 3 Hs kv.
  simpl.
  remove_nvars_r_simpl.
  autorewrite with SquiggleLazyEq list. 
  repeat (rewrite remove_nvars_nops;[| noRepDis]).
  repeat rewrite remove_nvars_app_r.
  autorewrite with SquiggleLazyEq list.
  simpl. 
  setoid_rewrite remove_nvars_comm at 2.
  autorewrite with SquiggleLazyEq list. 
  repeat rewrite remove_nvars_app_l.
  pose proof (size_pos e2).
  pose proof (size_pos e1).
  apply varsOfClassApp in Hs. repnd.
  unfold cps_preserves_fvars in Hind.
  do 2 (rewrite Hind; [ | simpl; omega | ntwfauto | assumption]).
  apply disjoint_sym in Hcvdis.
  clear Hind.
  rewrite remove_nvars_nop;[|noRepDis].
  rewrite remove_nvars_nop;[|noRepDis].
  reflexivity.
Qed.


Lemma cps_cvt_constr_fvars : forall  o lbt lkv c,
  (forall es, 
     (size es < size (oterm o lbt))
      -> nt_wf es 
      -> varsOfClass (all_vars es) USERVAR
      -> eq_set (free_vars (cps_cvt es)) (free_vars es))
  -> length lbt = length lkv 
  -> (forall b, LIn b lbt -> (bt_wf b /\ get_vars b = []))
    -> varsOfClass (all_vars (oterm o lbt)) USERVAR
    -> disjoint lkv (all_vars (oterm o lbt))
    -> eq_set (free_vars (cps_cvts' cps_cvt lkv lbt c))
            (free_vars (oterm o lbt) ++ (remove_nvars  lkv (free_vars c))).
Proof using.
  induction lbt as [| b lbt IHlbt]; intros ? ? Hyp Hl Hf Hs Hdis;
    simpl in Hl; dlist_len_name lkv kv;[auto|].
  simpl in *.
  destruct b as [blv bnt].
  simpl.
  autorewrite with list SquiggleLazyEq.
  repeat progress (autorewrite with SquiggleLazyEq list in *; 
    simpl in * ).
  repnd.
  rewrite IHlbt; simpl;
    autorewrite with SquiggleLazyEq list; eauto;
     [| intros; apply Hyp; eauto; omega | disjoint_reasoningv ].
  clear IHlbt.
  dLin_hyp. simpl in *. repnd. subst.
  autorewrite with SquiggleLazyEq in *.
  rewrite remove_nvars_app_r.
  rewrite remove_nvars_app_l.
  setoid_rewrite flat_map_fapp in Hdis.
  rewrite remove_nvars_nop; [|disjoint_reasoningv2].
  rewrite app_assoc.
  rewrite Hyp; auto; [omega| ntwfauto].
Qed.

Hint Resolve varsOfClassSubset subsetAllVarsLbt2 subsetAllVarsLbt3
  subsetAllVarsLbt3 subset_disjoint:  CerticoqCPS.
Hint Resolve userVarsContVar disjoint_sym_eauto : CerticoqCPS.


Lemma cps_cvt_aux_fvars : forall e,
  nt_wf e ->
  varsOfClass (all_vars e) USERVAR  -> 
  eq_set (free_vars (cps_cvt e)) (free_vars e).
Proof using.
  intros e.
(** Induction on size of the term. Subterm-based induction does not work in this approach.
    Recall that Let_e e1 (x.e2) is treated like App_e (Lam_e (x.e2)) e1.
    Note that (Lam_e (x.e2)) is not a structural subterm of (Let_e e1 (x.e2)).
    However, size (Lam_e (x.e2)) < (Let_e e1 (x.e2)), thus allowing us to invoke the 
    induction hypothesis on (Lam_e (x.e2))
 *)  
  induction e as [v | o lbt Hind] using NTerm_better_ind3;
  intros  Hwf Hs;
  [    unfold all_vars in Hs;
    simpl in *;
    autorewrite with core list SquiggleLazyEq SquiggleLazyEq2;
    simpl; rewrite remove_nvars_nops; auto;apply disjoint_sym; eauto using
               @userVarsContVar |].
Local Opaque cps_cvt_val' is_valueb. 
  simpl. 
  cases_if.
(* e is a value; use the lemma above *)
- simpl. autorewrite with list SquiggleLazyEq SquiggleLazyEq2. simpl.
Local Transparent cps_cvt_val' is_valueb.
  pose proof cps_cvt_val_aux_fvars as Hccc.
  unfold cps_preserves_fvars, cps_cvt_val_step in Hccc.
  rewrite Hccc; clear Hccc; [simpl; autorewrite with list| | ntwfauto | assumption].
  + rewrite remove_nvars_nop;[auto|].
    autorewrite with list SquiggleLazyEq in *.
    setoid_rewrite flat_map_fapp in Hs.
    apply varsOfClassApp in Hs. repnd.
    apply disjoint_sym.
    eauto using userVarsContVar.
  + intros ? ? Hss Hsv. destruct lbt;
      [destruct es; simpl in Hss|];apply Hind; auto.

(* e is not a value *)
- pose proof Hwf as Hwfb.
  destruct o as [c| nc];[destruct c | destruct nc ]; illFormedCase;
  inverts Hwf as Hbt Hnb; simpl in Hnb.
(** data constructor when not all subterms are values *)
  + 
    repeat progress (autorewrite with list allvarsSimpl in Hs; 
      simpl in Hs).
    addContVarsSpec (S (Datatypes.length lbt)) Hs kv.
    rename lvcvf into lkv. simpl.
    simpl. repnd.
    simpl in *.
    rewrite  cps_cvt_constr_fvars with (o:=(Can (NDCon dc nargs))); 
      autorewrite with list allvarsSimpl; auto;[| | disjoint_reasoningv; fail].
    * simpl. autorewrite with list SquiggleLazyEq SquiggleLazyEq2.
      setoid_rewrite flat_map_fapp in Hcvdis.
      rewrite remove_nvars_nop;[| disjoint_reasoningv].
      rewrite (remove_nvars_nop lkv);[| noRepDis]. simpl.
      autorewrite with list SquiggleLazyEq.
       simpl.
      autorewrite with list SquiggleLazyEq.
      refl.
    * intros ? Hin.
      pose proof Hin as Hinb.
      split; [ntwfauto|].
      eapply map_eq_repeat_implies in Hnb; eauto.
      unfold num_bvars in Hnb.
      apply length_zero_iff_nil in Hnb. assumption.

(** App_e *)
  + dnumvbars Hnb bt.
    apply cps_cvt_apply_fvars; auto.
    unfold cps_preserves_fvars.
    intros; apply Hind; auto;[]. simpl in *. omega.

(** Proj_e *)
  + dnumvbars Hnb bt. unfold num_bvars. simpl.
    addContVarsSpec 2 Hs kv. repnd.
    simpl in *. dlist_len_name lkv kv; simpl in *.
    repeat progress (autorewrite with list SquiggleLazyEq SquiggleLazyEq2 in *; simpl in * ).
    rewrite remove_nvars_nops;[|noRepDis].
    autorewrite with list SquiggleLazyEq.
    autorewrite with  SquiggleLazyEq in Hs.
    rewrite Hind;[| omega | ntwfauto | tauto].
    autorewrite with list SquiggleLazyEq.
    rewrite remove_nvars_nop;[auto| inauto; eauto].

(** Let_e *)
  + dnumvbars Hnb b.
    rename blv0 into blv1.
    unsimpl (cps_cvt (Let_e blv1 bnt bnt0)).
    rewrite cps_cvt_let_as_app_lam.
    remember (Lam_e blv1 bnt0) as lam.
    repeat progress (autorewrite with list SquiggleLazyEq in Hs; simpl in Hs).
    pose cps_cvt_apply_fvars as Hccc. unfold cps_cvt_apply_step, cps_preserves_fvars in Hccc.
    rewrite Hccc; clear Hccc;
      [
        | subst lam;
          intros;  simpl in *; apply Hind;[omega | ntwfauto |assumption]
        | subst lam; ntwfauto;in_reasoning; subst; ntwfauto
        | subst lam; simpl in *; unfold App_e, Lam_e;
              repeat progress (autorewrite with list SquiggleLazyEq; simpl); tauto
              ].
    subst lam. clear.
    simpl. autorewrite with list SquiggleLazyEq.
    apply eqsetv_prop. intros. repeat rewrite in_app_iff.
    tauto. 

(** Match_e *)
  + 
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    addContVarsSpec 2 Hs kv. repnd.
    Local Opaque size.
    simpl in *.
    Local Transparent size. simpl in Hs.
    repeat progress (autorewrite with list SquiggleLazyEq SquiggleLazyEq2 in *; simpl in * ).
    unfold cps_cvt_branches'.
    rewrite flat_map_map.
    unfold compose. simpl.

    rewrite eqset_flat_maps with (g:=fun b => kv::(free_vars_bterm b)).
    * rewrite remove_nvars_flat_map. unfold compose.
      rewrite eqset_flat_maps with (g:=fun b => kv::(free_vars_bterm b));
        [| intros; remove_nvars_r_simpl;
           rewrite remove_nvars_nops;[| noRepDis];
           rewrite remove_nvars_nop;[refl|
              try terms2.disjoint_flat2]].
      rewrite Hind;[| simpl;omega | ntwfauto | tauto].
      clear Hind.
      rewrite remove_nvars_nop;[|inauto; eauto].
      rewrite remove_nvars_flat_map. unfold compose.
      rewrite eq_flat_maps with (g:=fun b => (free_vars_bterm b));[auto;fail|].
      intros.
      rewrite remove_nvars_cons_r, memvar_singleton.
      autorewrite with SquiggleLazyEq. 
      rewrite remove_nvars_nop;[refl|terms2.disjoint_flat2].

    * intros ? Hin. destruct x as [xlv xnt]. simpl.
      autorewrite with SquiggleLazyEq.
      repnd.
      rewrite Hind;
        [|eapply (size_subterm4 ((bterm [] bnt)::lbt)); right; eauto 
         | ntwfauto 
         | eauto using varsOfClassSubset, subsetAllVarsLbt2 ].
      autorewrite with list SquiggleLazyEq SquiggleLazyEq2.
      rewrite (remove_nvars_nop xlv [kv]);[|terms2.disjoint_flat2].
      rewrite eqset_app_comm. refl.
Qed.

(* Print Assumptions cps_cvt_aux_fvars.
close under global context *)

Corollary cps_cvt_val_fvars : forall (e : NTerm),
 nt_wf e
 -> varsOfClass (all_vars e) USERVAR 
 -> eq_set (free_vars (cps_cvt_val' cps_cvt e)) (free_vars e).
Proof using.
  intros ? Hwf Hs.
  pose proof cps_cvt_val_aux_fvars as Hccc.
  unfold cps_preserves_fvars, cps_cvt_val_step in Hccc.
  rewrite Hccc; clear Hccc; auto.
  intros.
  rewrite cps_cvt_aux_fvars; auto.
Qed.

Corollary cps_cvt_val_closed : forall e,
  nt_wf e
  -> varsOfClass (all_vars e) USERVAR 
  -> closed e
  -> closed (cps_cvt_val' cps_cvt  e).
Proof using.
  intros ? ? Hwf Hcl.
  unfold closed in *.
  apply null_iff_nil.
  unfold cps_cvt_val.
  rewrite cps_cvt_val_fvars; auto;
  rewrite Hcl; auto.
Qed.

Lemma isvalueb_ssubst_aux : forall t sub,
sub_range_sat sub is_value 
-> (is_valueb (ssubst_aux t sub)) = is_valueb t.
Proof.
  intro t. induction t as [v | o lbt Hind] using NTerm_better_ind; intros ? Hsr.
- simpl. dsub_find sf;[| refl]; symmetry in Heqsf.
  apply is_valueb_corr.  eapply Hsr. apply sub_find_some. eauto.
- simpl. destruct o; try refl.
  destruct c; try refl.
  rewrite map_map.
  f_equal.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  unfold compose.
  simpl.
  eapply Hind; eauto.
Qed.

(*
Hint Constructors is_value : CerticoqCPS.
Lemma isvalue_ssubst_aux : forall t sub,
sub_range_sat sub is_value 
-> (is_value (ssubst_aux t sub)) <-> is_value t.
Proof.
  intro t. induction t as [v | o lbt Hind] using NTerm_better_ind; intros ? Hsr.
- simpl. dsub_find sf;[| refl]; symmetry in Heqsf.
  apply sub_find_some in Heqsf. apply Hsr in Heqsf.
  split; auto with CerticoqCPS.
- simpl. destruct o; [| split; intro H; inverts H].
  destruct c; split; intros; try apply lam_is_value; try apply fix_is_value; try apply H.
  split. intros.
  Print is_value.
   econstructor.
  rewrite map_map.
  f_equal.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  unfold compose.
  simpl.
  eapply Hind; eauto.
Qed.
*)
Hint Rewrite isvalueb_ssubst_aux : CerticoqCPS.

Definition cps_ssubst_commutes (e : NTerm) (cps_cvt' : NTerm -> CTerm) := 
  forall (sub : Substitution),
nt_wf e
-> sub_range_sat sub is_value (* can we get rid of this ?*)
-> sub_range_sat sub nt_wf
-> sub_range_sat sub closed
-> varsOfClass (all_vars e ++ dom_sub sub ++ flat_map all_vars (range sub)) USERVAR
->  let sub_c := (map_sub_range (cps_cvt_val' cps_cvt)) sub in
      (ssubst_aux (cps_cvt' e) sub_c)= (cps_cvt' (ssubst_aux e sub)).

Lemma val_outer_ssubst_aux : forall t sub,
disjoint [contVar] (dom_sub sub)
->ssubst_aux (val_outer t) sub = val_outer (ssubst_aux t sub).
Proof.
  intros ? ? Hdis. unfold val_outer.
  simpl. unfold KLam_c, Ret_c.
  autorewrite with SquiggleLazyEq.
  rewrite sub_filter_disjoint1; [|disjoint_reasoningv2].
  repeat f_equal.
 rewrite sub_find_none_if;
     [refl|disjoint_reasoningv2].
Qed.

(*
Hint Resolve sub_filter_subset flat_map_monotone varsOfClassSubset map_monotone : SquiggleLazyEq. 
*)

Lemma contVars1 : contVars 1 = [contVar].
Proof.
  unfold contVar, contVars.
  addFreshVarsSpec2 lvn Hfr.
  simpl in *. repnd.
  dlist_len_name lvn v.
  refl.
Qed.

Lemma cps_cvt_val_ssubst_commutes_aux : 
  cps_cvt_val_step2 cps_ssubst_commutes.
Proof using.
  simpl. unfold cps_ssubst_commutes. intros ? Hyp.
  nterm_ind e as [v | o lbt Hind] Case;
  intros Hev ?  Hwf Hisv Hwfs Hcs  Hs;
  applydup userVarsContVar in Hs as Hdisvc; simpl in Hdisvc;
  [ | destruct o;[destruct c; inverts Hwf as Hbt Hnb; simpl in Hnb | inverts Hev]];
    [| clear Hind | clear Hind| ].
- simpl. symmetry.
  dsub_find sf; symmetry in Heqsf; [|erewrite sub_find_none_map; eauto; fail].
  erewrite sub_find_some_map; eauto.
(* Lambda case *)
- dnumvbars Hnb bt. simpl.
  unfold cps_cvt_lambda, Lam_c, Ret_c.
  do 4 f_equal.
  autorewrite with SquiggleLazyEq.
  rewrite sub_find_sub_filter;[| cpx].
  do 2 f_equal.
  rewrite sub_filter_map_range_comm.
  rewrite (cons_as_app _ btlv0).
  rewrite eqset_app_comm.
  rewrite sub_filter_app_r.
  rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2].
  rwsimpl Hs.
  simpl in Hbt. dLin_hyp.
  apply Hyp; auto; simpl; try omega; try ntwfauto.
  repnd.
  rwsimplC. dands; unfold range, dom_sub, dom_lmap; eauto with subset.
- simpl. f_equal. setoid_rewrite map_map.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  simpl. f_equal. unfold KLam_c, Ret_c.
  do 4 f_equal.
  autorewrite with SquiggleLazyEq.
  rewrite sub_find_sub_filter;[| cpx].
  do 2 f_equal.
  rewrite <- sub_filter_app_r.
  rewrite eqset_app_comm.
  rewrite sub_filter_app_r.
  rewrite sub_filter_map_range_comm.
  rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2].
  rewrite sub_filter_map_range_comm.
  rwsimpl Hs.
  apply Hyp; auto; simpl;[eapply size_subterm4; eauto | ntwfauto|].
  repnd.
  rwsimplC. dands; unfold range, dom_sub, dom_lmap; eauto with subset.
- simpl. f_equal. setoid_rewrite map_map.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  simpl. f_equal. 
  apply map_eq_repeat_implies with (v:= (bterm lv nt)) in Hnb;[| assumption].
  unfold num_bvars in Hnb. simpl in Hnb.
  dlist_len_name lv vv.
  autorewrite with SquiggleLazyEq.
  simpl in Hev.
  rewrite ball_map_true in Hev. unfold compose in Hev.
  applydup_clear Hev in Hin.
  simpl in *.
  apply Hind with (lv:=[]); auto;[| ntwfauto|].
  + intros.  apply Hyp; eauto. eapply lt_trans; eauto.
    eapply size_subterm4; eauto.
  + repeat rewrite varsOfClassApp in Hs.
    repnd. varsOfClassSimpl. tauto.
Qed.



Lemma cps_cvt_apply_ssubst_commutes_aux : 
  cps_cvt_apply_step cps_ssubst_commutes.
Proof.
  intros ? ? Hind ? Hwf H1s H2s H3s Hs. 
  simpl. unfold cps_cvt_apply. simpl.
  addContVarsSpec 3 Hs kv. repnd. clear Heqlvcvf.
  simpl in *.
  unfold KLam_c, Ret_c.
  do 4 f_equal.
  rwsimplC.
  do 3 (rewrite sub_filter_map_range_comm;
        rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2]).
  do 3 (rewrite (sub_find_none_if); 
          [| rwsimplC ; apply disjoint_singleton_l; disjoint_reasoningv2]).
  unfold Call_c.
  dLin_hyp. unfold App_e in Hs.
  rwsimpl  Hs.
  pose proof (size_pos e1).
  pose proof (size_pos e2).
  do 4 f_equal;[| do 5 f_equal];
    (apply Hind; auto; [try omega| ntwfauto | rwsimplC; try tauto]).
Qed.

Lemma cps_cvt_constr_subst_aux : forall sub,
sub_range_sat sub is_value (* can we get rid of this ?*)
-> sub_range_sat sub nt_wf
-> sub_range_sat sub closed
-> varsOfClass (dom_sub sub ++ flat_map all_vars (range sub)) true
->  forall lbt lkv c,
  (forall es, 
     (size es <  S (addl (map size_bterm lbt)))
      -> cps_ssubst_commutes es cps_cvt)
  -> length lbt = length lkv
  -> (forall b, LIn b lbt -> (bt_wf b /\ get_vars b = []))
    -> varsOfClass (flat_map all_vars_bt lbt) USERVAR 
    -> disjoint (lkv++free_vars c) (dom_sub sub)
   -> let sf := (map_sub_range (cps_cvt_val' cps_cvt) sub) in
     (ssubst_aux (cps_cvts' cps_cvt lkv lbt c)  sf)
       = cps_cvts' cps_cvt lkv  (map (fun t : BTerm => ssubst_bterm_aux t sub) lbt) 
              c.
Proof using.
  induction lbt as [| b lbt IHlbt]; intros ? ? Hyp Hl Hf Hvc Hd;
    simpl in Hl; dlist_len_name lkv kv;
      [ apply ssubst_aux_trivial_disj;
        autorewrite with SquiggleLazyEq;auto|].
  destruct b as [blv bnt].
  simpl in *.
  dLin_hyp. simpl in *. repnd. subst.
- rwsimplC.
  repeat progress (autorewrite with SquiggleLazyEq list in *; 
    simpl in * ).
  unfold Ret_c, KLam_c.
  do 3 f_equal;[|do 4 f_equal].
+ apply Hyp; auto;[ omega | ntwfauto | rwsimplC; tauto].
+ rewrite sub_filter_map_range_comm.
  rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2].
  rewrite IHlbt; simpl;
    autorewrite with SquiggleLazyEq list; eauto;
     [intros; apply Hyp; omega | tauto | disjoint_reasoningv ].
Qed.


Lemma eval_c_ssubst_aux_commute : forall (e : NTerm),
  cps_ssubst_commutes e cps_cvt.
Proof using.
Local Opaque is_valueb cps_cvt_val'.
  intros ?. unfold closed.
  induction e as [xx | o lbt Hind] using NTerm_better_ind3;
  intros ?  Hwf Hisv Hwfs Hcs  Hs;
  applydup userVarsContVar in Hs as Hdisvc; simpl in Hdisvc;
  [ | simpl; 
      setoid_rewrite (isvalueb_ssubst_aux (oterm o lbt) sub);
      [cases_if as Hd;[| destruct o; inverts Hwf as Hbt Hnb;
        [destruct c; inverts Hd| destruct n]; simpl in Hnb] | assumption] ].
(* variable case *)
Local Opaque   ssubst_aux.
Local Transparent is_valueb.
- simpl. rewrite cps_val_outer;[| rewrite isvalueb_ssubst_aux; auto; fail].
  rewrite val_outer_ssubst_aux;
    [| autorewrite with SquiggleLazyEq; disjoint_reasoningv2].
  f_equal. apply cps_cvt_val_ssubst_commutes_aux; auto. simpl.
  intros es ?. pose proof (size_pos es). omega.
(* value oterm *)
- 
Local Opaque is_valueb.
Local Transparent ssubst_aux.
  rewrite val_outer_ssubst_aux;
    [| autorewrite with SquiggleLazyEq; disjoint_reasoningv2].
  f_equal. apply cps_cvt_val_ssubst_commutes_aux; auto.
(* constructor*)
- simpl. unfold KLam_c. autorewrite with list SquiggleLazyEq. 
  do 3 f_equal. clear H0. clear Hdisvc.
  autorewrite with SquiggleLazyEq in *.
  simpl in *.
  repnd.
  apply' map_eq_repeat_implies Hnb.
  addContVarsSpec (S (Datatypes.length lbt)) Hs1 kv.
  simpl.
  rewrite sub_filter_map_range_comm.
  rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2].
  unfold num_bvars in Hnb.
  setoid_rewrite length_zero_iff_nil in Hnb.
  rewrite cps_cvt_constr_subst_aux; auto;
    [ rwsimplC; try tauto
      | simpl; rwsimplC; disjoint_reasoningv2].

Local Transparent is_valueb.

(* App_e *)
- dnumvbars Hnb bt.
  change ((cps_cvt_apply cps_cvt (cps_cvt btnt) btnt0))
    with (cps_cvt (App_e btnt btnt0)).
  rewrite cps_cvt_apply_ssubst_commutes_aux; auto; [|ntwfauto].
  simpl in *.
  intros. apply Hind. omega.
(* Proj_e *)
- dnumvbars Hnb bt. unfold num_bvars. simpl.
  addContVarsSpec 2 Hs kv. repnd. clear Heqlvcvf.
  simpl.
  rwsimplC.
  unfold KLam_c, Ret_c.
  do 4 f_equal.
  do 2 (rewrite sub_filter_map_range_comm;
        rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2]).
  do 2 (rewrite (sub_find_none_if); 
          [| rwsimplC ; apply disjoint_singleton_l; disjoint_reasoningv2]).
  do 2 f_equal.
  simpl in *.
  dLin_hyp.
  rwsimpl Hs.
  apply Hind; auto;[omega| ntwfauto | rwsimplC; tauto].

(* Let_e *)
- 
  dnumvbars Hnb bt.
  change (cps_cvt_apply cps_cvt (val_outer (cps_cvt_lambda cps_cvt btlv0 btnt0)) btnt)
    with (cps_cvt ((Let_e btlv0 btnt btnt0))).
  rewrite cps_cvt_let_as_app_lam.
  rwsimpl Hs.
  rewrite cps_cvt_apply_ssubst_commutes_aux; unfold Lam_e, App_e in *;
    simpl in *;auto;
    [ | intros; apply Hind; auto; omega 
      | ntwfauto 
      | rwsimplC; dands; try tauto].
  autorewrite with SquiggleLazyEq.
  refl.
- 
  dnumvbars Hnb bt. unfold num_bvars. simpl.
  addContVarsSpec 2 Hs kv. repnd. clear Heqlvcvf.
  simpl. unfold KLam_c, Ret_c.
  do 4 f_equal.
  rwsimplC.
  do 2 (rewrite sub_filter_map_range_comm;
        rewrite (sub_filter_disjoint1 sub); [|disjoint_reasoningv2]).
  do 1 (rewrite (sub_find_none_if); 
          [| rwsimplC ; apply disjoint_singleton_l; disjoint_reasoningv2]).
  simpl in *.
  dLin_hyp.
  rwsimpl Hs.
  do 2 f_equal;[| do 6 f_equal];
    [ apply Hind; auto;[omega| ntwfauto | rwsimplC; tauto] |].
  setoid_rewrite map_map.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  simpl.
  rwsimplC.
  rwsimpl Hcvdis.
  do 1 (rewrite (sub_find_none_if); 
          [| apply disjoint_singleton_l; 
            rewrite <- dom_sub_sub_filter;
            rwsimplC;apply disjoint_sym, disjoint_remove_nvars2; disjoint_reasoningv2]).
  unfold Ret_c.
  do 4 f_equal.
  rewrite sub_filter_map_range_comm.
  repnd.
  pose proof Hin as Hins.
  apply size_subterm4 in Hins.
  apply Hind; auto;[omega| ntwfauto | rwsimplC; dands; 
    unfold range, dom_sub, dom_lmap; eauto with subset].
Qed.


Lemma eval_c_ssubst_commute : forall (e : NTerm) (sub : Substitution) ,
nt_wf e
-> sub_range_sat sub is_value (* can we get rid of this ?*)
-> sub_range_sat sub nt_wf
-> sub_range_sat sub closed
-> varsOfClass (all_vars e ++ dom_sub sub ++ flat_map all_vars (range sub)) USERVAR
->  let sub_c := (map_sub_range (cps_cvt_val' cps_cvt)) sub in
      (ssubst (cps_cvt e) sub_c)= (cps_cvt (ssubst e sub)).
Proof using.
  intros.
  change_to_ssubst_aux8;[apply eval_c_ssubst_aux_commute; assumption|].
  subst sub_c.
  rewrite disjoint_flat_map_r.
  setoid_rewrite map_map.
  autorewrite with SquiggleLazyEq in H3. repnd.
  intros t Hin.
  apply in_map_iff in Hin.
  exrepnd.
  specialize (H0 _ _ Hin0).
  specialize (H1 _ _ Hin0).
  specialize (H2 _ _ Hin0).
  simpl in *.
  apply (f_equal free_vars) in Hin1.
  rewrite <- Hin1.
  apply in_sub_eta in Hin0. repnd.
  eapply varsOfClassSubset in H3;[| eapply subset_flat_map_r; eauto].
  rewrite cps_cvt_val_fvars; auto.
  rewrite H2.
  auto.
Qed.

  Local Transparent ssubst_bterm.
Local Transparent cps_cvt_val'.


(** What happens when e does not compute further, e.g. eval e e ? 
Should we prove something more about such cases, e.g. the CPS converted term
does not admit any evaluations in the user space?*)

Theorem cps_cvt_corr : forall e v,
  nt_wf e ->
  varsOfClass (all_vars e) USERVAR -> 
  eval e v ->
  closed e ->
  forall k, closed k ->
    forall v',
      eval_c (Ret_c (cps_cvt e) k) v' <->
        eval_c (Ret_c (cps_cvt v) k) v'.
Proof using.
  intros ? ? Hwf Hvc He.  induction He; try (simpl ; tauto; fail); [ | | | |]. 
  (* beta reduction case (eval_App_e) *)
- intros Hcle ? Hcl ?.
   unfold App_e in *. simpl.
   unfold cps_cvt_apply.
  repeat progress (autorewrite with list allvarsSimpl in Hvc; 
    simpl in Hvc).
  addContVarsSpec 3 Hvc kv.
  simpl.
  repnd.
  (* now lets fulfil the assumptions in the induction hypotheses *)
  unfold closed in Hcle. simpl in Hcle.
  autorewrite with core list in Hcle.
  apply app_eq_nil in Hcle.
  autorewrite with SquiggleLazyEq in *. repnd.
  specialize (IHHe1 ltac:(ntwfauto) Hvc0  Hcle0).
  specialize (IHHe2 ltac:(ntwfauto) Hvc Hcle).
  specialize (IHHe3 ltac:(apply' eval_preseves_wf He1; 
                      ntwfauto; eauto using eval_preseves_wf)).
  (* IHHe3 needs more work : 2 more hyps *)
  applydup (eval_preseves_varclass USERVAR) in He1 as Hvs1;[| assumption].
  applydup (eval_preseves_varclass USERVAR) in He2 as Hvs2;[| assumption].
  unfold Lam_e in Hvs1.
  rwsimpl Hvs1. repnd.
  dest_imp IHHe3 HH;[apply ssubst_allvars_varclass_nb;  rwsimplC; tauto|].

  (* IHHe3 has 1 more hyp *)
  pose proof (subset_step_app x e1' v2) as Hsss.
  simpl in IHHe3. unfold subst in IHHe3.
  applydup eval_reduces_fvars in He1 as Hss.
  applydup eval_reduces_fvars in He2 as Hss2.
  unfold subset in Hss, Hss2.
  rewrite Hcle0 in Hss. apply subsetv_nil_r in Hss.
  rewrite Hcle in Hss2. apply subsetv_nil_r in Hss2.
  simpl in Hss, Hsss.
  autorewrite with list core SquiggleLazyEq in *.
  rewrite Hss in Hsss.
  rewrite Hss2 in Hsss. simpl in Hsss.
  rewrite subsetv_nil_r in Hsss.
  dest_imp IHHe3 HH.
  rewrite <- IHHe3;[| assumption]. clear IHHe3.
  rewrite eval_ret.
  simpl. unfold subst. 
  assert (sub_range_sat [(kv, k)] closed) as Hcs by
    (intros ? ? ?; in_reasoning; cpx).
  rewrite ssubstRet_c by assumption.
  rewrite ssubstKlam_c; [| try assumption| noRepDis].
  rewrite ssubstRet_c by assumption.
  rewrite ssubstKlam_c; [| assumption| noRepDis].
  rewrite ssubstCall_c by assumption.
  do 3 rewrite ssubst_vterm. simpl.
  rewrite <- beq_var_refl.
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite ssubst_trivial2_cl;
    [|assumption|];
    [| unfold closed; symmetry;rewrite cps_cvt_aux_fvars; [| ntwfauto|]; 
       try rewrite Hcle0; [ tauto | eauto ]].
  rewrite ssubst_trivial2_cl;
    [|assumption|];
    [| unfold closed; symmetry;rewrite cps_cvt_aux_fvars; [| ntwfauto|]; 
       try rewrite Hcle; [ try tauto | eauto ]].

  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(contVar , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list core SquiggleLazyEq.
    symmetry.
    rewrite cps_cvt_aux_fvars;[| ntwfauto|]; try rewrite Hcle; [  | eauto ].
    simpl. rewrite Hcl. simpl.
    remove_nvars_r_simpl.
    autorewrite with SquiggleLazyEq.
    rewrite remove_nvars_nops;[| noRepDis].
    autorewrite with SquiggleLazyEq. refl.

  rewrite IHHe1; [| assumption]. simpl. clear IHHe1.
  unfold  val_outer, cps_cvt_lambda.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite ssubstRet_c by assumption.
  simpl ssubst at 1.
  rename Hcs into Hcsss.
  rename Hclk into Hclkk.
  autorewrite with SquiggleLazyEq.
  match goal with
  [|- context [Ret_c _ (ssubst ?k _)]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(kv0 , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list core SquiggleLazyEq.
    pose proof Hss as Hssb.
    apply null_iff_nil, null_remove_nvars_subsetv in Hss.
    symmetry.
    rewrite cps_cvt_aux_fvars;
      [| apply' eval_preseves_wf He1; ntwfauto; fail
       | tauto].
    simpl.
    rewrite remove_nvars_app_r.
    rewrite cons_as_app.
    repeat rewrite <- remove_nvars_app_l. rewrite remove_nvars_eq.
    rewrite remove_nvars_comm, Hssb. reflexivity.

  rewrite substLam_cTrivial2 by  assumption.
  rewrite ssubst_vterm. simpl.
  autorewrite with SquiggleLazyEq.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite ssubstRet_c by assumption.
  rewrite ssubstKlam_c; [| try assumption| noRepDis].
  rewrite ssubstCall_c by assumption.
  do 2 rewrite ssubst_vterm. simpl.
  rewrite <- beq_var_refl.
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite ssubst_trivial2_cl;[| assumption | 
      apply null_iff_nil; rewrite cps_cvt_aux_fvars; [ | ntwfauto|]; try rewrite Hcle; eauto].
  rewrite ssubst_trivial2_cl;[| assumption | assumption].
  clear Hcs.
  rename Hclk into Hclkb.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(fresh_var [] , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed.
    match type of Hclkb with
    closed ?k => remember k as kr
    end.
    simpl. autorewrite with list core SquiggleLazyEq.
    rewrite Hclkb, Hcl. simpl.
    rewrite remove_nvars_eq. reflexivity.
  
  clear Hcs.
  rewrite IHHe2 by assumption. clear IHHe2.
  pose proof (cps_val v2) as Hv.
  simpl in Hv.
  dest_imp Hv Hvv;[eauto using eval_yields_value'|].
  rewrite Hv. clear Hv.
  rename Hclk into Hclk3b.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [assumption |  assert (sub_range_sat [(contVar , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
  rewrite eval_ret. simpl. unfold subst. 
  rewrite ssubstRet_c by assumption.
  rewrite ssubst_vterm. simpl.
  assert (closed (cps_cvt_val' cps_cvt v2)) as Hc2v by 
    (ntwfauto; eauto using cps_cvt_val_closed, eval_preseves_wf).
  rewrite ssubst_trivial2_cl; [| assumption | 
    try assumption
      ].
  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?kk]] => 
      assert (sub_range_sat [(kv1 , kk)] closed)
       as Hcs by
        (intros ? ? ?; in_reasoning; cpx)
  end.

  autorewrite with SquiggleLazyEq.
  rewrite eval_ret.
  simpl. unfold subst.
  rewrite ssubstCall_c by assumption.
  rewrite ssubst_vterm. simpl ssubst_aux.
  rewrite <- beq_var_refl. 
  do 2 (rewrite ssubst_trivial2_cl;[| assumption | 
    assumption
      ]).
  rewrite eval_call. simpl.
  unfold subst.
  autorewrite with SquiggleLazyEq.
  rewrite ssubstRet_c.
  applydup userVarsContVar in Hvs0.
  rewrite <- ssubst_sub_filter2 with (l:=[contVar]).
  Focus 3. 
    rewrite cps_cvt_aux_fvars;
       [apply userVarsContVar in Hvs1; disjoint_reasoningv
         |(apply' eval_preseves_wf He1; 
                      ntwfauto) 
        | assumption].

  Focus 2. unfold disjoint_bv_sub.
     intros ? ? Hin.
     repeat in_reasoning; inverts Hin; try rewrite Hc2v;
     try rewrite Hcl; auto.
  rewrite ssubst_vterm. simpl.
  autorewrite with SquiggleLazyEq.
  rewrite not_eq_beq_var_false;[| apply disjoint_neq; disjoint_reasoning2].
  rewrite <- (eval_c_ssubst_commute);[refl
     | apply' eval_preseves_wf He1; 
                      ntwfauto; eauto using eval_preseves_wf
     | | | | rwsimplC; try tauto ]; 
    intros ? ? Hin; rewrite in_single_iff in Hin;
    inverts Hin; subst;auto;
        [eapply eval_yields_value'; eauto
        | ntwfauto; eauto using eval_preseves_wf].

(* reduction inside constructor : eval_Con_e *)
- admit.

(* eval_Let_e *)
- admit.

(* eval_Match_e *)
- admit.

(* eval_Proj_e *)
- admit.
Admitted.



(** 
** Evaluation of CPS converted terms respects alpha equality. *
*
* It was needed when CPS conversion picked contiuation variables based on the
variables in the given user term.
Free variables and bound variables of a term may change during evaluation, and hence,
different continuation variables were picked by CPS conversion 
in the proof [cps_cvt_corr] above. Therefore, reasoning about alpha equality was needed to resolve the mismatch.
It was hard to prove that when CPS conversion is forced to pick different variables while converting the same term,
the results are respectively alpha equal. CPS conversion has too many cases, and unlike many other proofs
about substitution and alpha equality, this proof could not be done generically.
A partially completed proof was done in the CPSAlphaVarChoice branch of git.

Now that we have a separate class of variables for continuation variables, that mismatch does not
arise. Nevertheless, the proof that evaluation of CPS converted terms respects alpha equality,
 which has mostly been revived, except for the last case
of [eval_c_respects_α] below, may be useful if we need to change variables 
(e.g. to achieve Barendregt convetion) after CPS conversion.
*)

(** unlike [eval_c], this relation supports rewriting with alpha equality.
    rewritability at the 2nd argument is obvious. the lemma [eval_c_respects_α] below
    enables rewriting at the 1st argument *)
Definition eval_cα (a b : CTerm):= exists bα,
  eval_c a bα /\ alpha_eq b bα.


Definition defbranch : (@branch CPSGenericTermSig) := (0%N, bterm [] (vterm nvarx)).

Lemma match_c_alpha : forall brs discriminee t2,
alpha_eq (Match_c discriminee brs) t2
-> exists discriminee2, exists brs2,
t2= (Match_c discriminee2 brs2)
/\ alpha_eq discriminee discriminee2.
Proof using.
  intros ? ? ? Hal.
  inverts Hal. simpl in *.
  dlist_len_name lbt2 lb. 
  pose proof (H3 0 ltac:(omega)) as Hd.
  repeat rewrite selectbt_cons in Hd. simpl in Hd.
  repeat alphahypsd3.
  exists nt2.
  exists (combine (map fst brs) lbt2).
  split; [| assumption].
  unfold Match_c. rewrite map_length in *.
  f_equal; f_equal;
    [ f_equal
      |rewrite <- snd_split_as_map, combine_split; try rewrite map_length; auto].
  apply eq_maps2 with (defa := defbranch) (defc := defbranch);
    [rewrite length_combine_eq; rewrite map_length; auto|].
  intros ? ?.
  specialize (H3 (S n) ltac:(omega)).
  repeat rewrite selectbt_cons in H3. simpl in H3.
  replace (n-0) with n in H3 by omega.
  apply alphaeqbt_numbvars in H3.
  unfold defbranch.
  rewrite combine_nth;[| rewrite map_length; auto].
  simpl.
  f_equal.
-  rewrite <- (map_nth fst). refl.
-  rewrite <- (map_nth snd). simpl. assumption.
Qed.


Lemma con_c_alpha : forall d vs t2,
alpha_eq (Con_c d vs) t2
-> exists vs2, t2 = (Con_c d vs2) /\ bin_rel_nterm alpha_eq vs vs2.
Proof using.
  intros ? ? ? Hal.
  apply alpha_eq_bterm_nil in Hal.
  exrepnd. subst.
  eexists. split;[| apply Hal0].
  destruct Hal0.
  unfold Con_c. rewrite H. reflexivity.
Qed.




(* this lemma would have been needed anyway when variables are changed after CPS 
conversion, in order to make them distinct *)

Lemma eval_c_respects_α : 
  forall a b, 
    eval_c a b
    -> forall aα,
        alpha_eq a aα
        -> exists bα, eval_c aα bα /\ alpha_eq b bα.
Proof using.
  intros ? ? He.
  induction He; intros ? Ha.
(* eval_Halt_c*)
- inverts Ha as Hl Hb. simpl in *.  repeat alphahypsd3.
  eexists. split;[constructor| assumption].

(* eval_Ret_c*)
- inverts Ha as Hl Hb. simpl in *.  repeat alphahypsd3.
  clear Hb.
  inverts Hb0bt0. simpl in *. repeat alphahypsd3. 
  clear H30bt2 H30bt0. 
  rename H3 into Hbb.
  specialize (Hbb 0 ltac:(simpl; omega)).
  repeat rewrite selectbt_cons in Hbb.
  simpl in Hbb.
  eapply apply_bterm_alpha_congr  with (lnt1:=[v]) (lnt2:=[nt2]) in Hbb;
    auto;[| prove_bin_rel_nterm ].
  apply IHHe in Hbb. exrepnd.
  eexists. split; [constructor; apply Hbb1| assumption].

(* eval_Call_c*)
- inverts Ha. simpl in *. repeat alphahypsd3. clear H3.
  inverts H30bt0. simpl in *. repeat alphahypsd3.
  rename H3 into Hbb.
  specialize (Hbb 0 ltac:(simpl; omega)).
  repeat rewrite selectbt_cons in Hbb.
  eapply apply_bterm_alpha_congr  with (lnt1:=[v2, v1]) (lnt2:=[nt2, nt0]) in Hbb;
    auto;[| prove_bin_rel_nterm ].
  apply IHHe in Hbb. exrepnd.
  eexists. split; [constructor; apply Hbb1| assumption].

(* eval_Match_c*)
- pose proof Ha as Hab.
  (* Branches of the matches are respectively alpha equal. So is the discriminee *)
  apply match_c_alpha in Ha.
  exrepnd. subst.
  (* Arguments of the constructor in the discriminees are respectively alpha equal *)
  apply con_c_alpha in Ha1.
  exrepnd. subst.
  inverts Hab as Hl Hbt Hmap. unfold find_branch in H.
  revert H.

  (* find_branch will succeed, and the resultant branch will have the same index.
    find_branch makes it selection based on properties that are preserved by alpha equality.
    Thus the picked branch in both cases are alpha equal *)
  destFind;  intro Hbr; [| inverts Hbr].
  eapply list_find_same_compose 
    with (g := fun p => decide ((d, Datatypes.length vs) = p))
        (def:=defbranch)
      in Heqsn;[ | | apply Hmap];[|intros a; destruct a; simpl; refl].
  clear Hmap Heqsnl.
  exrepnd. simpl in Hl, Hbt. rewrite Hl in Hbt. clear Hl.
  destruct bss as [dc b]. inverts Hbr.
  simpl in Hbt. rewrite map_length in Hbt.
  apply lt_n_S in Heqsn1.
  specialize (Hbt (S n) Heqsn1). clear Heqsn1.
  repeat rewrite selectbt_cons in Hbt.
  simpl in Hbt.
  replace (n-0) with n in Hbt by omega.
  unfold selectbt in Hbt. 
  repeat rewrite map_nth with (d := defbranch) in Hbt.
  repeat rewrite @Decidable_spec in *. 
  inverts Heqsn4.
  inverts Heqsn0.
  rewrite <- Heqsn3 in Hbt.

  (* substuting alpha equal constructor args into alpha equal branches results 
    in alpha equal terms*)
  eapply apply_bterm_alpha_congr in  Hbt;
    [| apply Ha0|  auto].
  simpl in Hbt.

  (* use the induction hypothesis *)
  eapply IHHe in Hbt.
  exrepnd.
  eexists. split;[ | apply Hbt0].
  econstructor;[| apply Hbt1].
  unfold find_branch.
  apply proj1 in Ha0.
  rewrite <- Ha0.
  rewrite Heqsn2.
  refl.

(* eval_Proj_c *)
- inverts Ha as Hl Hbt.
  simpl in *. repeat alphahypsd3.
  clear Hbt. pose proof Hbt0bt0 as Halb.
  inverts Hbt0bt0 as Hlf Hbtf.
  rewrite Hlf.
  pose proof H as Hl.
  rewrite Hlf in Halb.
  apply select_lt in Hl.
  specialize (Hbtf _ Hl).
  apply select_selectbt, proj1 in H.
  rewrite H in Hbtf.
  pose proof Hbtf as Hn. hide_hyp Hbtf.
  repeat alphahypsd3. 
  show_hyp Hbtf.
  rewrite Hn1 in Hbtf.
  match type of Halb with
    alpha_eq ?l ?r=>
      apply apply_bterm_alpha_congr with (lnt1 := [l]) (lnt2 := [r]) in Hbtf;
        [| prove_bin_rel_nterm | simpl; auto  ]
  end.
  match type of Hbtf with
    alpha_eq ?l ?r=>
      assert (alpha_eq (Ret_c k l) (Ret_c nt2 r)) as Hal
        by (unfold Ret_c; repeat prove_alpha_eq4)
  end.
  apply IHHe in Hal.
  exrepnd.
  eexists. split;[ | apply Hal0].
  pose proof (conj Hn1 Hl) as Hs. rewrite Hlf in Hs.
  apply select_selectbt in Hs.

  (* prove a general lemma in certicoq about [Hn0] *)
  (* nt0 must be a lambda for fix to reduce. because nt0 is alpha equal to a lambda,
    we can show that nt0 also must be a lamda *)
(*  Local Opaque ssubst_bterm.
  simpl in Hn0.
  inverts Hn0 as Hnt Hnt2 Hnt3.
  destruct nt0;
   [apply isvarc_ssubst_ot in Hnt3; auto with SquiggleLazyEq;contradiction|].
  simpl in Hnt3. inverts Hnt3.
  specialize (Hnt2 0 ltac:(simpl; omega)).
  simpl in *.
  destruct l;[inverts Hnt|].
  destruct l;[|inverts Hnt].
  clear Hnt. simpl in Hnt2.
  do 2 rewrite selectbt_cons in Hnt2.
  simpl in Hnt2. destruct b0 as [lvl ntl].
  apply alphaeqbt_numbvars in Hnt2.
  (* FIX : fold ssubst_bterm. Some tactics seem to be ignoring its opacity *)
  do 2 rewrite num_bvars_ssubst_bterm in Hnt2.
  unfold num_bvars in Hnt2.
  simpl in Hnt2.
  dlist_len_name lvl lvl.
  econstructor; eauto. *)
Abort.

(*
Print Assumptions eval_c_respects_α.
Closed under the global context
*)

Require Import Coq.Classes.Morphisms.

(*
Global Instance eval_cα_proper :
  Proper (alpha_eq ==> alpha_eq ==> iff) eval_cα.
Proof using.
  intros ? ? H1eq ? ? H2eq. unfold eval_cα.
  split; intro H; exrepnd;
  apply' eval_c_respects_α  H1;
  try apply H1 in H1eq; try symmetry in H1eq;
  try apply H1 in H1eq; exrepnd; clear H1;
  eexists; split; eauto.
  - rewrite <- H1eq0, <- H2eq. assumption.
  - rewrite <- H1eq0, H2eq. assumption.
Qed.
*)


(** Useful for rewriting. *)
Lemma eval_retα :
  forall x c v v', eval_cα (Ret_c (KLam_c x c) v) v' 
  <-> eval_cα (c{x := v}) v'.
Proof using.
  unfold eval_cα; intros; split ; intro; exrepnd; eexists; eauto.
  inversion H1. subst. eexists; eauto.
Qed.

(** Useful for rewriting. *)
Lemma eval_callα : forall xk x c v1 v2 v',
   eval_cα (Call_c (Lam_c x xk c) v1 v2) v'
  <-> eval_cα (ssubst c [(x,v2);(xk,v1)]) v'.
Proof using.
  unfold eval_cα; intros; split ; intro; exrepnd; eexists; eauto.
  inversion H1. subst. eexists; eauto.
Qed.

Global Instance proper_retcα : Proper  (alpha_eq ==> alpha_eq ==> alpha_eq) Ret_c.
Proof using.
  intros ? ? Hal1 ? ? Hal2.
  constructor; auto. simpl.
  prove_alpha_eq4; unfold selectbt; simpl;[| | omega];
  prove_alpha_eq4; assumption.
Qed.

End VarsOf2Class.